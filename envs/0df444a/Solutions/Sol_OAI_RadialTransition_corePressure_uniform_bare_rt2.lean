-- Prove2me | solution 1 for OAI.RadialTransition.corePressure_uniform_bare_rt2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:23.984699+00:00
-- url     : https://prove2.me/submissions/0c1547da-b81b-4240-813f-045b07cc8160

import Mathlib
import Definitions.Def_RadialTransition
import Definitions.Def_OAIQ112R000

section
-- module Solutions.OAIQ112_RT.Compat
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uIndex uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section Shell

theorem independent_of_simplex_gram
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (v : ι → E) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : (Fintype.card ι : ℝ) * ε < 1 / 2)
    (hgram : ∀ i j,
      |inner ℝ (v i) (v j) - ((1 : ℝ) / 2 + if i = j then 1 / 2 else 0)| ≤ ε) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let S : ℝ := ∑ j, c j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (c j)
  have hCS : (∑ j, |c j|) ^ 2 ≤ (Fintype.card ι : ℝ) * S := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |c j|))
  have hterm (j k : ι) :
      c j * c k * ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0) -
        ε * |c j| * |c k| ≤ c j * c k * inner ℝ (v j) (v k) := by
    have hh : |c j * c k * (inner ℝ (v j) (v k) -
        ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0))| ≤ ε * |c j| * |c k| := by
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hgram j k)
        (mul_nonneg (abs_nonneg (c j)) (abs_nonneg (c k)))]
    have hh' := (abs_le.mp hh).1
    nlinarith [hh']
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) fun k _ => hterm j k
  have hlin : (∑ j, ∑ k, c j * c k * inner ℝ (v j) (v k)) = 0 := by
    have hh : inner ℝ (∑ j, c j • v j) (∑ j, c j • v j) = 0 := by rw [hc]; simp
    simpa only [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm, real_inner_comm] using hh
  have href : (∑ j, ∑ k,
      c j * c k * ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0)) =
      (1 / 2 : ℝ) * (∑ j, c j) ^ 2 + (1 / 2 : ℝ) * S := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    simp only [S, sq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have herr : (∑ j, ∑ k, ε * |c j| * |c k|) = ε * (∑ j, |c j|) ^ 2 := by
    simp only [sq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    ext j
    congr 1
    ext k
    ring
  simp only [Finset.sum_sub_distrib] at hsum
  rw [hlin, href, herr] at hsum
  have hSzero : S = 0 := by
    have he := mul_le_mul_of_nonneg_left hCS hε
    nlinarith [sq_nonneg (∑ j, c j)]
  have hci : c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hSzero i
      (Finset.mem_univ i)
  nlinarith [hci]

theorem no_five_unit_shell (x : Fin 5 → Position)
    (hx : ∀ i j, i ≠ j → 1 ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ 1 + (1 : ℝ) / 1000) : False := by
  let v : Fin 4 → Position := fun i => x i.succ - x 0
  have hsq (i j : Fin 5) (hij : i ≠ j) :
      1 ≤ ‖x i - x j‖ ^ 2 ∧ ‖x i - x j‖ ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 := by
    have h := hx i j hij
    rw [dist_eq_norm] at h
    constructor <;> nlinarith [h.1, h.2]
  have hnorm (i : Fin 4) :
      1 ≤ ‖v i‖ ^ 2 ∧ ‖v i‖ ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 :=
    hsq i.succ 0 (Fin.succ_ne_zero i)
  have hgram (i j : Fin 4) :
      |inner ℝ (v i) (v j) - ((1 : ℝ) / 2 + if i = j then 1 / 2 else 0)| ≤
      (2001 / 1000000 : ℝ) := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
      have h := hnorm i
      rw [abs_le]
      constructor <;> nlinarith [h.1, h.2]
    · rw [ite_eq_right hij, add_zero, abs_le]
      have hi := hnorm i
      have hj := hnorm j
      have hd := hsq i.succ j.succ (by simpa using hij)
      have heq : v i - v j = x i.succ - x j.succ := by simp [v]
      have hp := norm_sub_sq_real (v i) (v j)
      rw [heq] at hp
      constructor <;> nlinarith [hi.1, hi.2, hj.1, hj.2, hd.1, hd.2, hp]
  have hind := independent_of_simplex_gram v (by norm_num : (0 : ℝ) ≤ 2001 / 1000000)
    (by norm_num : (Fintype.card (Fin 4) : ℝ) * (2001 / 1000000) < 1 / 2) hgram
  have hdim := hind.fintype_card_le_finrank
  norm_num [Position, finrank_euclideanSpace] at hdim

theorem no_five_shell (x : Fin 5 → Position) {l : ℝ} (hl : 0 < l)
    (hx : ∀ i j, i ≠ j → l ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ (1 + (1 : ℝ) / 1000) * l) : False := by
  apply no_five_unit_shell (fun i => l⁻¹ • x i)
  intro i j hij
  have h := hx i j hij
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hl.le)
    simpa [ne_of_gt hl] using hh
  · have hh := mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr hl.le)
    calc
      l⁻¹ * dist (x i) (x j) ≤ l⁻¹ * ((1 + (1 : ℝ) / 1000) * l) := hh
      _ = 1 + (1 : ℝ) / 1000 := by field_simp

theorem shellGraph_cliqueFree {V : Type uV} (x : V → Position) {l : ℝ} (hl : 0 < l) :
    (shellGraph x l).CliqueFree 5 := by
  classical
  intro s hs
  let e : Fin 5 ≃ s := (Finset.equivFinOfCardEq hs.card_eq).symm
  apply no_five_shell (fun i => x (e i)) hl
  intro i j hij
  have hne : (e i : V) ≠ (e j : V) := fun h => hij (e.injective (Subtype.ext h))
  have hh := hs.isClique (e i).property (e j).property hne
  exact hh.2

end Shell

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoundedCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _
theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
theorem clamp01_eq_zero {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  exact max_eq_left (le_trans (min_le_right _ _) hx)
theorem clamp01_eq_one {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  simp [clamp01, min_eq_left hx]
theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

theorem shellStep_pos (t : ℝ) : 0 < shellStep t := div_pos (microLength_pos t) (by norm_num)

theorem coreReal_nonneg (t r : ℝ) : 0 ≤ coreReal t r := by
  apply mul_nonneg (sq_nonneg t)
  apply le_min
  · linarith [clamp01_le_one ((r - microLength t) / shellStep t),
      clamp01_nonneg ((r - microLength t - 2 * shellStep t) / shellStep t)]
  · exact clamp01_nonneg _

theorem coreReal_le (t r : ℝ) : coreReal t r ≤ t ^ 2 := by
  have hh : min
      (1 - clamp01 ((r - microLength t) / shellStep t) +
        clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t))
      (clamp01 (1 + t * (1 - r))) ≤ 1 :=
    (min_le_right _ _).trans (clamp01_le_one _)
  simpa only [coreReal, mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg t)

theorem continuous_coreReal (t : ℝ) : Continuous (coreReal t) := by
  unfold coreReal
  exact continuous_const.mul
    (((continuous_const.sub (continuous_clamp01.comp
      ((continuous_id.sub continuous_const).div_const _))).add
      (continuous_clamp01.comp
        (((continuous_id.sub continuous_const).sub continuous_const).div_const _))).min
      (continuous_clamp01.comp
        (continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id)))))

theorem continuous_corePotential (t : ℝ) : Continuous (corePotential t) :=
  (continuous_coreReal t).comp NNReal.continuous_coe

theorem bounded_corePotential (t : ℝ) : IsBoundedPotential (corePotential t) := by
  refine ⟨t ^ 2, sq_nonneg t, fun r => ?_⟩
  change |coreReal t r| ≤ t ^ 2
  rw [abs_of_nonneg (coreReal_nonneg t r)]
  exact coreReal_le t r

theorem coreReal_zero_plateau (t r : ℝ)
    (hlo : microLength t + shellStep t ≤ r)
    (hhi : r ≤ microLength t + 2 * shellStep t) : coreReal t r = 0 := by
  have hd := shellStep_pos t
  have hdown : clamp01 ((r - microLength t) / shellStep t) = 1 :=
    clamp01_eq_one ((le_div_iff₀ hd).mpr (by linarith))
  have hup : clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) = 0 :=
    clamp01_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  simp only [coreReal, hdown, hup, sub_self, add_zero,
    min_eq_left (clamp01_nonneg _), mul_zero]

theorem coreReal_zero_outer {t r : ℝ} (ht : 0 < t) (hr : 1 + 1 / t ≤ r) :
    coreReal t r = 0 := by
  have hc : clamp01 (1 + t * (1 - r)) = 0 := by
    apply clamp01_eq_zero
    have hm := mul_le_mul_of_nonneg_left hr ht.le
    have hd := div_mul_cancel₀ (1 : ℝ) (ne_of_gt ht)
    nlinarith [hm, hd]
  have hs : 0 ≤ 1 - clamp01 ((r - microLength t) / shellStep t) +
      clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) := by
    linarith [clamp01_le_one ((r - microLength t) / shellStep t),
      clamp01_nonneg ((r - microLength t - 2 * shellStep t) / shellStep t)]
  simp only [coreReal, hc, min_eq_right hs, mul_zero]

theorem coreReal_full_left {t r : ℝ} (ht : 0 ≤ t)
    (hl : r ≤ microLength t) (hr : r ≤ 1) : coreReal t r = t ^ 2 := by
  have hd := shellStep_pos t
  have hdown : clamp01 ((r - microLength t) / shellStep t) = 0 :=
    clamp01_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  have hup : clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) = 0 :=
    clamp01_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  have hc : clamp01 (1 + t * (1 - r)) = 1 :=
    clamp01_eq_one (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hr)])
  simp [coreReal, hdown, hup, hc]

theorem coreReal_full_right {t r : ℝ} (ht : 0 ≤ t)
    (hl : microLength t + 3 * shellStep t ≤ r) (hr : r ≤ 1) :
    coreReal t r = t ^ 2 := by
  have hd := shellStep_pos t
  have hdown : clamp01 ((r - microLength t) / shellStep t) = 1 :=
    clamp01_eq_one ((le_div_iff₀ hd).mpr (by linarith))
  have hup : clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) = 1 :=
    clamp01_eq_one ((le_div_iff₀ hd).mpr (by linarith))
  have hc : clamp01 (1 + t * (1 - r)) = 1 :=
    clamp01_eq_one (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hr)])
  simp [coreReal, hdown, hup, hc]

theorem coreReal_full_of_not_shell {t r : ℝ} (ht : 0 ≤ t) (hr : r ≤ 1)
    (hs : ¬(microLength t ≤ r ∧ r ≤ (1 + (1 : ℝ) / 1000) * microLength t)) :
    coreReal t r = t ^ 2 := by
  by_cases hlo : microLength t ≤ r
  · apply coreReal_full_right ht ?_ hr
    have hhi : (1 + (1 : ℝ) / 1000) * microLength t < r :=
      lt_of_not_ge (fun hh => hs ⟨hlo, hh⟩)
    dsimp [shellStep]
    linarith [hhi]
  · exact coreReal_full_left ht (le_of_not_ge hlo) hr

theorem twice_pair_sum {N : ℕ} (F : Fin N → Fin N → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    2 * (∑ i, ∑ j with i < j, F i j) =
      ∑ i, ∑ j, if i ≠ j then F i j else 0 := by
  classical
  simp only [Finset.sum_filter]
  have hswap : (∑ i, ∑ j, if j < i then F i j else 0) =
      ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF j i]
  calc
    2 * (∑ i, ∑ j, if i < j then F i j else 0) =
      (∑ i, ∑ j, if i < j then F i j else 0) +
      (∑ i, ∑ j, if j < i then F i j else 0) := by rw [hswap]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_ge h.le]
      · simp [h]
      · simp [h, ne_of_gt h, not_lt_of_ge h.le]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem dist_lt_one_of_coordinate_half {x y : Position}
    (h : ∀ k : Fin 3, |x k - y k| < 1 / 2) : dist x y < 1 := by
  have hh : dist x y ^ 2 < 1 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hc (k : Fin 3) : dist (x k) (y k) ^ 2 < (1 / 4 : ℝ) := by
      rw [Real.dist_eq]
      have hp := h k
      nlinarith [abs_nonneg (x k - y k)]
    have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      Finset.univ_nonempty (fun k _ => hc k)
    norm_num at hs
    linarith
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem packing_card_bound {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  classical
  let f : X → (Fin 3 → Fin (⌊2 * L⌋₊ + 1)) := fun x k =>
    ⟨⌊2 * (x : Position) k⌋₊,
      Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [(hX.1 x x.property k).2]))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : Position) ≠ y := fun h => hne (Subtype.ext h)
    have hlo := hX.2 x x.property y y.property hne'
    have hhi : dist (x : Position) y < 1 := by
      apply dist_lt_one_of_coordinate_half
      intro k
      have he : ⌊2 * (x : Position) k⌋₊ = ⌊2 * (y : Position) k⌋₊ :=
        congrArg Fin.val (congrFun hxy k)
      have hx0 := (hX.1 x x.property k).1
      have hy0 := (hX.1 y y.property k).1
      have hxL := Nat.floor_le (show 0 ≤ 2 * (x : Position) k by positivity)
      have hyL := Nat.floor_le (show 0 ≤ 2 * (y : Position) k by positivity)
      have hxU := Nat.lt_floor_add_one (2 * (x : Position) k)
      have hyU := Nat.lt_floor_add_one (2 * (y : Position) k)
      rw [he] at hxL hxU
      apply abs_lt.mpr
      constructor <;> linarith
    linarith
  simpa using Fintype.card_le_of_injective f hf

theorem packing_card_set_bddAbove (L : ℝ) :
    BddAbove {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X} := by
  refine ⟨(⌊2 * L⌋₊ + 1) ^ 3, ?_⟩
  rintro n ⟨X, rfl, hX⟩
  exact packing_card_bound hX

theorem packingNumber_attained (L : ℝ) :
    ∃ X : Finset Position, X.card = packingNumber L ∧ IsPacking L X := by
  exact Nat.sSup_mem (s := {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X})
    ⟨0, ∅, by simp [IsPacking]⟩ (packing_card_set_bddAbove L)

theorem packing_card_le {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ packingNumber L :=
  le_csSup (packing_card_set_bddAbove L) ⟨X, rfl, hX⟩

theorem packingNumber_bound (L : ℝ) :
    packingNumber L ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained L
  simpa only [hcard] using packing_card_bound hX

theorem packingNumber_pos {L : ℝ} (hL : 0 ≤ L) : 0 < packingNumber L := by
  have hh : IsPacking L {0} := by
    constructor
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst x
      intro k
      simp [hL]
    · intro x hx y hy hne
      simp only [Finset.mem_singleton] at hx hy
      exact (hne (hx.trans hy.symm)).elim
  have := packing_card_le hh
  simp only [Finset.card_singleton] at this
  omega

theorem packingTranslate_mem_cube {n : ℕ} {s L : ℝ} (hs : 0 ≤ s)
    (hn : (n : ℝ) * (s + 1) ≤ L) (j : Fin 3 → Fin n)
    {x : Position} (hx : x ∈ cube s) : packingTranslate s j x ∈ cube L := by
  intro k
  have hj : (j k : ℝ) + 1 ≤ n := by exact_mod_cast (j k).isLt
  have hj0 : 0 ≤ (j k : ℝ) := by positivity
  have hx0 : 0 ≤ x k := (hx k).1
  have hh := mul_le_mul_of_nonneg_right hj (show 0 ≤ s + 1 by linarith)
  simp only [packingTranslate_apply]
  constructor
  · positivity
  · linarith [(hx k).2]

theorem packingTranslate_dist_same {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n)
    (x y : Position) : dist (packingTranslate s j x) (packingTranslate s j y) = dist x y := by
  simp only [dist_eq_norm]
  congr 1
  ext k
  simp only [PiLp.sub_apply, packingTranslate_apply]
  ring

theorem packingTranslate_separated {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {j k : Fin 3 → Fin n} (hjk : j ≠ k) {x y : Position}
    (hx : x ∈ cube s) (hy : y ∈ cube s) :
    1 ≤ dist (packingTranslate s j x) (packingTranslate s k y) := by
  have hcoord {j k : Fin 3 → Fin n} {x y : Position}
      (hx : x ∈ cube s) (hy : y ∈ cube s) (q : Fin 3) (h : j q < k q) :
      1 ≤ dist (packingTranslate s j x) (packingTranslate s k y) := by
    have hq : (j q : ℝ) + 1 ≤ (k q : ℝ) := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ s + 1 by linarith)
    have hlo : 1 ≤ packingTranslate s k y q - packingTranslate s j x q := by
      simp only [packingTranslate_apply]
      linarith [(hx q).2, (hy q).1]
    have hnorm := PiLp.norm_apply_le (packingTranslate s k y - packingTranslate s j x) q
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at hnorm
    calc
      1 ≤ packingTranslate s k y q - packingTranslate s j x q := hlo
      _ ≤ |packingTranslate s k y q - packingTranslate s j x q| := le_abs_self _
      _ ≤ ‖packingTranslate s k y - packingTranslate s j x‖ := hnorm
      _ = dist (packingTranslate s j x) (packingTranslate s k y) := by rw [← dist_eq_norm, dist_comm]
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hjk
  rcases lt_or_gt_of_ne hq with h | h
  · exact hcoord hx hy q h
  · simpa only [dist_comm] using hcoord hy hx q h

theorem packingNumber_replication {s L : ℝ} (hs : 0 ≤ s) (n : ℕ)
    (hn : (n : ℝ) * (s + 1) ≤ L) :
    n ^ 3 * packingNumber s ≤ packingNumber L := by
  classical
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained s
  let f : (Fin 3 → Fin n) × X → Position := fun a => packingTranslate s a.1 a.2
  have hsep (a b : (Fin 3 → Fin n) × X) (hab : a ≠ b) : 1 ≤ dist (f a) (f b) := by
    by_cases hj : a.1 = b.1
    · have hx : (a.2 : Position) ≠ b.2 := by
        intro hx
        apply hab
        exact Prod.ext hj (Subtype.ext hx)
      dsimp [f]
      rw [hj, packingTranslate_dist_same]
      exact hX.2 _ a.2.property _ b.2.property hx
    · exact packingTranslate_separated hs hj (hX.1 _ a.2.property) (hX.1 _ b.2.property)
  have hfinj : Function.Injective f := by
    intro a b h
    by_contra hab
    have := hsep a b hab
    norm_num [h] at this
  let Y := Finset.univ.image f
  have hYcard : Y.card = n ^ 3 * packingNumber s := by
    rw [Finset.card_image_of_injective _ hfinj]
    simp [hcard]
  have hY : IsPacking L Y := by
    constructor
    · intro y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      exact packingTranslate_mem_cube hs hn a.1 (hX.1 _ a.2.property)
    · intro y hy z hz hyz
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
      exact hsep a b (fun hab => hyz (congrArg f hab))
  rw [← hYcard]
  exact packing_card_le hY

theorem packing_ratio_bound {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ 8 := by
  have hc : (packingNumber s : ℝ) ≤ ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 := by
    exact_mod_cast packingNumber_bound s
  have hf := Nat.floor_le (show 0 ≤ 2 * s by positivity)
  have hg : ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := by
    gcongr
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (s + 1) ^ 3)).mpr
  nlinarith [hc.trans hg]

theorem packing_ratios_bdd :
    BddAbove {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3} := by
  refine ⟨8, ?_⟩
  rintro r ⟨s, hs, rfl⟩
  exact packing_ratio_bound hs

theorem packing_ratios_nonempty :
    ({r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3}).Nonempty :=
  ⟨_, 0, le_rfl, rfl⟩

theorem packing_ratio_le_density {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ packingDensity :=
  le_csSup packing_ratios_bdd ⟨s, hs, rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have h := packing_ratio_le_density (s := 0) le_rfl
  have hp : (0 : ℝ) < packingNumber 0 := by exact_mod_cast packingNumber_pos (L := 0) le_rfl
  norm_num at h
  exact hp.trans_le h

theorem packing_lower_approximation {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun L : ℝ => ((⌊L / (s + 1)⌋₊ : ℝ) / L) ^ 3 * packingNumber s)
      atTop (nhds ((packingNumber s : ℝ) / (s + 1) ^ 3)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ (s + 1)⁻¹ by positivity)).pow 3
  have h' := h.mul_const (packingNumber s : ℝ)
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using h'

theorem packing_lower_approximation_le {s L : ℝ} (hs : 0 ≤ s) (hL : 0 < L) :
    ((⌊L / (s + 1)⌋₊ : ℝ) / L) ^ 3 * packingNumber s ≤
      (packingNumber L : ℝ) / L ^ 3 := by
  have hn : (⌊L / (s + 1)⌋₊ : ℝ) * (s + 1) ≤ L := by
    apply (le_div_iff₀ (by positivity : 0 < s + 1)).mp
    exact Nat.floor_le (by positivity)
  have h := packingNumber_replication hs ⌊L / (s + 1)⌋₊ hn
  have hr : (⌊L / (s + 1)⌋₊ : ℝ) ^ 3 * packingNumber s ≤ packingNumber L := by
    exact_mod_cast h
  calc
    _ = ((⌊L / (s + 1)⌋₊ : ℝ) ^ 3 * packingNumber s) / L ^ 3 := by ring
    _ ≤ (packingNumber L : ℝ) / L ^ 3 := div_le_div_of_nonneg_right hr (by positivity)

theorem packing_upper_approximation_le {L : ℝ} (hL : 0 < L) :
    (packingNumber L : ℝ) / L ^ 3 ≤ packingDensity * (1 + L⁻¹) ^ 3 := by
  have h := packing_ratio_le_density hL.le
  have h' : (packingNumber L : ℝ) ≤ packingDensity * (L + 1) ^ 3 :=
    (div_le_iff₀ (by positivity : 0 < (L + 1) ^ 3)).mp h
  apply (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr
  calc
    _ ≤ packingDensity * (L + 1) ^ 3 := h'
    _ = packingDensity * (1 + L⁻¹) ^ 3 * L ^ 3 := by field_simp

theorem packingDensity_limit : IsPackingDensity packingDensity := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, ⟨s, hs, rfl⟩, har⟩ :=
      (lt_csSup_iff packing_ratios_bdd packing_ratios_nonempty).mp ha
    have he := (packing_lower_approximation hs).eventually_const_lt har
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with L hlow hL
    exact hlow.trans_le (packing_lower_approximation_le hs hL)
  · intro a ha
    have hu : Tendsto (fun L : ℝ => packingDensity * (1 + L⁻¹) ^ 3)
        atTop (nhds packingDensity) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero).pow 3
      simpa using h.const_mul packingDensity
    filter_upwards [hu.eventually_lt_const ha, eventually_gt_atTop (0 : ℝ)] with L hhi hL
    exact (packing_upper_approximation_le hL).trans_lt hhi

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_LatticeStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem cellOf_mem_cubeCells {L : ℝ} {x : Position} (hx : x ∈ cube L) :
    cellOf x ∈ cubeCells L := by
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellOf]
  intro k
  exact ⟨Int.floor_nonneg.mpr (by linarith [(hx k).1]), Int.floor_mono (by linarith [(hx k).2])⟩

theorem card_cubeCells {L : ℝ} (hL : 1 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ 216 * L ^ 3 := by
  have hf : 0 ≤ ⌊4 * L⌋ := Int.floor_nonneg.mpr (by linarith)
  have heq : (cubeCells L).card = (⌊4 * L⌋ + 1).toNat ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, Int.card_Icc]
  rw [heq]
  have hc : (((⌊4 * L⌋ + 1).toNat : ℕ) : ℝ) = (⌊4 * L⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ ⌊4 * L⌋ + 1 by omega))
  push_cast
  rw [hc]
  have hb : (⌊4 * L⌋ : ℝ) + 1 ≤ 6 * L := by
    have hh := Int.floor_le (4 * L)
    linarith
  calc
    _ ≤ (6 * L) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast (show 0 ≤ ⌊4 * L⌋ + 1 by omega)) hb 3
    _ = _ := by ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FinitePartition
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem isClosed_cube (L : ℝ) : IsClosed (cube L) := by
  have heq : cube L = ⋂ k : Fin 3, {x : Position | x k ∈ Icc 0 L} := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_iInter, mem_Icc]
  rw [heq]
  exact isClosed_iInter (fun k : Fin 3 =>
    isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k))

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isClosed_cube L).measurableSet

theorem volume_cube (L : ℝ) : volume (cube L) = ENNReal.ofReal L ^ 3 := by
  have heq : cube L = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin 3 => Icc (0 : ℝ) L) := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun _ : Fin 3 => measurableSet_Icc)).nullMeasurableSet]
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem measurableSet_configurationCube (L : ℝ) (N : ℕ) :
    MeasurableSet (configurationCube L N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq]
  exact MeasurableSet.univ_pi (fun _ : Fin N => measurableSet_cube L)

theorem volume_configurationCube (L : ℝ) (N : ℕ) :
    volume (configurationCube L N) = ENNReal.ofReal L ^ (3 * N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq, volume_pi]
  rw [Measure.pi_pi]
  simp [volume_cube, ← pow_mul]

theorem continuous_energy {φ : Potential} (hφ : Continuous φ) (N : ℕ) :
    Continuous (energy φ (N := N)) := by
  unfold energy
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _
    (fun j _ => hφ.comp ((continuous_apply i).nndist (continuous_apply j))))

theorem energy_abs_bound {φ : Potential} {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ r : ℝ≥0, |φ r| ≤ M) {N : ℕ} (x : Fin N → Position) :
    |energy φ x| ≤ (N : ℝ) ^ 2 * M := by
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N with i < j, |φ (nndist (x i) (x j))| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, M := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (Finset.sum_le_sum (fun j _ => hφ _))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp; ring

theorem integrableOn_boltzmann {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) (L : ℝ) (N : ℕ) (β : ℝ) :
    IntegrableOn (fun x : Fin N → Position => Real.exp (-β * energy φ x))
      (configurationCube L N) := by
  obtain ⟨M, hM, hφM⟩ := hb
  have hfinite : volume (configurationCube L N) < ⊤ := by
    rw [volume_configurationCube]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  apply IntegrableOn.of_bound hfinite ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_energy hφ N))).stronglyMeasurable.aestronglyMeasurable) (Real.exp (|β| * ((N : ℝ) ^ 2 * M)))
  filter_upwards [] with x
  change |Real.exp (-β * energy φ x)| ≤ _
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * energy φ x ≤ |-β * energy φ x| := le_abs_self _
    _ = |β| * |energy φ x| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_abs_bound hM hφM x) (abs_nonneg _)

theorem integral_const_configurationCube {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (c : ℝ) :
    (∫ _x : Fin N → Position in configurationCube L N, c) = L ^ (3 * N) * c := by
  rw [setIntegral_const, Measure.real, volume_configurationCube, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hL]
  rfl

theorem partition_zero (φ : Potential) (L β : ℝ) : partition φ L 0 β = 1 := by
  have heq : (fun x : Fin 0 → Position => Real.exp (-β * energy φ x)) = fun _ => (1 : ℝ) := by
    funext x
    simp [energy]
  unfold partition
  rw [heq, setIntegral_const, Measure.real, volume_configurationCube]
  simp

theorem partition_nonneg {φ : Potential} (L : ℝ) (N : ℕ) (β : ℝ) :
    0 ≤ partition φ L N β := by
  exact mul_nonneg (by positivity) (integral_nonneg fun x => (Real.exp_pos _).le)

theorem partition_upper_of_energy_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : ∀ x ∈ configurationCube L N, E ≤ energy φ x) :
    partition φ L N β ≤ (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * E) := by
  have hfinite : volume (configurationCube L N) ≠ ⊤ := by
    simp [volume_configurationCube]
  have hconst : IntegrableOn (fun _ : Fin N → Position => Real.exp (-β * E))
      (configurationCube L N) := integrableOn_const hfinite
  have hc := setIntegral_mono_on (integrableOn_boltzmann hφ hb L N β) hconst
    (measurableSet_configurationCube L N) (fun x hx =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hE x hx) (neg_nonpos.mpr hβ)))
  rw [integral_const_configurationCube hL] at hc
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_assoc _ _ _).symm

theorem partition_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ) :
    partition φ L N β ≤ (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
  have hh := partition_upper_of_energy_lower hφ hb hL hβ N (fun x _ => hstable N x)
  have heq : (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * (-(B * N))) =
      (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    have he : -β * -(B * (N : ℝ)) = (N : ℝ) * (β * B) := by ring
    rw [he]
    ring
  exact hh.trans_eq heq

theorem grandTerm_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) (N : ℕ) :
    Real.exp (t * h * N) * partition φ L N β ≤
      (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial := by
  have hh := mul_le_mul_of_nonneg_left (partition_stability_upper hφ hb hstable hL hβ N)
    (Real.exp_pos (t * h * N)).le
  apply hh.trans_eq
  rw [Real.exp_add, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul (β * B) N,
    ← Real.exp_nat_mul (t * h) N]
  have he : t * h * (N : ℝ) = (N : ℝ) * (t * h) := by ring
  rw [he]
  ring

theorem grandPartition_summable {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ L N β) :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    (grandTerm_stability_upper hφ hb hstable hL hβ t h)
    (Real.summable_pow_div_factorial _)

theorem grandPartition_bounds {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    1 ≤ grandPartition φ t L β h ∧
      grandPartition φ t L β h ≤ Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
  have hs := grandPartition_summable hφ hb hstable hL hβ t h
  constructor
  · have hh := hs.le_tsum 0 (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    convert hh using 1 <;> first | rfl | norm_num [partition_zero]
  · have hh := hs.tsum_le_tsum (grandTerm_stability_upper hφ hb hstable hL hβ t h)
      (Real.summable_pow_div_factorial _)
    have he : (∑' N : ℕ, (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial) =
        Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact hh.trans_eq he

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialProducts
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uOtherIndex uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem orderedEnergy_fin (φ : Potential) {N : ℕ} (x : Fin N → Position) :
    orderedEnergy φ x = energy φ x := by
  have h := twice_pair_sum (fun i j => φ (nndist (x i) (x j)))
    (fun i j => by rw [nndist_comm])
  have hh : (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j then φ (nndist (x i) (x j)) else 0) = 2 * energy φ x := h.symm
  have he : orderedEnergy φ x = (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j then φ (nndist (x i) (x j)) else 0) / 2 := by
    unfold orderedEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij]
  rw [he, hh]
  ring

theorem orderedEnergy_equiv {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (φ : Potential) (x : κ → Position) :
    orderedEnergy φ (x ∘ e) = orderedEnergy φ x := by
  classical
  unfold orderedEnergy
  congr 1
  have hi (i : ι) : (∑ j : ι, if i ≠ j then φ (nndist (x (e i)) (x (e j))) else 0) =
      ∑ j : κ, if e i ≠ j then φ (nndist (x (e i)) (x j)) else 0 := by
    convert e.sum_comp (fun j => if e i ≠ j then φ (nndist (x (e i)) (x j)) else 0) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [ne_eq, e.injective.eq_iff]
  simpa only [Function.comp_apply, hi] using
    e.sum_comp (fun i => ∑ j, if i ≠ j then φ (nndist (x i) (x j)) else 0)

theorem continuous_orderedEnergy {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) : Continuous (fun x : ι → Position => orderedEnergy φ x) := by
  classical
  unfold orderedEnergy
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact hφ.comp ((continuous_apply i).nndist (continuous_apply j))
  · exact continuous_const

theorem orderedEnergy_abs_bound {ι : Type uIndex} [Fintype ι] {φ : Potential} {M : ℝ}
    (hM : 0 ≤ M) (hφM : ∀ r, |φ r| ≤ M) (x : ι → Position) :
    |orderedEnergy φ x| ≤ (Fintype.card ι : ℝ)^2 * M := by
  classical
  have hh : |∑ i : ι, ∑ j : ι, if i ≠ j then φ (nndist (x i) (x j)) else 0| ≤
      ∑ i : ι, ∑ j : ι, M := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact hφM _
    · simpa using hM
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold orderedEnergy
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) hM]

theorem integrable_orderedBoltzmann {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    (μ : Measure (ι → Position)) [IsFiniteMeasure μ] :
    Integrable (fun x : ι → Position => Real.exp (-β * orderedEnergy φ x)) μ := by
  obtain ⟨M, hM, hφM⟩ := hb
  apply Integrable.of_bound ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_orderedEnergy hφ))).aestronglyMeasurable)
    (Real.exp (|β| * ((Fintype.card ι : ℝ)^2 * M)))
  filter_upwards [] with x
  change |Real.exp _| ≤ _
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * orderedEnergy φ x ≤ |-β * orderedEnergy φ x| := le_abs_self _
    _ = |β| * |orderedEnergy φ x| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (orderedEnergy_abs_bound hM hφM x) (abs_nonneg β)

theorem rawPartition_nonneg (φ : Potential) (A : Set Position) (ι : Type uIndex) [Fintype ι] (β : ℝ) :
    0 ≤ rawPartition φ A ι β := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem rawPartition_equiv {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (φ : Potential) (A : Set Position) (β : ℝ) :
    rawPartition φ A ι β = rawPartition φ A κ β := by
  have hp := measurePreserving_piCongrLeft (fun _ : κ => volume.restrict A) e
  have hh := hp.integral_comp' (fun x => Real.exp (-β * orderedEnergy φ x))
  have he (x : ι → Position) : orderedEnergy φ ((MeasurableEquiv.piCongrLeft (fun _ : κ => Position) e) x) =
      orderedEnergy φ x := by
    have ht := orderedEnergy_equiv e φ ((MeasurableEquiv.piCongrLeft (fun _ : κ => Position) e) x)
    simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply] using ht.symm
  simpa only [rawPartition, he] using hh

theorem measure_pi_add {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ ν : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    Measure.pi (fun i => μ i + ν i) =
      ∑ T : Finset ι, Measure.pi (fun i => if i ∈ T then μ i else ν i) := by
  classical
  have hσ (T : Finset ι) : ∀ i, SigmaFinite (if i ∈ T then μ i else ν i) := by
    intro i
    split_ifs <;> infer_instance
  refine Measure.pi_eq (μ := fun i => μ i + ν i) (fun s hs => ?_)
  simp only [Measure.finsetSum_apply, Measure.pi_pi, Measure.add_apply]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  have he (i : ι) : (if i ∈ T then μ i else ν i) (s i) =
      if i ∈ T then μ i (s i) else ν i (s i) := by split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp

theorem sum_split_four {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (F : ι → ι → ℝ) :
    (∑ i, ∑ j, F i j) =
      (∑ i : Subtype p, ∑ j : Subtype p, F i j) +
      (∑ i : Subtype p, ∑ j : {j // ¬p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : Subtype p, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)]
  simp_rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => F _ j)]
  simp only [Finset.sum_add_distrib]
  ring

theorem orderedEnergy_split {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (φ : Potential) (x : ι → Position) :
    orderedEnergy φ x = orderedEnergy φ (fun i : Subtype p => x i) +
      orderedEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j)) := by
  classical
  have hn (i : Subtype p) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  unfold orderedEnergy
  rw [sum_split_four p]
  dsimp only
  have hpp (i j : Subtype p) : (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) =
      if i ≠ j then φ (nndist (x i) (x j)) else 0 := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Subtype.coe_ne_coe.mpr h]
  have hmm (i j : {i // ¬p i}) : (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) =
      if i ≠ j then φ (nndist (x i) (x j)) else 0 := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Subtype.coe_ne_coe.mpr h]
  have hpm (i : Subtype p) (j : {i // ¬p i}) :
      (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) = φ (nndist (x i) (x j)) := by
    rw [ite_eq_left (hn i j)]
  have hmp (i : {i // ¬p i}) (j : Subtype p) :
      (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) = φ (nndist (x i) (x j)) := by
    rw [ite_eq_left (hn j i).symm]
  simp_rw [hpp, hmm, hpm, hmp]
  have hs : (∑ i : {i // ¬p i}, ∑ j : Subtype p, φ (nndist (x i) (x j))) =
      ∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j)) := by
    rw [Finset.sum_comm]
    simp_rw [nndist_comm]
  rw [hs]
  ring_nf

theorem orderedEnergy_split_le {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (φ : Potential) (x : ι → Position)
    (hc : ∀ i j, p i → ¬p j → φ (nndist (x i) (x j)) ≤ 0) :
    orderedEnergy φ x ≤ orderedEnergy φ (fun i : Subtype p => x i) +
      orderedEnergy φ (fun i : {i // ¬p i} => x i) := by
  rw [orderedEnergy_split p]
  have hh : (∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    exact hc i j i.property j.property
  linarith

theorem sector_product_integral {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (F : (Subtype p → Position) → ℝ) (G : ({i // ¬p i} → Position) → ℝ)
    (μ ν : Measure Position) [SigmaFinite μ] [SigmaFinite ν] :
    (∫ x : ι → Position, F (fun i => x i) * G (fun i => x i)
      ∂Measure.pi (fun i => if p i then μ else ν)) =
      (∫ x : Subtype p → Position, F x ∂Measure.pi (fun _ => μ)) *
        ∫ x : {i // ¬p i} → Position, G x ∂Measure.pi (fun _ => ν) := by
  have : ∀ i : ι, SigmaFinite (if p i then μ else ν) := by
    intro i
    split_ifs <;> infer_instance
  have hp := measurePreserving_piEquivPiSubtypeProd (fun i => if p i then μ else ν) p
  have hh := hp.integral_comp' (fun z => F z.1 * G z.2)
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply,
    Subtype.prop, ite_true, if_true, (fun i : {i // ¬p i} => i.property), ite_false, if_false] at hh
  exact hh.trans (integral_prod_mul F G)

theorem sector_raw_lower {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) :
    rawPartition φ A (Subtype p) β * rawPartition φ B {i // ¬p i} β ≤
      ∫ x : ι → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if p i then volume.restrict A else volume.restrict B) := by
  let μ := fun i : ι => if p i then volume.restrict A else volume.restrict B
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have : ∀ i, IsFiniteMeasure (μ i) := by
    intro i
    dsimp [μ]
    split_ifs <;> infer_instance
  have hiA := integrable_orderedBoltzmann hφ hb β (Measure.pi (fun _ : Subtype p => volume.restrict A))
  have hiB := integrable_orderedBoltzmann hφ hb β (Measure.pi (fun _ : {i // ¬p i} => volume.restrict B))
  have hp := measurePreserving_piEquivPiSubtypeProd μ p
  have hip : Integrable (fun z : (Subtype p → Position) × ({i // ¬p i} → Position) =>
      Real.exp (-β * orderedEnergy φ z.1) * Real.exp (-β * orderedEnergy φ z.2))
      ((Measure.pi (fun i : Subtype p => μ i)).prod (Measure.pi (fun i : {i // ¬p i} => μ i))) := by
    simpa only [μ, Subtype.prop, ite_true, if_true, (fun i : {i // ¬p i} => i.property), ite_false, if_false] using hiA.mul_prod hiB
  have his := hp.integrable_comp_of_integrable hip
  have hiQ := integrable_orderedBoltzmann hφ hb β (Measure.pi μ)
  have hae : ∀ᵐ x : ι → Position ∂Measure.pi μ, ∀ i, x i ∈ (if p i then A else B) := by
    apply ae_all_iff.mpr
    intro i
    apply (Measure.tendsto_eval_ae_ae (μ := μ)).eventually
    dsimp [μ]
    split_ifs <;> exact ae_restrict_mem (by assumption)
  have hh := integral_mono_ae his hiQ (hae.mono (fun x hx => ?_))
  · simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply, Function.comp_apply] at hh
    change (∫ x : ι → Position, Real.exp (-β * orderedEnergy φ (fun i : Subtype p => x i)) *
      Real.exp (-β * orderedEnergy φ (fun i : {i // ¬p i} => x i))
      ∂Measure.pi (fun i => if p i then volume.restrict A else volume.restrict B)) ≤ _ at hh
    have hprod := sector_product_integral p
      (fun x : Subtype p → Position => Real.exp (-β * orderedEnergy φ x))
      (fun x : {i // ¬p i} → Position => Real.exp (-β * orderedEnergy φ x))
      (volume.restrict A) (volume.restrict B)
    exact hprod.symm.trans_le hh
  · change Real.exp (-β * orderedEnergy φ (fun i : Subtype p => x i)) *
        Real.exp (-β * orderedEnergy φ (fun i : {i // ¬p i} => x i)) ≤ _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := orderedEnergy_split_le p φ x (fun i j hi hj => hc (x i)
      (by simpa [hi] using hx i) (x j) (by simpa [hj] using hx j))
    nlinarith

theorem rawPartition_union_sum {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    {A B : Set Position} (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤) :
    rawPartition φ (A ∪ B) ι β =
      ∑ T : Finset ι, ∫ x : ι → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if i ∈ T then volume.restrict A else volume.restrict B) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  unfold rawPartition
  simp_rw [Measure.restrict_union hab hB]
  rw [measure_pi_add]
  apply integral_finsetSum_measure
  intro T _
  have : ∀ i : ι, IsFiniteMeasure (if i ∈ T then volume.restrict A else volume.restrict B) := by
    intro i
    split_ifs <;> infer_instance
  exact integrable_orderedBoltzmann hφ hb β _

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PartitionReplication
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem rawPartition_setIntegral {ι : Type uIndex} [Fintype ι] (φ : Potential) (A : Set Position) (β : ℝ) :
    rawPartition φ A ι β = ∫ x in Set.univ.pi (fun _ : ι => A), Real.exp (-β * orderedEnergy φ x) := by
  rw [rawPartition, volume_pi, Measure.restrict_pi_pi]

theorem partitionOn_cube (φ : Potential) (L : ℝ) (N : ℕ) (β : ℝ) :
    partitionOn φ (cube L) N β = partition φ L N β := by
  rw [partitionOn, rawPartition_setIntegral]
  simp_rw [orderedEnergy_fin]
  have he : (Set.univ.pi (fun _ : Fin N => cube L)) = configurationCube L N := by
    ext x
    simp [configurationCube, Set.mem_pi]
  rw [he]
  rfl

theorem partitionOn_nonneg (φ : Potential) (A : Set Position) (N : ℕ) (β : ℝ) :
    0 ≤ partitionOn φ A N β := mul_nonneg (by positivity) (rawPartition_nonneg φ A _ β)

theorem partitionOn_zero (φ : Potential) (A : Set Position) (β : ℝ) :
    partitionOn φ A 0 β = 1 := by
  simp [partitionOn, rawPartition, orderedEnergy, Measure.real]

theorem rawPartition_mono {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    {A B : Set Position} (hAB : A ⊆ B) (hBfin : volume B ≠ ⊤) :
    rawPartition φ A ι β ≤ rawPartition φ B ι β := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hi : Integrable (fun x : ι → Position => Real.exp (-β * orderedEnergy φ x))
      (volume.restrict (Set.univ.pi (fun _ : ι => B))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact integrable_orderedBoltzmann hφ hb β _
  rw [rawPartition_setIntegral, rawPartition_setIntegral]
  exact integral_mono_measure (Measure.restrict_mono (Set.pi_mono (fun _ _ => hAB)) le_rfl)
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) hi

theorem partitionOn_mono {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    (β : ℝ) (N : ℕ) {A B : Set Position} (hAB : A ⊆ B) (hBfin : volume B ≠ ⊤) :
    partitionOn φ A N β ≤ partitionOn φ B N β :=
  mul_le_mul_of_nonneg_left (rawPartition_mono hφ hb β hAB hBfin) (by positivity)

theorem measurableSet_translate {a : Position} {A : Set Position} (hA : MeasurableSet A) :
    MeasurableSet (translateSet a A) := hA.preimage (measurable_id.sub_const a)

theorem orderedEnergy_add {ι : Type uIndex} [Fintype ι] (φ : Potential) (x : ι → Position) (a : Position) :
    orderedEnergy φ (fun i => a + x i) = orderedEnergy φ x := by
  simp only [orderedEnergy, nndist_add_left]

theorem rawPartition_translate {ι : Type uIndex} [Fintype ι] (φ : Potential)
    (A : Set Position) (a : Position) (β : ℝ) :
    rawPartition φ (translateSet a A) ι β = rawPartition φ A ι β := by
  let τ : (ι → Position) ≃ᵐ (ι → Position) := (Homeomorph.addLeft (fun _ : ι => a)).toMeasurableEquiv
  have hp : MeasurePreserving τ volume volume := measurePreserving_add_left volume _
  have hpre : τ ⁻¹' (Set.univ.pi (fun _ : ι => translateSet a A)) = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp [τ, translateSet, add_sub_cancel_left]
  have he (x : ι → Position) : orderedEnergy φ (τ x) = orderedEnergy φ x := orderedEnergy_add φ x a
  have hh := hp.setIntegral_preimage_emb τ.measurableEmbedding
    (fun x => Real.exp (-β * orderedEnergy φ x)) (Set.univ.pi (fun _ : ι => translateSet a A))
  rw [hpre] at hh
  simpa only [rawPartition_setIntegral, he] using hh.symm

theorem partitionOn_translate (φ : Potential) (A : Set Position) (a : Position) (N : ℕ) (β : ℝ) :
    partitionOn φ (translateSet a A) N β = partitionOn φ A N β := by
  simp only [partitionOn, rawPartition_translate]

theorem sum_all_subsets_card (N : ℕ) (F : ℕ → ℝ) :
    (∑ T : Finset (Fin N), F T.card) = ∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * F m := by
  have hh := Finset.sum_powerset (Finset.univ : Finset (Fin N)) (fun T => F T.card)
  simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.sum_powersetCard, nsmul_eq_mul] using hh

theorem factorial_choose_cancel {N m : ℕ} (hm : m ≤ N) :
    (N.factorial : ℝ)⁻¹ * (N.choose m : ℝ) =
      (m.factorial : ℝ)⁻¹ * ((N - m).factorial : ℝ)⁻¹ := by
  have hfac : (N.choose m : ℝ) * m.factorial * (N - m).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hm' : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hnm : ((N - m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - m)
  field_simp
  nlinarith [hfac]

theorem partitionOn_union_convolution {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), partitionOn φ A m β * partitionOn φ B (N - m) β) ≤
      partitionOn φ (A ∪ B) N β := by
  classical
  have hterm (T : Finset (Fin N)) :
      rawPartition φ A (Fin T.card) β * rawPartition φ B (Fin (N - T.card)) β ≤
      ∫ x : Fin N → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if i ∈ T then volume.restrict A else volume.restrict B) := by
    have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
    have hcardB : Fintype.card {i : Fin N // i ∉ T} = N - T.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
    have hh := sector_raw_lower (fun i => i ∈ T) hφ hb hβ hA hB hAfin hBfin hc
    have heA := rawPartition_equiv (Fintype.equivFinOfCardEq hcardA) φ A β
    have heB := rawPartition_equiv (Fintype.equivFinOfCardEq hcardB) φ B β
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    · convert heA.symm using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    · exact heB.symm
  have hh := Finset.sum_le_sum (fun T (_ : T ∈ (Finset.univ : Finset (Finset (Fin N)))) => hterm T)
  rw [← rawPartition_union_sum hφ hb β hB hab hAfin hBfin] at hh
  rw [sum_all_subsets_card N (fun m =>
    rawPartition φ A (Fin m) β * rawPartition φ B (Fin (N - m)) β)] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show (0 : ℝ) ≤ N.factorial by positivity))
  change _ ≤ (N.factorial : ℝ)⁻¹ * rawPartition φ (A ∪ B) (Fin N) β
  refine le_trans (le_of_eq ?_) hh'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hcancel := factorial_choose_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  unfold partitionOn
  calc
    _ = ((m.factorial : ℝ)⁻¹ * ((N - m).factorial : ℝ)⁻¹) *
        (rawPartition φ A (Fin m) β * rawPartition φ B (Fin (N - m)) β) := by ring
    _ = _ := by rw [← hcancel]; ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GrandPartition
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem partitionOn_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (N : ℕ) :
    partitionOn φ A N β ≤ (volume.real A) ^ N * Real.exp (β * B * N) / N.factorial := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  have hh : rawPartition φ A (Fin N) β ≤ (volume.real A) ^ N * Real.exp (β * B * N) := by
    calc
      _ ≤ ∫ _ : Fin N → Position, Real.exp (β * B * N)
          ∂Measure.pi (fun _ : Fin N => volume.restrict A) := by
        apply integral_mono (integrable_orderedBoltzmann hφ hb β _) (integrable_const _)
        intro x
        apply Real.exp_le_exp.mpr
        rw [orderedEnergy_fin]
        nlinarith [mul_le_mul_of_nonneg_left (hstable N x) hβ]
      _ = _ := by
        simp [integral_const, measureReal_def, Measure.pi_univ]
  have hh' := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ (N.factorial : ℝ)⁻¹ by positivity)
  simpa only [partitionOn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh'

theorem grandOn_term_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) (N : ℕ) :
    Real.exp (z * N) * partitionOn φ A N β ≤
      (volume.real A * Real.exp (β * B + z)) ^ N / N.factorial := by
  have hh := mul_le_mul_of_nonneg_left (partitionOn_stability_upper hφ hb hstable hβ hAfin N)
    (Real.exp_pos (z * N)).le
  apply hh.trans_eq
  rw [Real.exp_add, mul_pow, mul_pow, ← Real.exp_nat_mul (β * B) N,
    ← Real.exp_nat_mul z N]
  have he₁ : β * B * (N : ℝ) = (N : ℝ) * (β * B) := by ring
  have he₂ : z * (N : ℝ) = (N : ℝ) * z := by ring
  rw [he₁, he₂]
  ring

theorem grandOn_summable {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) :
    Summable (fun N : ℕ => Real.exp (z * N) * partitionOn φ A N β) :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A N β))
    (grandOn_term_upper hφ hb hstable hβ hAfin z)
    (Real.summable_pow_div_factorial _)

theorem grandOn_bounds {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) :
    1 ≤ grandOn φ A β z ∧ grandOn φ A β z ≤ Real.exp (volume.real A * Real.exp (β * B + z)) := by
  have hs := grandOn_summable hφ hb hstable hβ hAfin z
  constructor
  · have hh := hs.le_tsum 0 (fun N _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A N β))
    convert hh using 1 <;> first | rfl | norm_num [partitionOn_zero]
  · have hh := hs.tsum_le_tsum (grandOn_term_upper hφ hb hstable hβ hAfin z)
      (Real.summable_pow_div_factorial _)
    have he : (∑' N : ℕ, (volume.real A * Real.exp (β * B + z)) ^ N / N.factorial) =
        Real.exp (volume.real A * Real.exp (β * B + z)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact hh.trans_eq he

theorem grandOn_union_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β)
    {A D : Set Position} (hA : MeasurableSet A) (hD : MeasurableSet D) (had : Disjoint A D)
    (hAfin : volume A ≠ ⊤) (hDfin : volume D ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ D, φ (nndist x y) ≤ 0) (z : ℝ) :
    grandOn φ A β z * grandOn φ D β z ≤ grandOn φ (A ∪ D) β z := by
  have hUfin : volume (A ∪ D) ≠ ⊤ := (measure_union_le A D).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hAfin.lt_top, hDfin.lt_top⟩) |>.ne
  have hsA := grandOn_summable hφ hb hstable hβ hAfin z
  have hsD := grandOn_summable hφ hb hstable hβ hDfin z
  have hsU := grandOn_summable hφ hb hstable hβ hUfin z
  have hcov (N : ℕ) :
      (∑ m ∈ Finset.range (N + 1), (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β)) ≤
          Real.exp (z * N) * partitionOn φ (A ∪ D) N β := by
    have he : (∑ m ∈ Finset.range (N + 1), (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β)) =
        Real.exp (z * N) * ∑ m ∈ Finset.range (N + 1),
          partitionOn φ A m β * partitionOn φ D (N - m) β := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have he : z * (m : ℝ) + z * (N - m : ℕ) = z * N := by
        rw [Nat.cast_sub hmN]; ring
      calc
        _ = (Real.exp (z * m) * Real.exp (z * ((N - m : ℕ) : ℝ))) *
            (partitionOn φ A m β * partitionOn φ D (N - m) β) := by ring
        _ = _ := by rw [← Real.exp_add, he]
    rw [he]
    exact mul_le_mul_of_nonneg_left (partitionOn_union_convolution hφ hb hβ hA hD had hAfin hDfin hc N)
      (Real.exp_pos _).le
  have hnn (N : ℕ) : 0 ≤ ∑ m ∈ Finset.range (N + 1),
      (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β) := by
    apply Finset.sum_nonneg
    intro m _
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A m β))
      (mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ D (N - m) β))
  rw [grandOn, grandOn,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsA.norm hsD.norm]
  exact (Summable.of_nonneg_of_le hnn hcov hsU).tsum_le_tsum hcov hsU

theorem grandOn_mono {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) {A D : Set Position}
    (hsub : A ⊆ D) (hDfin : volume D ≠ ⊤) (z : ℝ) : grandOn φ A β z ≤ grandOn φ D β z := by
  have hAfin : volume A ≠ ⊤ := (measure_mono hsub).trans_lt hDfin.lt_top |>.ne
  exact (grandOn_summable hφ hb hstable hβ hAfin z).tsum_le_tsum
    (fun N => mul_le_mul_of_nonneg_left (partitionOn_mono hφ hb β N hsub hDfin) (Real.exp_pos _).le)
    (grandOn_summable hφ hb hstable hβ hDfin z)

theorem grandOn_translate (φ : Potential) (A : Set Position) (a : Position) (β z : ℝ) :
    grandOn φ (translateSet a A) β z = grandOn φ A β z := by
  simp only [grandOn, partitionOn_translate]

theorem grandOn_cube (φ : Potential) (L t β h : ℝ) :
    grandOn φ (cube L) β (t * h) = grandPartition φ t L β h := by
  simp only [grandOn, grandPartition, partitionOn_cube]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialReplication
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem volume_translateSet (A : Set Position) (a : Position) (hA : MeasurableSet A) :
    volume (translateSet a A) = volume A := by
  exact (measurePreserving_sub_right volume a).measure_preimage hA.nullMeasurableSet

theorem measurableSet_boxRegion {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) :
    MeasurableSet (boxRegion s j) := measurableSet_translate (measurableSet_cube s)

theorem volume_boxRegion {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) :
    volume (boxRegion s j) = ENNReal.ofReal s ^ 3 := by
  rw [boxRegion, volume_translateSet _ _ (measurableSet_cube s), volume_cube]

theorem boxRegion_subset_cube {n : ℕ} {s L : ℝ} (hs : 0 ≤ s)
    (hn : (n : ℝ) * (s + 2) ≤ L) (j : Fin 3 → Fin n) : boxRegion s j ⊆ cube L := by
  intro x hx k
  have hxx : ∀ k, 0 ≤ x k - (j k : ℝ) * (s + 2) ∧
      x k - (j k : ℝ) * (s + 2) ≤ s := hx
  have hj : (j k : ℝ) + 1 ≤ n := by exact_mod_cast (j k).isLt
  have hj0 : 0 ≤ (j k : ℝ) := by positivity
  have hp := mul_le_mul_of_nonneg_right hj (show 0 ≤ s + 2 by linarith)
  have hp0 : 0 ≤ (j k : ℝ) * (s + 2) := mul_nonneg hj0 (by linarith)
  exact ⟨by linarith [(hxx k).1], by linarith [(hxx k).2]⟩

theorem boxRegion_dist {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {j k : Fin 3 → Fin n}
    (hjk : j ≠ k) {x y : Position} (hx : x ∈ boxRegion s j) (hy : y ∈ boxRegion s k) :
    2 ≤ dist x y := by
  have hc {j k : Fin 3 → Fin n} {x y : Position} (q : Fin 3) (hq : j q < k q)
      (hx : x ∈ boxRegion s j) (hy : y ∈ boxRegion s k) : 2 ≤ dist x y := by
    have hq' : (j q : ℝ) + 1 ≤ (k q : ℝ) := by exact_mod_cast hq
    have hp := mul_le_mul_of_nonneg_right hq' (show 0 ≤ s + 2 by linarith)
    have hx' : x q - (j q : ℝ) * (s + 2) ≤ s := (hx q).2
    have hy' : 0 ≤ y q - (k q : ℝ) * (s + 2) := (hy q).1
    have hh : 2 ≤ y q - x q := by linarith
    calc
      2 ≤ y q - x q := hh
      _ ≤ |y q - x q| := le_abs_self _
      _ ≤ ‖y - x‖ := by simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) q
      _ = dist x y := by rw [← dist_eq_norm, dist_comm]
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hjk
  rcases lt_or_gt_of_ne hq with h | h
  · exact hc q h hx hy
  · simpa only [dist_comm] using hc q h hy hx

theorem boxRegion_disjoint {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {j k : Fin 3 → Fin n}
    (hjk : j ≠ k) : Disjoint (boxRegion s j) (boxRegion s k) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hh := boxRegion_dist hs hjk hx hy
  norm_num at hh

theorem grandOn_biUnion_lower {ι : Type uIndex} [DecidableEq ι]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β)
    (S : Finset ι) (A : ι → Set Position) (z : ℝ)
    (hA : ∀ i ∈ S, MeasurableSet (A i)) (hAfin : ∀ i ∈ S, volume (A i) ≠ ⊤)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (A i) (A j))
    (hc : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, φ (nndist x y) ≤ 0) :
    (∏ i ∈ S, grandOn φ (A i) β z) ≤ grandOn φ (⋃ i ∈ S, A i) β z := by
  induction S using Finset.induction_on with
  | empty =>
    simpa using (grandOn_bounds hφ hb hstable hβ (by simp : volume (∅ : Set Position) ≠ ⊤) z).1
  | @insert i S hi ih =>
    have hAs : ∀ j ∈ S, MeasurableSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hfins : ∀ j ∈ S, volume (A j) ≠ ⊤ := fun j hj => hAfin j (Finset.mem_insert_of_mem hj)
    have hU : MeasurableSet (⋃ j ∈ S, A j) := Finset.measurableSet_biUnion S hAs
    have hUfin : volume (⋃ j ∈ S, A j) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hfins) (measure_biUnion_finset_le S A)
    have hdU : Disjoint (A i) (⋃ j ∈ S, A j) := by
      simp only [Set.disjoint_iUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hi hj)
    have hcU : ∀ x ∈ A i, ∀ y ∈ ⋃ j ∈ S, A j, φ (nndist x y) ≤ 0 := by
      intro x hx y hy
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
      exact hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hi hj) x hx y hy
    have hi' := ih hAs hfins
      (fun j hj k hk hne => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
      (fun j hj k hk hne => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
    rw [Finset.prod_insert hi]
    have hnn := (grandOn_bounds hφ hb hstable hβ (hAfin i (Finset.mem_insert_self _ _)) z).1
    have hprod := mul_le_mul_of_nonneg_left hi' (show 0 ≤ grandOn φ (A i) β z by linarith)
    refine hprod.trans ?_
    have hu : (⋃ j ∈ insert i S, A j) = A i ∪ ⋃ j ∈ S, A j := by ext x; simp
    rw [hu]
    exact grandOn_union_lower hφ hb hstable hβ
      (hA i (Finset.mem_insert_self _ _)) hU hdU (hAfin i (Finset.mem_insert_self _ _)) hUfin hcU z

theorem grandPartition_replication {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β s L : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (n : ℕ)
    (hn : (n : ℝ) * (s + 2) ≤ L) (t h : ℝ) :
    grandPartition φ t s β h ^ (n ^ 3) ≤ grandPartition φ t L β h := by
  classical
  have hh := grandOn_biUnion_lower hφ hb hstable hβ Finset.univ (boxRegion s) (t * h)
    (fun j _ => measurableSet_boxRegion s j)
    (fun j _ => by rw [volume_boxRegion]; finiteness)
    (fun _ _ _ _ hne => boxRegion_disjoint hs hne)
    (fun _ _ _ _ hne _ hx _ hy => hc _ (boxRegion_dist hs hne hx hy))
  have hsub : (⋃ j ∈ (Finset.univ : Finset (Fin 3 → Fin n)), boxRegion s j) ⊆ cube L := by
    intro x hx
    obtain ⟨j, _, hx⟩ := Set.mem_iUnion₂.mp hx
    exact boxRegion_subset_cube hs hn j hx
  have hh' := hh.trans (grandOn_mono hφ hb hstable hβ hsub (by rw [volume_cube]; finiteness) (t * h))
  simpa only [boxRegion, grandOn_translate, grandOn_cube, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hh'

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ThermodynamicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem separated_box_limit {F : ℝ → ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hF0 : ∀ s, 0 ≤ s → 0 ≤ F s)
    (hFC : ∀ s, 0 ≤ s → F s ≤ C * s ^ 3)
    (hrep : ∀ (s L : ℝ) (n : ℕ), 0 ≤ s → (n : ℝ) * (s + δ) ≤ L →
      (n : ℝ) ^ 3 * F s ≤ F L) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ C ∧
      Tendsto (fun L : ℝ => F L / L ^ 3) atTop (nhds p) ∧
      ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ p := by
  let S : Set ℝ := {r | ∃ s : ℝ, 0 ≤ s ∧ r = F s / (s + δ) ^ 3}
  have hnon : S.Nonempty := ⟨_, 0, le_rfl, rfl⟩
  have hbound : ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ C := by
    intro s hs
    apply (div_le_iff₀ (by positivity : 0 < (s + δ) ^ 3)).mpr
    calc
      F s ≤ C * s ^ 3 := hFC s hs
      _ ≤ C * (s + δ) ^ 3 := by gcongr; linarith
  have hbd : BddAbove S := ⟨C, by rintro r ⟨s, hs, rfl⟩; exact hbound s hs⟩
  let p : ℝ := sSup S
  have hpC : p ≤ C := csSup_le hnon (by rintro r ⟨s, hs, rfl⟩; exact hbound s hs)
  have hsp (s : ℝ) (hs : 0 ≤ s) : F s / (s + δ) ^ 3 ≤ p := le_csSup hbd ⟨s, hs, rfl⟩
  have hp0 : 0 ≤ p := (div_nonneg (hF0 0 le_rfl) (by positivity)).trans (hsp 0 le_rfl)
  refine ⟨p, hp0, hpC, ?_, hsp⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, ⟨s, hs, rfl⟩, har⟩ := (lt_csSup_iff hbd hnon).mp ha
    have hlim : Tendsto (fun L : ℝ => ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s)
        atTop (nhds (F s / (s + δ) ^ 3)) := by
      have hh := ((tendsto_nat_floor_mul_div_atTop (show 0 ≤ (s + δ)⁻¹ by positivity)).pow 3).mul_const (F s)
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hh
    filter_upwards [hlim.eventually_const_lt har, eventually_gt_atTop (0 : ℝ)] with L hlo hL
    have hn : (⌊L / (s + δ)⌋₊ : ℝ) * (s + δ) ≤ L :=
      (le_div_iff₀ (by positivity : 0 < s + δ)).mp (Nat.floor_le (by positivity))
    have hh := div_le_div_of_nonneg_right (hrep s L ⌊L / (s + δ)⌋₊ hs hn)
      (show 0 ≤ L ^ 3 by positivity)
    have heq : ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s =
        ((⌊L / (s + δ)⌋₊ : ℝ) ^ 3 * F s) / L ^ 3 := by ring
    exact hlo.trans_le (heq ▸ hh)
  · intro a ha
    have hlim : Tendsto (fun L : ℝ => p * (1 + δ * L⁻¹) ^ 3) atTop (nhds p) := by
      have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_inv_atTop_zero.const_mul δ)).pow 3
      simpa using hh.const_mul p
    filter_upwards [hlim.eventually_lt_const ha, eventually_gt_atTop (0 : ℝ)] with L hhi hL
    apply lt_of_le_of_lt _ hhi
    apply (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (L + δ) ^ 3)).mp (hsp L hL.le)
    calc
      F L ≤ p * (L + δ) ^ 3 := hh
      _ = p * (1 + δ * L⁻¹) ^ 3 * L ^ 3 := by field_simp

theorem grandPressure_exists {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ Real.exp (β * B + t * h) / t ∧
      Tendsto (fun L : ℝ => Real.log (grandPartition φ t L β h) / (t * L ^ 3))
        atTop (nhds p) := by
  have hbnd (s : ℝ) (hs : 0 ≤ s) := grandPartition_bounds hφ hb hstable hs hβ t h
  obtain ⟨p, hp0, hpC, hlim, _⟩ := separated_box_limit
    (F := fun L => Real.log (grandPartition φ t L β h))
    (C := Real.exp (β * B + t * h)) (δ := 2) (Real.exp_pos _).le (by norm_num)
    (fun s hs => Real.log_nonneg (hbnd s hs).1)
    (fun s hs => by
      have hh := Real.log_le_log (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1])
        (hbnd s hs).2
      simpa only [Real.log_exp, mul_comm] using hh)
    (fun s L n hs hn => by
      have hh := Real.log_le_log
        (pow_pos (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1]) _)
        (grandPartition_replication hφ hb hstable hβ hs hc n hn t h)
      simpa only [Real.log_pow, Nat.cast_pow] using hh)
  refine ⟨p / t, div_nonneg hp0 ht.le, (div_le_div_of_nonneg_right hpC ht.le), ?_⟩
  simpa only [div_div, mul_comm] using hlim.div_const t

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_DensityMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem grandPressure_spec {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    Tendsto (fun L : ℝ => finiteGrandPressure φ t L β h) atTop (nhds (grandPressure φ t β h)) ∧
      0 ≤ grandPressure φ t β h ∧ grandPressure φ t β h ≤ Real.exp (β * B + t * h) / t := by
  obtain ⟨p, hp0, hpB, hlim⟩ := grandPressure_exists hφ hb hstable ht hβ hc h
  have he : grandPressure φ t β h = p := hlim.limsup_eq
  rw [he]
  exact ⟨hlim, hp0, hpB⟩

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ParticleMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

theorem measurable_particle_mk (n : ℕ) : Measurable (@Sigma.mk ℕ (fun n => Fin n → X) n) :=
  continuous_sigmaMk.measurable

theorem lintegral_particleBase (ν : Measure X) (z : ℝ) {f : ParticleState X → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂particleBase ν z) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (z*n) / n.factorial) *
        ∫⁻ x : Fin n → X, f ⟨n,x⟩ ∂Measure.pi (fun _ => ν) := by
  rw [particleBase, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_map hf (measurable_particle_mk n)]
  rfl

theorem particleBase_univ {ν : Measure X} (hA : ν univ ≠ ⊤) (z : ℝ) :
    particleBase ν z univ = ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp z)) := by
  let : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hA⟩
  have hV : 0 ≤ (ν univ).toReal := ENNReal.toReal_nonneg
  have hf (n : ℕ) : 0 ≤ ((ν univ).toReal * Real.exp z)^n / n.factorial := by positivity
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (z*n) / n.factorial) * (ν univ)^n =
      ENNReal.ofReal (((ν univ).toReal * Real.exp z)^n / n.factorial) := by
    rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_pow hV,
      ← ENNReal.ofReal_mul (by positivity), mul_pow, ← Real.exp_nat_mul]
    simp only [ENNReal.toReal_ofReal hV]
    congr 1
    rw [mul_comm z (n : ℝ)]
    ring
  have hh := lintegral_particleBase ν z (f := fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.pi_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hh
  rw [hh]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf (Real.summable_pow_div_factorial _)]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

instance particleBase_finite {ν : Measure X} (z : ℝ) [IsFiniteMeasure (ν)] :
    IsFiniteMeasure (particleBase ν z) := by
  constructor
  rw [particleBase_univ (measure_ne_top ν univ)]
  exact ENNReal.ofReal_lt_top

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FockIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section Fock
variable {X : Type uX} [MeasurableSpace X]
variable (F : ∀ (ι : Type) [Fintype ι], (ι → X) → ℝ≥0∞)
variable (heq : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X),
  F ι (x ∘ e) = F κ x)
include heq

lemma functional_integral_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (μ : κ → Measure X) [∀ i, SigmaFinite (μ i)] :
    (∫⁻ x, F ι x ∂Measure.pi (fun i => μ (e i))) = ∫⁻ x, F κ x ∂Measure.pi μ := by
  have hp := measurePreserving_piCongrLeft μ e
  have hh := MeasurePreserving.lintegral_map_equiv (F κ)
    (MeasurableEquiv.piCongrLeft (fun _ => X) e) hp
  rw [hh]
  apply lintegral_congr
  intro x
  have h := heq ι κ e (MeasurableEquiv.piCongrLeft (fun _ => X) e x)
  simpa [MeasurableEquiv.piCongrLeft, Function.comp_def] using h

end Fock

lemma fockCoeff_choose (z : ℝ) {N m : ℕ} (hm : m ≤ N) :
    fockCoeff z N * N.choose m = fockCoeff z m * fockCoeff z (N-m) := by
  have hz : z*(N:ℝ) = z*m + z*(N-m : ℕ) := by rw [Nat.cast_sub hm]; ring
  have hr : Real.exp (z*N)/(N.factorial:ℝ) * (N.choose m:ℝ) =
      (Real.exp (z*m)/m.factorial) * (Real.exp (z*(N-m : ℕ))/(N-m).factorial) := by
    calc
      _ = Real.exp (z*N) * ((N.factorial:ℝ)⁻¹ * (N.choose m:ℝ)) := by ring
      _ = Real.exp (z*N) * ((m.factorial:ℝ)⁻¹ * ((N-m).factorial:ℝ)⁻¹) := by rw [factorial_choose_cancel hm]
      _ = _ := by rw [hz, Real.exp_add]; ring
  have hh := congrArg ENNReal.ofReal hr
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (z*N)/(N.factorial:ℝ)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (z*m)/(m.factorial:ℝ)),
    ENNReal.ofReal_natCast, fockCoeff] using hh

lemma ennreal_subsets_card (N : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ T : Finset (Fin N), f T.card) = ∑ m ∈ Finset.range (N+1), (N.choose m:ℝ≥0∞)*f m := by
  have hh := Finset.sum_powerset (Finset.univ : Finset (Fin N)) (fun T => f T.card)
  simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.sum_powersetCard, nsmul_eq_mul] using hh

lemma ennreal_tsum_triangle (g : ℕ → ℕ → ℝ≥0∞) :
    (∑' N, ∑ m ∈ Finset.range (N+1), g m (N-m)) = ∑' m, ∑' n, g m n := by
  rw [← ENNReal.tsum_prod,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p : ℕ × ℕ => g p.1 p.2),
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  change (∑ m ∈ Finset.range (n+1), g m (n-m)) =
    ∑ b : {p : ℕ × ℕ // p ∈ Finset.HasAntidiagonal.antidiagonal n}, g b.1.1 b.1.2
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => g k l) n).symm.trans
    (Finset.sum_finset_coe (fun p : ℕ × ℕ => g p.1 p.2) (Finset.HasAntidiagonal.antidiagonal n)).symm

section MultisetFock
variable {X : Type uX}

lemma configurationMultiset_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → X) : configurationMultiset (x ∘ e) = configurationMultiset x :=
  e.sum_comp (fun i => {x i})

end MultisetFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MultisetEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uM uIndex uY

noncomputable section


open MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma measurable_particleBoltzmann {φ : Potential} (hφ : Continuous φ) (β : ℝ) :
    Measurable (fun s : ParticleState Position => Real.exp (-β * orderedEnergy φ s.2)) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro n
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_orderedEnergy hφ))

lemma lintegral_grandOn {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) {A : Set Position}
    (hAfin : volume A ≠ ⊤) (z : ℝ) :
    (∫⁻ s : ParticleState Position, ENNReal.ofReal (Real.exp (-β * orderedEnergy φ s.2))
      ∂particleBase (volume.restrict A) z) = ENNReal.ofReal (grandOn φ A β z) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  rw [lintegral_particleBase _ _ (measurable_particleBoltzmann hφ β).ennreal_ofReal,
    grandOn, ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A n β))
      (grandOn_summable hφ hb hstable hβ hAfin z)]
  apply tsum_congr
  intro n
  have hi := integrable_orderedBoltzmann (ι := Fin n) hφ hb β (Measure.pi (fun _ => volume.restrict A))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => (Real.exp_pos _).le)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [partitionOn, rawPartition, div_eq_mul_inv]
  ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CroppedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma measurable_cellOf : Measurable cellOf := by
  apply Measurable.of_eval
  intro k
  exact Int.measurable_floor.comp (measurable_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).measurable)

lemma measurableSet_gridRegion (k : Cell) : MeasurableSet (gridRegion k) :=
  measurable_cellOf (measurableSet_singleton k)

lemma gridRegion_subset_box (k : Cell) : gridRegion k ⊆ translateSet (gridOrigin k) (cube (1/4)) := by
  intro x hx i
  have hh : ⌊4*x i⌋ = k i := congrFun hx i
  have hl := Int.floor_le (4*x i)
  have hu := Int.lt_floor_add_one (4*x i)
  rw [hh] at hl hu
  change 0 ≤ x i - (k i : ℝ)/4 ∧ x i - (k i : ℝ)/4 ≤ 1/4
  constructor <;> linarith

lemma volume_gridRegion_le (k : Cell) : volume (gridRegion k) ≤ ENNReal.ofReal (1/64:ℝ) := by
  have hh := measure_mono (gridRegion_subset_box k) (μ := volume)
  rw [volume_translateSet _ _ (measurableSet_cube _), volume_cube] at hh
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at hh
  norm_num at hh ⊢
  exact hh

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MeasurableFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uIndex uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MeasurableFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma measurable_borel_sigma {ι : Type uIndex} [Countable ι] {Y : ι → Type uY}
    [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)] [∀ i, BorelSpace (Y i)]
    {Z : Type uZ} [MeasurableSpace Z] {f : (Σ i, Y i) → Z}
    (hf : ∀ i, Measurable (fun y : Y i => f ⟨i,y⟩)) :
    @Measurable _ _ (borel (Σ i, Y i)) _ f := by
  let : MeasurableSpace (Σ i, Y i) := borel (Σ i, Y i)
  let : BorelSpace (Σ i, Y i) := ⟨rfl⟩
  intro s hs
  have he : f ⁻¹' s = ⋃ i : ι, Sigma.mk i '' ((fun x : Y i => f ⟨i,x⟩) ⁻¹' s) :=
    (iUnion_image_preimage_sigma_mk_eq_self (f ⁻¹' s)).symm
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image.mpr (hf i hs))

variable (F : Multiset X → ℝ≥0∞)

lemma measurable_particleObservable (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun x : ParticleState X => F (s+particleMultiset x)) := by
  apply measurable_borel_sigma
  intro n
  exact hF s (Fin n)

end MeasurableFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ClusterConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma antidiagonal_map {X : Type uX} {Y : Type uY} (f : X → Y) (s : Multiset X) :
    (s.map f).antidiagonal = s.antidiagonal.map (fun p => (p.1.map f, p.2.map f)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.antidiagonal_cons, ih, Multiset.map_add, Multiset.map_map]
    congr 1 <;> apply Multiset.map_congr rfl <;> intro p hp <;> simp

lemma powerset_val_map {X : Type uX} (s : Finset X) :
    (s.powerset.val.map Finset.val) = s.val.powerset := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

lemma configurationMultiset_val {X : Type uX} {ι : Type} [Fintype ι] (x : ι → X) :
    configurationMultiset x = (Finset.univ.val.map x) := by
  simp only [configurationMultiset, Finset.sum]
  simpa only [Multiset.map_map, Function.comp_def] using
    Multiset.sum_map_singleton (Finset.univ.val.map x)

lemma configurationMultiset_subtype {X : Type uX} {ι : Type} [Fintype ι]
    (x : ι → X) (T : Finset ι) :
    configurationMultiset (fun i : T => x i) = T.val.map x := by
  unfold configurationMultiset
  calc
    (∑ i : T, {x i}) = ∑ i ∈ T, {x i} := Finset.sum_finset_coe (fun i => {x i}) T
    _ = _ := by
      change (T.val.map (fun i => {x i})).sum = T.val.map x
      simpa only [Multiset.map_map, Function.comp_def] using Multiset.sum_map_singleton (T.val.map x)

lemma clusterConvolution_add_ge {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s u : Multiset X) :
    F s*G u ≤ clusterConvolution F G (s+u) := by
  apply Multiset.single_le_sum (fun _ _ => bot_le)
  exact Multiset.mem_map.mpr ⟨(s,u), Multiset.mem_antidiagonal.mpr rfl, rfl⟩

lemma clusterConvolution_configuration {X : Type uX} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F G : Multiset X → ℝ≥0∞) (x : ι → X) :
    clusterConvolution F G (configurationMultiset x) =
      ∑ T : Finset ι, F (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
        G (configurationMultiset (fun i : T => x i)) := by
  classical
  rw [clusterConvolution, configurationMultiset_val, antidiagonal_map,
    Multiset.antidiagonal_eq_map_powerset, ← powerset_val_map]
  simp only [Multiset.map_map, Function.comp_def]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  · have hval : Finset.univ.val-T.val = Tᶜ.val := by
      change (Finset.univ \ T).val = Tᶜ.val
      rfl
    rw [hval]
    congr 1
    let e : {i // i ∉ T} ≃ {i // i ∈ Tᶜ} := Equiv.subtypeEquivProp (by simp)
    have hh := configurationMultiset_equiv e (fun i : {i // i ∈ Tᶜ} => x i)
    rw [configurationMultiset_subtype] at hh
    exact hh.symm
  · congr 1
    exact (configurationMultiset_subtype x T).symm

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ConvolutionIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma clusterConvolution_add {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s u : Multiset X) :
    clusterConvolution F G (s+u) =
      (s.antidiagonal.map (fun p => clusterConvolution (fun v => F (p.1+v)) (fun v => G (p.2+v)) u)).sum := by
  simp [clusterConvolution, Multiset.antidiagonal_add, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map]

section Measurable
variable {X : Type uX} [MeasurableSpace X]

lemma measurable_configuration_subtype {F : Multiset X → ℝ≥0∞} (hF : MeasurableConfiguration F)
    (s : Multiset X) {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Measurable (fun x : ι → X => F (s+configurationMultiset (fun i : Subtype p => x i))) := by
  exact (hF s (Subtype p)).comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))

lemma measurable_configuration_restrict {F : Multiset X → ℝ≥0∞} (hF : MeasurableConfiguration F)
    (s : Multiset X) {ι : Type} [Fintype ι] (T : Finset ι) :
    Measurable (fun x : ι → X => F (s+configurationMultiset (fun i : T => x i))) := by
  apply (hF s T).comp
  exact measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)

lemma measurable_multiset_sum {Y : Type uY} [MeasurableSpace Y] {ι : Type uIndex}
    (s : Multiset ι) (f : ι → Y → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => (s.map (fun i => f i x)).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact measurable_add.comp ((hf a).prodMk ih)

lemma measurable_clusterConvolution {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G) :
    MeasurableConfiguration (clusterConvolution F G) := by
  classical
  intro s ι _
  simp_rw [clusterConvolution_add, clusterConvolution_configuration]
  apply measurable_multiset_sum
  intro p
  apply Finset.measurable_sum
  intro T _
  exact (measurable_configuration_subtype hF p.1 (fun i => i ∉ T)).mul
    (measurable_configuration_restrict hG p.2 T)

lemma configuration_integral_card (F : Multiset X → ℝ≥0∞) (μ : Measure X) [SigmaFinite μ]
    (ι : Type) [Fintype ι] :
    (∫⁻ x : ι → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x : Fin (Fintype.card ι) → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ) := by
  exact functional_integral_equiv (fun _ι _ x => F (configurationMultiset x))
    (fun _ι _κ _ _ e x => congrArg F (configurationMultiset_equiv e x)) (Fintype.equivFin ι) (fun _ => μ)

lemma configuration_split_integral {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G)
    (μ : Measure X) [SigmaFinite μ] {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset ι) :
    (∫⁻ x : ι → X, F (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
      G (configurationMultiset (fun i : T => x i)) ∂Measure.pi (fun _ => μ)) =
      (∫⁻ x : {i // i ∉ T} → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ))*
      (∫⁻ x : T → X, G (configurationMultiset x) ∂Measure.pi (fun _ => μ)) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ T)
  have hG0 : Measurable (fun x : T → X => G (configurationMultiset x)) := by
    simpa only [zero_add] using hG 0 T
  have hF0 : Measurable (fun x : {i // i ∉ T} → X => F (configurationMultiset x)) := by
    simpa only [zero_add] using hF 0 {i // i ∉ T}
  have hmeas : Measurable (fun p : (T → X) × ({i // i ∉ T} → X) =>
      G (configurationMultiset p.1)*F (configurationMultiset p.2)) := by
    exact (hG0.comp measurable_fst).mul (hF0.comp measurable_snd)
  have hh := hp.lintegral_comp hmeas
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply] at hh
  have hi : Subtype.fintype (fun i : ι => i ∈ T) = Finset.Subtype.fintype T := Subsingleton.elim _ _
  rw [hi] at hh
  have hent := lintegral_prod_mul (μ := Measure.pi (fun _ : T => μ))
    (ν := Measure.pi (fun _ : {i // i ∉ T} => μ)) hG0.aemeasurable hF0.aemeasurable
  have hh := hh.trans hent
  simpa only [mul_comm] using hh

end Measurable
end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ConvolutionFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
section Fock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma particleBase_convolution {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G)
    (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, clusterConvolution F G (particleMultiset x) ∂particleBase μ z) =
      (∫⁻ x, F (particleMultiset x) ∂particleBase μ z)*
      (∫⁻ x, G (particleMultiset x) ∂particleBase μ z) := by
  classical
  have hmF := measurable_particleObservable F hF 0
  have hmG := measurable_particleObservable G hG 0
  have hmC := measurable_particleObservable _ (measurable_clusterConvolution hF hG) 0
  simp only [zero_add] at hmF hmG hmC
  rw [lintegral_particleBase μ z hmC, lintegral_particleBase μ z hmF,
    lintegral_particleBase μ z hmG]
  let A (n : ℕ) := ∫⁻ x : Fin n → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ)
  let B (n : ℕ) := ∫⁻ x : Fin n → X, G (configurationMultiset x) ∂Measure.pi (fun _ => μ)
  have hN (N : ℕ) :
      (∫⁻ x : Fin N → X, clusterConvolution F G (configurationMultiset x) ∂Measure.pi (fun _ => μ)) =
        ∑ k ∈ Finset.range (N+1), (N.choose k : ℝ≥0∞)* (A (N-k)*B k) := by
    simp_rw [clusterConvolution_configuration]
    rw [lintegral_finsetSum]
    · have hi (T : Finset (Fin N)) :
          (∫⁻ x : Fin N → X,
            F (configurationMultiset (fun i : {i // i ∉ T} => x i))*
            G (configurationMultiset (fun i : T => x i)) ∂Measure.pi (fun _ => μ)) = A (N-T.card)*B T.card := by
        rw [configuration_split_integral hF hG μ T,
          configuration_integral_card F μ, configuration_integral_card G μ]
        have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
        have hcardB : Fintype.card {i : Fin N // i ∉ T} = N-T.card := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
        rw [hcardB, Fintype.card_coe T]
      simp_rw [hi]
      exact ennreal_subsets_card N (fun k => A (N-k)*B k)
    · intro T _
      have hFa : Measurable (fun x : Fin N → X => F (configurationMultiset (fun i : {i // i ∉ T} => x i))) := by
        have hh := (hF 0 {i // i ∉ T}).comp (show Measurable (fun x : Fin N → X => fun i : {i // i ∉ T} => x i) from measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
        simpa only [zero_add, Function.comp_def] using hh
      have hGa : Measurable (fun x : Fin N → X => G (configurationMultiset (fun i : T => x i))) := by
        have hh := (hG 0 T).comp (show Measurable (fun x : Fin N → X => fun i : T => x i) from measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
        simpa only [zero_add, Function.comp_def] using hh
      exact hFa.mul hGa
  simp only [particleMultiset]
  simp_rw [hN, Finset.mul_sum]
  have hcoeff (N k : ℕ) (hk : k ∈ Finset.range (N+1)) :
      fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k)) =
        (fockCoeff z k*B k)*(fockCoeff z (N-k)*A (N-k)) := by
    rw [← mul_assoc, fockCoeff_choose z (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    ring
  have hsum (N : ℕ) :
      (∑ k ∈ Finset.range (N+1), fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k))) =
      ∑ k ∈ Finset.range (N+1), (fockCoeff z k*B k)*(fockCoeff z (N-k)*A (N-k)) := by
    exact Finset.sum_congr rfl (fun k hk => hcoeff N k hk)
  change (∑' N, ∑ k ∈ Finset.range (N+1), fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k))) = _
  simp_rw [hsum]
  rw [ennreal_tsum_triangle (fun k n => (fockCoeff z k*B k)*(fockCoeff z n*A n))]
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right, mul_comm]
  rfl

end Fock
end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ClusterWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uM uY uZ

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma configurationMultiset_card {X : Type uX} {ι : Type} [Fintype ι] (x : ι → X) :
    (configurationMultiset x).card = Fintype.card ι := by
  rw [configurationMultiset_val, Multiset.card_map]
  exact Finset.card_univ

lemma configurationMultiset_sum_map {X : Type uX} {M : Type uM} [AddCommMonoid M] {ι : Type} [Fintype ι]
    (x : ι → X) (f : X → M) : ((configurationMultiset x).map f).sum = ∑ i, f (x i) := by
  rw [configurationMultiset_val, Multiset.map_map]
  rfl

lemma configurationMultiset_prod_map {X : Type uX} {M : Type uM} [CommMonoid M] {ι : Type} [Fintype ι]
    (x : ι → X) (f : X → M) : ((configurationMultiset x).map f).prod = ∏ i, f (x i) := by
  rw [configurationMultiset_val, Multiset.map_map]
  rfl

lemma measurable_regionMask {A : Set Position} (hA : MeasurableSet A) : Measurable (regionMask A) :=
  measurable_const.indicator hA

lemma measurable_nearMask (r : ℝ) : Measurable (Function.uncurry (nearMask r)) := by
  have hs : MeasurableSet {p : Position × Position | ∀ k, |p.2 k-p.1 k| ≤ r} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp continuous_snd).sub
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp continuous_fst)).abs.measurable measurable_const
  exact measurable_const.indicator hs

lemma measurable_multiset_prod {Y : Type uY} {Z : Type uZ} [MeasurableSpace Y]
    (s : Multiset Z) (f : Z → Y → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => (s.map (fun i => f i x)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact measurable_mul.comp ((hf a).prodMk ih)

lemma measurable_starWeight {A : Set Position} (hA : MeasurableSet A) (r : ℝ) :
    MeasurableConfiguration (starWeight A r) := by
  intro s ι _
  classical
  have hprod (a : (ι → Position) → Position) (ha : Measurable a) :
      Measurable (fun y => ((s+configurationMultiset y).map (nearMask r (a y))).prod) := by
    simp only [Multiset.map_add, Multiset.prod_add, configurationMultiset_prod_map]
    apply Measurable.mul
    · apply measurable_multiset_prod
      intro v
      exact (measurable_nearMask r).comp (ha.prodMk measurable_const)
    · apply Finset.measurable_prod
      intro i _
      exact (measurable_nearMask r).comp (ha.prodMk (measurable_pi_apply i))
  have he (x : ι → Position) : starWeight A r (s+configurationMultiset x) =
      (s.map (fun a => regionMask A a * ((s+configurationMultiset x).map (nearMask r a)).prod)).sum +
      ∑ i, regionMask A (x i) * ((s+configurationMultiset x).map (nearMask r (x i))).prod := by
    unfold starWeight
    rw [Multiset.map_add, Multiset.sum_add, configurationMultiset_sum_map]
  simp_rw [he]
  apply Measurable.add
  · apply measurable_multiset_sum
    intro a
    exact measurable_const.mul (hprod (fun _ => a) measurable_const)
  · apply Finset.measurable_sum
    intro i _
    exact ((measurable_regionMask hA).comp (measurable_pi_apply i)).mul
      (hprod (fun x => x i) (measurable_pi_apply i))

lemma measurable_emptyWeight {X : Type uX} [MeasurableSpace X] :
    MeasurableConfiguration (emptyWeight (X := X)) := by
  intro s ι _
  simp only [emptyWeight, Multiset.card_add, configurationMultiset_card]
  exact measurable_const

lemma measurable_cellClusterWeight (t α r : ℝ) (k : Cell) :
    MeasurableConfiguration (cellClusterWeight t α r k) := by
  intro s ι _
  simp only [cellClusterWeight, Multiset.card_add, configurationMultiset_card]
  split_ifs
  · exact (measurable_emptyWeight s ι).add (measurable_const.mul (measurable_starWeight (measurableSet_gridRegion k) r s ι))
  · exact (measurable_emptyWeight s ι).add measurable_const

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MultiConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

section Multi
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma particleBase_emptyWeight (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, emptyWeight (particleMultiset x) ∂particleBase μ z) = 1 := by
  have hm := measurable_particleObservable (emptyWeight (X := X)) measurable_emptyWeight 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase μ z hm, tsum_eq_single 0]
  · simp [particleMultiset, emptyWeight, configurationMultiset_card]
  · intro n hn
    simp [particleMultiset, emptyWeight, configurationMultiset_card, hn]

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_finClusterProduct (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) : MeasurableConfiguration (finClusterProduct n W) := by
  induction n with
  | zero => exact measurable_emptyWeight
  | succ n ih => exact measurable_clusterConvolution (hW 0) (ih _ (fun i => hW i.succ))

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma finClusterProduct_ge (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (u : Fin n → Multiset X) : (∏ i, W i (u i)) ≤ finClusterProduct n W (∑ i, u i) := by
  induction n with
  | zero => simp [finClusterProduct, emptyWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    exact (mul_le_mul' le_rfl (ih (fun i => W i.succ) (fun i => u i.succ))).trans
      (clusterConvolution_add_ge (W 0) (finClusterProduct n (fun i => W i.succ)) _ _)

lemma particleBase_finClusterProduct (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, finClusterProduct n W (particleMultiset x) ∂particleBase μ z) =
      ∏ i, ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z := by
  induction n with
  | zero => simpa only [finClusterProduct, Fin.prod_univ_zero] using particleBase_emptyWeight μ z
  | succ n ih =>
    rw [finClusterProduct, particleBase_convolution (hW 0)
      (measurable_finClusterProduct _ _ (fun i => hW i.succ)), ih _ (fun i => hW i.succ), Fin.prod_univ_succ]

variable {I : Type} [Fintype I]

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_indexedClusterProduct (W : I → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) : MeasurableConfiguration (indexedClusterProduct W) :=
  measurable_finClusterProduct _ _ (fun _i => hW _)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma indexedClusterProduct_ge (W : I → Multiset X → ℝ≥0∞) (u : I → Multiset X) :
    (∏ i, W i (u i)) ≤ indexedClusterProduct W (∑ i, u i) := by
  have hh := finClusterProduct_ge (Fintype.card I)
    (fun i => W ((Fintype.equivFin I).symm i)) (fun i => u ((Fintype.equivFin I).symm i))
  rw [Equiv.sum_comp, Equiv.prod_comp (Fintype.equivFin I).symm (fun i => W i (u i))] at hh
  exact hh

lemma particleBase_indexedClusterProduct (W : I → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, indexedClusterProduct W (particleMultiset x) ∂particleBase μ z) =
      ∏ i, ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z := by
  rw [indexedClusterProduct, particleBase_finClusterProduct _ _ (fun _i => hW _)]
  exact Equiv.prod_comp (Fintype.equivFin I).symm (fun i => ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z)

end Multi
end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ClusterEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma configurationMultiset_fibers {X : Type uX} {ι I : Type} [Fintype ι] [Fintype I]
    (x : ι → X) (f : ι → I) :
    ∑ q : I, ((Finset.univ.filter (fun j => f j = q)).val.map x) = configurationMultiset x := by
  classical
  have hq (q : I) : ((Finset.univ.filter (fun j => f j=q)).val.map x) =
      ∑ j : ι, if f j=q then ({x j}:Multiset X) else 0 := by
    rw [← Finset.sum_filter]
    change _ = ((Finset.univ.filter (fun j => f j=q)).val.map (fun j => ({x j}:Multiset X))).sum
    simpa only [Multiset.map_map, Function.comp_def] using
      (Multiset.sum_map_singleton ((Finset.univ.filter (fun j => f j=q)).val.map x)).symm
  simp_rw [hq]
  rw [Finset.sum_comm]
  simp [configurationMultiset]

section Embed
variable {X : Type uX} {I Q : Type} [Fintype I] [Fintype Q]

lemma indexedClusterProduct_embedding (W : I → Multiset X → ℝ≥0∞)
    (h0 : ∀ i, 1 ≤ W i 0) (f : Q → I) (hf : Function.Injective f) (s : Q → Multiset X) :
    (∏ q, W (f q) (s q)) ≤ indexedClusterProduct W (∑ q, s q) := by
  classical
  let u (i : I) : Multiset X := ∑ q : Q, if f q=i then s q else 0
  have huv (q : Q) : u (f q) = s q := by
    simp [u, hf.eq_iff]
  have huz (i : I) (hi : i ∉ Finset.univ.image f) : u i = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact ite_eq_right (fun he => hi (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,he⟩))
  have hsum : ∑ i, u i = ∑ q, s q := by
    simp only [u]
    rw [Finset.sum_comm]
    simp
  have hp : (∏ q, W (f q) (s q)) = ∏ i ∈ Finset.univ.image f, W i (u i) := by
    rw [Finset.prod_image (fun a _ b _ hab => hf hab)]
    simp_rw [huv]
  rw [hp]
  have hle : (∏ i ∈ Finset.univ.image f, W i (u i)) ≤ ∏ i, W i (u i) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun _ _ => bot_le)
    intro i _ hi
    rw [huz i hi]
    exact h0 i
  apply hle.trans
  rw [← hsum]
  exact indexedClusterProduct_ge W u

end Embed
end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma same_cell_dist_lt {x y : Position} (h : cellOf x = cellOf y) : dist x y < 1 := by
  have hc (k : Fin 3) : |x k-y k| ≤ 1/4 := by
    have hh : ⌊4*x k⌋ = ⌊4*y k⌋ := congrFun h k
    have hxl := Int.floor_le (4*x k)
    have hxu := Int.lt_floor_add_one (4*x k)
    have hyl := Int.floor_le (4*y k)
    have hyu := Int.lt_floor_add_one (4*y k)
    rw [← hh] at hyl hyu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : dist x y ^ 2 ≤ 3*(1/4:ℝ)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ k : Fin 3, (1/4:ℝ)^2 := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.dist_eq] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hc k))
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

lemma coreFree_fiber_card {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (q : Quotient (coreFreeSetoid hx ht)) :
    (Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)).card ≤ 4 := by
  classical
  let S := Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)
  have hclique : (shellGraph x (microLength t)).IsClique S := by
    intro i hi j hj hij
    have hiq : Quotient.mk (coreFreeSetoid hx ht) i = q := (Finset.mem_filter.mp hi).2
    have hjq : Quotient.mk (coreFreeSetoid hx ht) j = q := (Finset.mem_filter.mp hj).2
    exact ⟨hij, hx i j hij (Quotient.exact (hiq.trans hjq.symm))⟩
  by_contra hc
  change ¬ S.card ≤ 4 at hc
  have h5 : 5 ≤ S.card := by omega
  exact (SimpleGraph.CliqueFree.mono h5 (shellGraph_cliqueFree x (microLength_pos t))) S
    ⟨hclique, rfl⟩

lemma coreFree_roots {ι : Type uIndex} [Fintype ι] {t L : ℝ} {x : ι → Position}
    (hx : CoreFree t x) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hbox : ∀ i, x i ∈ cube L) :
    Fintype.card (Quotient (coreFreeSetoid hx ht)) ≤ packingNumber L ∧
      Function.Injective (fun q : Quotient (coreFreeSetoid hx ht) => cellOf (x q.out)) := by
  classical
  let Q := Quotient (coreFreeSetoid hx ht)
  have hsep (q r : Q) (hqr : q ≠ r) : 1 ≤ dist (x q.out) (x r.out) := by
    by_contra! hh
    apply hqr
    have he : Quotient.mk (coreFreeSetoid hx ht) q.out = Quotient.mk (coreFreeSetoid hx ht) r.out :=
      Quotient.sound hh
    simpa only [Quotient.out_eq] using he
  have hinj : Function.Injective (fun q : Q => x q.out) := by
    intro q r he
    by_contra hne
    have hh := hsep q r hne
    change x q.out = x r.out at he
    rw [he, dist_self] at hh
    norm_num at hh
  constructor
  · let S := Finset.univ.image (fun q : Q => x q.out)
    have hp : IsPacking L S := by
      constructor
      · intro y hy
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
        exact hbox _
      · intro y hy z hz hyz
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
        exact hsep q r (fun he => hyz (congrArg (fun q : Q => x q.out) he))
    have hh := packing_card_le hp
    simpa only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hh
  · intro q r he
    by_contra hne
    exact (not_lt_of_ge (hsep q r hne)) (same_cell_dist_lt he)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FreeClusterCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma starWeight_ge_one {A : Set Position} {r : ℝ} {s : Multiset Position} {x : Position}
    (hx : x ∈ s) (hA : x ∈ A) (hr : ∀ y ∈ s, y ∈ nearCube r x) :
    1 ≤ starWeight A r s := by
  have hp : (s.map (nearMask r x)).prod = 1 := by
    apply Multiset.prod_eq_one
    intro a ha
    obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp ha
    exact indicator_of_mem (hr y hy) _
  have hs := Multiset.single_le_sum (fun _ _ => (bot_le : (0:ℝ≥0∞) ≤ _))
    _ (Multiset.mem_map.mpr ⟨x,hx,rfl⟩ : regionMask A x*(s.map (nearMask r x)).prod ∈
      s.map (fun y => regionMask A y*(s.map (nearMask r y)).prod))
  simpa only [hp, regionMask, indicator_of_mem hA, mul_one, starWeight] using hs

lemma cellClusterWeight_empty (t α r : ℝ) (k : Cell) : 1 ≤ cellClusterWeight t α r k 0 := by
  simp [cellClusterWeight, emptyWeight, starWeight]

lemma cellClusterWeight_ge {t α r : ℝ} {k : Cell} {s : Multiset Position}
    (hc : s.card ≤ 4) {x : Position} (hx : x ∈ s) (hk : cellOf x=k)
    (hr : ∀ y ∈ s, y ∈ nearCube r x) :
    ENNReal.ofReal (Real.exp (-t*α)) ≤ cellClusterWeight t α r k s := by
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal (Real.exp (-t*α)) ≤ _) (starWeight_ge_one hx (show x ∈ gridRegion k from hk) hr)
  rw [mul_one] at hh
  exact hh.trans (by simp only [cellClusterWeight, ite_eq_left hc]; exact le_add_self)

lemma coreFree_cell_cover {ι : Type} [Fintype ι] {t α L : ℝ} {x : ι → Position}
    (hx : CoreFree t x) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hbox : ∀ i, x i ∈ cube L) (hta : 0 ≤ t*α) :
    ENNReal.ofReal (Real.exp (-t*α*(packingNumber L:ℝ))) ≤
      indexedClusterProduct (fun k : cubeCells L =>
        cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val) (configurationMultiset x) := by
  classical
  let Q := Quotient (coreFreeSetoid hx ht)
  let S (q : Q) := Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)
  let s (q : Q) := (S q).val.map x
  let f (q : Q) : cubeCells L := ⟨cellOf (x q.out), cellOf_mem_cubeCells (hbox _)⟩
  let W (k : cubeCells L) := cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val
  have hroot := coreFree_roots hx ht hbox
  have hf : Function.Injective f := by
    intro q q' he
    exact hroot.2 (congrArg Subtype.val he)
  have hsum : ∑ q, s q = configurationMultiset x := by
    convert configurationMultiset_fibers x (Quotient.mk (coreFreeSetoid hx ht)) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro q _
    dsimp [s, S]
    congr 1
    ext i
    simp only [Multiset.count_filter]
    split_ifs <;> rfl
  have hW (q : Q) : ENNReal.ofReal (Real.exp (-t*α)) ≤ W (f q) (s q) := by
    apply cellClusterWeight_ge
    · simpa only [s, Multiset.card_map, S, Finset.card_def] using coreFree_fiber_card hx ht q
    · apply Multiset.mem_map.mpr
      refine ⟨q.out, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.out_eq q⟩
    · rfl
    · intro y hy
      obtain ⟨j,hj,rfl⟩ := Multiset.mem_map.mp hy
      have hjq : Quotient.mk (coreFreeSetoid hx ht) j = q := (Finset.mem_filter.mp hj).2
      have hd : dist (x j) (x q.out) < 1 := Quotient.exact (hjq.trans (Quotient.out_eq q).symm)
      intro d
      simpa only [Real.dist_eq] using (PiLp.dist_apply_le (x j) (x q.out) d).trans (hx.dist_bound j q.out hd)
  have hprod : ENNReal.ofReal (Real.exp (-t*α*(Fintype.card Q:ℝ))) ≤ ∏ q, W (f q) (s q) := by
    have hh := Finset.prod_le_prod' (fun q (_ : q ∈ (Finset.univ : Finset Q)) => hW q)
    simp only [Finset.prod_const, Finset.card_univ] at hh
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at hh
    rw [mul_comm (Fintype.card Q : ℝ)] at hh
    exact hh
  have hcount : ENNReal.ofReal (Real.exp (-t*α*(packingNumber L:ℝ))) ≤
      ENNReal.ofReal (Real.exp (-t*α*(Fintype.card Q:ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hc : (Fintype.card Q:ℝ) ≤ packingNumber L := by exact_mod_cast hroot.1
    nlinarith
  have hcover := indexedClusterProduct_embedding W (fun k => cellClusterWeight_empty _ _ _ _) f hf s
  rw [hsum] at hcover
  exact hcount.trans (hprod.trans hcover)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BadRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma after_removal_free {ι : Type uIndex} [Fintype ι] (t : ℝ) (x : ι → Position) :
    CoreFree t (fun i : {i // i ∉ badLabels t x} => x i) := by
  intro i j hij hd
  by_contra hs
  apply i.property
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.val, fun he => hij (Subtype.ext he), hd, hs⟩

lemma badLabels_energy {ι : Type uIndex} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (x : ι → Position) :
    t^2 * (badLabels t x).card / 2 ≤ orderedEnergy (corePotential t) x := by
  classical
  have hrow (i : ι) : (if i ∈ badLabels t x then t^2 else 0) ≤
      ∑ j, if i ≠ j then corePotential t (nndist (x i) (x j)) else 0 := by
    have hnon (j : ι) : (0:ℝ) ≤ if i ≠ j then corePotential t (nndist (x i) (x j)) else 0 := by
      split_ifs
      · exact coreReal_nonneg _ _
      · rfl
    by_cases hi : i ∈ badLabels t x
    · obtain ⟨j,hij,hd,hs⟩ := (Finset.mem_filter.mp hi).2
      have hfull : corePotential t (nndist (x i) (x j)) = t^2 := coreReal_full_of_not_shell ht hd.le hs
      rw [ite_eq_left hi]
      have hh := Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)
      simpa only [ite_eq_left hij, hfull] using hh
    · rw [ite_eq_right hi]
      exact Finset.sum_nonneg (fun j _ => hnon j)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  have hsum : (∑ i : ι, if i ∈ badLabels t x then t^2 else 0) = t^2*(badLabels t x).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsum] at hh
  exact div_le_div_of_nonneg_right hh (by norm_num)

lemma measurable_removalWeight (t β : ℝ) : MeasurableConfiguration (removalWeight t β) := by
  intro s ι _
  simp only [removalWeight, Multiset.card_add, configurationMultiset_card]
  exact measurable_const

lemma particleBase_removalWeight {μ : Measure Position} (hμ : μ univ ≠ ⊤) (t β z : ℝ) :
    (∫⁻ x, removalWeight t β (particleMultiset x) ∂particleBase μ z) =
      ENNReal.ofReal (Real.exp ((μ univ).toReal*Real.exp (z-β*t^2/2))) := by
  have hm := measurable_particleObservable _ (measurable_removalWeight t β) 0
  simp only [zero_add] at hm
  have hh := lintegral_particleBase μ (z-β*t^2/2) (f := fun _ => (1:ℝ≥0∞)) measurable_const
  simp only [lintegral_one] at hh
  rw [lintegral_particleBase μ z hm, ← particleBase_univ hμ (z-β*t^2/2), hh]
  apply tsum_congr
  intro n
  simp only [particleMultiset, removalWeight, configurationMultiset_card, Fintype.card_fin,
    lintegral_const]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 1
  ring_nf

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_StarIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma measurableSet_nearCube (r : ℝ) (x : Position) : MeasurableSet (nearCube r x) := by
  simp only [nearCube, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).sub continuous_const).abs.measurable) measurable_const

lemma nearCube_translate (r : ℝ) (x : Position) :
    nearCube r x = translateSet (x-WithLp.toLp 2 (fun _ : Fin 3 => r)) (cube (2*r)) := by
  ext y
  change (∀ k, |y k-x k| ≤ r) ↔ ∀ k, 0 ≤ y k-(x k-r) ∧ y k-(x k-r) ≤ 2*r
  simp only [abs_le]
  constructor <;> intro h k <;> obtain ⟨h1,h2⟩ := h k <;> constructor <;> linarith

lemma volume_nearCube (r : ℝ) (x : Position) :
    volume (nearCube r x) = ENNReal.ofReal (2*r)^3 := by
  rw [nearCube_translate, volume_translateSet _ _ (measurableSet_cube _), volume_cube]

lemma nearMask_self {r : ℝ} (hr : 0 ≤ r) (x : Position) : nearMask r x x = 1 := by
  apply indicator_of_mem
  intro k
  simpa using hr

lemma lintegral_nearMask_prod (n : ℕ) (r : ℝ) (x : Position) :
    (∫⁻ y : Fin n → Position, ∏ j, nearMask r x (y j) ∂Measure.pi (fun _ => volume)) =
      (ENNReal.ofReal (2*r)^3)^n := by
  have he (y : Fin n → Position) :
      (∏ j, nearMask r x (y j)) = (Set.pi univ (fun _ : Fin n => nearCube r x)).indicator (fun _ => 1) y := by
    simp [nearMask, Set.indicator, Finset.prod_boole, Set.mem_pi]
  simp_rw [he]
  change (∫⁻ y, (Set.pi univ (fun _ : Fin n => nearCube r x)).indicator (1 : (Fin n → Position) → ℝ≥0∞) y ∂Measure.pi (fun _ => volume)) = _
  rw [lintegral_indicator_one, Measure.pi_pi, volume_nearCube]
  · simp
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_nearCube r x)

lemma lintegral_rootStar (A : Set Position) (hA : MeasurableSet A) {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ x : Fin (n+1) → Position, regionMask A (x i)*∏ j, nearMask r (x i) (x j)
      ∂Measure.pi (fun _ => volume)) = volume A*(ENNReal.ofReal (2*r)^3)^n := by
  have hprod : Measurable (fun p : Position × (Fin n → Position) =>
      regionMask A p.1 * ∏ j, nearMask r p.1 (p.2 j)) := by
    apply ((measurable_regionMask hA).comp measurable_fst).mul
    apply Finset.measurable_prod
    intro j _
    exact (measurable_nearMask r).comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure Position)) i).lintegral_comp hprod
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply, Fin.removeNth_apply] at hh
  have he (x : Fin (n+1) → Position) : (∏ j, nearMask r (x i) (x j)) = ∏ j : Fin n, nearMask r (x i) (x (i.succAbove j)) := by
    rw [i.prod_univ_succAbove, nearMask_self hr, one_mul]
  simp_rw [he]
  rw [hh, lintegral_prod _ hprod.aemeasurable]
  have hfin (x : Position) : regionMask A x ≠ ⊤ := by
    by_cases hx : x ∈ A <;> simp [regionMask, hx]
  simp_rw [lintegral_const_mul' _ _ (hfin _)]
  simp_rw [lintegral_nearMask_prod]
  rw [lintegral_mul_const']
  · change (∫⁻ x, A.indicator (1 : Position → ℝ≥0∞) x) * _ = _
    rw [lintegral_indicator_one hA]
  · exact (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

lemma lintegral_starWeight (A : Set Position) (hA : MeasurableSet A) {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) :
    (∫⁻ x : Fin (n+1) → Position, starWeight A r (configurationMultiset x)
      ∂Measure.pi (fun _ => volume)) = (n+1 : ℕ)*(volume A*(ENNReal.ofReal (2*r)^3)^n) := by
  simp only [starWeight, configurationMultiset_sum_map, configurationMultiset_prod_map]
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_rootStar A hA hr]
    simp
  · intro i _
    apply ((measurable_regionMask hA).comp (measurable_pi_apply i)).mul
    apply Finset.measurable_prod
    intro j _
    have hm := (measurable_nearMask r).comp
      ((show Measurable (fun x : Fin (n+1) → Position => x i) from measurable_pi_apply i).prodMk
        (show Measurable (fun x : Fin (n+1) → Position => x j) from measurable_pi_apply j))
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hm

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma cluster_rate_le {h α : ℝ} (h1 : h ≤ α) (h4 : 4*h-9 ≤ α)
    {n : ℕ} (hn : n ≤ 3) : h*(n+1)-3*n ≤ α := by
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn3 : (n:ℝ) ≤ 3 := by exact_mod_cast hn
  by_cases hh : h ≤ 3
  · nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hh)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hn3) (sub_nonneg.mpr (le_of_not_ge hh))]

lemma core_cluster_coefficient_bound {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) {n : ℕ} (hn : n ≤ 3) :
    Real.exp (t*h*(n+1))/(n+1).factorial * Real.exp (-t*α) *
      ((n+1)*((2*((1+(1:ℝ)/1000)*microLength t))^3)^n) ≤ 3000 := by
  have hl := (microLength_pos t).le
  have hfac : (1:ℝ) ≤ (n+1).factorial := by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n+1)))
  have he : Real.exp (t*h*(n+1))*Real.exp (-t*α)*
      (((2*((1+(1:ℝ)/1000)*microLength t))^3)^n) =
      Real.exp (t*(h*(n+1)-3*n-α))*((2*(1+(1:ℝ)/1000))^3)^n := by
    have hbase : 2*((1+(1:ℝ)/1000)*microLength t) = (2*(1+(1:ℝ)/1000))*microLength t := by ring
    rw [hbase, mul_pow, mul_pow]
    have hexp : (microLength t^3)^n = Real.exp ((n:ℝ)*(3*(-t))) := by
      simp only [microLength, ← Real.exp_nat_mul, Nat.cast_ofNat]
    rw [hexp]
    calc
      _ = (Real.exp (t*h*(n+1))*Real.exp (-t*α)*Real.exp ((n:ℝ)*(3*(-t))))*
          ((2*(1+(1:ℝ)/1000))^3)^n := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have hrate : Real.exp (t*(h*(n+1)-3*n-α)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr (cluster_rate_le h1 h4 hn))
  have hpow : (n+1:ℝ)*((2*(1+(1:ℝ)/1000))^3)^n ≤ 3000 := by
    interval_cases n <;> norm_num
  calc
    _ ≤ Real.exp (t*h*(n+1))*Real.exp (-t*α)*
        (((2*((1+(1:ℝ)/1000)*microLength t))^3)^n)*(n+1) := by
      have hc : Real.exp (t*h*(n+1))/(n+1).factorial ≤ Real.exp (t*h*(n+1)) :=
        div_le_self (Real.exp_pos _).le hfac
      nlinarith [mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Real.exp_pos (-t*α)).le
          (mul_nonneg (show (0:ℝ) ≤ n+1 by positivity) (by positivity : 0 ≤ ((2*((1+(1:ℝ)/1000)*microLength t))^3)^n)))]
    _ = Real.exp (t*(h*(n+1)-3*n-α))*(((2*(1+(1:ℝ)/1000))^3)^n)*(n+1) := by rw [he]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right hrate
        (mul_nonneg (by positivity : 0 ≤ ((2*(1+(1:ℝ)/1000))^3)^n) (show (0:ℝ) ≤ n+1 by positivity))]

lemma lintegral_cellClusterWeight_sector {t α r : ℝ} (hr : 0 ≤ r) (k : Cell)
    {n : ℕ} (hn : n ≤ 3) :
    (∫⁻ x : Fin (n+1) → Position, cellClusterWeight t α r k (configurationMultiset x)
      ∂Measure.pi (fun _ => volume)) =
    ENNReal.ofReal (Real.exp (-t*α))*((n+1 : ℕ)*(volume (gridRegion k)*(ENNReal.ofReal (2*r)^3)^n)) := by
  have hn4 : n+1 ≤ 4 := by omega
  simp only [cellClusterWeight, emptyWeight, configurationMultiset_card, Fintype.card_fin,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, if_false, ite_eq_left hn4, zero_add]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_starWeight _ (measurableSet_gridRegion _) hr]

lemma particleBase_cellClusterWeight_le {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) (k : Cell) :
    (∫⁻ x, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset x)
      ∂particleBase volume (t*h)) ≤ 15001 := by
  have hl := (microLength_pos t).le
  have hm := measurable_particleObservable _ (measurable_cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k) 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase _ _ hm]
  have hz (n : ℕ) (hn : n ∉ Finset.range 5) :
      ENNReal.ofReal (Real.exp (t*h*n)/n.factorial)*
      (∫⁻ x : Fin n → Position, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset ⟨n,x⟩)
        ∂Measure.pi (fun _ => volume)) = 0 := by
    have hn4 : ¬n ≤ 4 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    have hn0 : n ≠ 0 := by omega
    simp [particleMultiset, cellClusterWeight, emptyWeight, configurationMultiset_card, hn4, hn0]
  rw [tsum_eq_sum hz]
  have hterm (n : ℕ) (hn : n ∈ Finset.range 5) :
      ENNReal.ofReal (Real.exp (t*h*n)/n.factorial)*
      (∫⁻ x : Fin n → Position, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset ⟨n,x⟩)
        ∂Measure.pi (fun _ => volume)) ≤ 3000 := by
    rcases n with _|n
    · norm_num [particleMultiset, cellClusterWeight, emptyWeight, starWeight, configurationMultiset, Finset.univ_eq_empty]
    have hn3 : n ≤ 3 := by have := Finset.mem_range.mp hn; omega
    change ENNReal.ofReal _ * (∫⁻ x : Fin (n+1) → Position,
      cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (configurationMultiset x) ∂Measure.pi (fun _ => volume)) ≤ _
    rw [lintegral_cellClusterWeight_sector (by positivity) k hn3]
    have hv : volume (gridRegion k) ≤ (1:ℝ≥0∞) :=
      (volume_gridRegion_le k).trans (by norm_num)
    apply le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hv le_rfl)) ))
    simp only [one_mul]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*((1+(1:ℝ)/1000)*microLength t)),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ (2*((1+(1:ℝ)/1000)*microLength t))^3)]
    have hnat : ((n+1:ℕ):ℝ≥0∞) = ENNReal.ofReal ((n+1:ℕ):ℝ) := by norm_cast
    rw [hnat, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have hb := ENNReal.ofReal_le_ofReal (core_cluster_coefficient_bound ht h1 h4 hn3)
    norm_num only [ENNReal.ofReal_ofNat, Nat.cast_add, Nat.cast_one] at hb ⊢
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    _ ≤ ∑ _n ∈ Finset.range 5, (3000:ℝ≥0∞) := Finset.sum_le_sum hterm
    _ ≤ 15001 := by norm_num

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma measurable_freeCoverWeight (L t α : ℝ) : MeasurableConfiguration (freeCoverWeight L t α) :=
  measurable_indexedClusterProduct _ (fun _ => measurable_cellClusterWeight _ _ _ _)

lemma core_boltzmann_cover {ι : Type} [Fintype ι] {t α L β : ℝ} {x : ι → Position}
    (ht0 : 0 ≤ t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hbox : ∀ i, x i ∈ cube L) (hta : 0 ≤ t*α) :
    ENNReal.ofReal (Real.exp (-β*orderedEnergy (corePotential t) x)) ≤
    ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (configurationMultiset x) := by
  classical
  let B := badLabels t x
  let good := configurationMultiset (fun i : {i // i ∉ B} => x i)
  let bad := configurationMultiset (fun i : B => x i)
  have hfree : ENNReal.ofReal (Real.exp (-t*α*packingNumber L)) ≤ freeCoverWeight L t α good :=
    coreFree_cell_cover (after_removal_free t x) ht (fun i => hbox i.val) hta
  have hsum : freeCoverWeight L t α good*removalWeight t β bad ≤
      clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (configurationMultiset x) := by
    rw [clusterConvolution_configuration]
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Finset ι)))
      (f := fun T : Finset ι => freeCoverWeight L t α (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
        removalWeight t β (configurationMultiset (fun i : T => x i)))
      (fun _ _ => (bot_le : (0:ℝ≥0∞) ≤ _)) (Finset.mem_univ B)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl

  have hb : ENNReal.ofReal (Real.exp (-β*orderedEnergy (corePotential t) x)) ≤
      removalWeight t β bad := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change -β*orderedEnergy (corePotential t) x ≤ -β*t^2*(configurationMultiset (fun i : B => x i)).card/2
    rw [configurationMultiset_card, Fintype.card_coe]
    have he := mul_le_mul_of_nonneg_left (badLabels_energy ht0 x) hβ
    dsimp [B]
    nlinarith
  have hc : ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      ENNReal.ofReal (Real.exp (-t*α*packingNumber L)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    convert (by norm_num : ENNReal.ofReal (Real.exp 0) = 1) using 2 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  calc
    _ ≤ removalWeight t β bad := hb
    _ = ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      (ENNReal.ofReal (Real.exp (-t*α*packingNumber L))*removalWeight t β bad) := by rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl ((mul_le_mul' hfree le_rfl).trans hsum)

lemma particleBase_ae_cube (L z : ℝ) :
    ∀ᵐ s : ParticleState Position ∂particleBase (volume.restrict (cube L)) z,
      ∀ i, s.2 i ∈ cube L := by
  rw [particleBase, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [(Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).ae_map_iff]
  rw [← Measure.restrict_pi_pi]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ : Fin n => measurableSet_cube L))] with x hx
  exact fun i => hx i (Set.mem_univ i)

lemma particleBase_restrict_le (A : Set Position) (z : ℝ) (F : Multiset Position → ℝ≥0∞)
    (hF : MeasurableConfiguration F) :
    (∫⁻ x, F (particleMultiset x) ∂particleBase (volume.restrict A) z) ≤
      ∫⁻ x, F (particleMultiset x) ∂particleBase volume z := by
  have hm := measurable_particleObservable F hF 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase _ _ hm, lintegral_particleBase _ _ hm]
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul' le_rfl
  rw [← Measure.restrict_pi_pi]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma particleBase_freeCoverWeight_le {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) (L : ℝ) :
    (∫⁻ x, freeCoverWeight L t α (particleMultiset x)
      ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ (15001:ℝ≥0∞)^(cubeCells L).card := by
  rw [freeCoverWeight, particleBase_indexedClusterProduct _ (fun _ => measurable_cellClusterWeight _ _ _ _)]
  have hh : ∀ k : cubeCells L,
      (∫⁻ x, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val (particleMultiset x)
        ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ 15001 := by
    intro k
    exact (particleBase_restrict_le _ _ _ (measurable_cellClusterWeight _ _ _ _)).trans
      (particleBase_cellClusterWeight_le ht h1 h4 k.val)
  simpa using Finset.prod_le_prod' (fun k (_ : k ∈ (Finset.univ : Finset (cubeCells L))) => hh k)

lemma stable_corePotential (t : ℝ) : StableWith (corePotential t) 0 := by
  intro N x
  simp only [zero_mul, neg_zero, energy]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => coreReal_nonneg _ _))

lemma core_grand_upper {t α L β h : ℝ} (hL : 0 ≤ L)
    (ht0 : 0 ≤ t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hta : 0 ≤ t*α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    ENNReal.ofReal (grandPartition (corePotential t) t L β h) ≤
      ENNReal.ofReal (Real.exp (t*α*packingNumber L))*
      ((15001:ℝ≥0∞)^(cubeCells L).card *
        ENNReal.ofReal (Real.exp (L^3*Real.exp (t*h-β*t^2/2)))) := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; finiteness
  have hmass : (volume.restrict (cube L) univ).toReal = L^3 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_cube,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL]
  rw [← grandOn_cube]
  rw [← lintegral_grandOn (continuous_corePotential t) (bounded_corePotential t) (stable_corePotential t) hβ hfin]
  have hle := lintegral_mono_ae ((particleBase_ae_cube L (t*h)).mono (fun x hx => core_boltzmann_cover ht0 ht hβ hx hta))
  apply hle.trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change _ * (∫⁻ x, clusterConvolution (freeCoverWeight L t α) (removalWeight t β) (particleMultiset x) ∂particleBase (volume.restrict (cube L)) (t*h)) ≤ _
  rw [particleBase_convolution (measurable_freeCoverWeight _ _ _) (measurable_removalWeight _ _),
    particleBase_removalWeight (by simpa using hfin), hmass]
  exact mul_le_mul' le_rfl (mul_le_mul' (particleBase_freeCoverWeight_le ht0 h1 h4 L) le_rfl)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_TetraGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma dist_le_twice_coordinate {x y : Position} {a : ℝ} (ha : 0 ≤ a)
    (hxy : ∀ k, |x k-y k| ≤ a) : dist x y ≤ 2*a := by
  have hh : dist x y ^ 2 ≤ 3*a^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _k : Fin 3, a^2 := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.dist_eq] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hxy k))
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

lemma tetraEdge_pos (t : ℝ) : 0 < tetraEdge t := by
  unfold tetraEdge
  have := microLength_pos t
  positivity

lemma tetraEpsilon_pos (t : ℝ) : 0 < tetraEpsilon t := div_pos (microLength_pos t) (by norm_num)

lemma tetraVertex_zero (t : ℝ) : tetraVertex t 0 = 0 := by ext k; simp [tetraVertex]

lemma tetraVertex_coordinate (t : ℝ) (i : Fin 4) (k : Fin 3) :
    0 ≤ tetraVertex t i k ∧ tetraVertex t i k ≤ 2*microLength t := by
  have hl := (microLength_pos t).le
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 : Real.sqrt (2:ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  change 0 ≤ (if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2) ∧
    (if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2) ≤ 2*microLength t
  split_ifs
  · exact ⟨le_rfl, by positivity⟩
  · constructor
    · exact div_nonneg (mul_nonneg (tetraEdge_pos t).le hs0) (by norm_num)
    · unfold tetraEdge
      nlinarith [mul_le_mul_of_nonneg_left hs2 (tetraEdge_pos t).le]

lemma tetraVertex_dist (t : ℝ) {i j : Fin 4} (hij : i ≠ j) :
    dist (tetraVertex t i) (tetraVertex t j) = tetraEdge t := by
  have hs : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : (tetraEdge t*Real.sqrt 2/2)^2 = (tetraEdge t)^2/2 := by
    calc
      _ = (tetraEdge t)^2*(Real.sqrt 2)^2/4 := by ring
      _ = _ := by rw [hs]; ring
  have hd : dist (tetraVertex t i) (tetraVertex t j)^2 = (tetraEdge t)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | norm_num [tetraVertex, Fin.sum_univ_succ, Real.dist_eq, sq_abs]; nlinarith [ha]
  nlinarith [dist_nonneg (x := tetraVertex t i) (y := tetraVertex t j), tetraEdge_pos t]

lemma tetraRegion_error {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) (i : Fin 4) :
    dist (x i) (x 0+tetraVertex t i) ≤ 2*tetraEpsilon t := by
  cases i using Fin.cases with
  | zero => simp only [tetraVertex_zero, add_zero, dist_self]; positivity [tetraEpsilon_pos t]
  | succ i =>
    apply dist_le_twice_coordinate (tetraEpsilon_pos t).le
    intro k
    have hk := hx.2 i k
    change 0 ≤ x i.succ k-x 0 k-tetraVertex t i.succ k ∧ x i.succ k-x 0 k-tetraVertex t i.succ k ≤ tetraEpsilon t at hk
    change |x i.succ k-(x 0 k+tetraVertex t i.succ k)| ≤ tetraEpsilon t
    rw [abs_of_nonneg (by linarith : 0 ≤ x i.succ k-(x 0 k+tetraVertex t i.succ k))]
    linarith

lemma tetraRegion_core_zero {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) :
    energy (corePotential t) x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij := ne_of_lt (Finset.mem_filter.mp hj).2
  have hdist : dist (x 0+tetraVertex t i) (x 0+tetraVertex t j) = tetraEdge t := by
    rw [dist_add_left, tetraVertex_dist t hij]
  have hi := tetraRegion_error hx i
  have hj := tetraRegion_error hx j
  have hupper := dist_triangle4 (x i) (x 0+tetraVertex t i) (x 0+tetraVertex t j) (x j)
  have hlower := dist_triangle4 (x 0+tetraVertex t i) (x i) (x j) (x 0+tetraVertex t j)
  rw [hdist, dist_comm (x 0+tetraVertex t j) (x j)] at hupper
  rw [hdist, dist_comm (x 0+tetraVertex t i) (x i)] at hlower
  apply coreReal_zero_plateau
  · change microLength t + shellStep t ≤ dist (x i) (x j)
    dsimp [tetraEdge, tetraEpsilon, shellStep] at *
    linarith [microLength_pos t]
  · change dist (x i) (x j) ≤ microLength t + 2*shellStep t
    dsimp [tetraEdge, tetraEpsilon, shellStep] at *
    linarith [microLength_pos t]

lemma tetraRegion_cube {t a : ℝ} {x : Fin 4 → Position} (hx : x ∈ tetraRegion t a) :
    x ∈ configurationCube (a+3*microLength t) 4 := by
  intro i k
  have hl := (microLength_pos t).le
  cases i using Fin.cases with
  | zero => have hh := hx.1 k; constructor <;> linarith
  | succ i =>
    have hi := hx.2 i k
    change 0 ≤ x i.succ k-x 0 k-tetraVertex t i.succ k ∧ x i.succ k-x 0 k-tetraVertex t i.succ k ≤ tetraEpsilon t at hi
    have hv := tetraVertex_coordinate t i.succ k
    have h0 := hx.1 k
    dsimp [tetraEpsilon] at hi
    constructor <;> linarith

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PackingBlob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma packingBlob_distance {ν b : ℝ} {z x : Position} (hb : 0 ≤ b)
    (hx : x ∈ packingBlob ν b z) : dist x ((1+ν) • z) ≤ 2*b := by
  apply dist_le_twice_coordinate hb
  intro k
  have hk := hx k
  change 0 ≤ x k-(1+ν)*z k ∧ x k-(1+ν)*z k ≤ b at hk
  change |x k-(1+ν)*z k| ≤ b
  rw [abs_of_nonneg hk.1]
  exact hk.2

lemma packingBlob_separation {ν b : ℝ} {z w x y : Position} (hν : 0 ≤ ν) (hb : 0 ≤ b)
    (hzw : 1 ≤ dist z w) (hx : x ∈ packingBlob ν b z) (hy : y ∈ packingBlob ν b w) :
    1+ν-4*b ≤ dist x y := by
  have hz := packingBlob_distance hb hx
  have hw := packingBlob_distance hb hy
  have hd : dist ((1+ν) • z) ((1+ν) • w) = (1+ν)*dist z w := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), dist_eq_norm]
  have he := dist_triangle4 ((1+ν) • z) x y ((1+ν) • w)
  rw [hd, dist_comm ((1+ν) • z) x] at he
  have hm := mul_le_mul_of_nonneg_left hzw (show 0 ≤ 1+ν by linarith)
  linarith

lemma packingBlob_subset_cube {L ν b : ℝ} (hν : 0 ≤ ν) {z : Position} (hz : z ∈ cube L) :
    packingBlob ν b z ⊆ cube ((1+ν)*L+b) := by
  intro x hx k
  have hk := hx k
  change 0 ≤ x k-(1+ν)*z k ∧ x k-(1+ν)*z k ≤ b at hk
  have hzk := hz k
  have hl : 0 ≤ (1+ν)*z k := mul_nonneg (by linarith) hzk.1
  have hu := mul_le_mul_of_nonneg_left hzk.2 (show 0 ≤ 1+ν by linarith)
  constructor <;> linarith

lemma core_grand_packing_lower {L ν b t β h : ℝ} (ht : 0 < t) (hb : 0 ≤ b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β) :
    grandOn (corePotential t) (cube b) β (t*h) ^ packingNumber L ≤
      grandOn (corePotential t) (cube ((1+ν)*L+b)) β (t*h) := by
  classical
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained L
  let φ := corePotential t
  have hc := continuous_corePotential t
  have hbound := bounded_corePotential t
  have hstable := stable_corePotential t
  have hA (z : Position) : MeasurableSet (packingBlob ν b z) := measurableSet_translate (measurableSet_cube _)
  have hAfin (z : Position) : volume (packingBlob ν b z) ≠ ⊤ := by
    rw [packingBlob, volume_translateSet _ _ (measurableSet_cube _), volume_cube]
    finiteness
  have hdist (z : Position) (hz : z ∈ X) (w : Position) (hw : w ∈ X) (hne : z ≠ w)
      (x : Position) (hx : x ∈ packingBlob ν b z) (y : Position) (hy : y ∈ packingBlob ν b w) :
      1+1/t ≤ dist x y := by
    have hh := packingBlob_separation hν hb (hX.2 z hz w hw hne) hx hy
    linarith
  have hdisj : ∀ z ∈ X, ∀ w ∈ X, z ≠ w → Disjoint (packingBlob ν b z) (packingBlob ν b w) := by
    intro z hz w hw hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh := hdist z hz w hw hne x hx x hy
    rw [dist_self] at hh
    have := one_div_pos.mpr ht
    linarith
  have hcross : ∀ z ∈ X, ∀ w ∈ X, z ≠ w → ∀ x ∈ packingBlob ν b z,
      ∀ y ∈ packingBlob ν b w, φ (nndist x y) ≤ 0 := by
    intro z hz w hw hne x hx y hy
    exact le_of_eq (coreReal_zero_outer ht (hdist z hz w hw hne x hx y hy))
  have hprod := grandOn_biUnion_lower hc hbound hstable hβ X (packingBlob ν b) (t*h)
    (fun z _ => hA z) (fun z _ => hAfin z) hdisj hcross
  have hsub : (⋃ z ∈ X, packingBlob ν b z) ⊆ cube ((1+ν)*L+b) := by
    intro x hx
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
    exact packingBlob_subset_cube hν (hX.1 z hz) hxz
  have hcomp := grandOn_mono hc hbound hstable hβ hsub (by rw [volume_cube]; finiteness) (t*h)
  simp only [packingBlob, grandOn_translate, Finset.prod_const, hcard] at hprod
  exact hprod.trans hcomp

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CorePressureUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma core_nonpos_outer {t : ℝ} (ht : 1 ≤ t) :
    ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → corePotential t r ≤ 0 := by
  intro r hr
  have ht0 : 0 < t := by linarith
  have hinv : 1/t ≤ 1 := (div_le_one ht0).mpr ht
  rw [corePotential, coreReal_zero_outer ht0 (by linarith)]

lemma core_finitePressure_upper {t α L β h : ℝ} (hL : 1 ≤ L)
    (ht0 : 0 < t) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hα : 0 ≤ α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    finiteGrandPressure (corePotential t) t L β h ≤
      α*((packingNumber L:ℝ)/L^3)+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t := by
  have hL0 : 0 < L := by linarith
  have hh := core_grand_upper hL0.le ht0.le ht hβ (mul_nonneg ht0.le hα) h1 h4
  have hp := (grandPartition_bounds (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hL0.le hβ t h).1
  have hreal := ENNReal.toReal_mono (by finiteness :
      ENNReal.ofReal (Real.exp (t*α*packingNumber L)) *
        ((15001:ℝ≥0∞)^(cubeCells L).card * ENNReal.ofReal (Real.exp (L^3*Real.exp (t*h-β*t^2/2)))) ≠ ⊤) hh
  simp only [ENNReal.toReal_ofReal (show 0 ≤ grandPartition (corePotential t) t L β h by linarith),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofNat] at hreal
  have hlog := Real.log_le_log (show 0 < grandPartition (corePotential t) t L β h by linarith) hreal
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hlog
  have hc := mul_le_mul_of_nonneg_right (card_cubeCells hL) (show 0 ≤ Real.log (15001:ℝ) from Real.log_nonneg (by norm_num))
  have hden : 0 < t*L^3 := by positivity
  dsimp only [finiteGrandPressure]
  apply (div_le_iff₀ hden).mpr
  have heq : (α*((packingNumber L:ℝ)/L^3)+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t)*(t*L^3) =
      t*α*packingNumber L+216*L^3*Real.log 15001+L^3*Real.exp (t*h-β*t^2/2) := by
    field_simp
    ring
  rw [heq]
  linarith

lemma corePressure_upper {t α β h : ℝ} (ht0 : 1 ≤ t)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hβ : 0 ≤ β) (hα : 0 ≤ α) (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) :
    grandPressure (corePotential t) t β h ≤
      α*packingDensity+(216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t := by
  have htpos : 0 < t := by linarith
  have hl := (grandPressure_spec (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) htpos hβ (core_nonpos_outer ht0) h).1
  have hr := packingDensity_limit.const_mul α |>.add_const ((216*Real.log 15001+Real.exp (t*h-β*t^2/2))/t)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  exact core_finitePressure_upper hL htpos ht hβ hα h1 h4

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CorePressureLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma packing_dilated_limit {ν b : ℝ} (hν : 0 ≤ ν) :
    Tendsto (fun L : ℝ => (packingNumber L:ℝ)/((1+ν)*L+b)^3) atTop
      (nhds (packingDensity/(1+ν)^3)) := by
  have hn : (1+ν)^3 ≠ 0 := by positivity
  have hh : Tendsto (fun L : ℝ => (1+ν+b*L⁻¹)^3) atTop (nhds ((1+ν)^3)) := by
    simpa using ((tendsto_const_nhds (x := 1+ν)).add (tendsto_inv_atTop_zero.const_mul b)).pow 3
  apply (packingDensity_limit.div hh hn).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he : 1+ν+b*L⁻¹ = ((1+ν)*L+b)/L := by field_simp
  dsimp only [Pi.div_apply]
  rw [he, div_pow]
  field_simp

lemma corePressure_packing_lower {ν b t β h : ℝ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β) :
    packingDensity/(1+ν)^3 * (Real.log (grandOn (corePotential t) (cube b) β (t*h))/t) ≤
      grandPressure (corePotential t) t β h := by
  have ht0 : 0 < t := by linarith
  have hc := continuous_corePotential t
  have hbound := bounded_corePotential t
  have hstable := stable_corePotential t
  have hlocal := (grandOn_bounds hc hbound hstable hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)).1
  have hlimL : Tendsto (fun L : ℝ => (1+ν)*L+b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop (by linarith : 0 < 1+ν) tendsto_id)
  have hright := ((grandPressure_spec hc hbound hstable ht0 hβ (core_nonpos_outer ht) h).1).comp hlimL
  have hleft := (packing_dilated_limit (b := b) hν).mul_const
    (Real.log (grandOn (corePotential t) (cube b) β (t*h))/t)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hS : 0 < (1+ν)*L+b := by positivity
  have hprod := core_grand_packing_lower (L := L) ht0 hb hν hsep hβ (h := h)
  have hlog := Real.log_le_log (pow_pos (show 0 < grandOn (corePotential t) (cube b) β (t*h) by linarith) _) hprod
  rw [Real.log_pow] at hlog
  rw [grandOn_cube] at hlog
  rw [grandOn_cube] at hlog
  have hden : 0 < t*((1+ν)*L+b)^3 := by positivity
  dsimp only [finiteGrandPressure, Function.comp_def]
  apply (le_div_iff₀ hden).mpr
  rw [grandOn_cube]
  calc
    _ = (packingNumber L:ℝ)*Real.log (grandPartition (corePotential t) t b β h) := by
      field_simp
    _ ≤ _ := hlog

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_TetraIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma measurableSet_tetraRegion (t a : ℝ) : MeasurableSet (tetraRegion t a) := by
  apply MeasurableSet.inter
  · exact (measurableSet_cube a).preimage (measurable_pi_apply 0)
  · change MeasurableSet {x : Fin 4 → Position | ∀ j : Fin 3, x j.succ-x 0-tetraVertex t j.succ ∈ cube (tetraEpsilon t)}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_cube _).preimage (((measurable_pi_apply j.succ).sub (measurable_pi_apply 0)).sub measurable_const)

lemma lintegral_tetra_fiber (t : ℝ) (x : Position) :
    (∫⁻ y : Fin 3 → Position, ∏ j, regionMask (cube (tetraEpsilon t)) (y j-x-tetraVertex t j.succ)
      ∂Measure.pi (fun _ => volume)) = (ENNReal.ofReal (tetraEpsilon t)^3)^3 := by
  have he (y : Fin 3 → Position) :
      (∏ j, regionMask (cube (tetraEpsilon t)) (y j-x-tetraVertex t j.succ)) =
      (Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t)))).indicator (fun _ => 1) y := by
    simp only [regionMask, Set.indicator, Finset.prod_boole]
    have hm : (∀ j : Fin 3, y j-x-tetraVertex t j.succ ∈ cube (tetraEpsilon t)) ↔
        y ∈ Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t))) := by
      simp [Set.mem_pi, translateSet, sub_sub]
    simp [hm]
  simp_rw [he]
  change (∫⁻ y, (Set.pi univ (fun j : Fin 3 => translateSet (x+tetraVertex t j.succ) (cube (tetraEpsilon t)))).indicator (1 : (Fin 3 → Position) → ℝ≥0∞) y ∂Measure.pi (fun _ => volume)) = _
  rw [lintegral_indicator_one, Measure.pi_pi]
  · simp_rw [volume_translateSet _ _ (measurableSet_cube _), volume_cube]
    simp
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_translate (measurableSet_cube _))

lemma volume_tetraRegion (t a : ℝ) :
    volume (tetraRegion t a) = ENNReal.ofReal a^3*(ENNReal.ofReal (tetraEpsilon t)^3)^3 := by
  let F (p : Position × (Fin 3 → Position)) : ℝ≥0∞ :=
    regionMask (cube a) p.1 * ∏ j, regionMask (cube (tetraEpsilon t)) (p.2 j-p.1-tetraVertex t j.succ)
  have hF : Measurable F := by
    apply ((measurable_regionMask (measurableSet_cube _)).comp measurable_fst).mul
    apply Finset.measurable_prod
    intro j _
    apply (measurable_regionMask (measurableSet_cube _)).comp
    fun_prop
  have he (x : Fin 4 → Position) :
      (tetraRegion t a).indicator (fun _ => (1:ℝ≥0∞)) x =
      F (x 0, fun j => x j.succ) := by
    by_cases h1 : x 0 ∈ cube a <;>
      by_cases h2 : ∀ j : Fin 3, x j.succ-x 0-tetraVertex t j.succ ∈ cube (tetraEpsilon t) <;>
      simp [F, regionMask, tetraRegion, Set.indicator, Finset.prod_boole, h1, h2]

  rw [← lintegral_indicator_one (measurableSet_tetraRegion t a)]
  change (∫⁻ x, (tetraRegion t a).indicator (fun _ => (1:ℝ≥0∞)) x) = _
  rw [volume_pi]
  simp_rw [he]
  have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin 4 => (volume : Measure Position)) 0).lintegral_comp hF
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply] at hh
  have her (x : Fin 4 → Position) : Fin.removeNth 0 x = fun j => x j.succ := by
    funext j
    simp only [Fin.removeNth_apply, Fin.succAbove_zero]
  simp_rw [her] at hh
  rw [hh, lintegral_prod _ hF.aemeasurable]
  have hfin (x : Position) : regionMask (cube a) x ≠ ⊤ := by
    by_cases hx : x ∈ cube a <;> simp [regionMask, hx]
  simp only [F]
  simp_rw [lintegral_const_mul' _ _ (hfin _), lintegral_tetra_fiber]
  rw [lintegral_mul_const']
  · change (∫⁻ x, (cube a).indicator (1 : Position → ℝ≥0∞) x) * _ = _
    rw [lintegral_indicator_one (measurableSet_cube _), volume_cube]
  · exact ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

lemma partitionOn_tetra_lower (t a β : ℝ) (ha : 0 ≤ a) :
    a^3*(tetraEpsilon t)^9/24 ≤ partitionOn (corePotential t) (cube (a+3*microLength t)) 4 β := by
  have hs : tetraRegion t a ⊆ configurationCube (a+3*microLength t) 4 := fun _ hx => tetraRegion_cube hx
  have hc : Set.univ.pi (fun _ : Fin 4 => cube (a+3*microLength t)) = configurationCube (a+3*microLength t) 4 := by
    ext x
    simp [configurationCube, Set.mem_pi]
  have hfin : volume (cube (a+3*microLength t)) ≠ ⊤ := by rw [volume_cube]; finiteness
  let : IsFiniteMeasure (volume.restrict (cube (a+3*microLength t))) := isFiniteMeasure_restrict.mpr hfin
  have hi := integrable_orderedBoltzmann (ι := Fin 4) (continuous_corePotential t) (bounded_corePotential t) β (Measure.pi (fun _ : Fin 4 => volume.restrict (cube (a+3*microLength t))))
  rw [← Measure.restrict_pi_pi, hc, ← volume_pi] at hi
  have hle := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Eventually.of_forall (fun x : Fin 4 → Position => (Real.exp_pos (-β*orderedEnergy (corePotential t) x)).le)) hi
  have he : (∫ x in tetraRegion t a, Real.exp (-β*orderedEnergy (corePotential t) x)) =
      a^3*(tetraEpsilon t)^9 := by
    have hh : (∫ x in tetraRegion t a, Real.exp (-β*orderedEnergy (corePotential t) x)) =
        ∫ _x in tetraRegion t a, (1:ℝ) := by
      apply setIntegral_congr_fun (measurableSet_tetraRegion t a)
      intro x hx
      change Real.exp (-β*orderedEnergy (corePotential t) x) = 1
      rw [orderedEnergy_fin, tetraRegion_core_zero hx, mul_zero, Real.exp_zero]
    rw [hh, integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      volume_tetraRegion, smul_eq_mul, mul_one, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (tetraEpsilon_pos t).le]
    ring
  rw [he] at hle
  rw [partitionOn, rawPartition_setIntegral, hc]
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div]
  linarith

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreLocalLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma partitionOn_one (φ : Potential) {b : ℝ} (hb : 0 ≤ b) (β : ℝ) :
    partitionOn φ (cube b) 1 β = b^3 := by
  simp [partitionOn, rawPartition, orderedEnergy, Measure.real, Measure.pi_univ,
    volume_cube, ENNReal.toReal_ofReal hb]

lemma blobTetraConstant_pos {b : ℝ} (hb : 0 < b) : 0 < blobTetraConstant b := by
  unfold blobTetraConstant
  positivity

lemma partitionOn_blob_tetra {t b β : ℝ} (hb : 0 ≤ b) (ht : 3*microLength t ≤ b/2) :
    blobTetraConstant b*Real.exp (-9*t) ≤ partitionOn (corePotential t) (cube b) 4 β := by
  have hsub : cube (b/2+3*microLength t) ⊆ cube b := by
    intro x hx k
    have hh := hx k
    exact ⟨hh.1, by linarith [hh.2]⟩
  have hp := partitionOn_mono (continuous_corePotential t) (bounded_corePotential t) β 4 hsub
    (by rw [volume_cube]; finiteness)
  have h1 := partitionOn_tetra_lower t (b/2) β (by positivity)
  have he : (b/2)^3*tetraEpsilon t^9/24 = blobTetraConstant b*Real.exp (-9*t) := by
    dsimp [tetraEpsilon, microLength, blobTetraConstant]
    rw [div_pow, div_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (9:ℝ)*(-t) = -9*t by ring]
    ring
  rw [he] at h1
  exact h1.trans hp

lemma core_local_grand_monomer {t b β h : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β) :
    Real.exp (t*h)*b^3 ≤ grandOn (corePotential t) (cube b) β (t*h) := by
  have hs := grandOn_summable (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)
  have hh := hs.le_tsum 1 (fun n _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg _ _ _ _))
  simpa only [Nat.cast_one, mul_one, partitionOn_one _ hb, grandOn] using hh

lemma core_local_grand_tetra {t b β h : ℝ} (hb : 0 ≤ b) (hβ : 0 ≤ β)
    (ht : 3*microLength t ≤ b/2) :
    blobTetraConstant b*Real.exp (t*(4*h-9)) ≤ grandOn (corePotential t) (cube b) β (t*h) := by
  have hs := grandOn_summable (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) hβ (by rw [volume_cube]; finiteness : volume (cube b) ≠ ⊤) (t*h)
  have hh := hs.le_tsum 4 (fun n _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg _ _ _ _))
  have hl := mul_le_mul_of_nonneg_left (partitionOn_blob_tetra hb ht (β := β)) (Real.exp_pos (t*h*4)).le
  have he : Real.exp (t*h*4)*(blobTetraConstant b*Real.exp (-9*t)) =
      blobTetraConstant b*Real.exp (t*(4*h-9)) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hl
  exact hl.trans hh

lemma core_local_log_monomer {t b β h : ℝ} (ht : 0 < t) (hb : 0 < b) (hβ : 0 ≤ β) :
    h+Real.log (b^3)/t ≤ Real.log (grandOn (corePotential t) (cube b) β (t*h))/t := by
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (pow_pos hb 3)) (core_local_grand_monomer hb.le hβ (t := t) (h := h))
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hb.ne'), Real.log_exp] at hh
  apply (le_div_iff₀ ht).mpr
  calc
    _ = t*h+Real.log (b^3) := by field_simp
    _ ≤ _ := hh

lemma core_local_log_tetra {t b β h : ℝ} (ht : 0 < t) (hb : 0 < b) (hβ : 0 ≤ β)
    (htb : 3*microLength t ≤ b/2) :
    4*h-9+Real.log (blobTetraConstant b)/t ≤ Real.log (grandOn (corePotential t) (cube b) β (t*h))/t := by
  have hh := Real.log_le_log (mul_pos (blobTetraConstant_pos hb) (Real.exp_pos _)) (core_local_grand_tetra hb.le hβ htb (h := h))
  rw [Real.log_mul (blobTetraConstant_pos hb).ne' (Real.exp_ne_zero _), Real.log_exp] at hh
  apply (le_div_iff₀ ht).mpr
  calc
    _ = Real.log (blobTetraConstant b)+t*(4*h-9) := by field_simp; ring
    _ ≤ _ := hh

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma bareLimit_eq (h : ℝ) : bareLimit h = bareAlpha h*packingDensity := by
  have hp := packingDensity_pos.le
  simp only [bareLimit, bareAlpha, max_mul_of_nonneg _ _ hp, zero_mul]
  congr 2 <;> ring

lemma packing_coefficient_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1 ∧ |packingDensity/(1+ν)^3-packingDensity| < ε := by
  have hh : Tendsto (fun x : ℝ => packingDensity/(1+x⁻¹)^3) atTop (nhds packingDensity) := by
    have hh : Tendsto (fun x : ℝ => (1+x⁻¹)^3) atTop (nhds (1:ℝ)) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero).pow 3
    simpa [div_eq_mul_inv] using (hh.inv₀ (by norm_num : (1:ℝ) ≠ 0)).const_mul packingDensity
  have he := (Metric.tendsto_atTop.mp hh ε hε)
  obtain ⟨x, hx⟩ := he
  let y := max x 1
  have hy : 1 ≤ y := le_max_right _ _
  refine ⟨y⁻¹, inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ hy, ?_⟩
  simpa only [Real.dist_eq] using hx y (le_max_left _ _)

lemma tendsto_core_micro : Tendsto microLength atTop (nhds 0) := by
  exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

lemma corePressure_lower_branch {ν b t β h : ℝ} (ht : 1 ≤ t) (hb : 0 < b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β)
    (htb : 3*microLength t ≤ b/2) :
    packingDensity/(1+ν)^3*h-packingDensity*|Real.log (b^3)|/t ≤
      grandPressure (corePotential t) t β h ∧
    packingDensity/(1+ν)^3*(4*h-9)-packingDensity*|Real.log (blobTetraConstant b)|/t ≤
      grandPressure (corePotential t) t β h := by
  let c := packingDensity/(1+ν)^3
  have hp := packingDensity_pos
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcp : c ≤ packingDensity := by
    dsimp [c]
    exact div_le_self packingDensity_pos.le (one_le_pow₀ (by linarith))
  have ht0 : 0 < t := by linarith
  have hl := corePressure_packing_lower ht hb.le hν hsep hβ (h := h)
  have hh (z : ℝ) : -packingDensity*|z|/t ≤ c*(z/t) := by
    have hz := neg_abs_le z
    have h1 := mul_le_mul_of_nonneg_left hz hc0
    have h2 := mul_le_mul_of_nonneg_right hcp (abs_nonneg z)
    have h3 : -packingDensity*|z| ≤ c*z := by nlinarith
    have h4 := div_le_div_of_nonneg_right h3 ht0.le
    simpa only [mul_div_assoc] using h4
  constructor
  · have hm := mul_le_mul_of_nonneg_left (core_local_log_monomer ht0 hb hβ (h := h)) hc0
    have he := hh (Real.log (b^3))
    dsimp only [c] at hm he
    rw [mul_add] at hm
    simp only [neg_mul, neg_div] at he
    linarith
  · have hm := mul_le_mul_of_nonneg_left (core_local_log_tetra ht0 hb hβ htb (h := h)) hc0
    have he := hh (Real.log (blobTetraConstant b))
    dsimp only [c] at hm he
    rw [mul_add] at hm
    simp only [neg_mul, neg_div] at he
    linarith

lemma corePressure_uniform_bare_rt2_oai {β₀ H ε : ℝ} (hβ₀ : 0 < β₀) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ β h : ℝ, β₀ ≤ β → |h| ≤ H →
      |grandPressure (corePotential t) t β h-bareLimit h| ≤ ε := by
  let D : ℝ := 4*H+10
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ν, hν, _, hc⟩ := packing_coefficient_approx (div_pos hε (mul_pos (by norm_num : (0:ℝ)<2) hD))
  let b := ν/10
  let c := packingDensity/(1+ν)^3
  let K := packingDensity*(|Real.log (b^3)|+|Real.log (blobTetraConstant b)|)
  have hb : 0 < b := by dsimp [b]; positivity
  have hp := packingDensity_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim1 : Tendsto (fun t : ℝ => 1/t) atTop (nhds 0) := by simpa using tendsto_inv_atTop_zero
  have hsep : ∀ᶠ t : ℝ in atTop, 1/t+4*b ≤ ν := by
    have hh := ((hlim1.add_const (4*b)).eventually (eventually_le_nhds (by dsimp [b]; linarith : 0+4*b < ν)))
    exact hh
  have hmic : ∀ᶠ t : ℝ in atTop, 3*microLength t ≤ b/2 :=
    (tendsto_core_micro.const_mul 3).eventually (eventually_le_nhds (by linarith : (3:ℝ)*0 < b/2))
  have hsmall : ∀ᶠ t : ℝ in atTop, 2*((1+(1:ℝ)/1000)*microLength t) < 1 := by
    have hh := (tendsto_core_micro.const_mul (2*(1+(1:ℝ)/1000))).eventually
      (eventually_lt_nhds (by norm_num : 2*(1+(1:ℝ)/1000)*0 < 1))
    simpa only [mul_assoc] using hh
  have herror : ∀ᶠ t : ℝ in atTop, K/t ≤ ε/2 := by
    have hh : Tendsto (fun t : ℝ => K/t) atTop (nhds 0) := by simpa [div_eq_mul_inv] using hlim1.const_mul K
    exact hh.eventually (eventually_le_nhds (by positivity : (0:ℝ)<ε/2))
  have hupper : ∀ᶠ t : ℝ in atTop, (216*Real.log 15001+1)/t ≤ ε := by
    have hh : Tendsto (fun t : ℝ => (216*Real.log 15001+1)/t) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hlim1.const_mul (216*Real.log 15001+1)
    exact hh.eventually (eventually_le_nhds hε)
  filter_upwards [eventually_ge_atTop (max 1 (2*H/β₀)), hsep, hmic, hsmall, herror, hupper]
    with t ht hsep hmic hsmall herror hupper
  intro β h hβ hh
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hβpos : 0 < β := hβ₀.trans_le hβ
  have hhH := abs_le.mp hh
  have hα0 : 0 ≤ bareAlpha h := le_max_left _ _
  have hα1 : h ≤ bareAlpha h := (le_max_left _ _).trans (le_max_right _ _)
  have hα4 : 4*h-9 ≤ bareAlpha h := (le_max_right _ _).trans (le_max_right _ _)
  have hup := corePressure_upper ht1 hsmall hβpos.le hα0 hα1 hα4
  have hexp : Real.exp (t*h-β*t^2/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hth : 2*H ≤ t*β₀ := (div_le_iff₀ hβ₀).mp ((le_max_right _ _).trans ht)
    have hh1 := mul_le_mul_of_nonneg_right hth ht0.le
    have hh2 := mul_le_mul_of_nonneg_right hβ (sq_nonneg t)
    have hh3 := mul_le_mul_of_nonneg_left hhH.2 ht0.le
    nlinarith
  have hup' : grandPressure (corePotential t) t β h-bareLimit h ≤ ε := by
    rw [bareLimit_eq]
    have hdiv := div_le_div_of_nonneg_right (show 216*Real.log 15001+Real.exp (t*h-β*t^2/2) ≤ 216*Real.log 15001+1 by linarith) ht0.le
    linarith
  have hlo := corePressure_lower_branch ht1 hb hν.le hsep hβpos.le hmic (h := h)
  have hz := (grandPressure_spec (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) ht0 hβpos.le (core_nonpos_outer ht1) h).2.1
  have hcoeff (x : ℝ) (hx : |x| ≤ D) : |packingDensity*x-c*x| ≤ ε/2 := by
    have he : packingDensity*x-c*x = (packingDensity-c)*x := by ring
    rw [he, abs_mul]
    have hcx : |packingDensity-c| ≤ ε/(2*D) := by
      dsimp [c]
      rw [abs_sub_comm]
      exact hc.le
    calc
      _ ≤ (ε/(2*D))*D := mul_le_mul hcx hx (abs_nonneg _) (by positivity)
      _ = ε/2 := by field_simp
  have he1 := hcoeff h (hh.trans (by dsimp [D]; linarith))
  have he4 := hcoeff (4*h-9) (by rw [abs_le]; dsimp [D]; constructor <;> linarith)
  have hlog1 : packingDensity*|Real.log (b^3)|/t ≤ ε/2 := by
    apply le_trans _ herror
    apply div_le_div_of_nonneg_right _ ht0.le
    dsimp [K]
    nlinarith [packingDensity_pos, abs_nonneg (Real.log (blobTetraConstant b))]
  have hlog4 : packingDensity*|Real.log (blobTetraConstant b)|/t ≤ ε/2 := by
    apply le_trans _ herror
    apply div_le_div_of_nonneg_right _ ht0.le
    dsimp [K]
    nlinarith [packingDensity_pos, abs_nonneg (Real.log (b^3))]
  have hlo' : bareLimit h-grandPressure (corePotential t) t β h ≤ ε := by
    have h1 : packingDensity*h ≤ grandPressure (corePotential t) t β h+ε := by
      have hh := (abs_le.mp he1).2
      dsimp only [c] at hh
      linarith [hlo.1]
    have h4 : packingDensity*(4*h-9) ≤ grandPressure (corePotential t) t β h+ε := by
      have hh := (abs_le.mp he4).2
      dsimp only [c] at hh
      linarith [hlo.2]
    have hm : bareLimit h ≤ grandPressure (corePotential t) t β h+ε :=
      max_le (by linarith) (max_le h1 h4)
    linarith
  exact abs_le.mpr ⟨by linarith, hup'⟩

end RadialTransition
end

end OAI
end

theorem solution : type_of% @OAI.RadialTransition.corePressure_uniform_bare_rt2_oai := @OAI.RadialTransition.corePressure_uniform_bare_rt2_oai
