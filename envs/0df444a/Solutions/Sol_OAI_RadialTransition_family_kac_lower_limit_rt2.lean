-- Prove2me | solution 1 for OAI.RadialTransition.family_kac_lower_limit_rt2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:49:47.669857+00:00
-- url     : https://prove2.me/submissions/98647f5c-b359-42f4-be79-7d86818a3ca6

import Mathlib
import Definitions.Def_RadialTransition
import Definitions.Def_OAIQ112R000
import Theorems.Thm_OAI_RadialTransition_family_kac_deletion_rt2

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

theorem shell_edge_bound {V : Type uV} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.CliqueFree 5) :
    8 * G.edgeFinset.card ≤ 3 * (Fintype.card V) ^ 2 := by
  obtain ⟨H, hdec, hmax⟩ := SimpleGraph.exists_isTuranMaximal (V := V) (r := 4) (by norm_num)
  let _ : DecidableRel H.Adj := hdec
  have hle := hmax.2 hG
  obtain ⟨e⟩ := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph
    (G := H) (by norm_num : 0 < 4)).mp hmax
  have heq := e.card_edgeFinset_eq
  have hb := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := Fintype.card V) (r := 4)
  rw [← heq] at hb
  norm_num at hb
  omega

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

theorem sum_adj_indicator {V : Type uV} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * G.edgeFinset.card := by
  classical
  have hi (i : V) : (∑ j, if G.Adj i j then (1 : ℝ) else 0) = G.degree i := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
    simp
  simp_rw [hi]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RadialKernel
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

theorem rawBumpProfile_nonneg (r : ℝ) : 0 ≤ rawBumpProfile r :=
  Real.smoothTransition.nonneg _

theorem rawBumpProfile_le_one (r : ℝ) : rawBumpProfile r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem continuous_rawBumpProfile : Continuous rawBumpProfile := by
  exact Real.smoothTransition.continuous.comp (by fun_prop)

theorem bumpIntegral_pos : 0 < bumpIntegral := by
  apply contDiff_rawBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    compactSupport_rawBump (fun x => rawBumpProfile_nonneg ‖x‖) (x := 0)
  simp [rawBump, rawBumpProfile, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]

theorem bumpProfile_nonneg (r : ℝ) : 0 ≤ bumpProfile r :=
  div_nonneg (rawBumpProfile_nonneg r) bumpIntegral_pos.le

theorem bumpProfile_bound (r : ℝ) : |bumpProfile r| ≤ bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (bumpProfile_nonneg r)]
  simpa [bumpProfile, one_div] using
    div_le_div_of_nonneg_right (rawBumpProfile_le_one r) bumpIntegral_pos.le

theorem bumpProfile_zero {r : ℝ} (hr : 1 ≤ r) : bumpProfile r = 0 := by
  rw [bumpProfile, rawBumpProfile_zero hr, zero_div]

theorem continuous_bumpProfile : Continuous bumpProfile :=
  continuous_rawBumpProfile.div_const _

theorem integral_bump : ∫ x : Position, bump x = 1 := by
  change (∫ x : Position, rawBump x / bumpIntegral) = 1
  rw [integral_div, ← bumpIntegral, div_self bumpIntegral_pos.ne']

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellStability
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

theorem symmetric_row_quadratic {I : Type uI} [Fintype I] (J : I → I → ℝ) (n : I → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsymm : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, (n i) ^ 2 := by
  have ht (i j : I) : 2 * (J i j * n i * n j) ≤
      J i j * (n i ^ 2 + n j ^ 2) := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => ht i j
  have hs : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsymm]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hl
  rw [hs] at hl
  have hb : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem core_ordered_lower_small_diameter {V : Type uV} [Fintype V] [DecidableEq V] {t : ℝ} (ht : 0 ≤ t)
    (x : V → Position) (hx : ∀ i j, dist (x i) (x j) ≤ 1) :
    t ^ 2 / 4 * (Fintype.card V : ℝ) ^ 2 - t ^ 2 * Fintype.card V ≤
      ∑ i, ∑ j, if i ≠ j then coreReal t (dist (x i) (x j)) else 0 := by
  classical
  let G := shellGraph x (microLength t)
  have hG : G.CliqueFree 5 := shellGraph_cliqueFree x (microLength_pos t)
  have hbound : (8 : ℝ) * G.edgeFinset.card ≤ 3 * (Fintype.card V : ℝ) ^ 2 := by
    have hh : 8 * G.edgeFinset.card ≤ 3 * Fintype.card V ^ 2 := by
      simpa using shell_edge_bound G hG
    exact_mod_cast hh
  have hterm (i j : V) :
      t ^ 2 * ((if i ≠ j then (1 : ℝ) else 0) - (if G.Adj i j then 1 else 0)) ≤
      (if i ≠ j then coreReal t (dist (x i) (x j)) else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_left hij]
      by_cases hA : G.Adj i j
      · simp only [hA, ite_true, if_true, sub_self, mul_zero]
        exact coreReal_nonneg _ _
      · simp only [hA, ite_false, if_false, sub_zero, mul_one]
        rw [coreReal_full_of_not_shell ht (hx i j)]
        intro h
        exact hA ⟨hij, h⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm i j
  have hcount : (∑ i : V, ∑ j : V, if i ≠ j then (1 : ℝ) else 0) =
      (Fintype.card V : ℝ) ^ 2 - Fintype.card V := by
    have hite (i j : V) : (if i ≠ j then (1 : ℝ) else 0) =
        1 - (if i = j then 1 else 0) := by by_cases h : i = j <;> simp [h]
    simp_rw [hite]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hcount, sum_adj_indicator G] at hsum
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg t)
  nlinarith [hsum, hb]

theorem sum_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] (q : V → I) :
    ∑ i, occupation q i = Fintype.card V := by
  classical
  simpa [occupation] using Fintype.sum_fiberwise q (fun _ => (1 : ℝ))

theorem sum_subtype_le_of_nonneg {V : Type uV} [Fintype V] (p : V → Prop)
    (f : V → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (by classical exact ∑ a : {a // p a}, f a) ≤ ∑ a, f a := by
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype p f
  have hz : 0 ≤ ∑ a : {a // ¬p a}, f a := Finset.sum_nonneg (fun a _ => hf a)
  linarith

theorem core_ordered_cells {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] [DecidableEq V]
    {t : ℝ} (ht : 0 ≤ t) (q : V → I) (x : V → Position)
    (c : V → V → ℝ) (hc : ∀ a b, 0 ≤ c a b)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1) :
    t ^ 2 / 4 * (∑ i, occupation q i ^ 2) - t ^ 2 * Fintype.card V ≤
      ∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0 := by
  classical
  let F (a b : V) := if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0
  have hF (a b : V) : 0 ≤ F a b := by
    exact ite_nonneg (mul_nonneg (hc a b) (coreReal_nonneg _ _)) le_rfl
  have hlocal (i : I) : t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤
      ∑ a : {a // q a = i}, ∑ b, F a b := by
    have hl := core_ordered_lower_small_diameter ht (fun a : {a // q a = i} => x a)
      (fun a b => hdiam a b (a.property.trans b.property.symm))
    change t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤ _ at hl
    apply hl.trans
    apply Finset.sum_le_sum
    intro a _
    have heq : (∑ b : {b // q b = i},
        if a ≠ b then coreReal t (dist (x a) (x b)) else 0) =
        ∑ b : {b // q b = i}, F a b := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · subst b; simp [F]
      · have hab' : (a : V) ≠ (b : V) := fun hh => hab (Subtype.ext hh)
        simp [F, hab, hab', hsame a b (a.property.trans b.property.symm)]
    rw [heq]
    exact sum_subtype_le_of_nonneg (fun b => q b = i) (F a) (hF a)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  rw [Fintype.sum_fiberwise q (fun a => ∑ b, F a b)] at hs
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_occupation] using hs

theorem sum_by_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (f : I → ℝ) :
    (∑ a, f (q a)) = ∑ i, occupation q i * f i := by
  classical
  rw [← Fintype.sum_fiberwise q (fun a => f (q a))]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun a : {a // q a = i} => f (q a)) = (fun _ => f i) := by
    funext a
    rw [a.property]
  rw [heq]
  simp [occupation]

theorem lifted_row_quadratic {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (J : I → I → ℝ) {M : ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (∑ a, ∑ b, J (q a) (q b)) ≤ M * ∑ i, occupation q i ^ 2 := by
  classical
  have heq : (∑ a, ∑ b, J (q a) (q b)) =
      ∑ i, ∑ j, J i j * occupation q i * occupation q j := by
    calc
      _ = ∑ a, ∑ j, occupation q j * J (q a) j := by
        apply Finset.sum_congr rfl
        intro a _
        exact sum_by_occupation q (J (q a))
      _ = ∑ i, occupation q i * ∑ j, occupation q j * J i j :=
        sum_by_occupation q (fun i => ∑ j, occupation q j * J i j)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [heq]
  exact symmetric_row_quadratic J (occupation q) M hJ hJsy hrow

theorem modified_energy_cell_bound {N : ℕ} {I : Type uI} [Fintype I]
    {t M : ℝ} (ht : 0 ≤ t) (q : Fin N → I) (x : Fin N → Position)
    (c K : Fin N → Fin N → ℝ) (J : I → I → ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hcsy : ∀ a b, c a b = c b a)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1)
    (hK : ∀ a b, 0 ≤ K a b) (hKsy : ∀ a b, K a b = K b a)
    (hKJ : ∀ a b, K a b ≤ J (q a) (q b))
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (t ^ 2 / 8 - M / 2) * (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤
      ∑ a, ∑ b with a < b, (c a b * coreReal t (dist (x a) (x b)) - K a b) := by
  classical
  have hcore := core_ordered_cells ht q x c hc hsame hdiam
  have hrow' := lifted_row_quadratic q J hJ hJsy hrow
  have hatt : (∑ a, ∑ b, if a ≠ b then K a b else 0) ≤
      M * ∑ i, occupation q i ^ 2 := by
    apply le_trans ?_ hrow'
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply le_trans ?_ (hKJ a b)
    split_ifs
    · exact le_rfl
    · exact hK a b
  have hpair := twice_pair_sum
    (fun a b => c a b * coreReal t (dist (x a) (x b)) - K a b)
    (fun a b => by rw [hcsy a b, dist_comm (x a), hKsy a b])
  have heq : (∑ a, ∑ b, if a ≠ b then
      c a b * coreReal t (dist (x a) (x b)) - K a b else 0) =
      (∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0) -
      (∑ a, ∑ b, if a ≠ b then K a b else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [hab]
  rw [heq] at hpair
  simp only [Fintype.card_fin] at hcore
  nlinarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ScaledKernels
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

theorem scaledBump_radial {R : ℝ} (hR : 0 < R) (x : Position) :
    scaledBump R x = scaledBumpProfile R ‖x‖ := by
  simp [scaledBump, scaledBumpProfile, bump, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, div_eq_mul_inv, mul_comm]

theorem integral_scaledBump {R : ℝ} (hR : 0 < R) :
    ∫ x : Position, scaledBump R x = 1 := by
  unfold scaledBump
  rw [integral_const_mul, Measure.integral_comp_inv_smul, integral_bump]
  simp [Position, abs_of_pos (pow_pos hR 3), hR.ne']

theorem scaledBumpProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledBumpProfile R r :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le 3)) (bumpProfile_nonneg _)

theorem scaledBumpProfile_bound {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    |scaledBumpProfile R r| ≤ bumpIntegral⁻¹ := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [abs_of_nonneg (scaledBumpProfile_nonneg hR0 r)]
  unfold scaledBumpProfile
  apply le_trans (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bumpProfile_bound (r / R)))
    (inv_nonneg.mpr (pow_nonneg hR0.le 3)))
  exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
    (inv_le_one_of_one_le₀ (one_le_pow₀ hR))

theorem scaledBumpProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledBumpProfile R r = 0 := by
  rw [scaledBumpProfile, bumpProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)),
    mul_zero]

theorem continuous_scaledBumpProfile (R : ℝ) : Continuous (scaledBumpProfile R) :=
  continuous_const.mul (continuous_bumpProfile.comp (continuous_id.div_const _))

theorem attractionProfile_nonneg {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    0 ≤ attractionProfile a R r := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)

theorem summable_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    Summable (fun n => a n * scaledBumpProfile (R n) r) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)
  · intro n
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n)

theorem attractionProfile_bound {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    |attractionProfile a R r| ≤ (∑' n, a n) * bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (attractionProfile_nonneg ha hR r)]
  unfold attractionProfile
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n))
    (summable_attractionProfile ha hR hs r) (hs.mul_right _)

theorem continuous_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    Continuous (attractionProfile a R) := by
  apply continuous_tsum (fun n => continuous_const.mul (continuous_scaledBumpProfile (R n)))
    (hs.mul_right bumpIntegral⁻¹)
  intro n r
  change |a n * scaledBumpProfile (R n) r| ≤ a n * bumpIntegral⁻¹
  rw [abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (scaledBumpProfile_bound (hR n) r) (ha n)

theorem continuous_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    Continuous (familyPotential t a R) := by
  exact ((continuous_coreReal t).sub (continuous_const.mul
    (continuous_attractionProfile ha hR hs))).comp NNReal.continuous_coe

theorem bounded_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    IsBoundedPotential (familyPotential t a R) := by
  refine ⟨t ^ 2 + |t| * ((∑' n, a n) * bumpIntegral⁻¹), ?_, ?_⟩
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _)
      (mul_nonneg (tsum_nonneg ha) (inv_nonneg.mpr bumpIntegral_pos.le)))
  · intro r
    apply le_trans (abs_sub _ _)
    rw [abs_of_nonneg (coreReal_nonneg t r), abs_mul]
    exact add_le_add (coreReal_le t r)
      (mul_le_mul_of_nonneg_left (attractionProfile_bound ha hR hs r) (abs_nonneg t))

theorem familyPotential_nonpos_outer {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) {t : ℝ} (ht : 1 ≤ t)
    {r : ℝ≥0} (hr : 2 ≤ (r : ℝ)) : familyPotential t a R r ≤ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv : 1 / t ≤ 1 := by simpa using inv_le_one_of_one_le₀ ht
  have hz := coreReal_zero_outer ht0 (show 1 + 1 / t ≤ (r : ℝ) by linarith)
  dsimp [familyPotential]
  rw [hz, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg ht0.le (attractionProfile_nonneg ha hR r))

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

theorem mem_rangeCells (R : ℝ) (i j : Cell) : j ∈ rangeCells R i ↔ CellReach R i j := by
  simp only [rangeCells, Fintype.mem_piFinset, Finset.mem_Icc, CellReach, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem cellReach_symm {R : ℝ} {i j : Cell} (h : CellReach R i j) : CellReach R j i := by
  intro k
  simpa only [abs_sub_comm] using h k

theorem cellMargin_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellMargin R := by
  have hh := Int.le_ceil (4 * R)
  have : (0 : ℝ) ≤ (cellMargin R : ℝ) := by dsimp [cellMargin]; push_cast; linarith
  exact_mod_cast this

theorem card_rangeCells {R : ℝ} (hR : 1 ≤ R) (i : Cell) :
    ((rangeCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  have hm := cellMargin_nonneg (le_trans zero_le_one hR)
  have hm1 : 0 ≤ 2 * cellMargin R + 1 := by omega
  have heq : (rangeCells R i).card = (2 * cellMargin R + 1).toNat ^ 3 := by
    simp only [rangeCells, Fintype.card_piFinset, Int.card_Icc]
    simp_rw [show ∀ k, i k + cellMargin R + 1 - (i k - cellMargin R) =
        2 * cellMargin R + 1 by intro k; ring]
    simp
  rw [heq]
  have hcast : (((2 * cellMargin R + 1).toNat : ℕ) : ℝ) = 2 * (cellMargin R : ℝ) + 1 := by
    have hh := Int.toNat_of_nonneg hm1
    exact_mod_cast hh
  push_cast
  rw [hcast]
  have hb : 2 * (cellMargin R : ℝ) + 1 ≤ 13 * R := by
    have hc := Int.ceil_lt_add_one (4 * R)
    dsimp [cellMargin]
    push_cast
    linarith
  calc
    _ ≤ (13 * R) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast hm1) hb 3
    _ = _ := by ring

theorem cellReach_of_dist {x y : Position} {R : ℝ} (hxy : dist x y ≤ R) :
    CellReach R (cellOf x) (cellOf y) := by
  intro k
  have hc : |x k - y k| ≤ R := by
    simpa only [Real.dist_eq] using (PiLp.dist_apply_le x y k).trans hxy
  have hxl := Int.floor_le (4 * x k)
  have hyl := Int.floor_le (4 * y k)
  have hxu := Int.lt_floor_add_one (4 * x k)
  have hyu := Int.lt_floor_add_one (4 * y k)
  have hceil := Int.le_ceil (4 * R)
  have hb : |((⌊4 * y k⌋ : ℤ) : ℝ) - (⌊4 * x k⌋ : ℤ)| ≤ (⌈4 * R⌉ : ℤ) + (1 : ℝ) := by
    rcases abs_le.mp hc with ⟨hc1, hc2⟩
    apply abs_le.mpr
    constructor <;> linarith
  dsimp [cellOf, cellMargin]
  exact_mod_cast hb

theorem cellMajorant_nonneg {R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W) (i j : Cell) :
    0 ≤ cellMajorant R W i j :=
  ite_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) hW) le_rfl

theorem cellMajorant_symm (R W : ℝ) (i j : Cell) :
    cellMajorant R W i j = cellMajorant R W j i := by
  unfold cellMajorant
  have hh : CellReach R i j ↔ CellReach R j i := ⟨cellReach_symm, cellReach_symm⟩
  by_cases h : CellReach R i j
  · simp [h, hh.mp h]
  · simp [h, show ¬ CellReach R j i from fun hji => h (hh.mpr hji)]

theorem cellMajorant_row {I : Type uI} [Fintype I]
    (e : I → Cell) (he : Function.Injective e) {R W : ℝ} (hR : 1 ≤ R) (hW : 0 ≤ W)
    (i : Cell) : ∑ j, cellMajorant R W i (e j) ≤ 2197 * W := by
  classical
  let s := Finset.univ.filter (fun j => CellReach R i (e j))
  have hcard : s.card ≤ (rangeCells R i).card := by
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact (mem_rangeCells R i (e j)).mpr (Finset.mem_filter.mp hj).2
    · exact he.injOn
  have hsum : (∑ j, cellMajorant R W i (e j)) = (s.card : ℝ) * ((R ^ 3)⁻¹ * W) := by
    simp [cellMajorant, s, ← Finset.sum_filter]
  rw [hsum]
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc : (s.card : ℝ) ≤ 2197 * R ^ 3 :=
    (by exact_mod_cast hcard : (s.card : ℝ) ≤ (rangeCells R i).card).trans (card_rangeCells hR i)
  calc
    _ ≤ (2197 * R ^ 3) * ((R ^ 3)⁻¹ * W) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR0.le _)) hW)
    _ = _ := by field_simp

theorem same_cell_diameter {x y : Position} (h : cellOf x = cellOf y) :
    dist x y ≤ 1 := by
  have hc (k : Fin 3) : |x k - y k| ≤ 1 / 4 := by
    have hh : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxl := Int.floor_le (4 * x k)
    have hxu := Int.lt_floor_add_one (4 * x k)
    have hyl := Int.floor_le (4 * y k)
    have hyu := Int.lt_floor_add_one (4 * y k)
    rw [← hh] at hyl hyu
    apply abs_le.mpr
    constructor <;> linarith
  have hs : dist x y ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ k : Fin 3, (1 / 4 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Real.dist_eq] using pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem scaledBumpProfile_le_cellMajorant {R : ℝ} (hR : 1 ≤ R) (x y : Position) :
    scaledBumpProfile R (dist x y) ≤ cellMajorant R bumpIntegral⁻¹ (cellOf x) (cellOf y) := by
  have hR0 := lt_of_lt_of_le zero_lt_one hR
  by_cases h : CellReach R (cellOf x) (cellOf y)
  · simp only [cellMajorant, ite_eq_left h, scaledBumpProfile]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (bumpProfile_bound _))
      (inv_nonneg.mpr (pow_nonneg hR0.le _))
  · have hd : R ≤ dist x y := le_of_not_ge (fun hh => h (cellReach_of_dist hh))
    simp [cellMajorant, h, scaledBumpProfile_zero hR0 hd]

theorem summable_cellMajorant {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i j : Cell) :
    Summable (fun n => a n * cellMajorant (R n) bumpIntegral⁻¹ i j) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
      (inv_nonneg.mpr bumpIntegral_pos.le) i j)
  · intro n
    apply mul_le_mul_of_nonneg_left ?_ (ha n)
    unfold cellMajorant
    split_ifs
    · exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
        (inv_le_one_of_one_le₀ (one_le_pow₀ (hR n)))
    · exact inv_nonneg.mpr bumpIntegral_pos.le

theorem familyCellMajorant_nonneg {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (i j : Cell) :
    0 ≤ familyCellMajorant t a R i j := by
  apply mul_nonneg ht (tsum_nonneg _)
  intro n
  exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
    (inv_nonneg.mpr bumpIntegral_pos.le) i j)

theorem familyCellMajorant_symm (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) :
    familyCellMajorant t a R i j = familyCellMajorant t a R j i := by
  unfold familyCellMajorant
  congr 1
  apply tsum_congr
  intro n
  rw [cellMajorant_symm]

theorem familyCellMajorant_row {I : Type uI} [Fintype I] (e : I → Cell)
    (he : Function.Injective e) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i : Cell) :
    ∑ j, familyCellMajorant t a R i (e j) ≤ 2197 * t * bumpIntegral⁻¹ * ∑' n, a n := by
  simp only [familyCellMajorant, ← Finset.mul_sum]
  have hswap : (∑ j, ∑' n, a n * cellMajorant (R n) bumpIntegral⁻¹ i (e j)) =
      ∑' n, a n * ∑ j, cellMajorant (R n) bumpIntegral⁻¹ i (e j) := by
    rw [← Summable.tsum_finsetSum (fun j _ => summable_cellMajorant ha hR hs i (e j))]
    simp_rw [Finset.mul_sum]
  rw [hswap]
  calc
    _ ≤ t * ∑' n, a n * (2197 * bumpIntegral⁻¹) := by
      apply mul_le_mul_of_nonneg_left ?_ ht
      apply Summable.tsum_le_tsum
      · intro n
        exact mul_le_mul_of_nonneg_left
          (cellMajorant_row e he (hR n) (inv_nonneg.mpr bumpIntegral_pos.le) i) (ha n)
      · simpa only [Finset.mul_sum] using
          summable_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
            summable_cellMajorant ha hR hs i (e j))
      · exact hs.mul_right _
    _ = _ := by rw [tsum_mul_right]; ring

theorem attraction_le_familyCellMajorant {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (x y : Position) :
    t * attractionProfile a R (dist x y) ≤ familyCellMajorant t a R (cellOf x) (cellOf y) := by
  apply mul_le_mul_of_nonneg_left ?_ ht
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (scaledBumpProfile_le_cellMajorant (hR n) x y) (ha n))
    (summable_attractionProfile ha hR hs _) (summable_cellMajorant ha hR hs _ _)

theorem family_energy_cell_bound {I : Type uI} [Fintype I] {N : ℕ}
    (e : I → Cell) (he : Function.Injective e) (q : Fin N → I) (x : Fin N → Position)
    (hq : ∀ j, e (q j) = cellOf (x j)) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
        (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤ energy (familyPotential t a R) x := by
  have hh := modified_energy_cell_bound ht q x (fun _ _ => 1)
    (fun i j => t * attractionProfile a R (dist (x i) (x j)))
    (fun i j => familyCellMajorant t a R (e i) (e j))
    (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun i j hij => same_cell_diameter (by rw [← hq i, ← hq j, hij]))
    (fun i j => mul_nonneg ht (attractionProfile_nonneg ha hR _))
    (fun i j => by rw [dist_comm (x i) (x j)])
    (fun i j => by simpa only [hq] using attraction_le_familyCellMajorant ht ha hR hs (x i) (x j))
    (fun i j => familyCellMajorant_nonneg ht ha hR (e i) (e j))
    (fun i j => familyCellMajorant_symm t a R (e i) (e j))
    (fun i => familyCellMajorant_row e he ht ha hR hs (e i))
  simpa only [one_mul, energy, familyPotential, coe_nndist] using hh

theorem stable_familyPotential {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 8) :
    StableWith (familyPotential t a R) (t ^ 2 / 2) := by
  classical
  intro N x
  let S : Finset Cell := Finset.univ.image (fun j => cellOf (x j))
  let q : Fin N → S := fun j => ⟨cellOf (x j), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hh := family_energy_cell_bound (fun i : S => (i : Cell)) Subtype.val_injective q x
    (fun _ => rfl) ht ha hR hs
  have hn : 0 ≤ (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
      (∑ i, occupation q i ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hcoerc) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  change -(t ^ 2 / 2 * (N : ℝ)) ≤ _
  linarith

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

theorem partition_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (β : ℝ) : 0 < partition φ L N β := by
  unfold partition
  apply mul_pos (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-β * energy φ x)).le))
    (integrableOn_boltzmann hφ hb L N β)).mpr
  have heq : Function.support (fun x : Fin N → Position => Real.exp (-β * energy φ x)) = univ := by
    ext x
    simp [Function.mem_support]
  rw [heq, Measure.restrict_apply_univ]
  rw [volume_configurationCube]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ ((ENNReal.ofReal_pos.mpr hL).ne'))

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
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem grandPartition_tail_le_one {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 0 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    (∑' n : {n : ℕ // ⌊D * L ^ 3⌋₊ < n},
      Real.exp (t * h * (n : ℕ)) * partition φ L n β) ≤ 1 := by
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let h' := h + t⁻¹
  have hs := grandPartition_summable hφ hb hstable hL hβ t h'
  have hfac : Summable (fun n : ℕ => Real.exp (-D * L ^ 3) *
      (Real.exp (t * h' * n) * partition φ L n β)) := hs.mul_left _
  have hsub := (grandPartition_summable hφ hb hstable hL hβ t h).subtype (fun n => m < n)
  have hh (n : {n : ℕ // m < n}) :
      Real.exp (t * h * (n : ℕ)) * partition φ L n β ≤
      Real.exp (-D * L ^ 3) * (Real.exp (t * h' * (n : ℕ)) * partition φ L n β) := by
    have hn : D * L ^ 3 < (n : ℕ) := (Nat.floor_lt (by positivity)).mp n.property
    have hfield : t * h' = t * h + 1 := by dsimp [h']; field_simp
    rw [← mul_assoc, ← Real.exp_add, hfield]
    apply mul_le_mul_of_nonneg_right _ (partition_nonneg L n β)
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum := hsub.tsum_le_tsum hh (hfac.subtype (fun n => m < n))
  have hsuble := Summable.tsum_subtype_le _ {n : ℕ | m < n}
    (fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (partition_nonneg L n β))) hfac
  have hh' := hsum.trans hsuble
  rw [tsum_mul_left] at hh'
  have hbound := mul_le_mul_of_nonneg_left
    (grandPartition_bounds hφ hb hstable hL hβ t h').2 (Real.exp_pos (-D * L ^ 3)).le
  have heq : β * B + t * h' = β * B + t * h + 1 := by dsimp [h']; field_simp; ring
  rw [heq, ← Real.exp_add] at hbound
  apply hh'.trans (hbound.trans _)
  apply Real.exp_le_one_iff.mpr
  nlinarith [pow_nonneg hL (3 : ℕ)]

theorem finiteGrandPressure_max_term {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 1 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    ∃ n : ℕ, (n : ℝ) / L ^ 3 ∈ Icc 0 D ∧
      finiteGrandPressure φ t L β h ≤
        h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
          Real.log ((D + 2) * L ^ 3) / (t * L ^ 3) := by
  classical
  have hL0 : 0 < L := by linarith
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let F (n : ℕ) := Real.exp (t * h * n) * partition φ L n β
  have hs : Summable F := grandPartition_summable hφ hb hstable hL0.le hβ t h
  obtain ⟨n, hn, hnmax⟩ := (Finset.range (m+1)).exists_max_image F (by simp)
  have hnle : n ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
  have hnD : (n : ℝ) ≤ D * L ^ 3 :=
    (by exact_mod_cast hnle : (n : ℝ) ≤ m).trans (Nat.floor_le (by positivity))
  have hge1 : 1 ≤ F n := by
    have hh := hnmax 0 (by simp)
    simpa [F, partition_zero] using hh
  have htail : (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ 1 := by
    let e : {k : ℕ // k ∉ Finset.range (m+1)} ≃ {k : ℕ // m < k} :=
      Equiv.subtypeEquivProp (by funext k; apply propext; simp)
    have he := e.tsum_eq (fun k => F k)
    change (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) =
      (∑' k : {k : ℕ // m < k}, F k) at he
    rw [he]
    exact grandPartition_tail_le_one hφ hb hstable ht hL0.le hβ hD
  have hgrand : grandPartition φ t L β h ≤ ((m : ℝ) + 2) * F n := by
    rw [grandPartition, ← hs.sum_add_tsum_compl (s := Finset.range (m+1))]
    have hsum := Finset.sum_le_card_nsmul (Finset.range (m+1)) F (F n) hnmax
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
    change (∑ k ∈ Finset.range (m+1), F k) + (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ _
    nlinarith
  have hV : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hmD : (m : ℝ) + 2 ≤ (D + 2) * L ^ 3 := by
    have hm := Nat.floor_le (show 0 ≤ D * L ^ 3 by positivity)
    dsimp only [m]
    nlinarith
  have hgrand' := hgrand.trans (mul_le_mul_of_nonneg_right hmD (by linarith : 0 ≤ F n))
  have hlog := Real.log_le_log (show 0 < grandPartition φ t L β h by
    linarith [(grandPartition_bounds hφ hb hstable hL0.le hβ t h).1]) hgrand'
  have hFp : 0 < F n := by linarith
  rw [Real.log_mul (by positivity) hFp.ne'] at hlog
  have hFlog : Real.log (F n) = t * h * n + Real.log (partition φ L n β) := by
    simp only [F, Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL0 n β).ne', Real.log_exp]
  rw [hFlog] at hlog
  refine ⟨n, ⟨by positivity, (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr hnD⟩, ?_⟩
  have hden : 0 < t * L ^ 3 := by positivity
  change Real.log (grandPartition φ t L β h) / (t * L ^ 3) ≤ _
  apply (div_le_iff₀ hden).mpr
  have he : (h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
      Real.log ((D + 2) * L ^ 3) / (t * L ^ 3)) * (t * L ^ 3) =
      Real.log ((D + 2) * L ^ 3) + (t * h * n + Real.log (partition φ L n β)) := by
    dsimp only [finiteCanonical]
    field_simp
    ring
  rw [he]
  exact hlog

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

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem continuous_particleCount : Continuous (particleCount (X := X)) :=
  continuous_sigma (fun _ => continuous_const)

theorem measurable_particle_mk (n : ℕ) : Measurable (@Sigma.mk ℕ (fun n => Fin n → X) n) :=
  continuous_sigmaMk.measurable

theorem measurable_particle_iff {Y : Type uY} [MeasurableSpace Y] {f : ParticleState X → Y} :
    Measurable f ↔ ∀ n, Measurable (fun x : Fin n → X => f ⟨n,x⟩) := by
  constructor
  · intro hf n
    exact hf.comp (measurable_particle_mk n)
  · intro hf s hs
    have he : f ⁻¹' s = ⋃ n : ℕ, Sigma.mk n '' ((fun x : Fin n → X => f ⟨n,x⟩) ⁻¹' s) := by
      exact (iUnion_image_preimage_sigma_mk_eq_self (f ⁻¹' s)).symm
    rw [he]
    apply MeasurableSet.iUnion
    intro n
    exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image.mpr (hf n hs)

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
-- module Solutions.OAIQ112_RT.RadialTransition_CellInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uY uZ

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

section PairCells
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}

lemma pairBetween_lower (v : X → Y → ℝ) {J : ℝ} (hv : ∀ x y, -J ≤ v x y)
    (s : ParticleState X) (t : ParticleState Y) :
    -J * particleCount s * particleCount t ≤ pairBetween v s t := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hv (s.2 i) (t.2 j)))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pairBetween, particleCount, mul_comm, mul_left_comm] using hh

end PairCells

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ConfigurationMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MapConfigurations
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

lemma measurable_mapParticle {f : X → Y} (hf : Measurable f) : Measurable (mapParticle f) := by
  apply measurable_particle_iff.mpr
  intro n
  exact (measurable_particle_mk n).comp (measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i)))

lemma particleBase_map (μ : Measure X) [IsFiniteMeasure μ] (z : ℝ)
    {f : X → Y} (hf : Measurable f) :
    Measure.map (mapParticle f) (particleBase μ z) = particleBase (Measure.map f μ) z := by
  unfold particleBase
  rw [Measure.map_sum (measurable_mapParticle hf).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul,
    Measure.map_map (measurable_mapParticle hf) (measurable_particle_mk n)]
  congr 1
  rw [← Measure.pi_map_pi (fun _ : Fin n => hf.aemeasurable)]
  exact (Measure.map_map (measurable_particle_mk n)
    (show Measurable (fun x : Fin n → X => fun i => f (x i)) from
      measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i)))).symm

end MapConfigurations
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

lemma continuous_radialPair {φ : Potential} (hφ : Continuous φ) :
    Continuous (Function.uncurry (radialPair φ)) :=
  hφ.comp (continuous_fst.nndist continuous_snd)

lemma pairWithin_radial (φ : Potential) (s : ParticleState Position) :
    pairWithin (radialPair φ) s = orderedEnergy φ s.2 := by
  classical
  unfold pairWithin orderedEnergy
  have hh : (∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else radialPair φ (s.2 i) (s.2 j)) =
      ∑ i : Fin s.1, ∑ j : Fin s.1, if i ≠ j then φ (nndist (s.2 i) (s.2 j)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij, radialPair]
  rw [hh]
  ring_nf

lemma continuous_radialPair_comp {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {φ : Potential} (hφ : Continuous φ) {f : X → Position} {g : Y → Position}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => radialPair φ (f p.1) (g p.2)) := by
  change Continuous (fun p : X × Y => φ (nndist (f p.1) (g p.2)))
  exact hφ.comp ((hf.comp continuous_fst).nndist (hg.comp continuous_snd))

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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellDifferences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma pairWithin_abs_bound {X : Type uX} (v : X → X → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ x y, |v x y| ≤ K) (s : ParticleState X) :
    |pairWithin v s| ≤ (1/2:ℝ) * (K * particleCount s * particleCount s) := by
  classical
  unfold pairWithin
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j)| ≤
        ∑ i : Fin s.1, ∑ j : Fin s.1, |if i = j then 0 else v (s.2 i) (s.2 j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin s.1, ∑ j : Fin s.1, K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · simpa only [abs_zero] using hK
      · exact hv _ _
    _ = _ := by simp [particleCount]; ring

lemma pairBetween_abs_bound {X : Type uX} {Y : Type uY} (v : X → Y → ℝ) {K : ℝ}
    (hv : ∀ x y, |v x y| ≤ K) (s : ParticleState X) (t : ParticleState Y) :
    |pairBetween v s t| ≤ K * particleCount s * particleCount t := by
  unfold pairBetween
  calc
    |∑ i : Fin s.1, ∑ j : Fin t.1, v (s.2 i) (t.2 j)| ≤
        ∑ i : Fin s.1, ∑ j : Fin t.1, |v (s.2 i) (t.2 j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin s.1, ∑ j : Fin t.1, K :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hv _ _))
    _ = _ := by simp [particleCount]; ring

lemma double_sum_diagonal {I : Type uI} [Fintype I] [DecidableEq I] (a : I → I → ℝ) :
    (∑ i, ∑ j, a i j) = ∑ i, a i i + ∑ i, ∑ j, if i = j then 0 else a i j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2; ext j
    rw [show a i j = (if i = j then a i j else 0) + (if i = j then 0 else a i j) by split_ifs <;> simp]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

section CellDifferences
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairCellEnergy_abs_bound (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hv : ∀ i j a b, |v i j a b| ≤ K i j)
    (x : ∀ i, ParticleState (X i)) :
    |pairCellEnergy v x| ≤ (1/2:ℝ) * ∑ i, ∑ j, K i j * cellN i x * cellN j x := by
  let a i j := K i j * cellN i x * cellN j x
  have hi : (∑ i, |pairWithin (v i i) (x i)|) ≤ (1/2:ℝ) * ∑ i, a i i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => pairWithin_abs_bound _ (hK i i) (hv i i) (x i))
  have hc : (∑ i, ∑ j, |if i = j then 0 else pairBetween (v i j) (x i) (x j)|) ≤
      ∑ i, ∑ j, if i = j then 0 else a i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · simp
    · exact pairBetween_abs_bound _ (hv i j) _ _
  unfold pairCellEnergy cellHamiltonian
  calc
    _ ≤ |∑ i, pairWithin (v i i) (x i)| +
        |(1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else pairBetween (v i j) (x i) (x j)| := abs_add_le _ _
    _ ≤ (∑ i, |pairWithin (v i i) (x i)|) + (1/2:ℝ) *
        ∑ i, ∑ j, |if i = j then 0 else pairBetween (v i j) (x i) (x j)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      apply add_le_add (Finset.abs_sum_le_sum_abs _ _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (1/2:ℝ) * ∑ i, a i i + (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else a i j :=
      add_le_add hi (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = _ := by rw [← mul_add, ← double_sum_diagonal]

end CellDifferences

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PressureContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma stable_family_of_master {t : ℝ} {a m R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hsa : Summable a) (hsm : Summable m)
    (ham : ∀ n, a n ≤ m n)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, m n) ≤ (t^2/8)/8) :
    StableWith (familyPotential t a R) (t^2/2) := by
  apply stable_familyPotential ht ha hR hsa
  have hcoeff : 0 ≤ 2197*t*bumpIntegral⁻¹ := mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)
  have hh := (mul_le_mul_of_nonneg_left (hsa.tsum_le_tsum ham hsm) hcoeff).trans hrow
  nlinarith [sq_nonneg t]

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

lemma measurable_particle_prod {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Z]
    {f : ParticleState X → ParticleState Y → Z}
    (hf : ∀ m n, Measurable (fun p : (Fin m → X) × (Fin n → Y) => f ⟨m,p.1⟩ ⟨n,p.2⟩)) :
    Measurable (Function.uncurry f) := by
  let : MeasurableSpace (Σ m : ℕ, (Fin m → X) × ParticleState Y) := borel _
  let : BorelSpace (Σ m : ℕ, (Fin m → X) × ParticleState Y) := ⟨rfl⟩
  let e := Homeomorph.sigmaProdDistrib (X := fun m : ℕ => Fin m → X) (Y := ParticleState Y)
  have h : Measurable (fun q : Σ m : ℕ, (Fin m → X) × ParticleState Y =>
      f ⟨q.1,q.2.1⟩ q.2.2) := by
    apply measurable_borel_sigma
    intro m
    let : MeasurableSpace (Σ n : ℕ, (Fin n → Y) × (Fin m → X)) := borel _
    let : BorelSpace (Σ n : ℕ, (Fin n → Y) × (Fin m → X)) := ⟨rfl⟩
    let e' := Homeomorph.sigmaProdDistrib (X := fun n : ℕ => Fin n → Y) (Y := Fin m → X)
    have h' : Measurable (fun q : Σ n : ℕ, (Fin n → Y) × (Fin m → X) =>
        f ⟨m,q.2.2⟩ ⟨q.1,q.2.1⟩) := by
      apply measurable_borel_sigma
      intro n
      exact (hf m n).comp measurable_swap
    exact (h'.comp e'.continuous.measurable).comp measurable_swap
  exact h.comp e.continuous.measurable

end MeasurableFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PairEnsembles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section MeasurablePairs
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

lemma measurable_pairWithin (v : X → X → ℝ)
    (hv : Measurable (Function.uncurry v)) : Measurable (pairWithin v) := by
  apply measurable_particle_iff.mpr
  intro n
  change Measurable (fun a : Fin n → X => (1/2:ℝ) *
    ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else v (a i) (a j))
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : i = j
  · simp only [h, ite_true, if_true]; exact measurable_const
  · simp only [h, ite_false, if_false]
    exact hv.comp (show Measurable (fun a : Fin n → X => (a i, a j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma measurable_pairBetween (v : X → Y → ℝ)
    (hv : Measurable (Function.uncurry v)) : Measurable (Function.uncurry (pairBetween v)) := by
  apply measurable_particle_prod
  intro m n
  change Measurable (fun p : (Fin m → X) × (Fin n → Y) =>
    ∑ i : Fin m, ∑ j : Fin n, v (p.1 i) (p.2 j))
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    hv.comp (show Measurable (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j)) from
      ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))))

end MeasurablePairs
section MeasurablePairCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

lemma measurable_pairCellEnergy (v : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Measurable (Function.uncurry (v i j))) : Measurable (pairCellEnergy v) := by
  unfold pairCellEnergy cellHamiltonian
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun i _ => (measurable_pairWithin _ (hv i i)).comp (measurable_pi_apply i))
  · apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    by_cases h : i = j
    · simp only [h, ite_true, if_true]; exact measurable_const
    · simp only [h, ite_false, if_false]
      exact (measurable_pairBetween _ (hv i j)).comp
        (show Measurable (fun a : ∀ k, ParticleState (X k) => (a i, a j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))

end MeasurablePairCells

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoxEnsembles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma measurableSet_halfCube (L : ℝ) : MeasurableSet (halfCube L) := by
  have he : halfCube L = ⋂ k : Fin 3, {x : Position | 0 ≤ x k ∧ x k < L} := by
    ext x; simp only [halfCube, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k)).measurableSet.inter
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k) continuous_const).measurableSet

lemma halfCube_ae_cube (L : ℝ) : halfCube L =ᵐ[volume] cube L := by
  have hh := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => L)
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with x hx
  apply propext
  change (∀ k, 0 ≤ x k ∧ x k < L) ↔ (∀ k, 0 ≤ x k ∧ x k ≤ L)
  have hx' := eq_iff_iff.mp hx
  simpa only [Set.pi, Set.Ico, Set.Icc, Membership.mem, Set.Mem, Set.ofPred, Set.univ, Set.mem_univ, true_implies, forall_const, Pi.le_def, forall_and] using hx'

lemma restrict_halfCube (L : ℝ) : volume.restrict (halfCube L) = volume.restrict (cube L) :=
  Measure.restrict_congr_set (halfCube_ae_cube L)

lemma gridEmbed_injective (q : ℕ) : Function.Injective (@gridEmbed q) := by
  intro i j h
  funext k
  apply Fin.ext
  have hh : (i k : ℤ) = (j k : ℤ) := congrFun h k
  exact_mod_cast hh

lemma halfCube_grid_cover (q : ℕ) (x : Position) (hx : x ∈ halfCube ((q:ℝ)/4)) :
    ∃ i : GridIndex q, cellOf x = gridEmbed i := by
  have hh (k : Fin 3) : 0 ≤ cellOf x k ∧ cellOf x k < (q:ℤ) := by
    constructor
    · exact Int.floor_nonneg.mpr (by nlinarith [(hx k).1])
    · apply Int.floor_lt.mpr
      exact_mod_cast (show 4*x k < (q:ℝ) by linarith [(hx k).2])
  let i : GridIndex q := fun k => ⟨(cellOf x k).toNat, by have := hh k; omega⟩
  refine ⟨i, ?_⟩
  funext k
  simp only [gridEmbed, i]
  exact (Int.toNat_of_nonneg (hh k).1).symm

lemma volume_halfCube (L : ℝ) : volume (halfCube L) = ENNReal.ofReal L ^ 3 := by
  rw [measure_congr (halfCube_ae_cube L), volume_cube]

lemma blockEmbed_macro {m q : ℕ} (hq : 0 < q) (i : GridIndex m) (j : GridIndex q) :
    macroOf q (gridEmbed (blockEmbed i j)) = gridEmbed i := by
  funext d
  simp only [macroOf, gridEmbed, blockEmbed]
  have hj := (j d).isLt
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  have hj' : (0:ℤ) ≤ (j d : ℕ) ∧ (j d : ℤ) < q := by exact_mod_cast (show 0 ≤ (j d:ℕ) ∧ (j d:ℕ) < q from ⟨Nat.zero_le _, hj⟩)
  push_cast
  rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _),
    Int.mul_ediv_cancel _ (ne_of_gt hq'), Int.ediv_eq_zero_of_lt hj'.1 hj'.2, add_zero]

lemma blockEmbed_surjective {m q : ℕ} (hq : 0 < q) :
    Function.Surjective (fun p : GridIndex m × GridIndex q => blockEmbed p.1 p.2) := by
  intro k
  let i : GridIndex m := fun d => ⟨(k d : ℕ)/q, Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm m q] using (k d).isLt)⟩
  let j : GridIndex q := fun d => ⟨(k d : ℕ)%q, Nat.mod_lt _ hq⟩
  refine ⟨(i,j), ?_⟩
  funext d
  apply Fin.ext
  simpa only [blockEmbed, i, j, Nat.mul_comm] using Nat.div_add_mod (k d : ℕ) q

lemma card_boundaryCoord (q D : ℕ) : (boundaryCoord q D).card ≤ 2*D := by
  let lo := Finset.univ.filter (fun a : Fin q => (a:ℕ) < D)
  let hi := Finset.univ.filter (fun a : Fin q => q-D ≤ (a:ℕ))
  have hlo : lo.card ≤ D := by
    calc
      _ ≤ (Finset.range D).card := Finset.card_le_card_of_injOn Fin.val
        (by intro a ha; exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2)
        (fun a _ b _ h => Fin.ext h)
      _ = D := Finset.card_range D
  have hhi : hi.card ≤ D := by
    calc
      _ ≤ (Finset.range D).card := Finset.card_le_card_of_injOn (fun a : Fin q => q-1-(a:ℕ))
        (by intro a ha; have hh := (Finset.mem_filter.mp ha).2; have := a.isLt; apply Finset.mem_range.mpr; change q-1-(a:ℕ) < D; omega)
        (by intro a ha b hb h; apply Fin.ext; have := a.isLt; have := b.isLt; change q-1-(a:ℕ) = q-1-(b:ℕ) at h; omega)
      _ = D := Finset.card_range D
  have he : boundaryCoord q D = lo ∪ hi := by
    ext a; simp only [boundaryCoord, lo, hi, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [he]
  exact le_trans (Finset.card_union_le lo hi) (by omega)

lemma mem_boundaryGrid {q D : ℕ} {j : GridIndex q} :
    j ∈ boundaryGrid q D ↔ ∃ d, (j d:ℕ) < D ∨ q-D ≤ (j d:ℕ) := by
  simp only [boundaryGrid, Finset.mem_biUnion, Finset.mem_univ, true_and,
    boundarySlice, Fintype.mem_piFinset]
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨d, ?_⟩
    have h := hd d
    simpa only [ite_true, if_true, boundaryCoord, Finset.mem_filter, Finset.mem_univ, true_and] using h
  · rintro ⟨d,hd⟩
    refine ⟨d, ?_⟩
    intro k
    split_ifs with h
    · subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    · exact Finset.mem_univ _

lemma card_boundaryGrid (q D : ℕ) : (boundaryGrid q D).card ≤ 6*D*q^2 := by
  have hs (d : Fin 3) : (boundarySlice q D d).card = (boundaryCoord q D).card*q^2 := by
    rw [boundarySlice, Fintype.card_piFinset]
    fin_cases d <;> simp [Fin.prod_univ_three] <;> ring
  calc
    _ ≤ ∑ d : Fin 3, (boundarySlice q D d).card := Finset.card_biUnion_le
    _ = 3*((boundaryCoord q D).card*q^2) := by simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ 3*(2*D*q^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (card_boundaryCoord q D))
    _ = _ := by ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MacroRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma measurableSet_macroRegion (q : ℕ) (k : Cell) : MeasurableSet (macroRegion q k) := by
  exact (Set.to_countable {i : Cell | macroOf q i = k}).measurableSet.preimage measurable_cellOf

lemma macroRegion_translate {q : ℕ} (hq : 0 < q) (k : Cell) :
    macroRegion q k = translateSet (macroOrigin q k) (halfCube ((q:ℝ)/4)) := by
  ext x
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  constructor
  · intro hx d
    have hd : cellOf x d / (q:ℤ) = k d := congrFun hx d
    have hb := (Int.ediv_eq_iff_of_pos hq').mp hd
    have hl := Int.floor_le (4*x d)
    have hu := Int.lt_floor_add_one (4*x d)
    have hbl : ((k d:ℤ)*(q:ℤ):ℝ) ≤ (⌊4*x d⌋:ℝ) := by exact_mod_cast hb.1
    have hbu : (⌊4*x d⌋:ℝ)+1 ≤ ((k d:ℤ)*(q:ℤ)+(q:ℤ):ℝ) := by exact_mod_cast hb.2
    change 0 ≤ x d-(q:ℝ)*(k d:ℝ)/4 ∧ x d-(q:ℝ)*(k d:ℝ)/4 < (q:ℝ)/4
    push_cast at hbl hbu
    constructor <;> linarith
  · intro hx
    funext d
    apply (Int.ediv_eq_iff_of_pos hq').mpr
    have hd : 0 ≤ x d-(q:ℝ)*(k d:ℝ)/4 ∧ x d-(q:ℝ)*(k d:ℝ)/4 < (q:ℝ)/4 := hx d
    constructor
    · apply Int.le_floor.mpr
      push_cast
      linarith
    · apply Int.floor_lt.mpr
      push_cast
      linarith

lemma volume_macroRegion {q : ℕ} (hq : 0 < q) (k : Cell) :
    volume (macroRegion q k) = ENNReal.ofReal ((q:ℝ)/4)^3 := by
  rw [macroRegion_translate hq, volume_translateSet _ _ (measurableSet_halfCube _), volume_halfCube]

lemma macroRegion_subset_halfCube {m q : ℕ} (hq : 0 < q) (i : GridIndex m) :
    macroRegion q (gridEmbed i) ⊆ halfCube (((m:ℝ)*q)/4) := by
  intro x hx
  rw [macroRegion_translate hq] at hx
  intro d
  have hd : 0 ≤ x d-(q:ℝ)*(i d:ℝ)/4 ∧ x d-(q:ℝ)*(i d:ℝ)/4 < (q:ℝ)/4 := hx d
  have hi : (i d:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast (i d).isLt
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hin : (0:ℝ) ≤ (i d:ℝ) := by positivity
  constructor <;> nlinarith

lemma halfCube_macro_cover {m q : ℕ} (hq : 0 < q) (x : Position)
    (hx : x ∈ halfCube (((m:ℝ)*q)/4)) : ∃ i : GridIndex m, macroOf q (cellOf x) = gridEmbed i := by
  obtain ⟨k,hk⟩ := halfCube_grid_cover (m*q) x (by simpa only [Nat.cast_mul] using hx)
  obtain ⟨⟨i,j⟩,he⟩ := blockEmbed_surjective hq k
  refine ⟨i, ?_⟩
  rw [hk, ← he, blockEmbed_macro hq]

lemma halfCube_macro_union {m q : ℕ} (hq : 0 < q) :
    (⋃ i : GridIndex m, macroRegion q (gridEmbed i)) = halfCube (((m:ℝ)*q)/4) := by
  ext x
  simp only [mem_iUnion]
  exact ⟨fun ⟨i,hi⟩ => macroRegion_subset_halfCube hq i hi,
    fun hx => halfCube_macro_cover hq x hx⟩

lemma regionMeasure_map {A : Set Position} (hA : MeasurableSet A) :
    Measure.map Subtype.val (regionMeasure A) = volume.restrict A := map_comap_subtype_coe hA volume

lemma regionMeasure_univ {A : Set Position} (hA : MeasurableSet A) :
    regionMeasure A univ = volume A := by
  rw [regionMeasure, comap_subtype_coe_apply hA]
  simp only [Set.image_univ, Subtype.range_coe]

lemma regionMeasure_finite {A : Set Position} (hA : MeasurableSet A) (hAfin : volume A ≠ ⊤) :
    IsFiniteMeasure (regionMeasure A) := ⟨by rw [regionMeasure_univ hA]; exact lt_top_iff_ne_top.mpr hAfin⟩

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RangeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma lipschitz_bump : LipschitzWith bumpLip bump := Classical.choose_spec
  (ContDiff.lipschitzWith_of_hasCompactSupport compactSupport_bump contDiff_bump (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma scaledBump_nonneg {R : ℝ} (hR : 0 < R) (x : Position) : 0 ≤ scaledBump R x := by
  rw [scaledBump_radial hR]
  exact scaledBumpProfile_nonneg hR _

lemma continuous_scaledBump (R : ℝ) : Continuous (scaledBump R) :=
  continuous_const.mul (contDiff_bump.continuous.comp (continuous_id.const_smul R⁻¹))

lemma integrable_scaledBump {R : ℝ} (hR : 0 < R) : Integrable (scaledBump R) := by
  have hc : HasCompactSupport (scaledBump R) :=
    (compactSupport_bump.comp_smul (inv_ne_zero hR.ne')).mul_left
  exact (continuous_scaledBump R).integrable_of_hasCompactSupport hc

lemma scaledBump_bound {R : ℝ} (hR : 0 < R) (x : Position) :
    |scaledBump R x| ≤ (R^3)⁻¹*bumpIntegral⁻¹ := by
  unfold scaledBump
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))]
  exact mul_le_mul_of_nonneg_left (bumpProfile_bound _) (by positivity)

lemma scaledBump_zero {R : ℝ} (hR : 0 < R) {x : Position} (hx : R ≤ ‖x‖) : scaledBump R x = 0 := by
  rw [scaledBump_radial hR, scaledBumpProfile_zero hR hx]

lemma scaledBump_symm (R : ℝ) (x y : Position) : scaledBump R (x-y) = scaledBump R (y-x) := by
  unfold scaledBump bump
  rw [← neg_sub x y, smul_neg, norm_neg]

lemma scaledBump_oscillation {R : ℝ} (hR : 0 < R) (x y : Position) :
    |scaledBump R x-scaledBump R y| ≤ (bumpLip:ℝ)/R^4*dist x y := by
  have hh := lipschitz_bump.dist_le_mul (R⁻¹ • x) (R⁻¹ • y)
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hh
  simp only [Real.dist_eq] at hh
  calc
    _ = (R^3)⁻¹*|bump (R⁻¹ • x)-bump (R⁻¹ • y)| := by
      unfold scaledBump
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (R^3)⁻¹*((bumpLip:ℝ)*(R⁻¹*dist x y)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

lemma macroOrigin_mem {q : ℕ} (hq : 0 < q) (k : Cell) : macroOrigin q k ∈ macroRegion q k := by
  rw [macroRegion_translate hq]
  intro d
  change 0 ≤ (macroOrigin q k) d-(macroOrigin q k) d ∧
    (macroOrigin q k) d-(macroOrigin q k) d < (q:ℝ)/4
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  simp only [sub_self]; exact ⟨le_rfl, by positivity⟩

lemma macro_distance_origin {q : ℕ} (hq : 0 < q) (k : Cell) {x : Position}
    (hx : x ∈ macroRegion q k) : dist x (macroOrigin q k) ≤ (q:ℝ)/2 := by
  rw [macroRegion_translate hq] at hx
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hc (d : Fin 3) : |x d-(macroOrigin q k) d| ≤ (q:ℝ)/4 := by
    have hh : 0 ≤ x d-(macroOrigin q k) d ∧ x d-(macroOrigin q k) d < (q:ℝ)/4 := hx d
    rw [abs_of_nonneg hh.1]
    exact hh.2.le
  have hs : dist x (macroOrigin q k)^2 ≤ 3*((q:ℝ)/4)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _d : Fin 3, ((q:ℝ)/4)^2 := by
        apply Finset.sum_le_sum
        intro d _
        simpa only [Real.dist_eq] using pow_le_pow_left₀ (abs_nonneg _) (hc d) 2
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := macroOrigin q k)]

lemma macro_difference_dist {q : ℕ} (hq : 0 < q) {i j : Cell} {x y : Position}
    (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) :
    dist (x-y) (macroOrigin q i-macroOrigin q j) ≤ (q:ℝ) := by
  exact (dist_sub_sub_le x y _ _).trans (by linarith [macro_distance_origin hq i hx, macro_distance_origin hq j hy])

lemma macroReach_of_dist {q : ℕ} (hq : 0 < q) {R : ℝ} {i j : Cell} {x y : Position}
    (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) (hd : dist x y ≤ R) :
    CellReach (R/q+1) i j := by
  rw [macroRegion_translate hq] at hx hy
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  intro d
  have hxy : |y d-x d| ≤ R := by
    simpa only [Real.dist_eq, abs_sub_comm] using (PiLp.dist_apply_le x y d).trans hd
  have hxd : 0 ≤ x d-(q:ℝ)*(i d:ℝ)/4 ∧ x d-(q:ℝ)*(i d:ℝ)/4 < (q:ℝ)/4 := hx d
  have hyd : 0 ≤ y d-(q:ℝ)*(j d:ℝ)/4 ∧ y d-(q:ℝ)*(j d:ℝ)/4 < (q:ℝ)/4 := hy d
  have hceil := Int.le_ceil (4*(R/(q:ℝ)+1))
  have he : (q:ℝ)*(4*(R/(q:ℝ)+1)) = 4*R+4*q := by field_simp
  have hh := mul_le_mul_of_nonneg_left hceil hq0.le
  change (q:ℝ)*(4*(R/(q:ℝ)+1)) ≤ (q:ℝ)*(⌈4*(R/(q:ℝ)+1)⌉:ℝ) at hh
  rw [he] at hh
  have hc : |((j d:ℤ):ℝ)-(i d:ℝ)| ≤ (⌈4*(R/(q:ℝ)+1)⌉:ℤ)+(1:ℝ) := by
    apply abs_le.mpr
    have hab := abs_le.mp hxy
    constructor <;> nlinarith
  unfold cellMargin
  exact_mod_cast hc

lemma macroKernelError_nonneg (q : ℕ) (R : ℝ) (i j : Cell) : 0 ≤ macroKernelError q R i j := by
  unfold macroKernelError
  split_ifs <;> positivity

lemma macroKernelUpper_nonneg {q : ℕ} {R : ℝ} (hR : 0 < R) (i j : Cell) :
    0 ≤ macroKernelUpper q R i j := add_nonneg (scaledBump_nonneg hR _) (macroKernelError_nonneg _ _ _ _)

lemma macroKernelLower_nonneg (q : ℕ) (R : ℝ) (i j : Cell) : 0 ≤ macroKernelLower q R i j := le_max_left _ _

lemma macroKernel_symm (q : ℕ) (R : ℝ) (i j : Cell) : macroKernel q R i j = macroKernel q R j i :=
  scaledBump_symm _ _ _

lemma macroKernelError_symm (q : ℕ) (R : ℝ) (i j : Cell) :
    macroKernelError q R i j = macroKernelError q R j i := by
  unfold macroKernelError
  have he : CellReach (R/q+1) i j ↔ CellReach (R/q+1) j i := ⟨cellReach_symm, cellReach_symm⟩
  simp only [he]

lemma macroKernelUpper_symm (q : ℕ) (R : ℝ) (i j : Cell) :
    macroKernelUpper q R i j = macroKernelUpper q R j i := by
  unfold macroKernelUpper
  rw [macroKernel_symm, macroKernelError_symm]

lemma macroKernel_pair_bounds {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R)
    {i j : Cell} {x y : Position} (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) :
    macroKernelLower q R i j ≤ scaledBump R (x-y) ∧
      scaledBump R (x-y) ≤ macroKernelUpper q R i j := by
  have hc : |scaledBump R (x-y)-macroKernel q R i j| ≤ macroKernelError q R i j := by
    by_cases h : CellReach (R/q+1) i j
    · rw [macroKernelError, ite_eq_left h]
      exact (scaledBump_oscillation hR _ _).trans
        (mul_le_mul_of_nonneg_left (macro_difference_dist hq hx hy) (by positivity))
    · have hd : R < dist x y := lt_of_not_ge (fun hh => h (macroReach_of_dist hq hx hy hh))
      have hd' : R < dist (macroOrigin q i) (macroOrigin q j) :=
        lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) (macroOrigin_mem hq j) hh))
      rw [macroKernel, scaledBump_zero hR (by simpa only [dist_eq_norm] using hd.le),
        scaledBump_zero hR (by simpa only [dist_eq_norm] using hd'.le), sub_self, abs_zero,
        macroKernelError, ite_eq_right h]
  have hh := abs_le.mp hc
  constructor
  · exact max_le (scaledBump_nonneg hR _) (by linarith)
  · unfold macroKernelUpper
    linarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KernelError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

lemma macroKernelError_row {I : Type uI} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell) :
    ((q:ℝ)/4)^3*∑ j, macroKernelError q R i (e j) ≤ 5000*(bumpLip:ℝ)*q/R := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  let T := R/(q:ℝ)+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [div_nonneg hR0.le hq0.le]
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hh := cellMajorant_row e he hT (show 0 ≤ T^3*((bumpLip:ℝ)/R^4*q) by positivity) i
  have heq (j : I) : cellMajorant T (T^3*((bumpLip:ℝ)/R^4*q)) i (e j) = macroKernelError q R i (e j) := by
    unfold cellMajorant macroKernelError
    split_ifs <;> simp_all [T, hT0.ne']
  simp_rw [heq] at hh
  have hTq : (q:ℝ)*T ≤ 5*R := by dsimp [T]; field_simp; nlinarith
  have hc : ((q:ℝ)*T)^3 ≤ (5*R)^3 := pow_le_pow_left₀ (by positivity) hTq 3
  calc
    _ ≤ ((q:ℝ)/4)^3*(2197*(T^3*((bumpLip:ℝ)/R^4*q))) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (2197/64:ℝ)*((q:ℝ)*T)^3*((bumpLip:ℝ)*q/R^4) := by ring
    _ ≤ (2197/64:ℝ)*(5*R)^3*((bumpLip:ℝ)*q/R^4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
    _ ≤ _ := by field_simp; nlinarith [show (0:ℝ) ≤ bumpLip from NNReal.coe_nonneg _]

lemma macroRegions_disjoint (q m : ℕ) : Pairwise (Function.onFun Disjoint (fun i : GridIndex m => macroRegion q (gridEmbed i))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hij (gridEmbed_injective m (hx.symm.trans hy))

lemma macroRegions_integral {q m : ℕ} (hq : 0 < q) {f : Position → ℝ} (hf : Integrable f) :
    ∫ x in halfCube ((m:ℝ)*q/4), f x =
      ∑ j : GridIndex m, ∫ x in macroRegion q (gridEmbed j), f x := by
  rw [← halfCube_macro_union hq]
  exact integral_iUnion_fintype (fun _ => measurableSet_macroRegion _ _) (macroRegions_disjoint _ _) (fun _ => hf.integrableOn)

lemma macroKernel_center_error {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R)
    (i j : Cell) {y : Position} (hy : y ∈ macroRegion q j) :
    |scaledBump R (macroOrigin q i-y)-macroKernel q R i j| ≤ macroKernelError q R i j := by
  by_cases h : CellReach (R/q+1) i j
  · rw [macroKernelError, ite_eq_left h]
    exact (scaledBump_oscillation hR _ _).trans
      (mul_le_mul_of_nonneg_left (macro_difference_dist hq (macroOrigin_mem hq i) hy) (by positivity))
  · have hd : R < dist (macroOrigin q i) y := lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) hy hh))
    have hd' : R < dist (macroOrigin q i) (macroOrigin q j) :=
      lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) (macroOrigin_mem hq j) hh))
    rw [macroKernel, scaledBump_zero hR (by simpa only [dist_eq_norm] using hd.le),
      scaledBump_zero hR (by simpa only [dist_eq_norm] using hd'.le), sub_self, abs_zero,
      macroKernelError, ite_eq_right h]

lemma macroKernel_upper_integral {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R) (i j : Cell) :
    ((q:ℝ)/4)^3*(macroKernelUpper q R i j-2*macroKernelError q R i j) ≤
      ∫ y in macroRegion q j, scaledBump R (macroOrigin q i-y) := by
  have hh := setIntegral_mono_on
    (integrableOn_const (by rw [volume_macroRegion hq]; finiteness) :
      IntegrableOn (fun _ : Position => macroKernelUpper q R i j-2*macroKernelError q R i j) (macroRegion q j))
    ((integrable_scaledBump hR).comp_sub_left (macroOrigin q i)).integrableOn
    (measurableSet_macroRegion _ _) (fun y hy => ?_)
  · simpa only [setIntegral_const, Measure.real, volume_macroRegion hq,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ (q:ℝ)/4), smul_eq_mul] using hh
  · have hb := (abs_le.mp (macroKernel_center_error hq hR i j hy)).1
    unfold macroKernelUpper
    linarith

lemma macroKernel_lower_integral {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R) (i j : Cell) :
    (∫ y in macroRegion q j, scaledBump R (macroOrigin q i-y)) ≤
      ((q:ℝ)/4)^3*(macroKernelLower q R i j+2*macroKernelError q R i j) := by
  have hh := setIntegral_mono_on ((integrable_scaledBump hR).comp_sub_left (macroOrigin q i)).integrableOn
    (integrableOn_const (by rw [volume_macroRegion hq]; finiteness) :
      IntegrableOn (fun _ : Position => macroKernelLower q R i j+2*macroKernelError q R i j) (macroRegion q j))
    (measurableSet_macroRegion _ _) (fun y hy => ?_)
  · simpa only [setIntegral_const, Measure.real, volume_macroRegion hq,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ (q:ℝ)/4), smul_eq_mul] using hh
  · have hb := (abs_le.mp (macroKernel_center_error hq hR i j hy)).2
    have hm := le_max_right 0 (macroKernel q R i j-macroKernelError q R i j)
    change _ ≤ macroKernelLower q R i j at hm
    linarith

lemma macroKernelUpper_row {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell) :
    ((q:ℝ)/4)^3*∑ j : GridIndex m, macroKernelUpper q R i (gridEmbed j) ≤
      1+10000*(bumpLip:ℝ)*q/R := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hi := (integrable_scaledBump hR0).comp_sub_left (macroOrigin q i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : GridIndex m) _ => macroKernel_upper_integral hq hR0 i (gridEmbed j))
  rw [← macroRegions_integral hq hi] at hh
  have hle : (∫ y in halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q i-y)) ≤ 1 := by
    have ht := setIntegral_le_integral hi (Eventually.of_forall (fun y => scaledBump_nonneg hR0 _)) (s := halfCube ((m:ℝ)*q/4))
    simpa only [integral_sub_left_eq_self, integral_scaledBump hR0] using ht
  have hb := macroKernelError_row (@gridEmbed m) (gridEmbed_injective m) hq hR i
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  linear_combination hh + hle + 2*hb

lemma macroKernelLower_row_all {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : Cell)
    (hs : ∀ y ∉ halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q i-y) = 0) :
    1-10000*(bumpLip:ℝ)*q/R ≤
      ((q:ℝ)/4)^3*∑ j : GridIndex m, macroKernelLower q R i (gridEmbed j) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hi := (integrable_scaledBump hR0).comp_sub_left (macroOrigin q i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : GridIndex m) _ => macroKernel_lower_integral hq hR0 i (gridEmbed j))
  rw [← macroRegions_integral hq hi, setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    integral_sub_left_eq_self, integral_scaledBump hR0] at hh
  have hb := macroKernelError_row (@gridEmbed m) (gridEmbed_injective m) hq hR i
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  linear_combination hh + 2*hb

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_InteriorGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

lemma grid_inner_coords {m D : ℕ} {i : GridIndex m} (hi : i ∉ boundaryGrid m D) (d : Fin 3) :
    D ≤ (i d:ℕ) ∧ (i d:ℕ)+D < m := by
  have hn : ¬ ((i d:ℕ) < D ∨ m-D ≤ (i d:ℕ)) := fun h => hi (mem_boundaryGrid.mpr ⟨d,h⟩)
  omega

lemma grid_inner_reach {m : ℕ} {T : ℝ} (hT : 0 ≤ T) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin T).toNat) {j : Cell} (hj : CellReach T (gridEmbed i) j) :
    ∃ k : GridIndex m, gridEmbed k = j := by
  have hD : 0 ≤ cellMargin T := by unfold cellMargin; have := Int.ceil_nonneg (by positivity : 0 ≤ 4*T); omega
  have hd (d : Fin 3) : 0 ≤ j d ∧ j d < (m:ℤ) := by
    have hc := grid_inner_coords hi d
    have ha := abs_le.mp (hj d)
    have he : ((cellMargin T).toNat:ℤ) = cellMargin T := Int.toNat_of_nonneg hD
    change -cellMargin T ≤ j d-(i d:ℤ) ∧ j d-(i d:ℤ) ≤ cellMargin T at ha
    omega
  refine ⟨fun d => ⟨(j d).toNat, by have := hd d; omega⟩, ?_⟩
  funext d
  exact Int.toNat_of_nonneg (hd d).1

lemma macroKernel_support_inside {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 ≤ R) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin (R/q+1)).toNat) :
    ∀ y ∉ halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q (gridEmbed i)-y) = 0 := by
  intro y hy
  by_cases hR0 : R = 0
  · simp [hR0, scaledBump]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  apply scaledBump_zero hRpos
  rw [← dist_eq_norm]
  apply le_of_not_gt
  intro hd
  have hm : y ∈ macroRegion q (macroOf q (cellOf y)) := rfl
  have hr := macroReach_of_dist hq (macroOrigin_mem hq (gridEmbed i)) hm hd.le
  have hT : 0 ≤ R/(q:ℝ)+1 := by positivity
  obtain ⟨j, hj⟩ := grid_inner_reach hT i hi hr
  rw [← hj] at hm
  exact hy (macroRegion_subset_halfCube hq j hm)

lemma macroKernelLower_diagonal {q : ℕ} {R : ℝ} (hR : 0 < R) (i : Cell) :
    macroKernelLower q R i i ≤ (R^3)⁻¹*bumpIntegral⁻¹ := by
  apply max_le
  · have := bumpIntegral_pos; positivity
  · have hb := scaledBump_bound hR (macroOrigin q i-macroOrigin q i)
    have hn := macroKernelError_nonneg q R i i
    have ha := le_abs_self (scaledBump R (macroOrigin q i-macroOrigin q i))
    change macroKernel q R i i ≤ _ at ha
    linarith

lemma kernelRowError_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ kernelRowError q R := by
  unfold kernelRowError
  have := bumpIntegral_pos
  positivity

lemma macroKernelLower_row {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin (R/q+1)).toNat) :
    1-kernelRowError q R ≤ ((q:ℝ)/4)^3*∑ j : GridIndex m,
      (if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)) := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hall := macroKernelLower_row_all hq hR (gridEmbed i) (macroKernel_support_inside hq hR0.le i hi)
  have hs : (∑ j : GridIndex m, if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)) =
      (∑ j : GridIndex m, macroKernelLower q R (gridEmbed i) (gridEmbed j))-macroKernelLower q R (gridEmbed i) (gridEmbed i) := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset (GridIndex m))
      (fun j => macroKernelLower q R (gridEmbed i) (gridEmbed j)) (Finset.mem_univ i)
    have he : (∑ j : GridIndex m, if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)) =
        ∑ j ∈ Finset.univ.erase i, macroKernelLower q R (gridEmbed i) (gridEmbed j) := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      congr 1
      ext j
      simp [ne_comm]
    rw [he]
    linarith
  rw [hs, mul_sub]
  have hd := mul_le_mul_of_nonneg_left (macroKernelLower_diagonal (q := q) hR0 (gridEmbed i)) (show 0 ≤ ((q:ℝ)/4)^3 by positivity)
  have hsq : ((q:ℝ)/4)^2 ≤ R^2 := pow_le_pow_left₀ (by positivity) hR 2
  have hd' : ((q:ℝ)/4)^3*((R^3)⁻¹*bumpIntegral⁻¹) ≤ bumpIntegral⁻¹*q/R := by
    apply (le_div_iff₀ hR0).mpr
    have hb := bumpIntegral_pos
    have he : ((q:ℝ)/4)^3*((R^3)⁻¹*bumpIntegral⁻¹)*R =
        bumpIntegral⁻¹*((q:ℝ)/4)*(((q:ℝ)/4)^2/R^2) := by field_simp
    rw [he]
    have hh : ((q:ℝ)/4)^2/R^2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
    calc
      _ ≤ bumpIntegral⁻¹*((q:ℝ)/4)*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := by nlinarith [inv_nonneg.mpr hb.le]
  unfold kernelRowError
  linear_combination hall + hd + hd'

lemma kernelInterior_ratio (D : ℕ) :
    Tendsto (fun m : ℕ => (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ)/(m:ℝ)^3)
      atTop (nhds 1) := by
  classical
  have hcard (m : ℕ) : (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ) =
      (m:ℝ)^3-((boundaryGrid m D).card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (GridIndex m)) (boundaryGrid m D)
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hh
    have hr : (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ)+((boundaryGrid m D).card:ℝ) = (m:ℝ)^3 := by exact_mod_cast hh
    linarith
  have hz : Tendsto (fun m : ℕ => (6:ℝ)*D/(m:ℝ)) atTop (nhds (0:ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun m : ℕ => ((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (0:ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hz
    filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    have hb : ((boundaryGrid m D).card:ℝ) ≤ 6*D*(m:ℝ)^2 := by exact_mod_cast card_boundaryGrid m D
    apply (div_le_iff₀ (by positivity : 0 < (m:ℝ)^3)).mpr
    calc
      _ ≤ 6*D*(m:ℝ)^2 := hb
      _ = _ := by field_simp
  have ht' : Tendsto (fun m : ℕ => 1-((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (1:ℝ)) := by
    simpa using (tendsto_const_nhds.sub hsmall : Tendsto (fun m : ℕ => (1:ℝ)-((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (1-0)))
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [hcard]
  field_simp

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MacroUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition
section
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairWithin_nonneg {Y : Type uY} (v : Y → Y → ℝ) (hv : ∀ x y, 0 ≤ v x y) (s : ParticleState Y) :
    0 ≤ pairWithin v s := by
  unfold pairWithin
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs <;> simp_all)))

lemma pairCellEnergy_upper (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ) (M : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hKs : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, K i j ≤ M)
    (hv : ∀ i j x y, |v i j x y| ≤ K i j) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy v x ≤ M/2*∑ i, (particleCount (x i):ℝ)^2 := by
  have hh := (le_abs_self (pairCellEnergy v x)).trans (pairCellEnergy_abs_bound v K hK hv x)
  dsimp only [cellN] at hh
  have hr := symmetric_row_quadratic K (fun i => (particleCount (x i):ℝ)) M hK hKs hrow
  linarith

lemma pairCellEnergy_lower_cross (v : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hn : ∀ i a b, 0 ≤ v i i a b) (hv : ∀ i j a b, K i j ≤ v i j a b)
    (x : ∀ i, ParticleState (X i)) :
    (1/2:ℝ)*∑ i, ∑ j, (if i = j then 0 else K i j*(particleCount (x i):ℝ)*(particleCount (x j):ℝ)) ≤
      pairCellEnergy v x := by
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun (i:I) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (j:I) _ => show
      (if i = j then 0 else K i j*(particleCount (x i):ℝ)*(particleCount (x j):ℝ)) ≤
      (if i = j then 0 else pairBetween (v i j) (x i) (x j)) from by
        split_ifs
        · rfl
        · simpa only [neg_neg] using pairBetween_lower (v i j) (J := -K i j) (fun a b => by simpa using hv i j a b) (x i) (x j)))
  have hd : 0 ≤ ∑ i, pairWithin (v i i) (x i) :=
    Finset.sum_nonneg (fun i _ => pairWithin_nonneg _ (hn i) _)
  unfold pairCellEnergy cellHamiltonian
  linarith

end

lemma macro_attraction_upper {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R)
    (x : ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))) :
    pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x ≤
    (1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*∑ i, (particleCount (x i):ℝ)^2 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have he : (1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3) =
      ((1+10000*(bumpLip:ℝ)*q/R)/((q:ℝ)/4)^3)/2 := by ring
  rw [he]
  apply pairCellEnergy_upper _ (fun i j => macroKernelUpper q R (gridEmbed i) (gridEmbed j))
  · exact fun _ _ => macroKernelUpper_nonneg hR0 _ _
  · exact fun _ _ => macroKernelUpper_symm _ _ _ _
  · intro i
    apply (le_div_iff₀ (by positivity : 0 < ((q:ℝ)/4)^3)).mpr
    rw [mul_comm]
    exact macroKernelUpper_row hq hR _
  · intro i j y z
    rw [abs_of_nonneg (scaledBump_nonneg hR0 _)]
    exact (macroKernel_pair_bounds hq hR0 y.property z.property).2

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MacroLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma macroKernelLower_total {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) :
    (kernelInterior m q R).card*(1-kernelRowError q R)/((q:ℝ)/4)^3 ≤
      ∑ i : GridIndex m, ∑ j : GridIndex m, if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j) := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  let row (i : GridIndex m) := ∑ j : GridIndex m, if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)
  calc
    _ = ∑ i ∈ kernelInterior m q R, (1-kernelRowError q R)/((q:ℝ)/4)^3 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ kernelInterior m q R, row i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_iff₀ (by positivity : 0 < ((q:ℝ)/4)^3)).mpr
      rw [mul_comm]
      exact macroKernelLower_row hq hR i (Finset.mem_sdiff.mp hi).2
    _ ≤ ∑ i, row i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      exact Finset.sum_nonneg (fun j _ => by split_ifs; rfl; exact macroKernelLower_nonneg _ _ _ _)

lemma macro_attraction_lower {q m n : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R)
    (x : ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))) (hx : ∀ i, particleCount (x i) = n) :
    (kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3) ≤
      pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hh := pairCellEnergy_lower_cross
    (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position)))
    (fun i j => macroKernelLower q R (gridEmbed i) (gridEmbed j))
    (fun i a b => scaledBump_nonneg hR0 _) (fun i j a b => (macroKernel_pair_bounds hq hR0 a.property b.property).1) x
  simp only [hx] at hh
  have he (i j : GridIndex m) : (if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)*(n:ℝ)*n) =
      (n:ℝ)^2*(if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)) := by split_ifs <;> ring
  simp_rw [he, ← Finset.mul_sum] at hh
  have ht := mul_le_mul_of_nonneg_left (macroKernelLower_total (m := m) hq hR) (sq_nonneg (n:ℝ))
  calc
    _ = (1/2:ℝ)*((n:ℝ)^2*((kernelInterior m q R).card*(1-kernelRowError q R)/((q:ℝ)/4)^3)) := by ring
    _ ≤ _ := by linarith

lemma measurable_macroKacEnergy {φ : Potential} (hφ : Continuous φ) (m q : ℕ) (R lam : ℝ) :
    Measurable (macroKacEnergy φ m q R lam) := by
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro i hi
    exact (measurable_pairWithin _ (continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val).measurable).comp (measurable_pi_apply i)
  · apply measurable_const.mul
    apply measurable_pairCellEnergy
    intro i j
    exact ((continuous_scaledBump R).comp ((continuous_subtype_val.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd))).measurable

lemma macroKacEnergy_lower {φ : Potential} {q m : ℕ} (hq : 0 < q) {R lam : ℝ}
    (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (x : MacroState m q) :
    (∑ i : GridIndex m, (pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i) -
      lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(particleCount (x i):ℝ)^2)) ≤
      macroKacEnergy φ m q R lam x := by
  have hh := mul_le_mul_of_nonneg_left (macro_attraction_upper hq hR x) hlam
  unfold macroKacEnergy
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simpa only [mul_div_assoc, mul_assoc] using sub_le_sub_left hh (∑ i : GridIndex m, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i))

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CountWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma measurable_countWeight {φ : Potential} (hφ : Continuous φ) (β : ℝ) (F : ℕ → ℝ) :
    Measurable (fun s : ParticleState Position => F (particleCount s)*Real.exp (-β*orderedEnergy φ s.2)) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro n
  change Continuous (fun x : Fin n → Position => F n * Real.exp (-β*orderedEnergy φ x))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_orderedEnergy hφ)))

lemma lintegral_countWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) {A : Set Position} (hAfin : volume A ≠ ⊤) :
    (∫⁻ s : ParticleState Position,
      ENNReal.ofReal (F (particleCount s)*Real.exp (-β*orderedEnergy φ s.2))
      ∂particleBase (volume.restrict A) z) =
    ∑' n : ℕ, ENNReal.ofReal (F n*Real.exp (z*n)*partitionOn φ A n β) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  rw [lintegral_particleBase _ _ (measurable_countWeight hφ β F).ennreal_ofReal]
  apply tsum_congr
  intro n
  dsimp only [particleCount]
  have hi := (integrable_orderedBoltzmann (ι := Fin n) hφ hb β (Measure.pi (fun _ => volume.restrict A))).const_mul (F n)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => mul_nonneg (hF n) (Real.exp_pos _).le)), integral_const_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [partitionOn, rawPartition, div_eq_mul_inv]
  ring

lemma partitionOn_macroRegion (φ : Potential) {q : ℕ} (hq : 0 < q) (i : Cell) (n : ℕ) (β : ℝ) :
    partitionOn φ (macroRegion q i) n β = partition φ ((q:ℝ)/4) n β := by
  rw [macroRegion_translate hq, partitionOn_translate]
  have hh : partitionOn φ (halfCube ((q:ℝ)/4)) n β = partitionOn φ (cube ((q:ℝ)/4)) n β := by
    simp only [partitionOn, rawPartition, restrict_halfCube]
  rw [hh, partitionOn_cube]

section MapWeight
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]

lemma lintegral_pairWeight_map (v : Y → Y → ℝ) (hv : Measurable (Function.uncurry v))
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f) (β z : ℝ) (F : ℕ → ℝ) :
    (∫⁻ s : ParticleState X, ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin (fun x y => v (f x) (f y)) s)) ∂particleBase μ z) =
    ∫⁻ s : ParticleState Y, ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin v s)) ∂particleBase (Measure.map f μ) z := by
  have hfun : Measurable (fun s : ParticleState Y => ENNReal.ofReal (F (particleCount s)*Real.exp (-β*pairWithin v s))) := by
    apply Measurable.ennreal_ofReal
    exact (((continuous_of_discreteTopology : Continuous F).comp continuous_particleCount).measurable).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_pairWithin v hv)))
  rw [← particleBase_map μ z hf, lintegral_map hfun (measurable_mapParticle hf)]
  rfl

end MapWeight

lemma lintegral_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∫⁻ s : ParticleState (macroRegion q i), ENNReal.ofReal (F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s))
      ∂particleBase (regionMeasure (macroRegion q i)) z) =
    ∑' n : ℕ, ENNReal.ofReal (F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β) := by
  have hfin : volume (macroRegion q i) ≠ ⊤ := by rw [volume_macroRegion hq]; finiteness
  let : IsFiniteMeasure (regionMeasure (macroRegion q i)) := regionMeasure_finite (measurableSet_macroRegion _ _) hfin
  rw [lintegral_pairWeight_map (radialPair φ) (continuous_radialPair hφ).measurable _ Subtype.val measurable_subtype_coe,
    regionMeasure_map (measurableSet_macroRegion _ _)]
  simp only [pairWithin_radial]
  rw [lintegral_countWeight hφ hb β z F hF hfin]
  simp only [partitionOn_macroRegion φ hq]

lemma integrable_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    Integrable (fun s : ParticleState (macroRegion q i) => F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s))
      (particleBase (regionMeasure (macroRegion q i)) z) := by
  have hm : Measurable (fun s : ParticleState (macroRegion q i) => F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s)) := by
    exact ((continuous_of_discreteTopology.comp continuous_particleCount).measurable).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_pairWithin _
        (continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val).measurable)))
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall (fun s => mul_nonneg (hF _) (Real.exp_pos _).le))).mp
  rw [lintegral_macroWeight hφ hb hq i β z F hF,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)) hs]
  exact ENNReal.ofReal_ne_top

lemma integral_macroWeight {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (i : Cell) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    (∫ s : ParticleState (macroRegion q i), F (particleCount s)*
      Real.exp (-β*pairWithin (fun (x y : macroRegion q i) => radialPair φ x y) s)
      ∂particleBase (regionMeasure (macroRegion q i)) z) =
      ∑' n, F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun s => mul_nonneg (hF _) (Real.exp_pos _).le))
    (integrable_macroWeight hφ hb hq i β z F hF hs).aestronglyMeasurable,
    lintegral_macroWeight hφ hb hq i β z F hF,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => mul_nonneg (mul_nonneg (hF n) (Real.exp_pos _).le) (partition_nonneg _ _ _)))]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GridPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma integrable_macroProduct {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (m : ℕ) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    Integrable (macroProduct φ m q β F) (macroMeasure m q z) := by
  let (i : GridIndex m) : IsFiniteMeasure (regionMeasure (macroRegion q (gridEmbed i))) :=
    regionMeasure_finite (measurableSet_macroRegion _ _) (by rw [volume_macroRegion hq]; finiteness)
  exact Integrable.fintype_prod_dep (fun i => integrable_macroWeight hφ hb hq (gridEmbed i) β z F hF hs)

lemma integral_macroProduct {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {q : ℕ} (hq : 0 < q) (m : ℕ) (β z : ℝ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)) :
    (∫ x, macroProduct φ m q β F x ∂macroMeasure m q z) =
      (∑' n, F n*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)^(m^3) := by
  let (i : GridIndex m) : IsFiniteMeasure (regionMeasure (macroRegion q (gridEmbed i))) :=
    regionMeasure_finite (measurableSet_macroRegion _ _) (by rw [volume_macroRegion hq]; finiteness)
  unfold macroProduct macroMeasure
  rw [integral_fintype_prod_eq_prod (fun i : GridIndex m => fun s : ParticleState (macroRegion q (gridEmbed i)) => F (particleCount s)*Real.exp (-β*pairWithin (fun (y w : macroRegion q (gridEmbed i)) => radialPair φ y w) s))]
  simp only [integral_macroWeight hφ hb hq _ β z F hF hs, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin]

lemma macroQuad_upper {φ : Potential} {m q : ℕ} (hq : 0 < q) {β R lam : ℝ}
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (x : MacroState m q) :
    Real.exp (-β*macroKacEnergy φ m q R lam x) ≤
      macroProduct φ m q β (fun n => Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)) x := by
  have hh := mul_le_mul_of_nonpos_left (macroKacEnergy_lower (φ := φ) hq hR hlam x) (neg_nonpos.mpr hβ)
  apply (Real.exp_le_exp.mpr hh).trans_eq
  simp only [macroProduct, ← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma integrable_macroKac {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {β R lam z : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam)
    (hs : Summable (quadraticTerm φ ((q:ℝ)/4) β z (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2))) :
    Integrable (fun x => Real.exp (-β*macroKacEnergy φ m q R lam x)) (macroMeasure m q z) := by
  have hs' : Summable (fun n : ℕ => Real.exp (β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2)*Real.exp (z*n)*partition φ ((q:ℝ)/4) n β) := by
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    dsimp only [quadraticTerm]
    have he : β*lam*(1+10000*(bumpLip:ℝ)*q/R)/(2*((q:ℝ)/4)^3)*(n:ℝ)^2 = β*lam*(1+10000*(bumpLip:ℝ)*q/R)/2*(n:ℝ)^2/((q:ℝ)/4)^3 := by ring
    rw [he]; ring
  apply (integrable_macroProduct hφ hb hq m β z _ (fun _ => (Real.exp_pos _).le) hs').mono'
    (Real.measurable_exp.comp (measurable_const.mul (measurable_macroKacEnergy hφ m q R lam))).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by change |Real.exp (-β*macroKacEnergy φ m q R lam x)| ≤ _; rw [abs_of_pos (Real.exp_pos _)]; exact macroQuad_upper hq hβ hR hlam x)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoxPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma summable_sectorWeight (φ : Potential) (L β z : ℝ) (n : ℕ) :
    Summable (fun k : ℕ => (if k = n then (1:ℝ) else 0)*Real.exp (z*k)*partition φ L k β) :=
  summable_of_ne_finset_zero (s := {n}) (by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk])

lemma sectorWeight_tsum (φ : Potential) (L β z : ℝ) (n : ℕ) :
    (∑' k : ℕ, (if k = n then (1:ℝ) else 0)*Real.exp (z*k)*partition φ L k β) = Real.exp (z*n)*partition φ L n β := by
  simp only [ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq n _

lemma macroProduct_sector (φ : Potential) (m q : ℕ) (β : ℝ) (n : ℕ) (x : MacroState m q) :
    macroProduct φ m q β (fun k => if k = n then 1 else 0) x =
      if (∀ i, particleCount (x i) = n) then
        Real.exp (-β*∑ i : GridIndex m, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)) else 0 := by
  classical
  by_cases hh : ∀ i, particleCount (x i) = n
  · rw [ite_eq_left hh]
    simp only [macroProduct, hh, ite_true, if_true, one_mul, ← Real.exp_sum, ← Finset.mul_sum]
  · simp only [hh, ite_false, if_false]
    obtain ⟨i, hi⟩ := not_forall.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma macroSector_lower {φ : Potential} {m q : ℕ} (hq : 0 < q) {β R lam : ℝ}
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (n : ℕ) (x : MacroState m q) :
    Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3)))*
      macroProduct φ m q β (fun k => if k = n then 1 else 0) x ≤
    Real.exp (-β*macroKacEnergy φ m q R lam x) := by
  classical
  rw [macroProduct_sector]
  split_ifs with hh
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb := mul_le_mul_of_nonneg_left (macro_attraction_lower hq hR x hh) (mul_nonneg hβ hlam)
    unfold macroKacEnergy
    nlinarith
  · simpa only [mul_zero] using (Real.exp_pos _).le

lemma macroKac_partition_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {β R lam z : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam)
    (hi : Integrable (fun x => Real.exp (-β*macroKacEnergy φ m q R lam x)) (macroMeasure m q z)) (n : ℕ) :
    Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3)))*
      (Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)^(m^3) ≤
    boltzmannPartition (macroMeasure m q z) (fun x => β*macroKacEnergy φ m q R lam x) := by
  have hs := summable_sectorWeight φ ((q:ℝ)/4) β z n
  have hn (k : ℕ) : 0 ≤ (if k = n then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hh := integral_mono ((integrable_macroProduct hφ hb hq m β z _ hn hs).const_mul
    (Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3))))) hi
    (macroSector_lower hq hβ hR hlam n)
  rw [integral_const_mul, integral_macroProduct hφ hb hq m β z _ hn hs, sectorWeight_tsum] at hh
  simpa only [boltzmannPartition, neg_mul] using hh

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FamilyStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uAlpha

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma summable_prepend (v : ℝ) {f : ℕ → ℝ} (hf : Summable f) : Summable (prepend v f) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [prepend_succ] using hf

lemma tsum_prepend (v : ℝ) {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, prepend v f n) = v+∑' n, f n := by
  simpa only [prepend_zero, prepend_succ] using (summable_prepend v hf).tsum_eq_zero_add

lemma prepend_nonneg {a : ℝ} {b : ℕ → ℝ} (ha : 0 ≤ a) (hb : ∀ n, 0 ≤ b n) :
    ∀ n, 0 ≤ prepend a b n := by
  intro n; cases n with
  | zero => exact ha
  | succ n => exact hb n

lemma prepend_range {R : ℝ} {S : ℕ → ℝ} (hR : 1 ≤ R) (hS : ∀ n, 1 ≤ S n) :
    ∀ n, 1 ≤ prepend R S n := by
  intro n; cases n with
  | zero => exact hR
  | succ n => exact hS n

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma deletedKacPressure_sector_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) {R t a β h : ℝ} (ht : 0 < t)
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (ha : 0 ≤ a)
    (hs : Summable (kacSeries φ q R t a β h)) (n : ℕ) :
    h*((n:ℝ)/((q:ℝ)/4)^3)-finiteCanonical φ t ((q:ℝ)/4) n β+
      β*a/2*((kernelInterior m q R).card/(m:ℝ)^3)*(1-kernelRowError q R)*((n:ℝ)/((q:ℝ)/4)^3)^2 ≤
      deletedKacPressure φ m q R t a β h := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < (q:ℝ)/4 := by positivity
  have hta : 0 ≤ t*a := mul_nonneg ht.le ha
  have hi := integrable_macroKac (m := m) hφ hb hq hβ hR hta hs
  have hpos : 0 < Real.exp (t*h*n)*partition φ ((q:ℝ)/4) n β :=
    mul_pos (Real.exp_pos _) (partition_pos hφ hb hs0 n β)
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (pow_pos hpos _))
    (macroKac_partition_lower hφ hb hq hβ hR hta hi n)
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hpos.ne'), Real.log_exp, Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hs0 n β).ne', Real.log_exp] at hh
  unfold deletedKacPressure
  apply (le_div_iff₀ (by positivity : 0 < t*((m:ℝ)*q/4)^3)).mpr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first
  | rfl
  | unfold finiteCanonical
    simp only [Nat.cast_pow]
    field_simp [ht.ne', hq0.ne', hm0.ne']
    ring

lemma kernelInterior_fraction {m q : ℕ} (hm : 0 < m) (R : ℝ) :
    (0:ℝ) ≤ (kernelInterior m q R).card/(m:ℝ)^3 ∧ (kernelInterior m q R).card/(m:ℝ)^3 ≤ 1 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  have hc := Finset.card_le_card (Finset.subset_univ (kernelInterior m q R))
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using (by exact_mod_cast hc : ((kernelInterior m q R).card:ℝ) ≤ (Fintype.card (GridIndex m):ℝ))

lemma deletedKacPressure_branch_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) {B R t a β h D u : ℝ}
    (hst : StableWith φ B) (ht : 0 < t) (hq1 : 1 ≤ (q:ℝ)/4)
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (ha : 0 ≤ a)
    (hs : Summable (kacSeries φ q R t a β h)) (hD : Real.exp (β*B+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure φ t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      deletedKacPressure φ m q R t a β h+
        β*a/2*(1-((kernelInterior m q R).card/(m:ℝ)^3)*(1-kernelRowError q R))*D^2+
        Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  obtain ⟨n, hn, hmax⟩ := finiteGrandPressure_max_term hφ hb hst ht hq1 hβ hD
  have hsector := deletedKacPressure_sector_lower hφ hb hm hq ht hβ hR ha hs n
  let d := (n:ℝ)/((q:ℝ)/4)^3
  let v := ((kernelInterior m q R).card:ℝ)/(m:ℝ)^3
  have hv := kernelInterior_fraction (q := q) hm R
  have he := kernelRowError_nonneg q (le_trans (by linarith) hR)
  have hv' : 0 ≤ 1-v*(1-kernelRowError q R) := by dsimp only [v]; nlinarith [mul_nonneg hv.1 he]
  have hb0 : 0 ≤ β*a/2 := by positivity
  have hD0 : 0 ≤ D := hn.1.trans hn.2
  have hsq : d^2 ≤ D^2 := (sq_le_sq₀ hn.1 hD0).mpr hn.2
  have herror := mul_le_mul_of_nonneg_left hsq (mul_nonneg hb0 hv')
  have hdiff := mul_nonneg hb0 (sq_nonneg (u-d))
  dsimp only [d, v] at herror hdiff
  nlinarith

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_row_mono_mass {t a : ℝ} {b : ℕ → ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8 := by
  have hc : 0 ≤ 2197*t*bumpIntegral⁻¹ := by have := bumpIntegral_pos; positivity
  exact (mul_le_mul_of_nonneg_left (by linarith : (∑' n, b n) ≤ a+∑' n, b n) hc).trans hrow

lemma family_grand_prepend_limit {t β a R : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) (h : ℝ) :
    Tendsto (fun L : ℝ => finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t L β h) atTop
      (nhds (grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h)) := by
  have hba := prepend_nonneg ha hb
  have hRS := prepend_range hR hS
  have hsum := summable_prepend a hs
  have hrow' : 2197*t*bumpIntegral⁻¹*(∑' n, prepend a b n) ≤ (t^2/8)/8 := by rw [tsum_prepend _ hs]; exact hrow
  exact (grandPressure_spec (continuous_familyPotential hba hRS hsum t)
    (bounded_familyPotential hba hRS hsum t)
    (stable_family_of_master (by linarith) hba hRS hsum hsum (fun _ => le_rfl) hrow')
    (by linarith) hβ (fun _ hr => familyPotential_nonpos_outer hba hRS ht hr) h).1

lemma family_kac_lower_limit_rt2_oai {q : ℕ} (hq : 0 < q) {t β h R₀ a R D u : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hD : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure (familyPotential t b S) t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h+
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)+
      β*a/2*kernelRowError q R*D^2+Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  have ht0 : 0 < t := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR1 : 1 ≤ R := hq1.trans hR
  have hrowb := family_row_mono_mass ht0.le ha hrow
  have hstable := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrowb
  have hl := (family_grand_prepend_limit ht hβ.le ha hR1 hb hS hs hrow h).comp
    ((tendsto_natCast_atTop_atTop.atTop_mul_const hq0).atTop_div_const (by norm_num : (0:ℝ) < 4))
  have hf : Tendsto (fun m : ℕ => ((kernelInterior m q R).card:ℝ)/(m:ℝ)^3) atTop (nhds 1) :=
    kernelInterior_ratio (cellMargin (R/q+1)).toNat
  have he := ((((tendsto_const_nhds (x := (1:ℝ))).sub (hf.mul_const (1-kernelRowError q R))).const_mul (β*a/2)).mul_const (D^2))
  have htt := (((hl.add_const (boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4))).add he).add_const
    (Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3)))
  simp only [one_mul, sub_sub_cancel] at htt
  apply ge_of_tendsto htt
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hd := (abs_le.mp (family_kac_deletion_rt2 (h := h) hm hq ht hβ ha hR1 hb hS hs hR₀ hrange hrow)).1
  have hk := deletedKacPressure_branch_lower (continuous_familyPotential hb hS hs t)
    (bounded_familyPotential hb hS hs t) hm hq hstable ht0 hq1 hβ.le hR ha hks hD
  dsimp only [Function.comp_def]
  linarith

end RadialTransition
end

end OAI
end

theorem solution : type_of% @OAI.RadialTransition.family_kac_lower_limit_rt2_oai := @OAI.RadialTransition.family_kac_lower_limit_rt2_oai
