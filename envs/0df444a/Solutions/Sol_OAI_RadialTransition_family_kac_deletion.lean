-- Prove2me | solution 1 for OAI.RadialTransition.family_kac_deletion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:10:32.616531+00:00
-- url     : https://prove2.me/submissions/0cb79274-a15f-4528-972b-24a98cdaddc4

import Mathlib
import Definitions.Def_RadialDensityInterval
import Definitions.Def_OAIQWRTD000
import Theorems.Thm_OAI_RadialTransition_gibbs_bogoliubov

section
-- module Solutions.OAIQW_RadialTransition.Compat
namespace OAI.RadialTransition
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434


end OAI.RadialTransition
end

section
-- module Solutions.OAIQW_RadialTransition.ShellGeometry
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
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
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
-- module Solutions.OAIQW_RadialTransition.BoundedCore
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
-- module Solutions.OAIQW_RadialTransition.RadialKernel
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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.CellStability
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
      · simp only [hA, ite_true, sub_self, mul_zero]
        exact coreReal_nonneg _ _
      · simp only [hA, ite_false, sub_zero, mul_one]
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
      Finset.mem_univ, ite_true]
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
-- module Solutions.OAIQW_RadialTransition.ScaledKernels
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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.LatticeStability
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
-- module Solutions.OAIQW_RadialTransition.FinitePartition
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

theorem log_integral_exp_convex_mix {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (hH : Integrable (fun x => Real.exp (a * F x + b * G x)) μ)
    (hZF : 0 < ∫ x, Real.exp (F x) ∂μ) (hZG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (hZH : 0 < ∫ x, Real.exp (a * F x + b * G x) ∂μ) :
    Real.log (∫ x, Real.exp (a * F x + b * G x) ∂μ) ≤
      a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ) := by
  let c := a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ)
  have hpoint (x : X) : Real.exp (-c) * Real.exp (a * F x + b * G x) ≤
      a * ((∫ x, Real.exp (F x) ∂μ)⁻¹ * Real.exp (F x)) +
      b * ((∫ x, Real.exp (G x) ∂μ)⁻¹ * Real.exp (G x)) := by
    have hh := convexOn_exp.2 (mem_univ (F x - Real.log (∫ x, Real.exp (F x) ∂μ)))
      (mem_univ (G x - Real.log (∫ x, Real.exp (G x) ∂μ))) ha hb hab
    simp only [smul_eq_mul] at hh
    have heq : a * (F x - Real.log (∫ x, Real.exp (F x) ∂μ)) +
        b * (G x - Real.log (∫ x, Real.exp (G x) ∂μ)) = -c + (a * F x + b * G x) := by
      dsimp [c]; ring
    rw [heq, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log hZF, Real.exp_log hZG] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hi := integral_mono (hH.const_mul _) ((hF.const_mul _).const_mul a |>.add
      ((hG.const_mul _).const_mul b)) hpoint
  simp only [Pi.add_apply, integral_add ((hF.const_mul _).const_mul a) ((hG.const_mul _).const_mul b),
    integral_const_mul, inv_mul_cancel₀ hZF.ne', inv_mul_cancel₀ hZG.ne', mul_one, hab] at hi
  have hexp := Real.log_le_log (mul_pos (Real.exp_pos (-c)) hZH) hi
  rw [Real.log_mul (Real.exp_ne_zero _) hZH.ne', Real.log_exp, Real.log_one] at hexp
  change _ ≤ c
  linarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.SpatialProducts
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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PartitionReplication
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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.GrandPartition
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

theorem grandOn_cube (φ : Potential) (L t β h : ℝ) :
    grandOn φ (cube L) β (t * h) = grandPartition φ t L β h := by
  simp only [grandOn, grandPartition, partitionOn_cube]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.SpatialReplication
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

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.OccupationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem exp_weighted_sum_le {I : Type uI} [Fintype I] (w x : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) :
    Real.exp (∑ i, w i * x i) ≤ 1 - ∑ i, w i + ∑ i, w i * Real.exp (x i) := by
  have hh := convexOn_exp.map_add_sum_le (t := Finset.univ) (w := w) (p := x)
    (v := 1 - ∑ i, w i) (q := 0) (fun i _ => hw i) (by ring)
    (fun _ _ => mem_univ _) (sub_nonneg.mpr hs) (mem_univ _)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] using hh

theorem integral_exp_fraction_le {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => Real.exp (f x)) μ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Integrable (fun x => Real.exp (η * f x)) μ ∧
      (∫ x, Real.exp (η * f x) ∂μ) ≤ Real.exp (η * Real.log (∫ x, Real.exp (f x) ∂μ)) := by
  have hib : Integrable (fun x => Real.exp (η * f x)) μ := by
    apply hi.mono' (Real.measurable_exp.comp (measurable_const.mul hf)).aestronglyMeasurable
    filter_upwards [] with x
    change |Real.exp (η * f x)| ≤ Real.exp (f x)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_left (hf0 x) hη1)
  have hpos : 0 < ∫ x, Real.exp (η * f x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hib).mpr
    simp [Function.support, Real.exp_ne_zero]
  have hpos' : 0 < ∫ x, Real.exp (f x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi).mpr
    simp [Function.support, Real.exp_ne_zero]
  have hh := log_integral_exp_convex_mix (F := fun _ : X => (0 : ℝ)) (G := f)
    (sub_nonneg.mpr hη1) hη0 (by ring) (by simp) hi
    (by simpa using hib) (by simp) hpos' (by simpa using hpos)
  simp only [mul_zero, zero_add, Real.exp_zero, integral_const, probReal_univ, smul_eq_mul,
    one_mul, Real.log_one] at hh
  refine ⟨hib, ?_⟩
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

theorem occupation_moment_closure {I : Type uI} {X : Type uX} [Fintype I] [Nonempty I]
    [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (f : I → X → ℝ) (θ : I → I → ℝ) {C η : ℝ}
    (hC : 1 ≤ C) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hi : ∀ i, Integrable (fun x => Real.exp (f i x)) μ)
    (hθ : ∀ i j, 0 ≤ θ i j) (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hconditional : ∀ i, (∫ x, Real.exp (f i x) ∂μ) ≤
      C * (∫ x, Real.exp (η * ∑ j, θ i j * f j x) ∂μ)) :
    ∀ i, (∫ x, Real.exp (f i x) ∂μ) ≤ Real.exp (Real.log C / (1 - η)) := by
  classical
  let F (i : I) := ∫ x, Real.exp (f i x) ∂μ
  have hF1 (i : I) : 1 ≤ F i := by
    have hh := integral_mono (integrable_const (1 : ℝ)) (hi i)
      (fun x => Real.one_le_exp_iff.mpr (hf0 i x))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  obtain ⟨k, _, hk⟩ := Finset.univ.exists_max_image F Finset.univ_nonempty
  have hFm (i : I) : F i ≤ F k := hk i (Finset.mem_univ i)
  have hfrac (i : I) := integral_exp_fraction_le (hf i) (hf0 i) (hi i) hη0 hη1.le
  have hless (i : I) : ∫ x, Real.exp (η * ∑ j, θ i j * f j x) ∂μ ≤
      Real.exp (η * Real.log (F k)) := by
    let g : X → ℝ := fun x => 1 - ∑ j, θ i j + ∑ j, θ i j * Real.exp (η * f j x)
    have hig : Integrable g μ :=
      (integrable_const _).add (integrable_finsetSum _ (fun j _ => (hfrac j).1.const_mul _))
    have hpoint (x : X) : Real.exp (η * ∑ j, θ i j * f j x) ≤ g x := by
      have hh := exp_weighted_sum_le (θ i) (fun j => η * f j x) (hθ i) (hrow i)
      dsimp only [g]
      convert hh using 1
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hmix : Integrable (fun x => Real.exp (η * ∑ j, θ i j * f j x)) μ := by
      apply hig.mono' (Real.measurable_exp.comp
        (measurable_const.mul (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hf j))))).aestronglyMeasurable
      filter_upwards [] with x
      change |Real.exp (η * ∑ j, θ i j * f j x)| ≤ g x
      rw [abs_of_pos (Real.exp_pos _)]
      exact hpoint x
    have hh := integral_mono hmix hig hpoint
    have hexp1 : 1 ≤ Real.exp (η * Real.log (F k)) := by
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg hη0 (Real.log_nonneg (hF1 k))
    have hfs (j : I) : ∫ x, Real.exp (η * f j x) ∂μ ≤ Real.exp (η * Real.log (F k)) :=
      (hfrac j).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hF1 j]) (hFm j)) hη0))
    dsimp only [g] at hh
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun j _ => (hfrac j).1.const_mul _)),
      integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_finsetSum _ (fun j _ => (hfrac j).1.const_mul _)] at hh
    simp only [integral_const_mul] at hh
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hfs j) (hθ i j))
    rw [← Finset.sum_mul] at hs
    have := hrow i
    nlinarith
  have hkineq := (hconditional k).trans (mul_le_mul_of_nonneg_left (hless k) (by linarith))
  have hC0 : 0 < C := by linarith
  have hFk0 : 0 < F k := by linarith [hF1 k]
  have hlog := Real.log_le_log hFk0 hkineq
  rw [Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hb : Real.log (F k) ≤ Real.log C / (1 - η) := by
    apply (le_div_iff₀ (sub_pos.mpr hη1)).mpr
    nlinarith
  intro i
  apply (hFm i).trans
  simpa only [Real.exp_log hFk0] using Real.exp_le_exp.mpr hb

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.ParticleMeasure
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

theorem dirac_vacuum_le_particleBase (ν : Measure X) (z : ℝ) [SigmaFinite ν] :
    Measure.dirac (particleVacuum (X := X)) ≤ particleBase ν z := by
  have hh := Measure.le_sum (fun n : ℕ => ENNReal.ofReal (Real.exp (z*n) / n.factorial) •
    Measure.map (Sigma.mk n) (Measure.pi (fun _ : Fin n => ν))) 0
  rw [Measure.pi_of_empty _ Fin.elim0, Measure.map_dirac' (measurable_particle_mk 0)] at hh
  simpa [particleBase, particleVacuum] using hh

theorem lintegral_exp_particleCount (ν : Measure X) [IsFiniteMeasure ν] (z c : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * particleCount x)) ∂particleBase ν z) =
      ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+c))) := by
  have hf : Measurable (fun x : ParticleState X => ENNReal.ofReal (Real.exp (c * particleCount x))) :=
    (Real.measurable_exp.comp (measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (n : ℝ))).comp continuous_particleCount).measurable)).ennreal_ofReal
  rw [lintegral_particleBase ν z hf, ← particleBase_univ (measure_ne_top ν univ) (z+c)]
  have hh := lintegral_particleBase ν (z+c) (f := fun _ => 1) measurable_const
  rw [show particleBase ν (z+c) univ = ∫⁻ _, (1 : ℝ≥0∞) ∂particleBase ν (z+c) by simp, hh]
  apply tsum_congr
  intro n
  simp only [particleCount, lintegral_const, Measure.pi_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [add_mul, Real.exp_add]
  ring

theorem integrable_exp_particleCount (ν : Measure X) [IsFiniteMeasure ν] (z c : ℝ) :
    Integrable (fun x => Real.exp (c * particleCount x)) (particleBase ν z) := by
  have hf : Measurable (fun x : ParticleState X => Real.exp (c * particleCount x)) :=
    Real.measurable_exp.comp (measurable_const.mul ((continuous_of_discreteTopology : Continuous (fun n : ℕ => (n : ℝ))).comp continuous_particleCount).measurable)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (Real.exp_pos _).le]
  rw [lintegral_exp_particleCount]
  exact ENNReal.ofReal_lt_top

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.BoltzmannMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem boltzmannMeasure_probability {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E : X → ℝ} (hi : Integrable (fun x => Real.exp (-E x)) μ)
    (hp : 0 < boltzmannPartition μ E) : IsProbabilityMeasure (boltzmannMeasure μ E) := by
  constructor
  rw [boltzmannMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  change (ENNReal.ofReal (boltzmannPartition μ E))⁻¹ * ENNReal.ofReal (boltzmannPartition μ E) = 1
  rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]

theorem integral_boltzmann {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E : X → ℝ} (hE : Measurable E) (f : X → ℝ) :
    (∫ x, f x ∂boltzmannMeasure μ E) =
      (boltzmannPartition μ E)⁻¹ * ∫ x, Real.exp (-E x) * f x ∂μ := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-E x))) :=
    (Real.measurable_exp.comp hE.neg).ennreal_ofReal
  rw [boltzmannMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      hw (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hZ : 0 ≤ boltzmannPartition μ E := integral_nonneg (fun _ => (Real.exp_pos _).le)
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

theorem integrable_boltzmann {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E f : X → ℝ} (hE : Measurable E)
    (hi : Integrable (fun x => Real.exp (-E x) * f x) μ)
    (hp : 0 < boltzmannPartition μ E) : Integrable f (boltzmannMeasure μ E) := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-E x))) :=
    (Real.measurable_exp.comp hE.neg).ennreal_ofReal
  apply Integrable.smul_measure
  · apply (integrable_withDensity_iff_integrable_smul'
      hw
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using hi
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)

theorem log_boltzmann_difference_le {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E F : X → ℝ} (hE : Measurable E)
    (hiE : Integrable (fun x => Real.exp (-E x)) μ)
    (hiF : Integrable (fun x => Real.exp (-F x)) μ)
    (hpE : 0 < boltzmannPartition μ E) (hpF : 0 < boltzmannPartition μ F)
    (hi : Integrable (fun x => F x - E x) (boltzmannMeasure μ E)) :
    Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F) ≤
      ∫ x, F x - E x ∂boltzmannMeasure μ E :=
  gibbs_bogoliubov hE hiE hiF hpE hpF hi

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.CellMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uI

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

lemma cell_young {D G n : ℝ} (hD : 0 < D) : n * G ≤ D / 4 * n^2 + G^2 / D := by
  have hh := sq_nonneg (D*n - 2*G)
  have he : G^2 / D * D = G^2 := div_mul_cancel₀ _ hD.ne'
  nlinarith

theorem one_cell_exponential_moment {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν]
    (z : ℝ) {β D B J G : ℝ} (hβ : 0 ≤ β) (hD : 0 < D) (hJ : J ≤ D)
    {H : ParticleState X → ℝ} (hH : Measurable H)
    (henergy : ∀ x, (D-J/2) * (particleCount x : ℝ)^2 - B*particleCount x -
      (particleCount x : ℝ)*G ≤ H x - H particleVacuum) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*D/4*(particleCount x : ℝ)^2 - β*H x)) ∂particleBase ν z) ≤
      ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) *
      ENNReal.ofReal (Real.exp (β*G^2/D)) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂particleBase ν z := by
  let A := Real.exp (β*G^2/D - β*H particleVacuum)
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-β*H x))) :=
    (Real.measurable_exp.comp (measurable_const.mul hH)).ennreal_ofReal
  have hlower : ENNReal.ofReal (Real.exp (-β*H particleVacuum)) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂particleBase ν z := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂Measure.dirac particleVacuum :=
        (lintegral_dirac' _ hm).symm
      _ ≤ _ := lintegral_mono' (dirac_vacuum_le_particleBase ν z) le_rfl
  have hupper : (∫⁻ x, ENNReal.ofReal (Real.exp (β*D/4*(particleCount x : ℝ)^2 - β*H x)) ∂particleBase ν z) ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal A * ENNReal.ofReal (Real.exp (β*B*particleCount x)) ∂particleBase ν z := by
        apply lintegral_mono
        intro x
        dsimp only [A]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hy := cell_young (G := G) (n := (particleCount x : ℝ)) hD
        have hj := mul_nonneg (sub_nonneg.mpr hJ) (sq_nonneg (particleCount x : ℝ))
        have he := mul_le_mul_of_nonneg_left (henergy x) hβ
        have hy' := mul_le_mul_of_nonneg_left hy hβ
        have hj' := mul_nonneg hβ hj
        have heq : β * (G^2/D) = β*G^2/D := by ring
        nlinarith
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_exp_particleCount]
  calc
    _ ≤ _ := hupper
    _ = ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) *
        ENNReal.ofReal (Real.exp (β*G^2/D)) * ENNReal.ofReal (Real.exp (-β*H particleVacuum)) := by
      dsimp [A]
      rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [neg_mul]
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hlower

section ProductCells
variable {I : Type uI} [Fintype I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

omit [Fintype I] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]
  [∀ i, MeasurableSpace (X i)] in
theorem measurable_cellN (i : I) : Measurable (cellN (X := X) i) :=
  ((show Measurable (fun n : ℕ => (n : ℝ)) from continuous_of_discreteTopology.measurable).comp
    continuous_particleCount.measurable).comp (measurable_pi_apply i)

theorem integrable_exp_cell_total (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z c : ℝ) : Integrable (fun x => Real.exp (c * ∑ i, cellN i x))
      (Measure.pi (fun i => particleBase (ν i) z)) := by
  have hh := Integrable.fintype_prod_dep (fun i => integrable_exp_particleCount (ν i) z c)
  convert hh using 1
  ext x
  rw [Finset.mul_sum, Real.exp_sum]
  rfl

theorem cell_partition_pos (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hi : Integrable (fun x => Real.exp (-E x)) (Measure.pi (fun i => particleBase (ν i) z))) :
    0 < boltzmannPartition (Measure.pi (fun i => particleBase (ν i) z)) E := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr
  have hs : Function.support (fun x => Real.exp (-E x)) = univ := by
    ext x
    simp [Function.support, Real.exp_ne_zero]
  rw [hs]
  rw [Measure.pi_univ]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [particleBase_univ (measure_ne_top (ν i) univ)]
  exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

theorem weighted_square_le {I : Type uI} [Fintype I] (w n : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hrow : ∑ i, w i ≤ 1) :
    (∑ i, w i * n i)^2 ≤ ∑ i, w i * (n i)^2 := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg (n i)))
    (fun i (_ : i ∈ Finset.univ) => (show (w i * n i)^2 ≤ w i * (w i * (n i)^2) by nlinarith))
  exact hh.trans (mul_le_of_le_one_left (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg (n i)))) hrow)

theorem integrable_cell_numerator (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} {E f : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E) (hf : Measurable f)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x)
    (hfbound : ∀ x, f x ≤ D/2 * ∑ i, (cellN i x)^2) :
    Integrable (fun x => Real.exp (f x - E x)) (Measure.pi (fun i => particleBase (ν i) z)) := by
  apply (integrable_exp_cell_total ν z B).mono' (Real.measurable_exp.comp (hf.sub hE)).aestronglyMeasurable
  filter_upwards [] with x
  change |Real.exp (f x - E x)| ≤ Real.exp (B * ∑ i, cellN i x)
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [hstable x, hfbound x])

theorem uniform_cell_exponential_moment [Nonempty I] [DecidableEq I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B V : ℝ} (hD : 0 < D) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (θ : I → I → ℝ) (hθ : ∀ i j, 0 ≤ θ i j) (hθdiag : ∀ i, θ i i = 0)
    (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    {E : (∀ i, ParticleState (X i)) → ℝ} (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x)
    (hconditional : ∀ i x s, D/2 * (particleCount s : ℝ)^2 - B * particleCount s -
      (particleCount s : ℝ) * (D/8 * ∑ j, θ i j * cellN j x) ≤
      E (Function.update x i s) - E (Function.update x i particleVacuum)) :
    ∀ i, (∫ x, Real.exp (D/4 * (cellN i x)^2)
      ∂boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z)) E) ≤
      Real.exp (16/15 * V * Real.exp (z+B)) := by
  classical
  let μ := Measure.pi (fun j => particleBase (ν j) z)
  let F (i : I) (x : ∀ j, ParticleState (X j)) := D/4 * (cellN i x)^2
  let g (i : I) (x : ∀ j, ParticleState (X j)) := (1/16:ℝ) * ∑ j, θ i j * F j x
  let C := Real.exp (V * Real.exp (z+B))
  have hFmeas (i : I) : Measurable (F i) := measurable_const.mul ((measurable_cellN i).pow_const 2)
  have hF0 (i : I) (x : ∀ j, ParticleState (X j)) : 0 ≤ F i x := mul_nonneg (by positivity) (sq_nonneg _)
  have hθ1 (i j : I) : θ i j ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hθ i k) (Finset.mem_univ j)).trans (hrow i)
  have hFbound (i : I) (x : ∀ j, ParticleState (X j)) : F i x ≤ D/2 * ∑ j, (cellN j x)^2 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => (cellN j x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    dsimp [F]
    nlinarith [sq_nonneg (cellN i x)]
  have hgmeas (i : I) : Measurable (g i) :=
    measurable_const.mul (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hFmeas j)))
  have hgBound (i : I) (x : ∀ j, ParticleState (X j)) : g i x ≤ D/2 * ∑ j, (cellN j x)^2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => mul_le_of_le_one_left (hF0 j x) (hθ1 i j))
    have hsum : ∑ j, F j x = D/4 * ∑ j, (cellN j x)^2 := by simp only [F, Finset.mul_sum]
    have hn : 0 ≤ ∑ j, (cellN j x)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [g]
    rw [hsum] at hh
    nlinarith
  have hiE : Integrable (fun x => Real.exp (-E x)) μ := by
    simpa using integrable_cell_numerator ν z hE measurable_const hstable
      (f := fun _ => 0) (fun x => mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hp := cell_partition_pos ν z hiE
  let := boltzmannMeasure_probability hiE hp
  have hiF (i : I) := integrable_cell_numerator ν z hE (hFmeas i) hstable (hFbound i)
  have hig (i : I) := integrable_cell_numerator ν z hE (hgmeas i) hstable (hgBound i)
  have hif (i : I) : Integrable (fun x => Real.exp (F i x)) (boltzmannMeasure μ E) := by
    apply integrable_boltzmann hE _ hp
    convert hiF i using 1
    ext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hC1 : 1 ≤ C := Real.one_le_exp_iff.mpr (mul_nonneg hV (Real.exp_pos _).le)
  have hint (i : I) : (∫ x, Real.exp (F i x) ∂boltzmannMeasure μ E) ≤
      C*(∫ x, Real.exp (g i x) ∂boltzmannMeasure μ E) := by
    have hfmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (F i x - E x))) :=
      (Real.measurable_exp.comp ((hFmeas i).sub hE)).ennreal_ofReal
    have hgmeas' : Measurable (fun x => ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x - E x))) :=
      measurable_const.mul (Real.measurable_exp.comp ((hgmeas i).sub hE)).ennreal_ofReal
    have hlocal : lmarginal (fun j => particleBase (ν j) z) {i}
        (fun x => ENNReal.ofReal (Real.exp (F i x - E x))) ≤
      lmarginal (fun j => particleBase (ν j) z) {i}
        (fun x => ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x - E x))) := by
      rw [lmarginal_singleton, lmarginal_singleton]
      intro x
      have hginv (s : ParticleState (X i)) : g i (Function.update x i s) = g i x := by
        dsimp only [g, F, cellN]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [hθdiag]
        · simp [Function.update_of_ne hj]
      have hcur := one_cell_exponential_moment (ν i) z (β := 1) (D := D) (B := B) (J := D)
        (G := D/8 * ∑ j, θ i j * cellN j x) (by norm_num) hD le_rfl
        (H := fun s => E (Function.update x i s))
        (hE.comp (measurable_update x (a := i))) (fun s => by
          convert hconditional i x s using 1; ring)
      have hG : (D/8 * ∑ j, θ i j * cellN j x)^2 / D ≤ g i x := by
        have hh := weighted_square_le (θ i) (fun j => cellN j x) (hθ i) (hrow i)
        have hs : ∑ j, θ i j * F j x = D/4 * ∑ j, θ i j * (cellN j x)^2 := by
          dsimp only [F]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        dsimp only [g]
        rw [hs]
        apply (div_le_iff₀ hD).mpr
        nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hh)]
      have hCi : Real.exp ((ν i univ).toReal * Real.exp (z+B)) ≤ C :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hvol i) (Real.exp_pos _).le)
      simp only [one_mul, neg_one_mul] at hcur
      calc
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp (D/4*(particleCount s : ℝ)^2 -
            E (Function.update x i s))) ∂particleBase (ν i) z := by
          apply lintegral_congr
          intro s
          simp only [F, cellN, Function.update_self]
        _ ≤ _ := hcur
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x)) *
            ∫⁻ s, ENNReal.ofReal (Real.exp (-E (Function.update x i s))) ∂particleBase (ν i) z := by
          gcongr
        _ = _ := by
          rw [mul_assoc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply lintegral_congr
          intro s
          rw [hginv, Real.exp_sub]
          simp only [div_eq_mul_inv, Real.exp_neg, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have htotal := lintegral_le_of_lmarginal_le {i} hfmeas hgmeas' hlocal
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hiF i) (Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      ← ofReal_integral_eq_lintegral_ofReal (hig i) (Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      ← ENNReal.ofReal_mul (by linarith [hC1])] at htotal
    have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [hC1])
      (integral_nonneg (fun _ => (Real.exp_pos _).le)))).mp htotal
    rw [integral_boltzmann hE, integral_boltzmann hE]
    simp_rw [← Real.exp_add, neg_add_eq_sub]
    have hh := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hp.le)
    nlinarith
  have hc := occupation_moment_closure F θ hC1 (by norm_num : 0 ≤ (1/16:ℝ))
    (by norm_num : (1/16:ℝ) < 1) hFmeas hF0 hif hθ hrow hint
  intro i
  convert hc i using 1
  congr 1
  dsimp [C]
  rw [Real.log_exp]
  ring

end ProductCells
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.CellInteractions
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

section AbstractCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma double_sum_update (w : ∀ i j, X i → X j → ℝ)
    (hdiag : ∀ i a b, w i i a b = 0)
    (hsym : ∀ i j a b, w i j a b = w j i b a)
    (x : ∀ i, X i) (k : I) (s t : X k) :
    (∑ i, ∑ j, w i j (Function.update x k s i) (Function.update x k s j)) -
      (∑ i, ∑ j, w i j (Function.update x k t i) (Function.update x k t j)) =
      2 * ∑ j, (w k j s (x j) - w k j t (x j)) := by
  have hpoint (i j : I) :
      w i j (Function.update x k s i) (Function.update x k s j) -
        w i j (Function.update x k t i) (Function.update x k t j) =
      (if i = k then w k j s (x j) - w k j t (x j) else 0) +
      (if j = k then w i k (x i) s - w i k (x i) t else 0) := by
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j; simp [hdiag]
      · simp [hj, Function.update_of_ne]
    · by_cases hj : j = k
      · subst j; simp [hi, Function.update_of_ne]
      · simp [hi, hj, Function.update_of_ne]
  simp_rw [← Finset.sum_sub_distrib, hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  conv_lhs => arg 2; arg 2; intro i; rw [hsym i k (x i) s, hsym i k (x i) t]
  ring

lemma cellHamiltonian_update (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (vac : ∀ i, X i) (hU0 : ∀ i, U i (vac i) = 0)
    (hW0 : ∀ i j a, W i j (vac i) a = 0)
    (hsym : ∀ i j a b, W i j a b = W j i b a)
    (x : ∀ i, X i) (k : I) (s : X k) :
    cellHamiltonian U W (Function.update x k s) -
      cellHamiltonian U W (Function.update x k (vac k)) =
      U k s + ∑ j, if k = j then 0 else W k j s (x j) := by
  let w (i j : I) (a : X i) (b : X j) := if i = j then 0 else W i j a b
  have hwsym (i j : I) (a : X i) (b : X j) : w i j a b = w j i b a := by
    dsimp [w]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h, hsym i j a b]
  have hh := double_sum_update w (by simp [w]) hwsym x k s (vac k)
  have hu : (∑ i, U i (Function.update x k s i)) -
      (∑ i, U i (Function.update x k (vac k) i)) = U k s := by
    rw [← Finset.sum_sub_distrib]
    have he (i : I) : U i (Function.update x k s i) - U i (Function.update x k (vac k) i) =
        if i = k then U k s else 0 := by
      by_cases hi : i = k
      · subst i; simp [hU0]
      · simp [hi, Function.update_of_ne]
    simp_rw [he]
    simp
  have hz (j : I) : w k j (vac k) (x j) = 0 := by simp [w, hW0]
  simp only [hz, sub_zero] at hh
  change (∑ i, U i (Function.update x k s i)) + 1/2 * (∑ i, ∑ j, w i j _ _) -
      ((∑ i, U i (Function.update x k (vac k) i)) + 1/2 * (∑ i, ∑ j, w i j _ _)) = _
  dsimp only [w] at hh
  linarith

lemma cellHamiltonian_stable (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (n : ∀ i, X i → ℝ) (_hn : ∀ i x, 0 ≤ n i x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    {D B : ℝ} (_hD : 0 ≤ D) (hrow : ∀ i, ∑ j, J i j ≤ D)
    (hU : ∀ i a, D * (n i a)^2 - B * n i a - J i i/2 * (n i a)^2 ≤ U i a)
    (hW : ∀ i j a b, -J i j * n i a * n j b ≤ W i j a b)
    (x : ∀ i, X i) :
    D/2 * ∑ i, (n i (x i))^2 - B * ∑ i, n i (x i) ≤ cellHamiltonian U W x := by
  have hb := symmetric_row_quadratic J (fun i => n i (x i)) D hJ hJsym hrow
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hU i (x i))
  have hw := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      (if i = j then 0 else -J i j * n i (x i) * n j (x j)) ≤
      (if i = j then 0 else W i j (x i) (x j)) from by split_ifs; rfl; exact hW i j _ _))
  have hsplit : (∑ i, ∑ j, J i j * n i (x i) * n j (x j)) =
      (∑ i, J i i * (n i (x i))^2) +
      ∑ i, ∑ j, if i = j then 0 else J i j * n i (x i) * n j (x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have he (j : I) : J i j * n i (x i) * n j (x j) =
        (if i = j then J i j * n i (x i) * n j (x j) else 0) +
        (if i = j then 0 else J i j * n i (x i) * n j (x j)) := by split_ifs <;> simp
    calc
      _ = ∑ j, ((if i = j then J i j * n i (x i) * n j (x j) else 0) +
          (if i = j then 0 else J i j * n i (x i) * n j (x j))) :=
        Finset.sum_congr rfl (fun j _ => he j)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        congr 1
        ring
  have hwneg : (∑ i, ∑ j, if i = j then 0 else -J i j * n i (x i) * n j (x j)) =
      -(∑ i, ∑ j, if i = j then 0 else J i j * n i (x i) * n j (x j)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hwneg] at hw
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hu
  have hd : (∑ i, J i i / 2 * (n i (x i))^2) = (1/2:ℝ) * ∑ i, J i i * (n i (x i))^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hd] at hu
  unfold cellHamiltonian
  linarith

end AbstractCells

section PairCells
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}

theorem pairBetween_symm (v : X → Y → ℝ) (w : Y → X → ℝ)
    (hv : ∀ x y, v x y = w y x) (s : ParticleState X) (t : ParticleState Y) :
    pairBetween v s t = pairBetween w t s := by
  unfold pairBetween
  simp_rw [hv]
  exact Finset.sum_comm

lemma continuous_particle_prod [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : ParticleState X → ParticleState Y → Z}
    (hf : ∀ m n, Continuous (fun p : (Fin m → X) × (Fin n → Y) => f ⟨m,p.1⟩ ⟨n,p.2⟩)) :
    Continuous (Function.uncurry f) := by
  let e := Homeomorph.sigmaProdDistrib (X := fun m : ℕ => Fin m → X) (Y := ParticleState Y)
  have h : Continuous (fun q : Σ m : ℕ, (Fin m → X) × ParticleState Y =>
      f ⟨q.1,q.2.1⟩ q.2.2) := by
    apply continuous_sigma
    intro m
    let e' := Homeomorph.sigmaProdDistrib (X := fun n : ℕ => Fin n → Y) (Y := Fin m → X)
    have h' : Continuous (fun q : Σ n : ℕ, (Fin n → Y) × (Fin m → X) =>
        f ⟨m,q.2.2⟩ ⟨q.1,q.2.1⟩) := by
      apply continuous_sigma
      intro n
      exact (hf m n).comp continuous_swap
    exact (h'.comp e'.continuous).comp continuous_swap
  exact h.comp e.continuous

lemma continuous_pairWithin [TopologicalSpace X] (v : X → X → ℝ)
    (hv : Continuous (Function.uncurry v)) : Continuous (pairWithin v) := by
  apply continuous_sigma
  intro n
  change Continuous (fun a : Fin n → X => (1/2:ℝ) *
    ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else v (a i) (a j))
  apply continuous_const.mul
  apply continuous_finsetSum _
  intro i _
  apply continuous_finsetSum _
  intro j _
  split_ifs
  · exact continuous_const
  · exact hv.comp (show Continuous (fun a : Fin n → X => (a i, a j)) from
      (continuous_apply i).prodMk (continuous_apply j))

lemma continuous_pairBetween [TopologicalSpace X] [TopologicalSpace Y] (v : X → Y → ℝ)
    (hv : Continuous (Function.uncurry v)) : Continuous (Function.uncurry (pairBetween v)) := by
  apply continuous_particle_prod
  intro m n
  change Continuous (fun p : (Fin m → X) × (Fin n → Y) =>
    ∑ i : Fin m, ∑ j : Fin n, v (p.1 i) (p.2 j))
  apply continuous_finsetSum _
  intro i _
  apply continuous_finsetSum _
  intro j _
  exact hv.comp (show Continuous (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j)) from
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply j).comp continuous_snd))

lemma pairBetween_lower (v : X → Y → ℝ) {J : ℝ} (hv : ∀ x y, -J ≤ v x y)
    (s : ParticleState X) (t : ParticleState Y) :
    -J * particleCount s * particleCount t ≤ pairBetween v s t := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hv (s.2 i) (t.2 j)))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pairBetween, particleCount, mul_comm, mul_left_comm] using hh

lemma pairWithin_perturb_lower (v w : X → X → ℝ) {J : ℝ} (hJ : 0 ≤ J)
    (hv : ∀ x y, w x y - J ≤ v x y) (s : ParticleState X) :
    pairWithin w s - J/2 * (particleCount s : ℝ)^2 ≤ pairWithin v s := by
  classical
  have hp (i j : Fin s.1) :
      (if i = j then 0 else w (s.2 i) (s.2 j)) - J ≤
        (if i = j then 0 else v (s.2 i) (s.2 j)) := by
    split_ifs
    · linarith
    · exact hv _ _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  unfold pairWithin particleCount
  nlinarith

lemma pairWithin_core {t J : ℝ} (ht : 0 ≤ t) (hJ : 0 ≤ J)
    (pos : X → Position) (hdiam : ∀ x y, dist (pos x) (pos y) ≤ 1)
    (v : X → X → ℝ) (hv : ∀ x y, corePotential t (nndist (pos x) (pos y)) - J ≤ v x y)
    (s : ParticleState X) :
    t^2/8 * (particleCount s : ℝ)^2 - t^2/2 * particleCount s -
      J/2 * (particleCount s : ℝ)^2 ≤ pairWithin v s := by
  have hh := pairWithin_perturb_lower v (fun x y => corePotential t (nndist (pos x) (pos y))) hJ hv s
  have hc := core_ordered_lower_small_diameter ht (fun i : Fin s.1 => pos (s.2 i))
    (fun i j => hdiam _ _)
  simp only [Fintype.card_fin, ne_eq, ite_not] at hc
  dsimp only [pairWithin, corePotential, particleCount] at hh
  change (1/2:ℝ) * (∑ i : Fin s.1, ∑ j : Fin s.1,
    if i = j then 0 else coreReal t (dist (pos (s.2 i)) (pos (s.2 j)))) - _ ≤ _ at hh
  dsimp only [particleCount, pairWithin]
  linarith

end PairCells

section PhysicalCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

omit [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  [∀ i, SecondCountableTopology (X i)] in
lemma continuous_pairCellEnergy (v : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Continuous (Function.uncurry (v i j))) : Continuous (pairCellEnergy v) := by
  unfold pairCellEnergy cellHamiltonian
  apply Continuous.add
  · exact continuous_finsetSum _ (fun i _ => (continuous_pairWithin _ (hv i i)).comp (continuous_apply i))
  · apply continuous_const.mul
    apply continuous_finsetSum _
    intro i _
    apply continuous_finsetSum _
    intro j _
    split_ifs
    · exact continuous_const
    · exact (continuous_pairBetween _ (hv i j)).comp
        (show Continuous (fun x : ∀ i, ParticleState (X i) => (x i, x j)) from
          (continuous_apply i).prodMk (continuous_apply j))

theorem pairCell_exponential_moment [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v : ∀ i j, X i → X j → ℝ) (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) :
    ∀ i, (∫ x, Real.exp (β*(t^2/8)/4 * (cellN i x)^2)
      ∂boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z))
        (fun x => β * pairCellEnergy v x)) ≤
      Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) := by
  let D := t^2/8
  let B := t^2/2
  have hD : 0 < D := by dsimp [D]; positivity
  let U (i : I) := pairWithin (v i i)
  let W (i j : I) := pairBetween (v i j)
  have hU (i : I) (s : ParticleState (X i)) :
      D * (particleCount s : ℝ)^2 - B * particleCount s - J i i/2*(particleCount s : ℝ)^2 ≤ U i s :=
    pairWithin_core ht.le (hJ i i) (pos i) (hdiam i) (v i i) (hintra i) s
  have hW (i j : I) (s : ParticleState (X i)) (r : ParticleState (X j)) :
      -J i j * particleCount s * particleCount r ≤ W i j s r :=
    pairBetween_lower (v i j) (hcross i j) s r
  have hrowD (i : I) : ∑ j, J i j ≤ D := (hrow i).trans (by dsimp [D]; nlinarith [sq_nonneg t])
  have hH (x : ∀ i, ParticleState (X i)) :
      D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ pairCellEnergy v x := by
    exact cellHamiltonian_stable U W (fun _ s => particleCount s) (fun _ _ => Nat.cast_nonneg _)
      J hJ hJsym hD.le hrowD hU hW x
  let θ (i j : I) := if i = j then 0 else 8*J i j/D
  have hθ (i j : I) : 0 ≤ θ i j := by
    dsimp [θ]
    split_ifs
    · rfl
    · exact div_nonneg (mul_nonneg (by norm_num) (hJ i j)) hD.le
  have hθrow (i : I) : ∑ j, θ i j ≤ 1 := by
    have hle : ∑ j, θ i j ≤ 8/D * ∑ j, J i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      dsimp [θ]
      split_ifs
      · exact mul_nonneg (div_nonneg (by norm_num) hD.le) (hJ i j)
      · exact le_of_eq (by ring)
    refine hle.trans ?_
    calc
      _ ≤ 8/D * (D/8) := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
      _ = 1 := by field_simp
  have hcond (i : I) (x : ∀ j, ParticleState (X j)) (s : ParticleState (X i)) :
      D/2 * (particleCount s : ℝ)^2 - B*particleCount s -
        (particleCount s : ℝ)*(D/8 * ∑ j, θ i j * cellN j x) ≤
      pairCellEnergy v (Function.update x i s) -
        pairCellEnergy v (Function.update x i particleVacuum) := by
    rw [pairCellEnergy, pairCellEnergy,
      cellHamiltonian_update _ _ (fun _ => particleVacuum) (by simp)
        (by simp) (fun k j a b => pairBetween_symm _ _ (hvsym k j) a b)]
    have hJi : J i i ≤ D :=
      (Finset.single_le_sum (fun j _ => hJ i j) (Finset.mem_univ i)).trans (hrowD i)
    have hu := hU i s
    have hsq := mul_nonneg (sub_nonneg.mpr hJi) (sq_nonneg (particleCount s : ℝ))
    have hw := Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      (if i = j then 0 else -J i j * particleCount s * particleCount (x j)) ≤
        (if i = j then 0 else pairBetween (v i j) s (x j)) from by
          split_ifs; rfl; exact hW i j s (x j))
    have he : (∑ j, if i = j then 0 else -J i j * particleCount s * particleCount (x j)) =
        -(particleCount s : ℝ) * (D/8 * ∑ j, θ i j * cellN j x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [θ, cellN]
      split_ifs
      · ring
      · field_simp
    rw [he] at hw
    dsimp [U] at hu
    linarith
  apply uniform_cell_exponential_moment ν z (D := β*D) (B := β*B)
    (E := fun x => β * pairCellEnergy v x)
    (mul_pos hβ hD) hV hvol θ hθ (by simp [θ]) hθrow
    (measurable_const.mul (continuous_pairCellEnergy v hv).measurable)
  · intro x
    have hh := mul_le_mul_of_nonneg_left (hH x) hβ.le
    convert hh using 1 <;> first | rfl | ring
  · intro i x s
    have hh := mul_le_mul_of_nonneg_left (hcond i x s) hβ.le
    convert hh using 1 <;> first | rfl | ring

end PhysicalCells
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PerturbationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uI

noncomputable section


open MeasureTheory Set Filter

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

lemma secondMoment_of_exponential {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Measurable f) {c C : ℝ} (hc : 0 < c)
    (hi : Integrable (fun x => Real.exp (c*(f x)^2)) μ)
    (hb : ∫ x, Real.exp (c*(f x)^2) ∂μ ≤ C) :
    Integrable (fun x => (f x)^2) μ ∧ (∫ x, (f x)^2 ∂μ) ≤ C/c := by
  have hbound (x : X) : (f x)^2 ≤ c⁻¹ * Real.exp (c*(f x)^2) := by
    have hh := Real.add_one_le_exp (c*(f x)^2)
    rw [mul_comm c⁻¹, ← div_eq_mul_inv]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm, div_eq_mul_inv] using (le_of_lt (by linarith : (f x)^2*c < Real.exp (c*(f x)^2)))
  have hi' : Integrable (fun x => (f x)^2) μ :=
    (hi.const_mul c⁻¹).mono' (hf.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))] using hbound x))
  refine ⟨hi', ?_⟩
  have hh := integral_mono hi' (hi.const_mul c⁻¹) hbound
  rw [integral_const_mul] at hh
  exact hh.trans (by simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le))

lemma pairMoment_of_second {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C : ℝ} (hiF : Integrable (fun x => (f x)^2) μ) (hiG : Integrable (fun x => (g x)^2) μ)
    (hbF : ∫ x, (f x)^2 ∂μ ≤ C) (hbG : ∫ x, (g x)^2 ∂μ ≤ C) :
    Integrable (fun x => f x * g x) μ ∧ (∫ x, f x * g x ∂μ) ≤ C := by
  have hb (x : X) : |f x * g x| ≤ ((f x)^2+(g x)^2)/2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (f x-g x), sq_nonneg (f x+g x)]
  have hi : Integrable (fun x => f x*g x) μ :=
    ((hiF.add hiG).div_const 2).mono' (hf.mul hg).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hb x))
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi ((hiF.add hiG).div_const 2) (fun x => (le_abs_self _).trans (hb x))
  simp only [Pi.add_apply] at hh
  rw [integral_div, integral_add hiF hiG] at hh
  linarith

theorem log_partition_perturbation {X : Type uX} {I : Type uI} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} {E F : X → ℝ} (hE : Measurable E) (hF : Measurable F)
    (hiE : Integrable (fun x => Real.exp (-E x)) μ)
    (hiF : Integrable (fun x => Real.exp (-F x)) μ)
    (hpE : 0 < boltzmannPartition μ E) (hpF : 0 < boltzmannPartition μ F)
    (n : I → X → ℝ) (hn : ∀ i, Measurable (n i))
    (K : I → I → ℝ) (hK : ∀ i j, 0 ≤ K i j) {C : ℝ}
    (hsE : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ E))
    (hsF : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ F))
    (hbE : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ E ≤ C)
    (hbF : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ F ≤ C)
    (hd : ∀ x, |F x-E x| ≤ ∑ i, ∑ j, K i j * n i x * n j x) :
    |Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F)| ≤
      C * ∑ i, ∑ j, K i j := by
  have oneSide (E F : X → ℝ) (hE : Measurable E) (hF : Measurable F)
      (hiE : Integrable (fun x => Real.exp (-E x)) μ)
      (hiF : Integrable (fun x => Real.exp (-F x)) μ)
      (hpE : 0 < boltzmannPartition μ E) (hpF : 0 < boltzmannPartition μ F)
      (hsE : ∀ i, Integrable (fun x => (n i x)^2) (boltzmannMeasure μ E))
      (hbE : ∀ i, ∫ x, (n i x)^2 ∂boltzmannMeasure μ E ≤ C)
      (hd : ∀ x, |F x-E x| ≤ ∑ i, ∑ j, K i j * n i x * n j x) :
      Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F) ≤ C*∑ i, ∑ j, K i j := by
    have hp (i j : I) := pairMoment_of_second (hn i) (hn j) (hsE i) (hsE j) (hbE i) (hbE j)
    have hiTerm (i j : I) : Integrable (fun x => K i j * n i x * n j x) (boltzmannMeasure μ E) := by
      simpa only [mul_assoc] using (hp i j).1.const_mul (K i j)
    have hiSum := integrable_finsetSum (Finset.univ : Finset I) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset I) (fun j _ => hiTerm i j))
    have hiDiff : Integrable (fun x => F x-E x) (boltzmannMeasure μ E) :=
      hiSum.mono' (hF.sub hE).aestronglyMeasurable (Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hd x))
    apply (log_boltzmann_difference_le hE hiE hiF hpE hpF hiDiff).trans
    apply (integral_mono hiDiff hiSum (fun x => (le_abs_self _).trans (hd x))).trans
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hiTerm i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hiTerm _ j)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp_rw [mul_assoc, integral_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp i j).2 (hK i j)
  apply abs_le.mpr
  constructor
  · have hh := oneSide F E hF hE hiF hiE hpF hpE hsF hbF (fun x => by simpa only [abs_sub_comm] using hd x)
    linarith
  · exact oneSide E F hE hF hiE hiF hpE hpF hsE hbE hd

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.FockIntegral
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

lemma functional_sector_card (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    {N : ℕ} (T : Finset (Fin N)) :
    (∫⁻ x : Fin N → X, F (Fin N) x ∂Measure.pi (fun i => if i ∈ T then μ else ν)) =
      ∫⁻ x : Fin T.card ⊕ Fin (N-T.card) → X, F _ x
        ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
  classical
  have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
  have hcardB : Fintype.card {i : Fin N // i ∉ T} = N - T.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
  let eA := (Fintype.equivFinOfCardEq hcardA).symm
  let eB := (Fintype.equivFinOfCardEq hcardB).symm
  let e := (Equiv.sumCongr eA eB).trans (Equiv.sumCompl (fun i => i ∈ T))
  have hs : ∀ i : Fin N, SigmaFinite (if i ∈ T then μ else ν) := by
    intro i
    split_ifs <;> infer_instance
  have hh := (functional_integral_equiv F heq e (fun i => if i ∈ T then μ else ν)).symm
  have hm : (fun i => if e i ∈ T then μ else ν) = Sum.elim (fun _ : Fin T.card => μ) (fun _ : Fin (N-T.card) => ν) := by
    funext i
    cases i with
    | inl i => exact ite_eq_left (eA i).property
    | inr i => exact ite_eq_right (eB i).property
  rwa [hm] at hh

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

section FockAdd
variable {X : Type uX} [MeasurableSpace X]
variable (F : ∀ (ι : Type) [Fintype ι], (ι → X) → ℝ≥0∞)
variable (heq : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X),
  F ι (x ∘ e) = F κ x)

include heq in
lemma fockIntegral_add (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (z : ℝ) :
    fockIntegral F (μ+ν) z = ∑' m : ℕ, ∑' n : ℕ,
      fockCoeff z m * fockCoeff z n *
        ∫⁻ x : Fin m ⊕ Fin n → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
  classical
  unfold fockIntegral
  calc
    _ = ∑' N : ℕ, ∑ m ∈ Finset.range (N+1),
        fockCoeff z m * fockCoeff z (N-m) *
          ∫⁻ x : Fin m ⊕ Fin (N-m) → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
      apply tsum_congr
      intro N
      rw [measure_pi_add, lintegral_finsetSum_measure]
      simp_rw [functional_sector_card F heq μ ν]
      rw [ennreal_subsets_card N (fun m =>
        ∫⁻ x : Fin m ⊕ Fin (N-m) → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν))),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← mul_assoc, fockCoeff_choose z (Nat.le_of_lt_succ (Finset.mem_range.mp hm))]
    _ = _ := ennreal_tsum_triangle (fun m n => fockCoeff z m * fockCoeff z n *
      ∫⁻ x : Fin m ⊕ Fin n → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)))

end FockAdd
section MultisetFock
variable {X : Type uX}

lemma configurationMultiset_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → X) : configurationMultiset (x ∘ e) = configurationMultiset x :=
  e.sum_comp (fun i => {x i})

lemma configurationMultiset_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X) (y : κ → X) :
    configurationMultiset (Sum.elim x y) = configurationMultiset x + configurationMultiset y := by
  exact Fintype.sum_sum_type _

end MultisetFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.ConfigurationMaps
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
-- module Solutions.OAIQW_RadialTransition.MultisetEnergy
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

section MultisetEnergy
variable {X : Type uX}

lemma multisetPairing_symm {v : X → X → ℝ} (hv : ∀ x y, v x y = v y x) (s t : Multiset X) :
    multisetPairing v s t = multisetPairing v t s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [multisetPairing, Multiset.map_cons, Multiset.sum_cons] at *
    simp_rw [Multiset.sum_map_add, hv a]
    rw [ih]

lemma multisetEnergy_add {v : X → X → ℝ} (hv : ∀ x y, v x y = v y x) (s t : Multiset X) :
    multisetEnergy v (s+t) = multisetEnergy v s + multisetEnergy v t + multisetPairing v s t := by
  simp only [multisetEnergy, multisetPairing_add_left, multisetPairing_add_right, multisetDiagonal_add]
  rw [multisetPairing_symm hv t s]
  ring

lemma sum_map_configuration {ι : Type} [Fintype ι] {M : Type uM} [AddCommMonoid M]
    (f : X → M) (x : ι → X) : ((configurationMultiset x).map f).sum = ∑ i, f (x i) := by
  unfold configurationMultiset
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp [Multiset.sum_sum]

lemma multisetPairing_configuration {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : X → X → ℝ) (x : ι → X) (y : κ → X) :
    multisetPairing v (configurationMultiset x) (configurationMultiset y) = ∑ i, ∑ j, v (x i) (y j) := by
  simp only [multisetPairing, sum_map_configuration]

lemma multisetDiagonal_configuration {ι : Type} [Fintype ι] (v : X → X → ℝ) (x : ι → X) :
    multisetDiagonal v (configurationMultiset x) = ∑ i, v (x i) (x i) := by
  simp only [multisetDiagonal, sum_map_configuration]

lemma multisetEnergy_particle (v : X → X → ℝ) (s : ParticleState X) :
    multisetEnergy v (particleMultiset s) = pairWithin v s := by
  classical
  simp only [multisetEnergy, particleMultiset, multisetPairing_configuration, multisetDiagonal_configuration,
    pairWithin]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hh : (∑ j : Fin s.1, v (s.2 i) (s.2 j)) =
      v (s.2 i) (s.2 i) + ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j) := by
    conv_lhs =>
      arg 2; ext j
      rw [show v (s.2 i) (s.2 j) = (if i = j then v (s.2 i) (s.2 j) else 0) +
        (if i = j then 0 else v (s.2 i) (s.2 j)) by split_ifs <;> simp]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  linarith

lemma multisetPairing_fin_sum_left {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) (t : Multiset X) :
    multisetPairing v (∑ i ∈ T, s i) t = ∑ i ∈ T, multisetPairing v (s i) t := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetPairing_fin_sum_right {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) (t : Multiset X) :
    multisetPairing v t (∑ i ∈ T, s i) = ∑ i ∈ T, multisetPairing v t (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetDiagonal_fin_sum {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) :
    multisetDiagonal v (∑ i ∈ T, s i) = ∑ i ∈ T, multisetDiagonal v (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetEnergy_sum {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (v : X → X → ℝ) (s : ι → Multiset X) :
    multisetEnergy v (∑ i, s i) = ∑ i, multisetEnergy v (s i) +
      (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else multisetPairing v (s i) (s j) := by
  have hh (i : ι) : (∑ j, multisetPairing v (s i) (s j)) =
      multisetPairing v (s i) (s i) + ∑ j, if i = j then 0 else multisetPairing v (s i) (s j) := by
    conv_lhs =>
      arg 2; ext j
      rw [show multisetPairing v (s i) (s j) =
        (if i = j then multisetPairing v (s i) (s j) else 0) +
        (if i = j then 0 else multisetPairing v (s i) (s j)) by split_ifs <;> simp]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [multisetEnergy, multisetPairing_fin_sum_left, multisetDiagonal_fin_sum]
  simp_rw [multisetPairing_fin_sum_right, hh]
  simp only [multisetEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma multisetEnergy_mappedMulti {I : Type} [Fintype I] [DecidableEq I] (Y : I → Type uY)
    (pos : ∀ i, Y i → X) (v : X → X → ℝ) (x : ∀ i, ParticleState (Y i)) :
    multisetEnergy v (mappedMultiParticleMultiset Y pos x) =
      pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x := by
  unfold mappedMultiParticleMultiset pairCellEnergy cellHamiltonian
  rw [multisetEnergy_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [multisetEnergy_particle]
    rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rfl
    · exact multisetPairing_configuration v _ _

end MultisetEnergy

lemma continuous_radialPair {φ : Potential} (hφ : Continuous φ) :
    Continuous (Function.uncurry (radialPair φ)) :=
  hφ.comp (continuous_fst.nndist continuous_snd)

lemma radialPair_symm (φ : Potential) (x y : Position) : radialPair φ x y = radialPair φ y x := by
  simp only [radialPair, nndist_comm]

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

lemma multisetEnergy_radial (φ : Potential) (s : ParticleState Position) :
    multisetEnergy (radialPair φ) (particleMultiset s) = orderedEnergy φ s.2 := by
  rw [multisetEnergy_particle, pairWithin_radial]

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
-- module Solutions.OAIQW_RadialTransition.CroppedCells
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

lemma croppedCellMeasure_univ {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    croppedCellMeasure A k univ = volume (A ∩ gridRegion k) := by
  rw [croppedCellMeasure, comap_subtype_coe_apply (hA.inter (measurableSet_gridRegion k))]
  simp only [Set.image_univ, Subtype.range_coe]

lemma croppedCellMeasure_finite {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    IsFiniteMeasure (croppedCellMeasure A k) := by
  constructor
  rw [croppedCellMeasure_univ hA k]
  exact ((measure_mono inter_subset_right).trans (volume_gridRegion_le k)).trans_lt ENNReal.ofReal_lt_top

lemma croppedCellMeasure_volume {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    ((croppedCellMeasure A k) univ).toReal ≤ 1/64 := by
  rw [croppedCellMeasure_univ hA k]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((measure_mono (inter_subset_right (s := A))).trans (volume_gridRegion_le k))
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/64)] using hh

lemma croppedCellMeasure_map {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    Measure.map Subtype.val (croppedCellMeasure A k) = volume.restrict (A ∩ gridRegion k) :=
  map_comap_subtype_coe (hA.inter (measurableSet_gridRegion k)) volume

lemma croppedCell_diameter {A : Set Position} {k : Cell} (x y : CroppedCell A k) :
    dist (x : Position) y ≤ 1 :=
  same_cell_diameter (x.property.2.trans y.property.2.symm)

lemma croppedCell_partition {I : Type} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {A : Set Position} (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i) :
    volume.restrict A = ∑ i, Measure.map Subtype.val (croppedCellMeasure A (e i)) := by
  have hd : Pairwise (Disjoint on (fun i => A ∩ gridRegion (e i))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (he (hx.2.symm.trans hy.2))
  have hu : (⋃ i, A ∩ gridRegion (e i)) = A := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, gridRegion, mem_ofPred_eq]
    exact ⟨fun ⟨_,hx,_⟩ => hx, fun hx => by obtain ⟨i,hi⟩ := hcover x hx; exact ⟨i,hx,hi⟩⟩
  rw [← hu, Measure.restrict_iUnion hd (fun i => hA.inter (measurableSet_gridRegion (e i))), Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [hu, croppedCellMeasure_map hA]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.CellDifferences
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

lemma if_zero_sub (p : Prop) [Decidable p] (a b : ℝ) :
    (if p then 0 else a-b) = (if p then 0 else a) - (if p then 0 else b) := by
  split_ifs <;> simp

lemma pairWithin_sub {X : Type uX} (v w : X → X → ℝ) (s : ParticleState X) :
    pairWithin (fun x y => v x y-w x y) s = pairWithin v s - pairWithin w s := by
  classical
  unfold pairWithin
  simp_rw [if_zero_sub]
  simp_rw [Finset.sum_sub_distrib]
  ring

lemma pairBetween_sub {X : Type uX} {Y : Type uY} (v w : X → Y → ℝ) (s : ParticleState X) (t : ParticleState Y) :
    pairBetween (fun x y => v x y-w x y) s t = pairBetween v s t - pairBetween w s t := by
  unfold pairBetween
  simp_rw [Finset.sum_sub_distrib]

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
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

section CellDifferences
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairCellEnergy_sub (v w : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => v i j a b-w i j a b) x = pairCellEnergy v x-pairCellEnergy w x := by
  unfold pairCellEnergy cellHamiltonian
  simp_rw [pairWithin_sub, pairBetween_sub, if_zero_sub, Finset.sum_sub_distrib]
  ring

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

lemma pairCellEnergy_abs_difference (v w : ∀ i j, X i → X j → ℝ) (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hv : ∀ i j a b, |v i j a b-w i j a b| ≤ K i j)
    (x : ∀ i, ParticleState (X i)) :
    |pairCellEnergy v x-pairCellEnergy w x| ≤ (1/2:ℝ) * ∑ i, ∑ j, K i j * cellN i x * cellN j x := by
  rw [← pairCellEnergy_sub]
  exact pairCellEnergy_abs_bound _ K hK hv x

end CellDifferences
section PhysicalControl
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairCell_quadratic_bound
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (v : ∀ i j, X i → X j → ℝ)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ t^2/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) (x : ∀ i, ParticleState (X i)) :
    (t^2/8)/2 * ∑ i, (cellN i x)^2 - (t^2/2) * ∑ i, cellN i x ≤ pairCellEnergy v x := by
  apply cellHamiltonian_stable (fun i => pairWithin (v i i)) (fun i j => pairBetween (v i j))
    (fun _ s => particleCount s) (fun _ _ => Nat.cast_nonneg _) J hJ hJsym (by positivity) hrow
  · intro i s
    exact pairWithin_core ht (hJ i i) (pos i) (hdiam i) (v i i) (hintra i) s
  · intro i j s r
    exact pairBetween_lower (v i j) (hcross i j) s r

variable [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

omit [DecidableEq I] in
lemma cell_boltzmann_integrable (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} (hD : 0 ≤ D) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x) :
    Integrable (fun x => Real.exp (-E x)) (Measure.pi (fun i => particleBase (ν i) z)) := by
  simpa only [zero_sub] using integrable_cell_numerator ν z hE measurable_const hstable
    (f := fun _ => 0) (fun x => mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

omit [DecidableEq I] in
lemma cell_exponential_integrable (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} (hD : 0 ≤ D) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x) (i : I) :
    Integrable (fun x => Real.exp (D/4*(cellN i x)^2))
      (boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z)) E) := by
  have hp := cell_partition_pos ν z (cell_boltzmann_integrable ν z hD hE hstable)
  apply integrable_boltzmann hE _ hp
  have hbound (x : ∀ j, ParticleState (X j)) : D/4*(cellN i x)^2 ≤ D/2*∑ j, (cellN j x)^2 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => (cellN j x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [mul_nonneg hD (sq_nonneg (cellN i x)), mul_le_mul_of_nonneg_left hh hD]
  have hi := integrable_cell_numerator ν z hE (measurable_const.mul ((measurable_cellN i).pow_const 2))
    hstable hbound
  convert hi using 1
  ext x
  rw [← Real.exp_add]
  congr 1
  dsimp only [Pi.mul_apply]
  ring

lemma pairCell_second_moment [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v : ∀ i j, X i → X j → ℝ) (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) :
    let μ := Measure.pi (fun j => particleBase (ν j) z)
    let E := fun x => β * pairCellEnergy v x
    Integrable (fun x => Real.exp (-E x)) μ ∧ 0 < boltzmannPartition μ E ∧
    ∀ i, Integrable (fun x => (cellN i x)^2) (boltzmannMeasure μ E) ∧
      (∫ x, (cellN i x)^2 ∂boltzmannMeasure μ E) ≤
        Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4) := by
  dsimp only
  have hD : 0 < β*(t^2/8) := by positivity
  have hr (i : I) : ∑ j, J i j ≤ t^2/8 := (hrow i).trans (by nlinarith [sq_nonneg t])
  have hE : Measurable (fun x => β * pairCellEnergy v x) :=
    measurable_const.mul (continuous_pairCellEnergy v hv).measurable
  have hstable (x : ∀ i, ParticleState (X i)) :
      (β*(t^2/8))/2 * ∑ i, (cellN i x)^2 - (β*(t^2/2))*∑ i, cellN i x ≤ β*pairCellEnergy v x := by
    have hh := mul_le_mul_of_nonneg_left
      (pairCell_quadratic_bound pos hdiam ht.le v J hJ hJsym hr hintra hcross x) hβ.le
    convert hh using 1 <;> first | rfl | ring
  have hi := cell_boltzmann_integrable ν z hD.le hE hstable
  refine ⟨hi, cell_partition_pos ν z hi, fun i => ?_⟩
  exact secondMoment_of_exponential (measurable_cellN i) (by positivity)
    (cell_exponential_integrable ν z hD.le hE hstable i)
    (pairCell_exponential_moment ν pos hdiam ht hβ hV hvol v hv hvsym J hJ hJsym hrow hintra hcross i)

theorem pairCell_log_perturbation [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v w : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hw : ∀ i j, Continuous (Function.uncurry (w i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (hwsym : ∀ i j x y, w i j x y = w j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintrav : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcrossv : ∀ i j x y, -J i j ≤ v i j x y)
    (hintraw : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ w i i x y)
    (hcrossw : ∀ i j x y, -J i j ≤ w i j x y)
    (K : I → I → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hd : ∀ i j a b, |w i j a b-v i j a b| ≤ K i j) :
    let μ := Measure.pi (fun i => particleBase (ν i) z)
    |Real.log (boltzmannPartition μ (fun x => β*pairCellEnergy v x)) -
      Real.log (boltzmannPartition μ (fun x => β*pairCellEnergy w x))| ≤
      β/2 * (Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4)) * ∑ i, ∑ j, K i j := by
  dsimp only
  have hvdata := pairCell_second_moment (z := z) ν pos hdiam ht hβ hV hvol v hv hvsym J hJ hJsym hrow hintrav hcrossv
  have hwdata := pairCell_second_moment (z := z) ν pos hdiam ht hβ hV hvol w hw hwsym J hJ hJsym hrow hintraw hcrossw
  let K' i j := β/2*K i j
  have hd' (x : ∀ i, ParticleState (X i)) :
      |β*pairCellEnergy w x-β*pairCellEnergy v x| ≤ ∑ i, ∑ j, K' i j * cellN i x * cellN j x := by
    rw [← mul_sub, abs_mul, abs_of_pos hβ]
    calc
      _ ≤ β*((1/2:ℝ)*∑ i, ∑ j, K i j*cellN i x*cellN j x) :=
        mul_le_mul_of_nonneg_left (pairCellEnergy_abs_difference w v K hK hd x) hβ.le
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [K']
        ring
  have hh := log_partition_perturbation (E := fun x => β*pairCellEnergy v x) (F := fun x => β*pairCellEnergy w x)
    (measurable_const.mul (continuous_pairCellEnergy v hv).measurable)
    (measurable_const.mul (continuous_pairCellEnergy w hw).measurable)
    hvdata.1 hwdata.1 hvdata.2.1 hwdata.2.1 (cellN (X := X)) measurable_cellN
    K' (fun i j => mul_nonneg (by positivity) (hK i j))
    (fun i => (hvdata.2.2 i).1) (fun i => (hwdata.2.2 i).1)
    (fun i => (hvdata.2.2 i).2) (fun i => (hwdata.2.2 i).2) hd'
  have hs : (∑ i, ∑ j, K' i j) = β/2*(∑ i, ∑ j, K i j) := by
    simp only [K', Finset.mul_sum]
  rw [hs] at hh
  simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using hh

end PhysicalControl

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PressureContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma attractionProfile_mono {a b R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hR : ∀ n, 1 ≤ R n)
    (hsa : Summable a) (hsb : Summable b) (hab : ∀ n, a n ≤ b n) (r : ℝ) :
    attractionProfile a R r ≤ attractionProfile b R r :=
  Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (hab n) (scaledBumpProfile_nonneg (by linarith [hR n]) r))
    (summable_attractionProfile ha hR hsa r) (summable_attractionProfile hb hR hsb r)

lemma familyPotential_grid_lower {t : ℝ} {a m R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hm : ∀ n, 0 ≤ m n) (hR : ∀ n, 1 ≤ R n)
    (hsa : Summable a) (hsm : Summable m) (ham : ∀ n, a n ≤ m n) (x y : Position) :
    corePotential t (nndist x y)-familyCellMajorant t m R (cellOf x) (cellOf y) ≤
      familyPotential t a R (nndist x y) := by
  have hh := (mul_le_mul_of_nonneg_left (attractionProfile_mono ha hm hR hsa hsm ham (dist x y)) ht).trans
    (attraction_le_familyCellMajorant ht hm hR hsm x y)
  change coreReal t (dist x y)-_ ≤ coreReal t (dist x y)-t*attractionProfile a R (dist x y)
  linarith

lemma localMomentBound_nonneg {t β : ℝ} (hβ : 0 ≤ β) (z : ℝ) :
    0 ≤ localMomentBound t β z := by unfold localMomentBound; positivity

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
-- module Solutions.OAIQW_RadialTransition.MeasurableFock
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

variable (F : Multiset X → ℝ≥0∞)

lemma measurable_particleObservable (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun x : ParticleState X => F (s+particleMultiset x)) := by
  apply measurable_borel_sigma
  intro n
  exact hF s (Fin n)

lemma measurable_particlePairObservable (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun p : ParticleState X × ParticleState X => F (s+particleMultiset p.1+particleMultiset p.2)) := by
  apply measurable_particle_prod (f := fun x y => F (s+particleMultiset x+particleMultiset y))
  intro m n
  have hh := (hF s (Fin m ⊕ Fin n)).comp
    (show Measurable (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
      apply measurable_pi_iff.mpr
      intro i
      cases i with
      | inl i => exact (measurable_pi_apply i).comp measurable_fst
      | inr i => exact (measurable_pi_apply i).comp measurable_snd)
  change Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
  simpa only [configurationMultiset_sum, add_assoc, particleMultiset] using hh

lemma fockIntegral_eq_lintegral_meas (hF : MeasurableConfiguration F) (μ : Measure X) (z : ℝ) (s : Multiset X) :
    fockIntegral (fun _ι _ x => F (s+configurationMultiset x)) μ z =
      ∫⁻ x, F (s+particleMultiset x) ∂particleBase μ z := by
  rw [lintegral_particleBase μ z (measurable_particleObservable F hF s)]
  rfl

lemma particleBase_add_observable_meas (hF : MeasurableConfiguration F)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (μ+ν) z) =
      ∫⁻ x, ∫⁻ y, F (s+particleMultiset x+particleMultiset y) ∂particleBase ν z ∂particleBase μ z := by
  let G (ι : Type) [Fintype ι] (x : ι → X) := F (s+configurationMultiset x)
  have hG : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X), G ι (x ∘ e) = G κ x := by
    intros
    dsimp [G]
    rw [configurationMultiset_equiv]
  rw [← fockIntegral_eq_lintegral_meas F hF, fockIntegral_add G hG μ ν z]
  have hpair := (measurable_particlePairObservable F hF s)
  rw [lintegral_particleBase μ z hpair.lintegral_prod_right]
  apply tsum_congr
  intro m
  simp only [particleMultiset]
  have hinner (x : Fin m → X) :
      (∫⁻ y : ParticleState X, F (s+configurationMultiset x+configurationMultiset y.2) ∂particleBase ν z) =
      ∑' n : ℕ, fockCoeff z n * ∫⁻ y : Fin n → X, F (s+configurationMultiset x+configurationMultiset y)
        ∂Measure.pi (fun _ => ν) :=
    lintegral_particleBase ν z (measurable_particleObservable F hF (s+configurationMultiset x))
  simp_rw [hinner]
  rw [lintegral_tsum]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    rw [lintegral_const_mul' _ _ (by exact ENNReal.ofReal_ne_top)]
    rw [← mul_assoc]
    congr 1
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => X)
    have hs : ∀ i : Fin m ⊕ Fin n, SigmaFinite (Sum.elim (fun _ => μ) (fun _ => ν) i) := by
      intro i
      cases i
      · change SigmaFinite μ; infer_instance
      · change SigmaFinite ν; infer_instance
    have hp := measurePreserving_sumPiEquivProdPi_symm (Sum.elim (fun _ : Fin m => μ) (fun _ : Fin n => ν))
    rw [← hp.lintegral_comp (hF s (Fin m ⊕ Fin n))]
    change (∫⁻ p : (Fin m → X) × (Fin n → X), F (s+configurationMultiset (Sum.elim p.1 p.2))
      ∂(Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ => ν))) = _
    have hmeas : Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) :=
      (hF s (Fin m ⊕ Fin n)).comp e.symm.measurable
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    dsimp [G]
    rw [configurationMultiset_sum, add_assoc]
  · intro n
    apply Measurable.aemeasurable
    apply Measurable.const_mul
    have hh := (hF s (Fin m ⊕ Fin n)).comp
      (show Measurable (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
        apply measurable_pi_iff.mpr
        intro i
        cases i with
        | inl i => exact (measurable_pi_apply i).comp measurable_fst
        | inr i => exact (measurable_pi_apply i).comp measurable_snd)
    change Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
    simp only [configurationMultiset_sum, ← add_assoc] at hh
    exact hh.lintegral_prod_right

end MeasurableFock
section MeasurableMultiObservable
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_multiParticle_fixed (F : Multiset X → ℝ≥0∞)
    (hF : MeasurableConfiguration F) (s : Multiset X) (n : I → ℕ) :
    Measurable (fun x : ∀ i, Fin (n i) → X => F (s+∑ i, configurationMultiset (x i))) := by
  have hh := (hF s (Σ i, Fin (n i))).comp
    (show Measurable (fun x : ∀ i, Fin (n i) → X => fun p : Σ i, Fin (n i) => x p.1 p.2) from
      measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)))
  simpa only [Function.comp_def, configurationMultiset, Fintype.sum_sigma] using hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_configurationsInverse :
    @Measurable (I → ParticleState X) (Σ n : I → ℕ, ∀ i, Fin (n i) → X)
      _ (borel _) (configurationsEquiv (fun _ : I => X)).symm := by
  let : MeasurableSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := borel _
  let : BorelSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := ⟨rfl⟩
  exact (configurationsHomeomorph (fun _ : I => X)).symm.continuous.measurable

lemma measurable_multiParticleObservable (F : Multiset X → ℝ≥0∞)
    (hF : MeasurableConfiguration F) (s : Multiset X) :
    Measurable (fun x : I → ParticleState X => F (s+multiParticleMultiset x)) := by
  let : MeasurableSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := borel _
  let : BorelSpace (Σ n : I → ℕ, ∀ i, Fin (n i) → X) := ⟨rfl⟩
  have hc : Measurable (fun x : Σ n : I → ℕ, ∀ i, Fin (n i) → X =>
      F (s+∑ i, configurationMultiset (x.2 i))) :=
    measurable_borel_sigma (fun n => measurable_multiParticle_fixed F hF s n)
  change Measurable ((fun x : Σ n : I → ℕ, ∀ i, Fin (n i) → X =>
    F (s+∑ i, configurationMultiset (x.2 i))) ∘ (configurationsEquiv (fun _ : I => X)).symm)
  exact hc.comp (measurable_configurationsInverse (I := I) (X := X))

end MeasurableMultiObservable
section FiniteFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
include hF

lemma particleBase_zero_observable_meas (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (0 : Measure X) z) = F s := by
  rw [lintegral_particleBase _ _ (measurable_particleObservable F hF s)]
  rw [tsum_eq_single 0]
  · simp [particleMultiset, configurationMultiset]
  · intro n hn
    have hμ : Measure.pi (fun _ : Fin n => (0 : Measure X)) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [Measure.pi_univ]
      simp [hn]
    rw [hμ, lintegral_zero_measure, mul_zero]

lemma particleBase_fin_sum_observable_meas (n : ℕ) (μ : Fin n → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, μ i) z) =
      ∫⁻ x, F (s+multiParticleMultiset x) ∂Measure.pi (fun i => particleBase (μ i) z) := by
  induction n generalizing s with
  | zero =>
    simp only [Fin.sum_univ_zero]
    rw [particleBase_zero_observable_meas F hF]
    simp [multiParticleMultiset]
  | succ n ih =>
    rw [Fin.sum_univ_succ, particleBase_add_observable_meas F hF]
    simp_rw [ih]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ParticleState X) 0
    have hp := MeasurePreserving.symm e
      (measurePreserving_piFinSuccAbove (fun i => particleBase (μ i) z) 0)
    have hc := (measurable_multiParticleObservable F hF s (I := Fin (n+1)))
    rw [← hp.lintegral_comp hc]
    change _ = ∫⁻ p : ParticleState X × (Fin n → ParticleState X),
      F (s+multiParticleMultiset (e.symm p))
        ∂(particleBase (μ 0) z).prod (Measure.pi (fun i => particleBase (μ i.succ) z))
    have hpmeas : Measurable (fun p : ParticleState X × (Fin n → ParticleState X) =>
      F (s+multiParticleMultiset (e.symm p))) := hc.comp e.symm.measurable
    rw [lintegral_prod _ hpmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    congr 1
    simp [multiParticleMultiset, Fin.sum_univ_succ, e,
      MeasurableEquiv.piFinSuccAbove_symm_apply, add_assoc]

end FiniteFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.MeasurableProducts
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
section GeneralFock
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

lemma particleBase_sum_observable_meas (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
    (μ : I → Measure X) [∀ i, IsFiniteMeasure (μ i)] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, μ i) z) =
      ∫⁻ x, F (s+multiParticleMultiset x) ∂Measure.pi (fun i => particleBase (μ i) z) := by
  let e := (Fintype.equivFin I).symm
  have hs : (∑ i, μ i) = ∑ j, μ (e j) := (e.sum_comp μ).symm
  rw [hs, particleBase_fin_sum_observable_meas F hF]
  have hp := measurePreserving_piCongrLeft (fun i => particleBase (μ i) z) e
  rw [← hp.lintegral_comp (measurable_multiParticleObservable F hF s)]
  apply lintegral_congr
  intro x
  congr 1
  dsimp [multiParticleMultiset, MeasurableEquiv.piCongrLeft]
  simpa [Equiv.piCongrLeft] using
    congrArg (fun q => s+q) (e.sum_comp (fun i => particleMultiset (x (e.symm i))))

variable (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
  [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]

lemma particleBase_sum_map_observable_meas (F : Multiset X → ℝ≥0∞) (hF : MeasurableConfiguration F)
    (ν : ∀ i, Measure (Y i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, Y i → X) (hpos : ∀ i, Measurable (pos i)) (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (∑ i, Measure.map (pos i) (ν i)) z) =
      ∫⁻ x, F (s+mappedMultiParticleMultiset Y pos x) ∂Measure.pi (fun i => particleBase (ν i) z) := by
  rw [particleBase_sum_observable_meas F hF]
  simp_rw [← particleBase_map _ _ (hpos _)]
  rw [← Measure.pi_map_pi (fun i => (measurable_mapParticle (hpos i)).aemeasurable)]
  exact lintegral_map (measurable_multiParticleObservable F hF s)
    (measurable_pi_iff.mpr (fun i => (measurable_mapParticle (hpos i)).comp (measurable_pi_apply i)))

end GeneralFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.MeasurableEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MeasurableEnergy
variable {X : Type uX} [MeasurableSpace X]
lemma measurable_multisetPairing_right {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) (s : Multiset X)
    {ι : Type} [Fintype ι] : Measurable (fun x : ι → X => multisetPairing v s (configurationMultiset x)) := by
  induction s using Multiset.induction_on with
  | empty => simp only [multisetPairing_zero_left]; exact measurable_const
  | @cons a s ih =>
    simp only [multisetPairing, Multiset.map_cons, Multiset.sum_cons, sum_map_configuration] at *
    exact (Finset.measurable_sum _ (fun i _ => hv.comp (measurable_const.prodMk (measurable_pi_apply i)))).add ih

lemma measurable_multisetEnergy_configuration {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) {ι : Type} [Fintype ι] :
    Measurable (fun x : ι → X => multisetEnergy v (configurationMultiset x)) := by
  simp only [multisetEnergy, multisetPairing_configuration, multisetDiagonal_configuration]
  apply measurable_const.mul
  apply Measurable.sub
  · exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => hv.comp (show Measurable (fun x : ι → X => (x i, x j)) from (measurable_pi_apply i).prodMk (measurable_pi_apply j))))
  · exact Finset.measurable_sum _ (fun i _ => hv.comp (show Measurable (fun x : ι → X => (x i, x i)) from (measurable_pi_apply i).prodMk (measurable_pi_apply i)))

lemma measurableConfiguration_boltzmann {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) (hsym : ∀ x y, v x y = v y x) (β : ℝ) :
    MeasurableConfiguration (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy v s))) := by
  intro s ι _
  simp only [multisetEnergy_add hsym]
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_const.add (measurable_multisetEnergy_configuration hv)).add
      (measurable_multisetPairing_right hv s))))

end MeasurableEnergy
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PairEnsembles
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
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]
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
    · simp only [h, ite_true]; exact measurable_const
    · simp only [h, ite_false]
      exact (measurable_pairBetween _ (hv i j)).comp
        (show Measurable (fun a : ∀ k, ParticleState (X k) => (a i, a j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))

end MeasurablePairCells

section GeneralGrand
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma pairGrand_eq_cell {I : Type} [Fintype I] [DecidableEq I]
    (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, Y i → X) (hpos : ∀ i, Measurable (pos i))
    (v : X → X → ℝ) (hv : Measurable (Function.uncurry v)) (hsym : ∀ x y, v x y = v y x)
    {μ : Measure X} (hdecomp : μ = ∑ i, Measure.map (pos i) (ν i)) (β z : ℝ) :
    pairGrand v μ β z = boltzmannPartition (Measure.pi (fun i => particleBase (ν i) z))
      (fun x => β * pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x) := by
  have hcfg := measurableConfiguration_boltzmann hv hsym β
  have hleft : Measurable (fun x : ParticleState X => Real.exp (-β * multisetEnergy v (particleMultiset x))) := by
    apply measurable_particle_iff.mpr
    intro n
    exact Real.measurable_exp.comp (measurable_const.mul (measurable_multisetEnergy_configuration hv))
  have hright : Measurable (fun x : ∀ i, ParticleState (Y i) =>
      Real.exp (-(β * pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x))) := by
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply measurable_const.mul
    apply measurable_pairCellEnergy
    intro i j
    exact hv.comp (((hpos i).comp measurable_fst).prodMk ((hpos j).comp measurable_snd))
  rw [pairGrand, boltzmannPartition,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hleft.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hright.aestronglyMeasurable]
  congr 1
  have hh := particleBase_sum_map_observable_meas Y
    (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy v s))) hcfg ν pos hpos z 0
  simp only [zero_add, multisetEnergy_mappedMulti] at hh
  simpa only [hdecomp, neg_mul] using hh

end GeneralGrand

lemma pairGrand_radial {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hs : StableWith φ B) (hβ : 0 ≤ β) {A : Set Position}
    (hAfin : volume A ≠ ⊤) (z : ℝ) :
    pairGrand (radialPair φ) (volume.restrict A) β z = grandOn φ A β z := by
  have hm : Measurable (fun x : ParticleState Position => Real.exp (-β * multisetEnergy (radialPair φ) (particleMultiset x))) := by
    simpa only [multisetEnergy_radial] using measurable_particleBoltzmann hφ β
  rw [pairGrand, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hm.aestronglyMeasurable]
  simp only [multisetEnergy_radial]
  rw [lintegral_grandOn hφ hb hs hβ hAfin z,
    ENNReal.toReal_ofReal (zero_le_one.trans (grandOn_bounds hφ hb hs hβ hAfin z).1)]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.DeletedInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

theorem pairGrand_grid_perturbation {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I → Cell) (he : Function.Injective e) {A : Set Position}
    (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i)
    (v w : Position → Position → ℝ)
    (hv : Measurable (Function.uncurry v)) (hw : Measurable (Function.uncurry w))
    (hvcell : ∀ i j, Continuous (fun p : CroppedCell A (e i) × CroppedCell A (e j) => v p.1 p.2))
    (hwcell : ∀ i j, Continuous (fun p : CroppedCell A (e i) × CroppedCell A (e j) => w p.1 p.2))
    (hvsym : ∀ x y, v x y = v y x) (hwsym : ∀ x y, w x y = w y x)
    {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (z : ℝ)
    (J K : Cell → Cell → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J (e i) (e j) ≤ (t^2/8)/8)
    (hintrav : ∀ x y, cellOf x = cellOf y → corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ v x y)
    (hcrossv : ∀ x y, -J (cellOf x) (cellOf y) ≤ v x y)
    (hintraw : ∀ x y, cellOf x = cellOf y → corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ w x y)
    (hcrossw : ∀ x y, -J (cellOf x) (cellOf y) ≤ w x y)
    (hK : ∀ i j, 0 ≤ K i j)
    (hd : ∀ x y, |w x y-v x y| ≤ K (cellOf x) (cellOf y)) :
    |Real.log (pairGrand v (volume.restrict A) β z)-Real.log (pairGrand w (volume.restrict A) β z)| ≤
      β/2 * localMomentBound t β z * ∑ i, ∑ j, K (e i) (e j) := by
  let X i := CroppedCell A (e i)
  let ν i := croppedCellMeasure A (e i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => croppedCellMeasure_finite hA (e i)
  let pos : ∀ i, X i → Position := fun _ => Subtype.val
  have hpos (i : I) : Measurable (pos i) := measurable_subtype_coe
  have hcell (i : I) (x : X i) : cellOf (pos i x) = e i := x.property.2
  have heqv := pairGrand_eq_cell X ν pos hpos v hv hvsym (croppedCell_partition e he hA hcover) β z
  have heqw := pairGrand_eq_cell X ν pos hpos w hw hwsym (croppedCell_partition e he hA hcover) β z
  rw [heqv, heqw]
  apply pairCell_log_perturbation ν pos (fun i => croppedCell_diameter) ht hβ (by norm_num)
    (fun i => croppedCellMeasure_volume hA (e i))
    (fun i j x y => v (pos i x) (pos j y)) (fun i j x y => w (pos i x) (pos j y))
    hvcell hwcell (fun i j x y => hvsym _ _) (fun i j x y => hwsym _ _)
    (fun i j => J (e i) (e j)) (fun i j => hJ _ _) (fun i j => hJsym _ _) hrow
  · intro i x y
    simpa only [hcell] using hintrav (pos i x) (pos i y) ((hcell i x).trans (hcell i y).symm)
  · intro i j x y
    simpa only [hcell] using hcrossv (pos i x) (pos j y)
  · intro i x y
    simpa only [hcell] using hintraw (pos i x) (pos i y) ((hcell i x).trans (hcell i y).symm)
  · intro i j x y
    simpa only [hcell] using hcrossw (pos i x) (pos j y)
  · exact fun i j => hK _ _
  · intro i j x y
    simpa only [hcell] using hd (pos i x) (pos j y)

lemma measurable_deletedPair {G : Type uG} [DecidableEq G] (g : Cell → G)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ) :
    Measurable (Function.uncurry (deletedPair g φ χ)) := by
  have hp : MeasurableSet {p : Position × Position | g (cellOf p.1) = g (cellOf p.2)} := by
    have hh : MeasurableSet {p : Cell × Cell | g p.1 = g p.2} := Set.to_countable _ |>.measurableSet
    exact hh.preimage ((measurable_cellOf.comp measurable_fst).prodMk (measurable_cellOf.comp measurable_snd))
  exact ((continuous_radialPair hφ).measurable.ite hp measurable_const).add
    (continuous_radialPair hχ).measurable

lemma deletedPair_symm {G : Type uG} [DecidableEq G] (g : Cell → G) (φ χ : Potential) (x y : Position) :
    deletedPair g φ χ x y = deletedPair g φ χ y x := by
  simp only [deletedPair, show (g (cellOf y) = g (cellOf x)) = (g (cellOf x) = g (cellOf y)) from propext eq_comm, radialPair_symm φ y x, radialPair_symm χ y x]

lemma continuous_deletedPair_cell {G : Type uG} [DecidableEq G] (g : Cell → G)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ)
    (A : Set Position) (i j : Cell) :
    Continuous (fun p : CroppedCell A i × CroppedCell A j => deletedPair g φ χ p.1 p.2) := by
  have he : (fun p : CroppedCell A i × CroppedCell A j => deletedPair g φ χ p.1 p.2) =
      (fun p => (if g i = g j then radialPair φ p.1 p.2 else 0)+radialPair χ p.1 p.2) := by
    funext p
    have h₁ : cellOf (p.1 : Position) = i := p.1.property.2
    have h₂ : cellOf (p.2 : Position) = j := p.2.property.2
    simp only [deletedPair, h₁, h₂]
  rw [he]
  apply Continuous.add
  · split_ifs
    · exact continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val
    · exact continuous_const
  · exact continuous_radialPair_comp hχ continuous_subtype_val continuous_subtype_val

lemma deletionMajorant_nonneg {G : Type uG} [DecidableEq G] (g : Cell → G)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j) (i j : Cell) :
    0 ≤ deletionMajorant g W i j := ite_nonneg le_rfl (hW i j)

theorem deletedPair_grid_bound {I G : Type} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq G]
    (e : I → Cell) (he : Function.Injective e) (g : Cell → G) {A : Set Position}
    (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ)
    {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (z : ℝ)
    (J₀ J₁ W : Cell → Cell → ℝ)
    (hJ₀ : ∀ i j, 0 ≤ J₀ i j) (hJ₁ : ∀ i j, 0 ≤ J₁ i j)
    (hJsym : ∀ i j, J₀ i j + J₁ i j = J₀ j i + J₁ j i)
    (hrow : ∀ i, ∑ j, (J₀ (e i) (e j)+J₁ (e i) (e j)) ≤ (t^2/8)/8)
    (hlφ : ∀ x y, corePotential t (nndist x y)-J₀ (cellOf x) (cellOf y) ≤ radialPair φ x y)
    (hlχ : ∀ x y, -J₁ (cellOf x) (cellOf y) ≤ radialPair χ x y)
    (hW : ∀ i j, 0 ≤ W i j) (hbφ : ∀ x y, |radialPair φ x y| ≤ W (cellOf x) (cellOf y)) :
    |Real.log (pairGrand (radialPair (φ+χ)) (volume.restrict A) β z)-
      Real.log (pairGrand (deletedPair g φ χ) (volume.restrict A) β z)| ≤
      β/2 * localMomentBound t β z * ∑ i, ∑ j, deletionMajorant g W (e i) (e j) := by
  have hcore (x y : Position) : 0 ≤ corePotential t (nndist x y) := coreReal_nonneg _ _
  have hall (x y : Position) : corePotential t (nndist x y)-(J₀ (cellOf x) (cellOf y)+J₁ (cellOf x) (cellOf y)) ≤
      radialPair (φ+χ) x y := by
    change _ ≤ radialPair φ x y+radialPair χ x y
    linarith [hlφ x y, hlχ x y]
  have hd (x y : Position) : |deletedPair g φ χ x y-radialPair (φ+χ) x y| ≤
      deletionMajorant g W (cellOf x) (cellOf y) := by
    unfold deletedPair deletionMajorant
    change |(if _ then _ else _)+radialPair χ x y-(radialPair φ x y+radialPair χ x y)| ≤ _
    split_ifs with h
    · simp only [sub_self, abs_zero, le_refl]
    · rw [show (0:ℝ)+radialPair χ x y-(radialPair φ x y+radialPair χ x y) = -radialPair φ x y by ring, abs_neg]
      exact hbφ x y
  apply pairGrand_grid_perturbation e he hA hcover (radialPair (φ+χ)) (deletedPair g φ χ)
    (continuous_radialPair (hφ.add hχ)).measurable (measurable_deletedPair g hφ hχ)
    (fun i j => continuous_radialPair_comp (hφ.add hχ) continuous_subtype_val continuous_subtype_val)
    (fun i j => continuous_deletedPair_cell g hφ hχ A (e i) (e j))
    (radialPair_symm _) (deletedPair_symm g φ χ) ht hβ z
    (fun i j => J₀ i j+J₁ i j) (deletionMajorant g W)
    (fun i j => add_nonneg (hJ₀ i j) (hJ₁ i j)) hJsym hrow
  · exact fun x y _ => hall x y
  · intro x y; linarith [hall x y, hcore x y]
  · intro x y heq
    change _ ≤ (if g (cellOf x) = g (cellOf y) then radialPair φ x y else 0)+radialPair χ x y
    rw [ite_eq_left (congrArg g heq)]
    exact hall x y
  · intro x y
    unfold deletedPair
    split_ifs
    · linarith [hlφ x y, hlχ x y, hcore x y]
    · linarith [hlχ x y, hJ₀ (cellOf x) (cellOf y)]
  · exact deletionMajorant_nonneg g hW
  · exact hd

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.BoxEnsembles
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

lemma blockEmbed_injective {m q : ℕ} (hq : 0 < q) :
    Function.Injective (fun p : GridIndex m × GridIndex q => blockEmbed p.1 p.2) := by
  intro p r h
  have hi : p.1 = r.1 := gridEmbed_injective m (by
    have := congrArg (fun k => macroOf q (gridEmbed k)) h
    simpa only [blockEmbed_macro hq] using this)
  apply Prod.ext hi
  funext d
  apply Fin.ext
  have hh := congrArg (fun k : GridIndex (m*q) => (k d : ℕ)) h
  simp only [blockEmbed, hi] at hh
  omega

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
    simpa only [ite_true, boundaryCoord, Finset.mem_filter, Finset.mem_univ, true_and] using h
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

lemma inner_block_macro {m q D : ℕ} (hq : 0 < q) (i : GridIndex m) (j : GridIndex q)
    (hj : j ∉ boundaryGrid q D) {k : Cell}
    (hk : ∀ d, |k d-gridEmbed (blockEmbed i j) d| ≤ (D:ℤ)) :
    macroOf q k = gridEmbed i := by
  have hj' : ∀ d, D ≤ (j d:ℕ) ∧ (j d:ℕ)+D < q := by
    have hh := mt mem_boundaryGrid.mpr hj
    intro d
    have hn : ¬ ((j d:ℕ) < D ∨ q-D ≤ (j d:ℕ)) := fun h => hh ⟨d,h⟩
    omega
  funext d
  apply (Int.ediv_eq_iff_of_pos (by exact_mod_cast hq)).mpr
  have hkd := abs_le.mp (hk d)
  have hlow : (D:ℤ) ≤ (j d:ℤ) := by exact_mod_cast (hj' d).1
  have hupp : (j d:ℤ)+(D:ℤ) < (q:ℤ) := by exact_mod_cast (hj' d).2
  change -(D:ℤ) ≤ k d-((i d:ℕ)*q+(j d:ℕ):ℕ) ∧ k d-((i d:ℕ)*q+(j d:ℕ):ℕ) ≤ (D:ℤ) at hkd
  push_cast at hkd
  change (i d:ℤ)*(q:ℤ) ≤ k d ∧ k d < (i d:ℤ)*(q:ℤ)+(q:ℤ)
  constructor <;> omega

lemma sum_blockGrid {m q : ℕ} (hq : 0 < q) (F : GridIndex (m*q) → ℝ) :
    ∑ k, F k = ∑ i : GridIndex m, ∑ j : GridIndex q, F (blockEmbed i j) := by
  have hh := Fintype.sum_equiv (Equiv.ofBijective _ ⟨blockEmbed_injective (m := m) hq, blockEmbed_surjective hq⟩)
    (fun p => F (blockEmbed p.1 p.2)) F (fun _ => rfl)
  rw [Fintype.sum_prod_type] at hh
  exact hh.symm

lemma grid_sum_boundary_bound {m q D : ℕ} (hq : 0 < q) {C : ℝ} (hC : 0 ≤ C)
    (F : GridIndex (m*q) → ℝ)
    (hF : ∀ k, F k ≤ C)
    (hzero : ∀ i j, j ∉ boundaryGrid q D → F (blockEmbed i j) = 0) :
    ∑ k, F k ≤ (m:ℝ)^3*(6*D*q^2)*C := by
  rw [sum_blockGrid hq]
  have hsum (i : GridIndex m) : ∑ j : GridIndex q, F (blockEmbed i j) ≤ (6*D*q^2:ℕ)*C := by
    calc
      _ = ∑ j ∈ boundaryGrid q D, F (blockEmbed i j) :=
        (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzero i j hj)).symm
      _ ≤ ∑ _j ∈ boundaryGrid q D, C := Finset.sum_le_sum (fun j _ => hF _)
      _ = ((boundaryGrid q D).card:ℝ)*C := by simp
      _ ≤ (6*D*q^2:ℕ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast card_boundaryGrid q D) hC
  calc
    _ ≤ ∑ _i : GridIndex m, (6*D*q^2:ℕ)*C := Finset.sum_le_sum (fun i _ => hsum i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.MacroRegions
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

lemma macroRegion_partition {m q : ℕ} (hq : 0 < q) :
    volume.restrict (halfCube (((m:ℝ)*q)/4)) =
      ∑ i : GridIndex m, Measure.map Subtype.val (regionMeasure (macroRegion q (gridEmbed i))) := by
  have hd : Pairwise (fun i j : GridIndex m => Disjoint (macroRegion q (gridEmbed i)) (macroRegion q (gridEmbed j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (gridEmbed_injective m (hx.symm.trans hy))
  rw [← halfCube_macro_union hq, Measure.restrict_iUnion hd (fun i => measurableSet_macroRegion _ _), Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact (regionMeasure_map (measurableSet_macroRegion _ _)).symm

lemma grandOn_halfCube {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hs : StableWith φ B) (hβ : 0 ≤ β) (L z : ℝ) :
    grandOn φ (halfCube L) β z = grandOn φ (cube L) β z := by
  rw [← pairGrand_radial hφ hb hs hβ (by rw [volume_halfCube]; finiteness),
    ← pairGrand_radial hφ hb hs hβ (by rw [volume_cube]; finiteness), restrict_halfCube]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.RangeBounds
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

lemma cellMargin_mono {R S : ℝ} (h : R ≤ S) : cellMargin R ≤ cellMargin S := by
  unfold cellMargin
  have hc := Int.ceil_mono (show 4*R ≤ 4*S by linarith)
  omega

lemma cellReach_mono {R S : ℝ} {i j : Cell} (h : R ≤ S) (hc : CellReach R i j) : CellReach S i j :=
  fun d => (hc d).trans (cellMargin_mono h)

lemma cellMargin_toNat_le {R : ℝ} (hR : 1 ≤ R) : ((cellMargin R).toNat:ℝ) ≤ 6*R := by
  have hm := cellMargin_nonneg (zero_le_one.trans hR)
  have he : ((cellMargin R).toNat:ℝ) = (cellMargin R:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
  rw [he]
  have hc := Int.ceil_lt_add_one (4*R)
  unfold cellMargin
  push_cast
  linarith

lemma deletionMajorant_le {G : Type uG} [DecidableEq G] (g : Cell → G)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j) (i j : Cell) :
    deletionMajorant g W i j ≤ W i j := by
  unfold deletionMajorant
  split_ifs
  · exact hW i j
  · exact le_rfl

lemma deletionMajorant_grid_sum {m q : ℕ} (hq : 0 < q) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ k, ∑ j : GridIndex (m*q), W k (gridEmbed j) ≤ C)
    (hsupp : ∀ i j, ¬ CellReach R i j → W i j = 0) :
    ∑ i : GridIndex (m*q), ∑ j : GridIndex (m*q),
      deletionMajorant (macroOf q) W (gridEmbed i) (gridEmbed j) ≤
      (m:ℝ)^3*(6*(cellMargin R).toNat*q^2)*C := by
  apply grid_sum_boundary_bound hq hC
  · intro i
    exact (Finset.sum_le_sum (fun j _ => deletionMajorant_le (macroOf q) hW _ _)).trans (hrow _)
  · intro i j hj
    apply Finset.sum_eq_zero
    intro k _
    by_cases hc : CellReach R (gridEmbed (blockEmbed i j)) (gridEmbed k)
    · have hk : macroOf q (gridEmbed k) = gridEmbed i := inner_block_macro hq i j hj (by
        intro d
        simpa only [Int.toNat_of_nonneg (cellMargin_nonneg hR)] using hc d)
      simp only [deletionMajorant, blockEmbed_macro hq, hk, ite_true]
    · simp only [deletionMajorant, hsupp _ _ hc, ite_self]

lemma deletionMajorant_grid_sum_range {m q : ℕ} (hq : 0 < q) {R C : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ k, ∑ j : GridIndex (m*q), W k (gridEmbed j) ≤ C)
    (hsupp : ∀ i j, ¬ CellReach R i j → W i j = 0) :
    ∑ i : GridIndex (m*q), ∑ j : GridIndex (m*q),
      deletionMajorant (macroOf q) W (gridEmbed i) (gridEmbed j) ≤
      36*(m:ℝ)^3*q^2*R*C := by
  calc
    _ ≤ (m:ℝ)^3*(6*(cellMargin R).toNat*q^2)*C :=
      deletionMajorant_grid_sum hq (zero_le_one.trans hR) hC hW hrow hsupp
    _ ≤ (m:ℝ)^3*(6*(6*R)*q^2)*C := by gcongr; exact cellMargin_toNat_le hR
    _ = _ := by ring

lemma referenceMajorant_nonneg {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (i j : Cell) :
    0 ≤ referenceMajorant t a R i j :=
  add_nonneg (cellMajorant_nonneg (by norm_num) (by positivity) i j)
    (familyCellMajorant_nonneg ht ha hR i j)

lemma referenceMajorant_row {I : Type uI} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t) (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable a) (i : Cell) :
    ∑ j, referenceMajorant t a R i (e j) ≤ 2197*8*t^2+2197*t*bumpIntegral⁻¹*∑' n, a n := by
  simp only [referenceMajorant, Finset.sum_add_distrib]
  have hc := cellMajorant_row e he (R := 2) (W := 8*t^2) (by norm_num) (by positivity) i
  have ha' := familyCellMajorant_row e he ht ha hR hs i
  linarith

lemma referenceMajorant_support {t R₀ : ℝ} {a R : ℕ → ℝ} (hR₀ : 2 ≤ R₀)
    (hrange : ∀ n, R n ≤ R₀) (i j : Cell) (hc : ¬ CellReach R₀ i j) :
    referenceMajorant t a R i j = 0 := by
  have hc₂ : ¬ CellReach 2 i j := fun h => hc (cellReach_mono hR₀ h)
  have hcn (n : ℕ) : ¬ CellReach (R n) i j := fun h => hc (cellReach_mono (hrange n) h)
  simp only [referenceMajorant, familyCellMajorant, cellMajorant, ite_eq_right hc₂, ite_eq_right (hcn _),
    mul_zero, tsum_zero, add_zero]

lemma core_le_cellMajorant {t : ℝ} (ht : 1 ≤ t) (x y : Position) :
    corePotential t (nndist x y) ≤ cellMajorant 2 (8*t^2) (cellOf x) (cellOf y) := by
  by_cases hc : CellReach 2 (cellOf x) (cellOf y)
  · simp only [cellMajorant, ite_eq_left hc]
    have he : ((2:ℝ)^3)⁻¹*(8*t^2) = t^2 := by ring
    rw [he]
    exact coreReal_le t (dist x y)
  · have hd : 2 < dist x y := lt_of_not_ge (fun h => hc (cellReach_of_dist h))
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hz : corePotential t (nndist x y) = 0 := coreReal_zero_outer ht0
      (by change 1+1/t ≤ dist x y; have hi := one_div_le_one_div_of_le zero_lt_one ht; norm_num only [div_one] at hi; linarith)
    rw [hz, cellMajorant, ite_eq_right hc]

lemma family_abs_le_referenceMajorant {t : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (x y : Position) :
    |radialPair (familyPotential t a R) x y| ≤ referenceMajorant t a R (cellOf x) (cellOf y) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hc : |coreReal t (dist x y)| = coreReal t (dist x y) := abs_of_nonneg (coreReal_nonneg _ _)
  have ha' : |t*attractionProfile a R (dist x y)| = t*attractionProfile a R (dist x y) :=
    abs_of_nonneg (mul_nonneg ht0 (attractionProfile_nonneg ha hR _))
  calc
    _ ≤ |coreReal t (dist x y)|+|t*attractionProfile a R (dist x y)| := abs_sub _ _
    _ = coreReal t (dist x y)+t*attractionProfile a R (dist x y) := by rw [hc, ha']
    _ ≤ _ := add_le_add (core_le_cellMajorant ht x y) (attraction_le_familyCellMajorant ht0 ha hR hs x y)

lemma referenceRowBound_nonneg {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) :
    0 ≤ referenceRowBound t A := by
  unfold referenceRowBound
  have hb := bumpIntegral_pos.le
  positivity

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.MacroUpper
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

lemma pairCellEnergy_smul (a : ℝ) (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j x y => a*v i j x y) x = a*pairCellEnergy v x := by
  unfold pairCellEnergy cellHamiltonian pairWithin pairBetween
  have hh (i : I) (k l : Fin (x i).1) :
    (if k = l then (0:ℝ) else a*v i i ((x i).2 k) ((x i).2 l)) =
      a*(if k = l then 0 else v i i ((x i).2 k) ((x i).2 l)) := by split_ifs <;> simp
  simp_rw [hh, ← Finset.mul_sum]
  have hj (i j:I) : (if i = j then (0:ℝ) else a*∑ k, ∑ l, v i j ((x i).2 k) ((x j).2 l)) =
      a*(if i = j then 0 else ∑ k, ∑ l, v i j ((x i).2 k) ((x j).2 l)) := by split_ifs <;> simp
  simp_rw [hj, ← Finset.mul_sum]
  ring

end

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.LinearInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma zero_ite_add (p : Prop) [Decidable p] (a b : ℝ) :
    (if p then 0 else a+b) = (if p then 0 else a)+(if p then 0 else b) := by split_ifs <;> ring

section LinearPair
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

lemma pairWithin_add {Y : Type uY} (v w : Y → Y → ℝ) (s : ParticleState Y) :
    pairWithin (fun x y => v x y+w x y) s = pairWithin v s+pairWithin w s := by
  dsimp only [pairWithin]
  simp only [zero_ite_add, Finset.sum_add_distrib, mul_add]

lemma pairBetween_add {Y : Type uY} {Z : Type uZ} (v w : Y → Z → ℝ) (s : ParticleState Y) (t : ParticleState Z) :
    pairBetween (fun x y => v x y+w x y) s t = pairBetween v s t+pairBetween w s t := by
  simp only [pairBetween, Finset.sum_add_distrib]

lemma pairCellEnergy_add (v w : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => v i j a b+w i j a b) x = pairCellEnergy v x+pairCellEnergy w x := by
  dsimp only [pairCellEnergy, cellHamiltonian]
  simp only [pairWithin_add, pairBetween_add, zero_ite_add, Finset.sum_add_distrib, mul_add]
  ring

lemma pairCellEnergy_diagonal (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) :
    pairCellEnergy (fun i j a b => if i = j then v i j a b else 0) x = ∑ i, pairWithin (v i i) (x i) := by
  unfold pairCellEnergy cellHamiltonian
  simp only [ite_true]
  have hcross (i j : I) : (if i = j then 0 else pairBetween (fun a b => if i = j then v i j a b else 0) (x i) (x j)) = 0 := by
    split_ifs <;> simp only [pairBetween, Finset.sum_const_zero]
  simp only [hcross, Finset.sum_const_zero, mul_zero, add_zero]

end LinearPair

lemma continuous_singleAttraction (R lam : ℝ) : Continuous (singleAttraction R lam) :=
  continuous_const.mul ((continuous_scaledBumpProfile R).comp NNReal.continuous_coe)

lemma radialPair_singleAttraction {R : ℝ} (hR : 0 < R) (lam : ℝ) (x y : Position) :
    radialPair (singleAttraction R lam) x y = -lam*scaledBump R (x-y) := by
  rw [scaledBump_radial hR]
  rfl

lemma deletedPair_macro_energy {φ : Potential} {m q : ℕ} {R : ℝ} (hR : 0 < R) (lam : ℝ) (x : MacroState m q) :
    pairCellEnergy (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      deletedPair (macroOf q) φ (singleAttraction R lam) a b) x = macroKacEnergy φ m q R lam x := by
  classical
  have he : (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      deletedPair (macroOf q) φ (singleAttraction R lam) a b) =
    (fun i j : GridIndex m => fun (a : macroRegion q (gridEmbed i)) (b : macroRegion q (gridEmbed j)) =>
      (if i = j then radialPair φ a b else 0)+(-lam*scaledBump R ((a:Position)-(b:Position)))) := by
    funext i j a b
    have ha : macroOf q (cellOf (a:Position)) = gridEmbed i := a.property
    have hb : macroOf q (cellOf (b:Position)) = gridEmbed j := b.property
    simp only [deletedPair, ha, hb, radialPair_singleAttraction hR, (gridEmbed_injective m).eq_iff]
  rw [he, pairCellEnergy_add, pairCellEnergy_diagonal, pairCellEnergy_smul]
  simp only [macroKacEnergy, neg_mul, sub_eq_add_neg]

lemma deletedPair_macroKac {m q : ℕ} (hq : 0 < q)
    {φ : Potential} (hφ : Continuous φ) {R : ℝ} (hR : 0 < R) (lam β z : ℝ) :
    pairGrand (deletedPair (macroOf q) φ (singleAttraction R lam)) (volume.restrict (halfCube (((m:ℝ)*q)/4))) β z =
    boltzmannPartition (macroMeasure m q z) (fun x => β*macroKacEnergy φ m q R lam x) := by
  let X (i : GridIndex m) := macroRegion q (gridEmbed i)
  let ν (i : GridIndex m) := regionMeasure (X i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => regionMeasure_finite (measurableSet_macroRegion _ _)
    (by rw [volume_macroRegion hq]; finiteness)
  have hh := pairGrand_eq_cell (fun i : GridIndex m => ↥(X i)) ν (fun _ => Subtype.val)
    (fun _ => measurable_subtype_coe) (deletedPair (macroOf q) φ (singleAttraction R lam))
    (measurable_deletedPair _ hφ (continuous_singleAttraction R lam)) (deletedPair_symm _ _ _)
    (macroRegion_partition (m := m) hq) β z
  exact hh.trans (congrArg (boltzmannPartition (macroMeasure m q z)) (by
    funext x
    exact congrArg (β*·) (deletedPair_macro_energy hR lam x)))

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.FamilyStep
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

lemma attractionProfile_prepend {a R : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) (r : ℝ) :
    attractionProfile (prepend a b) (prepend R S) r = a*scaledBumpProfile R r+attractionProfile b S r := by
  unfold attractionProfile
  have he : (fun n => prepend a b n*scaledBumpProfile (prepend R S n) r) =
      prepend (a*scaledBumpProfile R r) (fun n => b n*scaledBumpProfile (S n) r) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_attractionProfile hb hS hs r)]

lemma familyPotential_prepend {a R t : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) :
    familyPotential t (prepend a b) (prepend R S) = familyPotential t b S+singleAttraction R (t*a) := by
  funext r
  simp only [familyPotential, Pi.add_apply, attractionProfile_prepend hb hS hs, singleAttraction]
  ring

lemma familyCellMajorant_prepend {a R t : ℝ} {b S : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b) (i j : Cell) :
    familyCellMajorant t (prepend a b) (prepend R S) i j =
      familyCellMajorant t b S i j+t*a*cellMajorant R bumpIntegral⁻¹ i j := by
  unfold familyCellMajorant
  have he : (fun n => prepend a b n * cellMajorant (prepend R S n) bumpIntegral⁻¹ i j) =
      prepend (a*cellMajorant R bumpIntegral⁻¹ i j) (fun n => b n*cellMajorant (S n) bumpIntegral⁻¹ i j) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_cellMajorant hb hS hs i j)]
  ring

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.KacDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_kac_deletion_oai {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ a R : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t ((m:ℝ)*q/4) β h-
      deletedKacPressure (familyPotential t b S) m q R t a β h| ≤
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  let : NeZero (m*q) := ⟨ne_of_gt (Nat.mul_pos hm hq)⟩
  have hba := prepend_nonneg ha hb
  have hRS := prepend_range hR hS
  have hsum := summable_prepend a hs
  have hrow' : 2197*t*bumpIntegral⁻¹*(∑' n, prepend a b n) ≤ (t^2/8)/8 := by rw [tsum_prepend _ hs]; exact hrow
  have hcont := continuous_familyPotential hba hRS hsum t
  have hbound := bounded_familyPotential hba hRS hsum t
  have hstable := stable_family_of_master ht0.le hba hRS hsum hsum (fun _ => le_rfl) hrow'
  let W := referenceMajorant t b S
  let K := fun i j => t*a*cellMajorant R bumpIntegral⁻¹ i j
  have hK : ∀ i j, 0 ≤ K i j := fun i j => mul_nonneg (mul_nonneg ht0.le ha) (cellMajorant_nonneg (zero_le_one.trans hR) (inv_nonneg.mpr bumpIntegral_pos.le) _ _)
  have hW : ∀ i j, 0 ≤ W i j := referenceMajorant_nonneg ht0.le hb hS
  have htotal (i j : Cell) : familyCellMajorant t b S i j+K i j = familyCellMajorant t (prepend a b) (prepend R S) i j :=
    (familyCellMajorant_prepend hb hS hs i j).symm
  have hcost := deletedPair_grid_bound (@gridEmbed (m*q)) (gridEmbed_injective _) (macroOf q)
    (measurableSet_halfCube ((m*q:ℕ)/4)) (halfCube_grid_cover (m*q))
    (continuous_familyPotential hb hS hs t) (continuous_singleAttraction R (t*a)) ht0 hβ (t*h)
    (familyCellMajorant t b S) K W (familyCellMajorant_nonneg ht0.le hb hS) hK
    (fun i j => by rw [htotal, htotal]; exact familyCellMajorant_symm _ _ _ _ _)
    (fun i => by simp_rw [htotal]; exact (familyCellMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le hba hRS hsum (gridEmbed i)).trans hrow')
    (familyPotential_grid_lower ht0.le hb hb hS hs hs (fun _ => le_rfl))
    (fun x y => by
      dsimp only [K, radialPair, singleAttraction]
      have hh := mul_le_mul_of_nonneg_left (scaledBumpProfile_le_cellMajorant hR x y) (mul_nonneg ht0.le ha)
      change -(t*a)*scaledBumpProfile R (dist x y) ≥ -(t*a*cellMajorant R bumpIntegral⁻¹ (cellOf x) (cellOf y))
      nlinarith)
    hW (family_abs_le_referenceMajorant ht hb hS hs)
  have hA : volume (halfCube (((m:ℝ)*q)/4)) ≠ ⊤ := by rw [volume_halfCube]; finiteness
  have hgrand := pairGrand_radial hcont hbound hstable hβ.le hA (t*h)
  rw [← familyPotential_prepend hb hS hs] at hcost
  simp only [Nat.cast_mul] at hcost
  rw [hgrand, grandOn_halfCube hcont hbound hstable hβ.le, grandOn_cube,
    deletedPair_macroKac hq (continuous_familyPotential hb hS hs t) (zero_lt_one.trans_le hR)] at hcost
  have hC : 0 ≤ referenceRowBound t (∑' n, b n) := referenceRowBound_nonneg ht0.le (tsum_nonneg hb)
  have hsumBound := deletionMajorant_grid_sum_range (m := m) hq (show 1 ≤ R₀ by linarith) hC hW
    (referenceMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le hb hS hs)
    (referenceMajorant_support hR₀ hrange)
  have hcoeff : 0 ≤ β/2*localMomentBound t β (t*h) :=
    mul_nonneg (by positivity) (localMomentBound_nonneg hβ.le _)
  have hlog := hcost.trans (mul_le_mul_of_nonneg_left hsumBound hcoeff)
  have hden : 0 < t*((m:ℝ)*q/4)^3 := by positivity
  unfold finiteGrandPressure deletedKacPressure
  rw [← sub_div, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  convert hlog using 1 <;> first | rfl | (unfold boxPressureConstant; field_simp; ring)

end RadialTransition
end

end OAI
end

theorem solution : type_of% @OAI.RadialTransition.family_kac_deletion_oai := @OAI.RadialTransition.family_kac_deletion_oai
