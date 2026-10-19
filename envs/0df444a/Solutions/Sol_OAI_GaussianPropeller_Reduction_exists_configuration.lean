-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.exists_configuration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:22:33.371672+00:00
-- url     : https://prove2.me/submissions/b44c7e9b-f3dc-47e6-a6d3-c813e7b193e5

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000
import Theorems.Thm_HairerSPDE_map_add_eq_withDensity
import Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_quantile_prob_concave
import Theorems.Thm_OAI_GaussianPropeller_Mills_gaussian_tail_le_sampford
import Theorems.Thm_OAI_GaussianPropeller_Mills_inverse_mills_ratio_deriv_le_one

section
-- module Solutions.OAIQW_GaussianPropeller.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_GaussianPropeller.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

theorem integrable_id_restrict (d : ℕ) (A : Set (Space d)) :
    Integrable (fun x : Space d => x) ((gaussian d).restrict A) :=
  (integrable_id_gaussian d).restrict

theorem value_nonneg {d k : ℕ} (A : Fin k → Set (Space d)) : 0 ≤ value A := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖centroid (A i)‖)

theorem sum_indicator_eq {d k : ℕ} {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {F : Type uF} [AddCommMonoid F] (f : Space d → F) :
    (fun x => ∑ i, (A i).indicator f x) =ᵐ[gaussian d] f := by
  classical
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi f
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) f
  · simp

theorem sum_centroid_eq_zero {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  have hi (i : Fin k) : Integrable ((A i).indicator (fun x => x)) (gaussian d) :=
    (integrable_id_gaussian d).indicator (hA.1 i)
  calc
    ∑ i, centroid (A i) = ∑ i, ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_indicator (hA.1 i)).symm
    _ = ∫ x, ∑ i, (A i).indicator (fun x => x) x ∂gaussian d :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = ∫ x, x ∂gaussian d := integral_congr_ae (sum_indicator_eq hA (fun x => x))
    _ = 0 := integral_id_stdGaussian

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

omit [NeZero k] in
theorem measurable_scoreCell (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  change MeasurableSet ({x | ∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫} ∩
    {x | ∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases h : j < i
    · simpa [h] using
        (measurableSet_lt (show Measurable (fun x : Space d => ⟪v j, x⟫) by fun_prop)
          (show Measurable (fun x : Space d => ⟪v i, x⟫) by fun_prop))
    · simp [h]

theorem exists_unique_scoreCell (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  let s := Finset.univ.filter (fun i => ⟪v i, x⟫ = scoreMax v x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := exists_scoreMax v x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := s.min' hs
  have hmax : ⟪v i, x⟫ = scoreMax v x := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hi : x ∈ scoreCell v i := by
    constructor
    · intro j
      rw [hmax]
      exact le_scoreMax v j x
    · intro j hji
      have hle : ⟪v j, x⟫ ≤ ⟪v i, x⟫ := hmax ▸ le_scoreMax v j x
      apply lt_of_le_of_ne hle
      intro heq
      have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.trans hmax⟩
      exact (not_lt_of_ge (s.min'_le j hmem)) hji
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    have hlt : i < j := lt_of_not_ge h
    exact (not_lt_of_ge (hi.1 j)) (hj.2 i hlt)
  · by_contra h
    have hlt : j < i := lt_of_not_ge h
    exact (not_lt_of_ge (hj.1 i)) (hi.2 j hlt)

theorem scoreCell_partition (v : Fin k → Space d) : IsPartition (scoreCell v) :=
  ⟨measurable_scoreCell v, Filter.Eventually.of_forall (exists_unique_scoreCell v)⟩

theorem scoreCell_score (v : Fin k → Space d) {i : Fin k} {x : Space d}
    (hx : x ∈ scoreCell v i) : ⟪v i, x⟫ = scoreMax v x := by
  exact le_antisymm (le_scoreMax v i x) ((scoreMax_le_iff _ _ _).mpr hx.1)

omit [NeZero k] in
theorem norm_moments_sq (A : Fin k → Set (Space d)) : ‖moments A‖ ^ 2 = value A :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [NeZero k] in
theorem pairing_integral {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) :
    ⟪v, moments A⟫ = ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
      ∂gaussian d := by
  rw [PiLp.inner_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hA.1 i), integral_inner (integrable_id_restrict d (A i))]
    rfl
  · intro i _
    exact ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i)

theorem pairing_le_width {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  rw [pairing_integral hA]
  have hi : Integrable (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x)
      (gaussian d) := integrable_finsetSum _ (fun i _ =>
        ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i))
  apply integral_mono_ae hi (integrable_scoreMax v)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem pairing_scoreCell (v : Tuple d k) :
    ⟪v, moments (scoreCell v.ofLp)⟫ = width v := by
  classical
  rw [pairing_integral (scoreCell_partition v.ofLp)]
  apply integral_congr_ae
  filter_upwards [] with x
  obtain ⟨i, hi, huniq⟩ := exists_unique_scoreCell v.ofLp x
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using scoreCell_score v.ofLp hi
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

omit [NeZero k] in
theorem merge_partition {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : IsPartition (merge A i j) := by
  classical
  constructor
  · intro l
    by_cases hli : l = i
    · simpa [merge, hli] using (hA.1 i).union (hA.1 j)
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm]
      · simpa [merge, hli, hlj] using hA.1 l
  · filter_upwards [hA.2] with x hx
    obtain ⟨l, hl, huniq⟩ := hx
    by_cases hlj : l = j
    · subst l
      refine ⟨i, ?_, ?_⟩
      · simp [merge, hl]
      · intro q hq
        by_cases hqi : q = i
        · exact hqi
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · have hqA : x ∈ A q := by simpa [merge, hqi, hqj] using hq
            exact False.elim (hqj (huniq q hqA))
    · refine ⟨l, ?_, ?_⟩
      · by_cases hli : l = i
        · subst l
          simp [merge, hl]
        · simp [merge, hli, hlj, hl]
      · intro q hq
        by_cases hqi : q = i
        · subst q
          have h : x ∈ A i ∨ x ∈ A j := by simpa [merge] using hq
          rcases h with hi | hj
          · exact huniq i hi
          · exact False.elim (hlj (huniq j hj).symm)
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · apply huniq q
            simpa [merge, hqi, hqj] using hq

omit [NeZero k] in
theorem centroid_union {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := by
  have hind : (A i ∪ A j).indicator (fun x => x) =ᵐ[gaussian d]
      (fun x => (A i).indicator (fun x => x) x + (A j).indicator (fun x => x) x) := by
    filter_upwards [hA.2] with x hx
    obtain ⟨l, _, huniq⟩ := hx
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j
    · exact False.elim (hij ((huniq i hi).trans (huniq j hj).symm))
    all_goals simp [Set.indicator, hi, hj]
  unfold centroid
  rw [← integral_indicator ((hA.1 i).union (hA.1 j)), integral_congr_ae hind,
    integral_add ((integrable_id_gaussian d).indicator (hA.1 i))
      ((integrable_id_gaussian d).indicator (hA.1 j)),
    integral_indicator (hA.1 i), integral_indicator (hA.1 j)]

omit [NeZero k] in
theorem value_merge {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) :
    value (merge A i j) = value A + 2 * ⟪centroid (A i), centroid (A j)⟫ := by
  classical
  have hcent : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := centroid_union hA hij
  have hfun (l : Fin k) : ‖centroid (merge A i j l)‖ ^ 2 =
      ‖centroid (A l)‖ ^ 2 +
      (if l = i then ‖centroid (A i) + centroid (A j)‖ ^ 2 - ‖centroid (A i)‖ ^ 2 else 0) +
      (if l = j then -‖centroid (A j)‖ ^ 2 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [merge, hij, hcent]
    · by_cases hlj : l = j
      · subst l
        simp [merge, hij.symm]
      · simp [merge, hli, hlj]
  unfold value
  simp_rw [hfun, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [norm_add_sq_real]
  ring

omit [NeZero k] in
theorem activeCount_merge_lt {A : Fin k → Set (Space d)} {i j : Fin k}
    (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    activeCount (merge A i j) < activeCount A := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    simp only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    by_cases hli : l = i
    · simpa only [hli] using hi
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm] at hl
      · simpa only [merge, ite_eq_right hli, ite_eq_right hlj] using hl
  · intro heq
    have hs : j ∈ activeLabels (merge A i j) := by
      rw [heq]
      simpa only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hnon : gaussian d (merge A i j j) ≠ 0 := (Finset.mem_filter.mp hs).2
    exact hnon (by simp [merge, hij.symm])

omit [NeZero k] in
theorem negative_inner_of_minimal {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    {i j : Fin k} (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    ⟪centroid (A i), centroid (A j)⟫ < 0 := by
  have hpart := merge_partition hA.1.1 hij
  have hvalue := value_merge hA.1.1 hij
  have hbound := hA.1.2 _ hpart
  have hle : ⟪centroid (A i), centroid (A j)⟫ ≤ 0 := by linarith
  apply lt_of_le_of_ne hle
  intro heq
  have heqval : value (merge A i j) = value A := by rw [heq, mul_zero, add_zero] at hvalue; exact hvalue
  have hopt : Optimal (merge A i j) := ⟨hpart, fun B hB => by rw [heqval]; exact hA.1.2 B hB⟩
  exact (not_lt_of_ge (hA.2 _ hopt)) (activeCount_merge_lt hij hi hj)

theorem width_moments_of_optimal {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by
  have hnorm : ‖moments (scoreCell (moments A).ofLp)‖ ≤ ‖moments A‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_moments_sq, norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  apply le_antisymm
  · rw [← pairing_scoreCell, ← norm_moments_sq]
    calc
      ⟪moments A, moments (scoreCell (moments A).ofLp)⟫ ≤
          ‖moments A‖ * ‖moments (scoreCell (moments A).ofLp)‖ := real_inner_le_norm _ _
      _ ≤ ‖moments A‖ * ‖moments A‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖moments A‖ ^ 2 := (sq _).symm
  · simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using pairing_le_width hA.1 (moments A)

omit [NeZero k] in
theorem centroid_eq_zero_of_null {A : Set (Space d)} (hA : gaussian d A = 0) : centroid A = 0 := by
  unfold centroid
  rw [Measure.restrict_eq_zero.mpr hA, integral_zero_measure]

theorem assigned_le_scoreMax {A : Fin k → Set (Space d)} (hA : IsPartition A) (v : Tuple d k) :
    (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x) ≤ᵐ[gaussian d]
      scoreMax v.ofLp := by
  classical
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem optimal_winning_ae {A : Fin k → Set (Space d)} (hA : Optimal A) :
    ∀ᵐ x ∂gaussian d, ∀ i, x ∈ A i → ⟪centroid (A i), x⟫ =
      scoreMax (fun j => centroid (A j)) x := by
  classical
  let v := moments A
  let f (x : Space d) := ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
  have hf : Integrable f (gaussian d) :=
    integrable_finsetSum _ (fun i _ =>
      ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1.1 i))
  have hgap : (fun x => scoreMax v.ofLp x - f x) =ᵐ[gaussian d] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (show 0 ≤ᵐ[gaussian d] (fun x => scoreMax v.ofLp x - f x) from
        (assigned_le_scoreMax hA.1 v).mono (fun x hx => sub_nonneg.mpr hx))
      ((integrable_scoreMax v).sub hf)).mp
    rw [integral_sub (integrable_scoreMax v) hf]
    have hi : (∫ x, f x ∂gaussian d) = value A := by
      rw [← pairing_integral hA.1, real_inner_self_eq_norm_sq, norm_moments_sq]
    rw [hi]
    exact sub_eq_zero.mpr (width_moments_of_optimal hA)
  filter_upwards [hgap, hA.1.2] with x hx hxA
  intro i hi
  obtain ⟨j, _, huniq⟩ := hxA
  have hiuniq : ∀ l, x ∈ A l → l = i := fun l hl => (huniq l hl).trans (huniq i hi).symm
  have hfx : f x = ⟪v.ofLp i, x⟫ := by
    dsimp only [f]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro l _ hli
      exact Set.indicator_of_notMem (fun hl => hli (hiuniq l hl)) _
    · simp
  change scoreMax v.ofLp x - f x = 0 at hx
  rw [hfx] at hx
  exact (sub_eq_zero.mp hx).symm

omit [NeZero k] in

theorem two_nonzero_centroids {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (hpos : 0 < value A) : ∃ i j, i ≠ j ∧ centroid (A i) ≠ 0 ∧ centroid (A j) ≠ 0 := by
  classical
  have hi : ∃ i, centroid (A i) ≠ 0 := by
    by_contra! h
    have hz : value A = 0 := by simp [value, h]
    linarith
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, j ≠ i ∧ centroid (A j) ≠ 0 := by
    by_contra! h
    have hz : ∑ j, centroid (A j) = centroid (A i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact h j hji
      · simp
    exact hi (hz.symm.trans (sum_centroid_eq_zero hA))
  obtain ⟨j, hji, hj⟩ := hj
  exact ⟨i, j, hji.symm, hi, hj⟩

omit [NeZero k] in
theorem active_centroid_ne_zero {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) : centroid (A i) ≠ 0 := by
  obtain ⟨j, l, hjl, hj, hl⟩ := two_nonzero_centroids hA.1.1 hpos
  have hjm : gaussian d (A j) ≠ 0 := fun hz => hj (centroid_eq_zero_of_null hz)
  have hlm : gaussian d (A l) ≠ 0 := fun hz => hl (centroid_eq_zero_of_null hz)
  by_cases hij : i = j
  · simpa only [hij] using hj
  · have hneg := negative_inner_of_minimal hA hij hi hjm
    intro hz
    simp only [hz, inner_zero_left] at hneg
    exact (lt_irrefl 0) hneg

omit [NeZero k] in
theorem active_centroid_ne_other {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i j : Fin k} (hi : gaussian d (A i) ≠ 0) (hij : i ≠ j) :
    centroid (A i) ≠ centroid (A j) := by
  by_cases hj : gaussian d (A j) = 0
  · rw [centroid_eq_zero_of_null hj]
    exact active_centroid_ne_zero hA hpos hi
  · intro heq
    have hneg := negative_inner_of_minimal hA hij hi hj
    rw [heq, real_inner_self_eq_norm_sq] at hneg
    exact (not_lt_of_ge (sq_nonneg _)) hneg

omit [NeZero k] in

theorem gaussian_hyperplane_null (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z, z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L (stdGaussian (Space d))).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass
      (gaussianReal (∫ x, L x ∂stdGaussian (Space d))
        (variance L (stdGaussian (Space d))).toNNReal) := nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (Space d)) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    measure_singleton] at h
  exact h

omit [NeZero k] in
theorem measurableSet_closedCell (z : Fin k → Space d) (i : Fin k) :
    MeasurableSet (closedCell z i) := by
  unfold closedCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    (by fun_prop) (by fun_prop))

theorem active_eq_closedCell_ae {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) :
    A i =ᵐ[gaussian d] closedCell (fun j => centroid (A j)) i := by
  classical
  have hnotie : ∀ j, i ≠ j → ∀ᵐ x ∂gaussian d,
      ⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫ := by
    intro j hij
    rw [ae_iff]
    change gaussian d {x | ¬⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫} = 0
    simpa only [not_not, inner_sub_left, sub_eq_zero] using
      gaussian_hyperplane_null (centroid (A i) - centroid (A j))
        (sub_ne_zero.mpr (active_centroid_ne_other hA hpos hi hij)) 0
  have hnt : ∀ᵐ x ∂gaussian d, ∀ j, i ≠ j →
      ⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫ := by
    exact ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun hij => hnotie j hij))
  filter_upwards [hA.1.1.2, optimal_winning_ae hA.1, hnt] with x hx hwin hnt
  apply propext
  constructor
  · intro hix j
    rw [hwin i hix]
    exact le_scoreMax (fun j => centroid (A j)) j x
  · intro hclosed
    obtain ⟨j, hj, _⟩ := hx
    by_cases hji : j = i
    · subst j
      exact hj
    · have hle := hclosed j
      rw [hwin j hj] at hle
      have heq := le_antisymm (le_scoreMax (fun l => centroid (A l)) i x) hle
      exact False.elim (hnt j (Ne.symm hji) (heq.trans (hwin j hj).symm))

end Reduction

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

theorem optimal_width_le {A : Fin k → Set (Space d)} (hA : Optimal A)
    (v : Tuple d k) : width v ≤ Real.sqrt (value A) * ‖v‖ := by
  have hn : ‖moments (scoreCell v.ofLp)‖ ≤ Real.sqrt (value A) := by
    apply (Real.le_sqrt (norm_nonneg _) (value_nonneg A)).mpr
    rw [norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  rw [← pairing_scoreCell]
  calc
    ⟪v, moments (scoreCell v.ofLp)⟫ ≤ ‖v‖ * ‖moments (scoreCell v.ofLp)‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * Real.sqrt (value A) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_comm _ _

omit [NeZero k] in
lemma sum_erase_zero (z : Fin k → Space d) (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, z j = -z i := by
  classical
  have hh := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  rw [hz] at hh
  exact eq_neg_of_add_eq_zero_left hh

omit [NeZero k] in
lemma sum_erased_centered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, (z j + ((k:ℝ)-1)⁻¹ • z i) = 0 := by
  classical
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  rw [Finset.sum_add_distrib, sum_erase_zero z hz i,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
    mul_inv_cancel₀ hk', one_smul, neg_add_cancel]

omit [NeZero k] in
lemma recentered_norm_sq (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by
  classical
  let b : ℝ := ((k:ℝ)-1)⁻¹
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  have he : ‖recentered z i‖^2 =
      ∑ j ∈ Finset.univ.erase i, ‖z j + b • z i‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ j, ‖if j = i then 0 else z j + b • z i‖^2) = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp_rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hn := Finset.sum_erase_add Finset.univ (fun j => ‖z j‖^2) (Finset.mem_univ i)
  have hi : ∑ j ∈ Finset.univ.erase i, 2 * (b * ⟪z j,z i⟫) = -2*b*‖z i‖^2 := by
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, ← sum_inner, sum_erase_zero z hz i, inner_neg_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hi, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  dsimp [b]
  rw [← hn]
  field_simp
  ring

lemma scoreMax_recentered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
  classical
  let f : Fin k → ℝ := fun j => ⟪z j + ((k:ℝ)-1)⁻¹ • z i,x⟫
  have hsum : ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    rw [← sum_inner, sum_erased_centered hk z hz i, inner_zero_left]
  have hnon : 0 ≤ (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f := by
    by_contra! hn
    have hh : ∑ j ∈ Finset.univ.erase i, f j < 0 := Finset.sum_neg
      (fun j hj => (Finset.le_sup' f hj).trans_lt hn) (erase_univ_nonempty hk i)
    linarith
  have hex : (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) f =
      omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    dsimp only [omittedMax, f]
    simp_rw [inner_add_left]
    exact (Finset.sup'_add _ _ _ _).symm
  rw [← hex]
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _
    by_cases hji : j = i
    · simpa only [ite_eq_left hji, inner_zero_left] using hnon
    · rw [ite_eq_right hji]
      exact Finset.le_sup' f (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
  · apply (Finset.sup'_le_iff _ _).mpr
    intro j hj
    have hh := le_scoreMax (recentered z i).ofLp j x
    change ⟪if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i,x⟫ ≤ _ at hh
    simpa only [ite_eq_right (Finset.ne_of_mem_erase hj)] using hh

lemma omittedMax_integrable (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    Integrable (omittedMax hk z i) (gaussian d) := by
  have heq : omittedMax hk z i = fun x => scoreMax (recentered z i).ofLp x -
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    funext x
    rw [scoreMax_recentered hk z hz i x]
    ring
  rw [heq]
  exact (integrable_scoreMax _).sub
    (Integrable.const_inner _ (integrable_id_gaussian d))

lemma integral_omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∫ x, omittedMax hk z i x ∂gaussian d = width (recentered z i) := by
  have heq : scoreMax (recentered z i).ofLp = fun x => omittedMax hk z i x +
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := funext (scoreMax_recentered hk z hz i)
  rw [width, heq]
  change _ = ∫ x, omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d
  have hi : Integrable (fun x : Space d => ⟪((k:ℝ)-1)⁻¹ • z i,x⟫) (gaussian d) :=
    Integrable.const_inner _ (integrable_id_gaussian d)
  rw [integral_add (omittedMax_integrable hk z hz i) hi]
  have hz0 : (∫ x : Space d, ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d) = 0 := by
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  rw [hz0, add_zero]

lemma scoreMax_eq_max_omitted (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : scoreMax z x = max ⟪z i,x⟫ (omittedMax hk z i x) := by
  classical
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact le_max_left _ _
    · exact (Finset.le_sup' (fun j => ⟪z j,x⟫)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).trans (le_max_right _ _)
  · apply max_le
    · exact le_scoreMax z i x
    · exact Finset.sup'_le _ _ (fun j _ => le_scoreMax z j x)

lemma positive_gap_eq (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) :
    max (⟪z i,x⟫ - omittedMax hk z i x) 0 = scoreMax z x - omittedMax hk z i x := by
  rw [scoreMax_eq_max_omitted hk z i x]
  simpa only [sub_self] using max_sub_sub_right ⟪z i,x⟫ (omittedMax hk z i x) (omittedMax hk z i x)

theorem optimal_loss_lower (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : Optimal A) (i : Fin k) :
    value A - Real.sqrt (value A) *
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) ≤
    ∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d := by
  let z : Fin k → Space d := fun j => centroid (A j)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1
  have hn : ‖recentered z i‖ =
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) := by
    rw [← show ‖recentered z i‖^2 = value A - ((k:ℝ)/((k:ℝ)-1)) *
      ‖centroid (A i)‖^2 from recentered_norm_sq hk z hz i, Real.sqrt_sq (norm_nonneg _)]
  have heq : (fun x => max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0) =
      fun x => scoreMax z x - omittedMax hk z i x := funext (positive_gap_eq hk z i)
  change _ ≤ ∫ x, max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0 ∂gaussian d
  rw [heq]
  have hiz : Integrable (scoreMax z) (gaussian d) := integrable_scoreMax (WithLp.toLp 2 z)
  rw [integral_sub hiz (omittedMax_integrable hk z hz i), integral_omittedMax hk z hz i]
  change _ ≤ width (moments A) - width (recentered z i)
  rw [width_moments_of_optimal hA]
  have hb := optimal_width_le hA (recentered z i)
  rw [hn] at hb
  linarith

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace

open scoped RealInnerProductSpace

namespace GaussianPropeller.Gram

variable {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] [DecidableEq ι] in

theorem independent_omit (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (i : ι) :
    LinearIndependent ℝ (fun j : {j : ι // j ≠ i} => z j) := by
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ E)
    (fun x hx => real_inner_self_pos.mpr hx) (-(innerₗ E) (z i))
  · intro j
    change 0 < -⟪z i, z j⟫
    exact neg_pos.mpr (hneg (Ne.symm j.property))
  · intro j l hjl
    exact (hneg (fun h => hjl (Subtype.ext h))).le

theorem sum_omit_eq {F : Type uF} [AddCommMonoid F] (f : ι → F) (i : ι)
    (hi : f i = 0) : (∑ j : {j : ι // j ≠ i}, f j) = ∑ j, f j := by
  rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp) f]
  simpa [hi] using Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)

theorem coefficients_constant (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (a : ι → ℝ) (ha : ∑ i, a i • z i = 0) (i j : ι) : a j = a i := by
  have hrel : ∑ l, (a l - a i) • z l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, ha,
      smul_zero, sub_self]
  have hrel' : ∑ l : {l : ι // l ≠ i}, (a l - a i) • z l = 0 := by
    rw [sum_omit_eq (fun l => (a l - a i) • z l) i (by simp)]
    exact hrel
  by_cases hji : j = i
  · rw [hji]
  · have hzero := (Fintype.linearIndependent_iff.mp (independent_omit z hneg i))
      (fun l => a l - a i) hrel' ⟨j, hji⟩
    exact sub_eq_zero.mp hzero

theorem affineIndependent (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0) :
    AffineIndependent ℝ z := by
  rw [affineIndependent_iff_of_fintype]
  intro a ha hrel i
  have hlin : ∑ j, a j • z j = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination Finset.univ ha] using hrel
  have hconst : ∀ j, a j = a i := coefficients_constant z hneg hsum a hlin i
  have hc : (Fintype.card ι : ℝ) * a i = 0 := by
    simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using ha
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hc).resolve_left hcard

theorem independent_differences (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : LinearIndependent ℝ (fun j : {j : ι // j ≠ i} => z j - z i) := by
  exact (affineIndependent_iff_linearIndependent_vsub ℝ z i).mp
    (affineIndependent z hneg hsum)

theorem span_omit_eq (z : ι → E) (hsum : ∑ i, z i = 0) (i : ι) :
    Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j)) =
      Submodule.span ℝ (Set.range z) := by
  classical
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hji : j ≠ i
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
    · have hji' : j = i := not_ne_iff.mp hji
      subst j
      let V := Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j))
      have hi : z i = -(∑ j ∈ Finset.univ.erase i, z j) := by
        have h := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
        rw [hsum] at h
        exact eq_neg_of_add_eq_zero_right h
      rw [hi]
      apply V.neg_mem
      apply V.sum_mem
      intro j hj
      exact Submodule.subset_span ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, rfl⟩

theorem finrank_span (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : Module.finrank ℝ (Submodule.span ℝ (Set.range z)) =
      Fintype.card ι - 1 := by
  rw [← span_omit_eq z hsum i, finrank_span_eq_card (independent_omit z hneg i)]
  simp [Fintype.card_subtype_compl (fun j : ι => j = i)]

theorem span_differences_eq (z : ι → E) (hsum : ∑ i, z i = 0) (i : ι) :
    Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j - z i)) =
      Submodule.span ℝ (Set.range z) := by
  classical
  let W := Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j - z i))
  have hdiff (j : ι) : z j - z i ∈ W := by
    by_cases hji : j = i
    · simp [hji]
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
  have hi : z i ∈ W := by
    have hh : (∑ j, (z j - z i)) = -(Fintype.card ι : ℝ) • z i := by
      simp [Finset.sum_sub_distrib, hsum, ← Nat.cast_smul_eq_nsmul ℝ, neg_smul]
    have hm : -(Fintype.card ι : ℝ) • z i ∈ W := by
      rw [← hh]
      exact W.sum_mem (fun j _ => hdiff j)
    have hcard : -(Fintype.card ι : ℝ) ≠ 0 := by
      have : Nonempty ι := ⟨i⟩
      exact neg_ne_zero.mpr (by exact_mod_cast Fintype.card_ne_zero)
    exact (W.smul_mem_iff hcard).mp hm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change z j ∈ W
    have h := W.add_mem (hdiff j) hi
    simpa only [sub_add_cancel] using h

omit [Fintype ι] [DecidableEq ι] in

theorem exists_inner_values [FiniteDimensional ℝ E] (v : ι → E)
    (hv : LinearIndependent ℝ v) (a : ι → ℝ) :
    ∃ h ∈ Submodule.span ℝ (Set.range v), ∀ i, ⟪h, v i⟫ = a i := by
  let W := Submodule.span ℝ (Set.range v)
  let b := Module.Basis.span hv
  let L : StrongDual ℝ W := LinearMap.toContinuousLinearMap (b.constr ℝ a)
  let h : W := (InnerProductSpace.toDual ℝ W).symm L
  refine ⟨h, h.property, fun i => ?_⟩
  have hi : ⟪h, b i⟫ = a i := by
    rw [InnerProductSpace.toDual_symm_apply]
    exact b.constr_basis ℝ a i
  change ⟪(h : E), ((b i) : E)⟫ = a i at hi
  simpa only [b, Module.Basis.coe_span_apply] using hi

theorem exists_translation [FiniteDimensional ℝ E] (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : ∃ h ∈ Submodule.span ℝ (Set.range z),
      (∀ j, j ≠ i → ⟪h, z i - z j⟫ = 1) ∧
        ⟪h, z i⟫ = ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by
  obtain ⟨h, hh, hpair⟩ := exists_inner_values
    (fun j : {j : ι // j ≠ i} => z j - z i)
    (independent_differences z hneg hsum i) (fun _ => -1)
  have hpair' (j : ι) (hji : j ≠ i) : ⟪h, z i - z j⟫ = 1 := by
    have hp := hpair ⟨j, hji⟩
    simp only [inner_sub_right] at hp ⊢
    linarith
  refine ⟨h, ?_, hpair', ?_⟩
  · rwa [span_differences_eq z hsum i] at hh
  · have hsum' : ∑ j : {j : ι // j ≠ i}, ⟪h, z i - z j⟫ =
        (Fintype.card ι : ℝ) - 1 := by
      simp only [show ∀ j : {j : ι // j ≠ i}, ⟪h, z i - z j⟫ = 1 from
        fun j => hpair' j j.property, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
        simp [Fintype.card_subtype_compl (fun j : ι => j = i)]
      rw [hcard, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩)]
      simp
    have hsum'' : (Fintype.card ι : ℝ) * ⟪h, z i⟫ =
        (Fintype.card ι : ℝ) - 1 := by
      rw [sum_omit_eq (fun j => ⟪h, z i - z j⟫) i (by simp)] at hsum'
      simpa only [inner_sub_right, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← inner_sum, hsum, inner_zero_right,
        sub_zero] using hsum'
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      have : Nonempty ι := ⟨i⟩
      exact_mod_cast Fintype.card_ne_zero
    exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using hsum'')

end GaussianPropeller.Gram

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm

lemma stdDensity_pos {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 < stdDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

lemma stdDensity_eq {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    stdDensity x = (Real.sqrt (2*Real.pi))⁻¹ ^ (Fintype.card ι) *
      Real.exp (-‖x‖^2/2) := by
  simp only [stdDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp [EuclideanSpace.norm_sq_eq]

lemma stdGaussian_map_add {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x+v) =
      (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (⟪v,x⟫-‖v‖^2/2))) := by
  -- Cameron–Martin, from the published HairerSPDE.map_add_eq_withDensity with representer ⟪v, ·⟫
  have hcov : ∀ L : StrongDual ℝ (EuclideanSpace ℝ ι),
      covarianceBilinDual (stdGaussian (EuclideanSpace ℝ ι))
        (InnerProductSpace.toDualMap ℝ _ v) L = L v := by
    intro L
    obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).surjective L
    have h := congrArg (fun B => B v w) (covarianceBilin_stdGaussian (E := EuclideanSpace ℝ ι))
    simp only [covarianceBilin_eq_covarianceBilinDual, innerSL_apply_apply] at h
    rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    exact h
  have hm : (stdGaussian (EuclideanSpace ℝ ι))[id] = 0 := by
    simpa using integral_id_stdGaussian (E := EuclideanSpace ℝ ι)
  rw [HairerSPDE.map_add_eq_withDensity _ hm v _ hcov]
  congr 1
  funext x
  rw [hcov, InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDualMap_apply_apply,
    real_inner_self_eq_norm_sq]

lemma translated_integral {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-v)).real A =
      ∫ x in A, Real.exp (-⟪v,x⟫-‖v‖^2/2) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  simp_rw [sub_eq_add_neg]
  rw [stdGaussian_map_add]
  simp only [inner_neg_left, norm_neg]
  rw [measureReal_def, withDensity_apply _ hA,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _
      (fun x => (Real.exp_pos (-⟪v,x⟫-‖v‖^2/2)).le)) (by fun_prop)]
  simp only [sub_eq_add_neg]

lemma integrable_exp_inner {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (t : ℝ) : Integrable (fun x => Real.exp (t*⟪h,x⟫)) (stdGaussian E) := by
  let L : StrongDual ℝ E := innerSL ℝ h
  have hi : Integrable (fun x : ℝ => Real.exp (t*x)) ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal L]
    exact integrable_exp_mul_gaussianReal t
  exact hi.comp_aemeasurable L.continuous.aemeasurable

lemma integrableExpSet_neg_inner_restrict {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (A : Set E) :
    integrableExpSet (fun x => -⟪h,x⟫) ((stdGaussian E).restrict A) = univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  change Integrable (fun x => Real.exp (t * -⟪h,x⟫)) ((stdGaussian E).restrict A)
  simpa only [inner_neg_left] using (integrable_exp_inner (-h) t).restrict (s := A)

lemma translation_derivative {ι : Type uι} [Fintype ι]
    (h : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    HasDerivAt (fun u : ℝ =>
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-u•h)).real A)
      (-⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫) 0 := by
  have hd := hasDerivAt_mgf (X := fun x => -⟪h,x⟫)
    (μ := (stdGaussian (EuclideanSpace ℝ ι)).restrict A) (t := 0) (by
      rw [integrableExpSet_neg_inner_restrict, interior_univ]; trivial)
  simp only [zero_mul, Real.exp_zero, mul_one, integral_neg] at hd
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u^2*‖h‖^2/2)) 0 0 := by
    convert (((hasDerivAt_pow 2 (0:ℝ)).neg.mul_const (‖h‖^2)).div_const 2).exp using 1 <;> first | rfl | simp
  have hp := he.mul hd
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul, zero_div,
    Real.exp_zero, one_mul, zero_add] at hp
  have hinner : (∫ x in A, ⟪h,x⟫ ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫ :=
    integral_inner (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ ι))).restrict h
  rw [hinner] at hp
  apply hp.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro u
  dsimp only [Pi.mul_apply]
  rw [translated_integral (u•h) A hA]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    starRingEnd_apply, star_trivial, mgf]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.exp_add]
  congr 1
  ring

end GaussianPropeller.Translation

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Quantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma Φ_zero : Φ 0 = 1/2 := by
  have h := Φ_neg 0
  simp only [neg_zero] at h
  linarith only [h]
lemma cdfIso_coe (x : ℝ) : (cdfIso x : ℝ) = Φ x := rfl
lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]
lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (q p) = p := by
  rw [q_of_mem hp, ← cdfIso_coe]
  exact congrArg Subtype.val (cdfIso.apply_symm_apply ⟨p,hp⟩)
lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  rw [q_of_mem (Φ_mem x)]
  exact cdfIso.symm_apply_apply x
lemma continuousOn_q : ContinuousOn q (Ioo (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : Ioo (0:ℝ) 1 => q p)
  have heq : (fun p : Ioo (0:ℝ) 1 => q p) = cdfIso.symm := by
    funext p
    exact q_of_mem p.2
  rw [heq]
  exact cdfIso.symm.continuous
lemma continuousAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt q p :=
  continuousOn_q.continuousAt (isOpen_Ioo.mem_nhds hp)
lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt q (φ (q p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_q hp) (hasDerivAt_Φ (q p))
    (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
  exact Φ_q hy

lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

end GaussianPropeller.Quantile

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ConeConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_open_pos {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) : 0 < γ U := by
  have hac : (volume : Measure E) ≪ γ := by
    rw [Translation.stdGaussian_density]
    exact withDensity_absolutelyContinuous' Translation.measurable_stdDensity.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (Translation.stdDensity_pos x))))
  by_contra! hz
  have heq : γ U = 0 := le_antisymm hz bot_le
  exact ne_of_gt (hU.measure_pos volume hne) (hac heq)

lemma prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by
  let U : Set E := {y | ∀ i, 0 < ⟪v i,x+y⟫}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall] using isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const : Continuous (fun _ : E => (0:ℝ)))
        (show Continuous (fun y : E => ⟪v i,x+y⟫) by fun_prop))
  have hn : U.Nonempty := ⟨e-x, by simpa only [U, mem_ofPred_eq, show x+(e-x)=e by abel] using he⟩
  have hs : U ⊆ shifted v x := fun y hy i => (hy i).le
  have hp : 0 < (γ).real (shifted v x) := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hU hn).trans_le (measure_mono hs))) (measure_ne_top _ _)
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hv : v i ≠ 0 := by intro hh; simpa only [hh, inner_zero_left, lt_self_iff_false] using he i
  let V : Set E := {y | ⟪v i,x+y⟫ < 0}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hnV : V.Nonempty := by
    refine ⟨-v i-x,?_⟩
    change ⟪v i,x+(-v i-x)⟫ < 0
    rw [show x+(-v i-x)= -v i by abel, inner_neg_right]
    exact neg_neg_of_pos (real_inner_self_pos.mpr hv)
  have hsV : V ⊆ (shifted v x)ᶜ := by
    intro y hy hz
    exact (not_lt_of_ge (hz i)) hy
  have hc : 0 < (γ).real (shifted v x)ᶜ := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hV hnV).trans_le (measure_mono hsV))) (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (measurableSet_shifted v x)] at hc
  exact ⟨hp, by change (γ).real (shifted v x) < 1; linarith only [hc]⟩

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

lemma integrable_mul_φ : Integrable (fun x : ℝ => x*φ x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [φ]
  rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
  ring

lemma tendsto_φ_atBot : Tendsto φ atBot (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0))
  have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  convert ht.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  · funext x; unfold φ; congr 2; ring
  · simp only [mul_zero]

lemma left_first_moment (a : ℝ) : ∫ x in Iic a, x*φ x = -φ a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -φ x) (x*φ x) x := by
    convert (hasDerivAt_φ x).neg using 1 <;> first | rfl | ring1
  simpa only [neg_zero, sub_zero, Pi.neg_apply] using integral_Iic_of_hasDerivAt_of_tendsto
    (continuous_φ.neg.continuousWithinAt) (fun x _ => hd x)
    integrable_mul_φ.integrableOn (tendsto_φ_atBot.neg)

lemma integral_positive_cdf (a : ℝ) :
    ∫ x : ℝ, max (a-x) 0 ∂gaussianReal 0 1 = a*Φ a+φ a := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [show ∀ x : ℝ, gaussianPDFReal 0 1 x = φ x by
    intro x; simp only [gaussianPDFReal, φ, NNReal.coe_one, mul_one, sub_zero], smul_eq_mul]
  have heq : ∫ x : ℝ, φ x * max (a-x) 0 = ∫ x in Iic a, (a-x)*φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic a)]
    · exact setIntegral_congr_fun measurableSet_Iic (fun x hx => by
        rw [max_eq_left (sub_nonneg.mpr hx)]; ring)
    · intro x hx
      simp only [mem_Iic, not_le] at hx
      rw [max_eq_right (sub_nonpos.mpr hx.le), mul_zero]
  rw [heq]
  simp_rw [sub_mul]
  rw [integral_sub (integrable_φ.const_mul a).integrableOn integrable_mul_φ.integrableOn,
    integral_const_mul, left_first_moment]
  simp only [Φ, sub_neg_eq_add]

lemma tail_integrable {X : Type uX} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioi 0) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (show Antitone (fun t : ℝ => μ {x | t ≤ f x}) from
      fun _ _ hst => measure_mono (fun _ h => hst.trans h)).measurable.aemeasurable
  · rw [← lintegral_eq_lintegral_meas_le μ hn hi.aemeasurable]
    exact hi.lintegral_lt_top.ne

lemma integral_cdf_tail (a c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), Φ (a-c*u)) = (a*Φ a+φ a)/c := by
  let f : ℝ → ℝ := fun x => max (a-x) 0 / c
  have hf : Integrable f (gaussianReal 0 1) := by
    exact (((integrable_const a).sub (IsGaussian.integrable_id (μ := gaussianReal 0 1))).sup
      (integrable_const 0)).div_const c
  have hn : 0 ≤ᵐ[gaussianReal 0 1] f := ae_of_all _ (fun x => div_nonneg (le_max_right _ _) hc.le)
  have heq (u : ℝ) (hu : 0 < u) : (gaussianReal 0 1).real {x | u ≤ f x} = Φ (a-c*u) := by
    rw [Φ_eq_gaussianReal]
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_Iic, f, le_div_iff₀ hc, le_max_iff]
    have hh : ¬ u*c ≤ 0 := not_le.mpr (mul_pos hu hc)
    simp only [hh, or_false]
    constructor <;> intro h <;> nlinarith only [h]
  have hi : IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) :=
    (tail_integrable hf hn).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => heq u hu))
  refine ⟨hi,?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq,
    ← hf.integral_eq_integral_meas_le hn]
  rw [show f = fun x => max (a-x) 0 / c from rfl, integral_div, integral_positive_cdf]

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma measurableSet_cone (v : κ → E) : MeasurableSet (cone v) := by
  simpa only [shifted, zero_add, ofPred_mem_eq] using measurableSet_shifted v 0

omit [Fintype κ] [Nonempty κ] in
lemma prob_zero [Fintype κ] [Nonempty κ] (v : κ → E) : prob v 0 = (γ).real (cone v) := by
  simp only [prob, shifted, zero_add, ofPred_mem_eq]

lemma prob_line_deriv (v : κ → E) (h : E) :
    HasDerivAt (fun u : ℝ => prob v (-u • h))
      (-⟪h, ∫ x in cone v, x ∂γ⟫) 0 := by
  have heq (u : ℝ) : prob v (-u • h) =
      ((γ).map (fun x => x-u•h)).real (cone v) := by
    unfold prob
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) (measurableSet_cone v)]
    apply congrArg ENNReal.toReal
    apply congrArg γ
    ext x
    change (-u•h+x ∈ cone v) ↔ (x-u•h ∈ cone v)
    rw [show -u•h+x = x-u•h by simp only [neg_smul, sub_eq_add_neg, add_comm]]
  simp_rw [heq]
  exact Translation.translation_derivative h (cone v) (measurableSet_cone v)

lemma prob_tangent (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (h : E) (u : ℝ) :
    prob v (-u • h) ≤ Φ (q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u) := by
  have hc : ConcaveOn ℝ univ (fun t : ℝ => q (prob v (-t•h))) := by
    refine ⟨convex_univ,?_⟩
    intro s _ t _ a b ha hb hab
    have hh := (quantile_prob_concave v e he).2 (mem_univ (-s•h)) (mem_univ (-t•h)) ha hb hab
    change a * q (prob v (-s•h))+b * q (prob v (-t•h)) ≤ q (prob v (-(a*s+b*t)•h))
    rw [show -(a*s+b*t)•h = a•(-s•h)+b•(-t•h) by module]
    exact hh
  have hd := (hasDerivAt_q (prob_mem v e he (-(0:ℝ)•h))).comp (0:ℝ) (prob_line_deriv v h)
  simp only [neg_zero, zero_smul] at hd
  have ht := concave_le_tangent hc (mem_univ 0) (mem_univ u) hd
  simp only [neg_zero, zero_smul, sub_zero] at ht
  have ht' : q (prob v (-u•h)) ≤ q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u := by
    calc
      _ ≤ q (prob v 0) + (φ (q (prob v 0)))⁻¹ * (-⟪h, ∫ x in cone v, x ∂γ⟫) * u := ht
      _ = _ := by ring
  have hh := strictMono_Φ.monotone ht'
  rwa [Φ_q (prob_mem v e he (-u•h))] at hh

lemma integral_prob_upper (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫)
    (h : E) (hβ : 0 < ⟪h, ∫ x in cone v, x ∂γ⟫) :
    (∫ u in Ioi (0:ℝ), prob v (-u • h)) ≤
      φ (q (prob v 0)) * (q (prob v 0)*prob v 0+φ (q (prob v 0))) /
      ⟪h, ∫ x in cone v, x ∂γ⟫ := by
  let a := q (prob v 0)
  let c := ⟪h, ∫ x in cone v, x ∂γ⟫ / φ a
  have hc : 0 < c := div_pos hβ (φ_pos a)
  calc
    _ ≤ ∫ u in Ioi (0:ℝ), Φ (a-c*u) := integral_mono_of_nonneg
      (ae_of_all (volume.restrict (Ioi (0:ℝ))) (fun u => measureReal_nonneg))
      (integral_cdf_tail a c hc).1
      (ae_of_all _ (prob_tangent v e he h))
    _ = (a*Φ a+φ a)/c := (integral_cdf_tail a c hc).2
    _ = _ := by
      dsimp [a,c]
      rw [Φ_q (prob_mem v e he 0)]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end GaussianPropeller.EhrhardCone

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ConeReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma difference_cone_eq [NeZero k] (z : Fin k → Space d) (i : Fin k) :
    EhrhardCone.cone (fun j : {j : Fin k // j ≠ i} => z i-z j) = closedCell z i := by
  ext x
  constructor
  · intro hx j
    by_cases hji : j = i
    · subst j; rfl
    · have hh := hx ⟨j,hji⟩
      simp only [inner_sub_left] at hh
      linarith only [hh]
  · intro hx j
    change 0 ≤ ⟪z i-z j,x⟫
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hx j)

omit [NeZero k] in
lemma gap_event_eq [NeZero k] (hk : 2 ≤ k) (z : Fin k → Space d) (i : Fin k)
    (h : Space d) (hh : ∀ j, j ≠ i → ⟪h,z i-z j⟫ = 1) {u : ℝ} (hu : 0 < u) :
    {x | u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0} =
      EhrhardCone.shifted (fun j : {j : Fin k // j ≠ i} => z i-z j) (-u•h) := by
  classical
  ext x
  have hpair (j : {j : Fin k // j ≠ i}) : ⟪z i-z j,-u•h+x⟫ = -u+(⟪z i,x⟫-⟪z j,x⟫) := by
    have hcomm : ⟪z i-z j,h⟫=1 := (real_inner_comm _ _).trans (hh j j.property)
    rw [inner_add_right, inner_smul_right, hcomm, mul_one, inner_sub_left]
  change (u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0) ↔
    ∀ j : {j : Fin k // j ≠ i}, 0 ≤ ⟪z i-z j,-u•h+x⟫
  simp only [le_max_iff, not_le.mpr hu, or_false, hpair]
  constructor
  · intro hx j
    have hm := Finset.le_sup' (fun j => ⟪z j,x⟫)
      (Finset.mem_erase.mpr ⟨j.property,Finset.mem_univ _⟩)
    change ⟪z j,x⟫ ≤ omittedMax hk z i x at hm
    linarith only [hx,hm]
  · intro hx
    have hm : omittedMax hk z i x ≤ ⟪z i,x⟫-u := by
      apply Finset.sup'_le
      intro j hj
      have hj' := hx ⟨j, Finset.ne_of_mem_erase hj⟩
      linarith only [hj']
    linarith only [hm]

lemma minimal_loss_upper (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    (∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d) ≤
      ((k:ℝ)/((k:ℝ)-1)) * φ (q ((gaussian d).real (A i))) *
      (q ((gaussian d).real (A i)) * (gaussian d).real (A i)+φ (q ((gaussian d).real (A i)))) := by
  classical
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  let z : Fin k → Space d := fun j => centroid (A j)
  let v : {j : Fin k // j ≠ i} → Space d := fun j => z i-z j
  have : Nonempty {j : Fin k // j ≠ i} := by
    obtain ⟨j,hj⟩ := erase_univ_nonempty hk i
    exact ⟨j,Finset.ne_of_mem_erase hj⟩
  have hneg : Pairwise (fun j l => ⟪z j,z l⟫ < 0) := fun j l hjl =>
    negative_inner_of_minimal hA hjl (hall j) (hall l)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1.1
  obtain ⟨h,_,hh,hpair⟩ := Gram.exists_translation z hneg hz i
  simp only [Fintype.card_fin] at hpair
  have hcone : EhrhardCone.cone v = closedCell z i := difference_cone_eq z i
  have hae : A i =ᵐ[gaussian d] EhrhardCone.cone v := by
    rw [hcone]; exact active_eq_closedCell_ae hA hpos (hall i)
  have hcentroid : (∫ x in EhrhardCone.cone v, x ∂gaussian d) = z i :=
    setIntegral_congr_set hae.symm
  have hp : EhrhardCone.prob v 0 = (gaussian d).real (A i) := by
    rw [EhrhardCone.prob_zero]
    exact congrArg ENNReal.toReal (measure_congr hae.symm)
  have he (j : {j : Fin k // j ≠ i}) : 0 < ⟪v j,z i⟫ := by
    dsimp [v]
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hn := hneg j.property
    nlinarith only [hn, sq_nonneg ‖z i‖]
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hβ : 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂stdGaussian (Space d)⟫ := by
    change 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫
    rw [hcentroid,hpair]
    exact div_pos (by linarith) hk0
  have hup := EhrhardCone.integral_prob_upper v (z i) he h hβ
  change (∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h)) ≤ _ at hup
  change _ ≤ φ (q (EhrhardCone.prob v 0)) *
    (q (EhrhardCone.prob v 0)*EhrhardCone.prob v 0+φ (q (EhrhardCone.prob v 0))) /
      ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫ at hup
  rw [hp,hcentroid,hpair] at hup
  have hfi : Integrable (fun x => max (⟪z i,x⟫-omittedMax hk z i x) 0) (gaussian d) :=
    ((Integrable.const_inner _ (integrable_id_gaussian d)).sub
      (omittedMax_integrable hk z hz i)).sup (integrable_const 0)
  rw [hfi.integral_eq_integral_meas_le (ae_of_all _ (fun x => le_max_right _ _))]
  have heq : (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) =
      ∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0} = _
    rw [gap_event_eq hk z i h hh hu]
    rfl
  change (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) ≤ _
  rw [heq]
  convert hup using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.OneCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.OneCell

lemma nonneg_of_deriv_nonneg (f f' : ℝ → ℝ) (hf : Continuous f)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x)
    (h0 : 0 ≤ f 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    hf.continuousOn (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => hpos x (interior_subset hx))
  exact h0.trans (hm (by simp) hx hx)

lemma exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2 := by
  have h := nonneg_of_deriv_nonneg
    (fun x => (1-x+x^2/2)-Real.exp (-x)) (fun x => -1+x+Real.exp (-x))
    (by fun_prop) (fun x => by convert
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_id x).neg.exp) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x _ => by have hh := Real.add_one_le_exp (-x); linarith)
    (by simp) hx
  linarith

lemma exp_neg_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    1-x+x^2/2-x^3/6 ≤ Real.exp (-x) := by
  have h := nonneg_of_deriv_nonneg
    (fun x => Real.exp (-x)-(1-x+x^2/2-x^3/6))
    (fun x => -Real.exp (-x)+1-x+x^2/2)
    (by fun_prop) (fun x => by convert
      (((hasDerivAt_id x).neg.exp).sub
        ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
          ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 3 x).div_const 6))) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x hx => by have hh := exp_neg_le_quadratic hx; linarith)
    (by simp) hx
  linarith

lemma exp_neg_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2-x^3/6+x^4/24 := by
  have h := nonneg_of_deriv_nonneg
    (fun x => (1-x+x^2/2-x^3/6+x^4/24)-Real.exp (-x))
    (fun x => -1+x-x^2/2+x^3/6+Real.exp (-x))
    (by fun_prop) (fun x => by convert
      (((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 3 x).div_const 6)).add
          ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_id x).neg.exp) using 1 <;> first | rfl | (solve | ring) | (dsimp; ring))
    (fun x hx => by have hh := exp_neg_ge_cubic hx; linarith)
    (by simp) hx
  linarith

lemma exp_neg_sq_upper (x : ℝ) :
    Real.exp (-x^2/2) ≤ 1-x^2/2+x^4/8-x^6/48+x^8/384 := by
  convert exp_neg_le_quartic (show (0:ℝ) ≤ x^2/2 by positivity) using 1 <;> ring_nf

lemma hasDerivAt_P (x : ℝ) : HasDerivAt P (P' x) x := by
  unfold P P' Q
  convert (((((((hasDerivAt_id x).add ((hasDerivAt_pow 3 x).div_const 2)).sub
    ((hasDerivAt_pow 5 x).div_const 24)).add ((hasDerivAt_pow 7 x).div_const 240)).sub
      ((hasDerivAt_pow 9 x).div_const 2688)).add ((hasDerivAt_pow 11 x).div_const 3456)).const_mul
      (398943/1000000:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2) using 1 <;> first | rfl | (solve | ring)

lemma hasDerivAt_P' (x : ℝ) : HasDerivAt P' (P'' x) x := by
  unfold P' P''
  convert (((((((hasDerivAt_const x 1).add (((hasDerivAt_pow 2 x).const_mul 3).div_const 2)).sub
    (((hasDerivAt_pow 4 x).const_mul 5).div_const 24)).add (((hasDerivAt_pow 6 x).const_mul 7).div_const 240)).sub
      (((hasDerivAt_pow 8 x).const_mul 9).div_const 2688)).add (((hasDerivAt_pow 10 x).const_mul 11).div_const 3456)).const_mul
      (398943/1000000:ℝ)).sub (hasDerivAt_id x) using 1 <;> first | rfl | (solve | ring)

lemma P''_nonpos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : P'' x ≤ 0 := by
  have hx2 : x^2 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx5 : x^5 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx7 : 0 ≤ x^7 := pow_nonneg hx.1 _
  have hx9 : x^9 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hf : 0 ≤ (1-x)*(13-5*x-5*x^2) := mul_nonneg (by linarith [hx.2]) (by linarith only [hx.2,hx2])
  have ha : 3*x-5*x^3/6 ≤ 13/6 := by nlinarith only [hf]
  unfold P''
  linarith only [ha,hx5,hx7,hx9]

lemma concaveOn_P : ConcaveOn ℝ (Icc (0:ℝ) 1) P :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (by unfold P Q; fun_prop) (fun x _ => (hasDerivAt_P x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_P' x).hasDerivWithinAt)
    (fun x hx => P''_nonpos (interior_subset hx))

lemma P_global_upper {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : P x ≤ 81/800 := by
  have hq : (153/250:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hpq : P (153/250) ≤ 10123/100000 := by norm_num [P,Q]
  have hdq : P' (153/250) ∈ Icc (0:ℝ) (11/1000000) := by norm_num [P']
  rcases lt_trichotomy x (153/250) with hlt | heq | hgt
  · have hh := concaveOn_P.le_slope_of_hasDerivAt hx hq hlt (hasDerivAt_P (153/250))
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hlt)).mp hh
    have hg : 0 ≤ P' (153/250)*(153/250-x) := mul_nonneg hdq.1 (sub_nonneg.mpr hlt.le)
    linarith only [hpq,hh',hg]
  · rw [heq]
    linarith only [hpq]
  · have hh := concaveOn_P.slope_le_of_hasDerivAt hq hx hgt (hasDerivAt_P (153/250))
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hgt)).mp hh
    have hg : P' (153/250)*(x-153/250) ≤ 11/1000000 := by
      calc
        _ ≤ (11/1000000)*(x-153/250) := mul_le_mul_of_nonneg_right hdq.2 (sub_nonneg.mpr hgt.le)
        _ ≤ _ := by linarith only [hx.2]
    linarith only [hpq,hh',hg]

lemma density_integrable : Integrable density := by
  change Integrable (fun x : ℝ => Real.exp (-x^2/2))
  simpa only [ show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma mul_density_integrable : Integrable (fun x : ℝ => x*density x) := by
  simpa only [density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma sq_density_integrable : Integrable (fun x : ℝ => x^2*density x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 2)
  simpa only [density, Real.rpow_two, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using h

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;> first | rfl | ring1 | (norm_num <;> ring1)

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_first_moment (a : ℝ) : ∫ x in Ioi a, x*density x = density a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -density x) (x*density x) x := by
    convert (hasDerivAt_density x).neg using 1 <;> first | rfl | ring1
  have ht : Tendsto (fun x => -density x) atTop (𝓝 (-0)) := tendsto_density.neg
  simpa only [neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
      mul_density_integrable.integrableOn ht

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

lemma tail_sub {a : ℝ} (ha : 0 ≤ a) : tail a = tail 0 - ∫ x in (0:ℝ)..a, density x := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi density_integrable.integrableOn ha
  change tail 0-tail a = _ at h
  linarith

lemma gaussianConst_bounds : (39/100:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  have hp := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  constructor
  · rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
    have hh := Real.pi_lt_d2
    nlinarith
  · rw [gaussianConst, inv_eq_one_div, div_le_iff₀ hspos]
    have hh := Real.pi_gt_d6
    nlinarith

lemma tendsto_mul_density : Tendsto (fun x : ℝ => x*density x) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0:ℝ) < 1/2) 1).mono_left atTop_le_cocompact
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp only [Real.rpow_one, abs_of_nonneg hx, density]
  rw [show -(1/2:ℝ)*x^2 = -x^2/2 by ring]

lemma tail_second_moment (a : ℝ) : ∫ x in Ioi a, x^2*density x = a*density a+tail a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -(x*density x))
      (x^2*density x-density x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_density x)).neg using 1 <;> first | rfl | (dsimp; ring)
  have ht : Tendsto (fun x : ℝ => -(x*density x)) atTop (𝓝 (-0)) := tendsto_mul_density.neg
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x)
    (sq_density_integrable.sub density_integrable).integrableOn ht
  rw [integral_sub sq_density_integrable.integrableOn density_integrable.integrableOn] at hh
  change (∫ x in Ioi a, x^2*density x)-tail a = -0- -(a*density a) at hh
  linarith

lemma integral_density_upper {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in (0:ℝ)..a, density x ≤ densityPrimitive a := by
  have hd (x : ℝ) : HasDerivAt densityPrimitive (densityUpper x) x := by
    unfold densityPrimitive densityUpper
    convert (((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 40)).sub ((hasDerivAt_pow 7 x).div_const 336)).add
      ((hasDerivAt_pow 9 x).div_const 3456)) using 1 <;> first | rfl | ring
  have hh : ∫ x in (0:ℝ)..a, densityUpper x = densityPrimitive a := by
    simpa only [densityPrimitive, zero_pow (by decide : 3≠0), zero_pow (by decide : 5≠0),
      zero_pow (by decide : 7≠0), zero_pow (by decide : 9≠0), zero_div, sub_zero, add_zero]
      using intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := a) (fun x _ => hd x)
        (by unfold densityUpper; apply Continuous.intervalIntegrable; fun_prop)
  rw [← hh]
  exact intervalIntegral.integral_mono_on ha density_integrable.intervalIntegrable
    (by unfold densityUpper; apply Continuous.intervalIntegrable; fun_prop)
    (fun x _ => exp_neg_sq_upper x)

lemma integral_density_lower : (479/560:ℝ) ≤ ∫ x in (0:ℝ)..1, density x := by
  have hd (x : ℝ) : HasDerivAt densityLowerPrimitive (densityLower x) x := by
    unfold densityLowerPrimitive densityLower
    convert ((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 40)).sub ((hasDerivAt_pow 7 x).div_const 336)) using 1 <;>
        first | rfl | ring
  have hh : ∫ x in (0:ℝ)..1, densityLower x = 479/560 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (fun x _ => hd x) (by unfold densityLower; apply Continuous.intervalIntegrable; fun_prop)
    norm_num [densityLowerPrimitive] at h ⊢
    linarith
  rw [← hh]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by unfold densityLower; apply Continuous.intervalIntegrable; fun_prop)
    density_integrable.intervalIntegrable
  intro x _
  have h := exp_neg_ge_cubic (show (0:ℝ) ≤ x^2/2 by positivity)
  convert h using 1 <;> first | rfl | (unfold densityLower; ring) | (unfold density; congr 1; ring)

lemma tail_second_bound : gaussianConst*(∫ x in Ioi (1:ℝ), x^2*density x)/4 ≤ 81/800 := by
  rw [tail_second_moment, one_mul, tail_sub (by norm_num : (0:ℝ) ≤ 1)]
  have hc := gaussianConst_bounds
  have h2 := tail_zero
  have hlow := integral_density_lower
  have he : density 1 ≤ 233/384 := by
    have h := exp_neg_sq_upper 1
    norm_num at h
    simpa only [density, one_pow, neg_div] using h
  have hneg : density 1-(∫ x in (0:ℝ)..1, density x) ≤ -(31/125:ℝ) := by
    linarith
  have hh := mul_le_mul_of_nonneg_left hneg (le_trans (by norm_num : (0:ℝ) ≤ 39/100) hc.1)
  have hh' := mul_le_mul_of_nonpos_right hc.1 (by norm_num : -(31/125:ℝ) ≤ 0)
  nlinarith only [hh,hh',h2]

lemma normalized_excess_small {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  have hp : 0 ≤ gaussianConst := gaussianConst_bounds.1.trans' (by norm_num)
  have hi : 0 ≤ ∫ x in (0:ℝ)..a, density x :=
    intervalIntegral.integral_nonneg ha.1 (fun x _ => (Real.exp_pos _).le)
  have hd : 0 ≤ density a := (Real.exp_pos _).le
  have hu : a*density a+a^2*(∫ x in (0:ℝ)..a, density x) ≤ Q a := by
    have h1 := mul_le_mul_of_nonneg_left (exp_neg_sq_upper a) ha.1
    have h2 := mul_le_mul_of_nonneg_left (integral_density_upper ha.1) (sq_nonneg a)
    unfold Q densityPrimitive at *
    change a*Real.exp (-a^2/2)+a^2*(∫ x in (0:ℝ)..a, density x) ≤ _
    nlinarith only [h1,h2]
  have hq : 0 ≤ Q a := (add_nonneg (mul_nonneg ha.1 hd) (mul_nonneg (sq_nonneg a) hi)).trans hu
  have h1 := mul_le_mul_of_nonneg_left hu hp
  have h2 := mul_le_mul_of_nonneg_right gaussianConst_bounds.2 hq
  have h3 := P_global_upper ha
  have h0 := tail_zero
  rw [tail_sub ha.1]
  unfold P at h3
  nlinarith only [h1,h2,h3,h0]

lemma normalized_excess_large {a : ℝ} (ha : 1 ≤ a) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  have he : ∫ x in Ioi a, a*(x-a)*density x = a*(density a-a*tail a) := by
    have hf : (fun x : ℝ => a*(x-a)*density x) =
        (fun x => a*(x*density x-a*density x)) := by ext x; ring
    rw [hf, integral_const_mul, integral_sub mul_density_integrable.integrableOn
      (density_integrable.const_mul a).integrableOn, integral_const_mul, tail_first_moment]
    rfl
  have hu : ∫ x in Ioi a, a*(x-a)*density x ≤ (∫ x in Ioi a, x^2*density x)/4 := by
    rw [← integral_div]
    apply setIntegral_mono_on
      (by convert (mul_density_integrable.sub (density_integrable.const_mul a)).const_mul a |>.integrableOn using 1; ext x; dsimp; ring)
      (sq_density_integrable.div_const 4).integrableOn measurableSet_Ioi
    intro x _
    have h : a*(x-a) ≤ x^2/4 := by nlinarith only [sq_nonneg (x-2*a)]
    have hd : 0 ≤ density x := (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_right h hd).trans_eq (by ring)
  have hm : (∫ x in Ioi a, x^2*density x) ≤ ∫ x in Ioi (1:ℝ), x^2*density x := by
    exact setIntegral_mono_set sq_density_integrable.integrableOn
      (ae_of_all _ (fun x => mul_nonneg (sq_nonneg x) (Real.exp_pos _).le))
      (ae_of_all _ (fun _ hx => Ioi_subset_Ioi ha hx))
  rw [he] at hu
  have hc : 0 ≤ gaussianConst := gaussianConst_bounds.1.trans' (by norm_num)
  have hu' := mul_le_mul_of_nonneg_left hu hc
  have hm' := mul_le_mul_of_nonneg_left hm hc
  have hb := tail_second_bound
  nlinarith only [hu',hm',hb]

lemma normalized_excess_bound {a : ℝ} (ha : 0 ≤ a) :
    a*gaussianConst*(density a-a*tail a) ≤ 81/800 := by
  rcases le_total a 1 with h | h
  · exact normalized_excess_small ⟨ha,h⟩
  · exact normalized_excess_large h

lemma integral_gaussianReal_std (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussianReal 0 1 = gaussianConst * ∫ x, f x*density x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul, gaussianConst, density]
  ring

lemma integral_excess_gaussian (a : ℝ) : ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 =
    gaussianConst*(density a-a*tail a) := by
  rw [integral_gaussianReal_std]
  congr 1
  have hh : ∫ x : ℝ, max (x-a) 0*density x = ∫ x in Ioi a, (x-a)*density x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi a)]
    · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [max_eq_left (sub_nonneg.mpr hx.le)])
    · intro x hx
      simp only [mem_Ioi, not_lt] at hx
      rw [max_eq_right (sub_nonpos.mpr hx), zero_mul]
  rw [hh]
  simp_rw [sub_mul]
  rw [integral_sub mul_density_integrable.integrableOn (density_integrable.const_mul a).integrableOn,
    integral_const_mul, tail_first_moment]
  rfl

lemma gaussian_excess_bound {a : ℝ} (ha : 0 ≤ a) :
    a*(∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1) ≤ 81/800 := by
  rw [integral_excess_gaussian]
  simpa only [mul_assoc] using normalized_excess_bound ha

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_unit_inner_gaussian (e : E) (he : ‖e‖=1) :
    (stdGaussian E).map (fun x => ⟪e,x⟫) = gaussianReal 0 1 := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E e) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map, he]
  norm_num

lemma projection_rearrangement {A : Set E} (hA : MeasurableSet A)
    (e : E) (he : ‖e‖=1) (a : ℝ) :
    ∫ x in A, ⟪e,x⟫ ∂stdGaussian E ≤ a*(stdGaussian E).real A+
      ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 := by
  let f : E → ℝ := fun x => ⟪e,x⟫
  have hi : Integrable f (stdGaussian E) := IsGaussian.integrable_id.const_inner e
  have hconst : Integrable (fun _ : E => a) (stdGaussian E) := integrable_const a
  have hpos : Integrable (fun x : E => max (f x-a) 0) (stdGaussian E) :=
    (hi.sub hconst).pos_part
  have hm : ∫ x, max (f x-a) 0 ∂stdGaussian E =
      ∫ x : ℝ, max (x-a) 0 ∂gaussianReal 0 1 := by
    rw [← integral_map (by fun_prop : AEMeasurable f (stdGaussian E))
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => max (x-a) 0) ((stdGaussian E).map f)),
      map_unit_inner_gaussian e he]
  have hp (x : E) : A.indicator f x ≤ A.indicator (fun _ => a) x+max (f x-a) 0 := by
    by_cases hx : x∈A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      linarith only [le_max_left (f x-a) 0]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_add]
      exact le_max_right _ _
  have hh := integral_mono_ae (hi.indicator hA) ((hconst.indicator hA).add hpos)
    (ae_of_all _ hp)
  simp only [Pi.add_apply] at hh
  rw [integral_indicator hA, integral_add (hconst.indicator hA) hpos,
    integral_indicator hA, setIntegral_const, smul_eq_mul, hm, mul_comm] at hh
  exact hh

lemma cell_norm_sq_le {A : Set E} (hA : MeasurableSet A) :
    ‖∫ x in A, x ∂stdGaussian E‖^2 ≤ (81/200:ℝ)*(stdGaussian E).real A := by
  let z : E := ∫ x in A, x ∂stdGaussian E
  change ‖z‖^2 ≤ _
  by_cases hz : z=0
  · rw [hz, norm_zero, zero_pow (by decide : 2≠0)]
    positivity
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hP : 0 < (stdGaussian E).real A := by
    apply lt_of_le_of_ne measureReal_nonneg
    intro h
    have hzero : stdGaussian E A = 0 := (measureReal_eq_zero_iff (by finiteness)).mp h.symm
    apply hz
    exact setIntegral_measure_zero _ hzero
  let e : E := ‖z‖⁻¹ • z
  have he : ‖e‖=1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hm : ∫ x in A, ⟪e,x⟫ ∂stdGaussian E = ‖z‖ := by
    have hi : Integrable (fun x : E => x) (stdGaussian E) := IsGaussian.integrable_id
    rw [integral_inner hi.restrict]
    change ⟪‖z‖⁻¹ • z,z⟫ = ‖z‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  let a : ℝ := ‖z‖/(2*(stdGaussian E).real A)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr := projection_rearrangement hA e he a
  rw [hm] at hr
  have hr' := mul_le_mul_of_nonneg_left hr ha
  have hb := gaussian_excess_bound ha
  have hh : a*‖z‖ ≤ a^2*(stdGaussian E).real A+81/800 := by
    nlinarith only [hr',hb]
  dsimp [a] at hh
  have hden : (stdGaussian E).real A ≠ 0 := hP.ne'
  field_simp at hh
  nlinarith only [hh,hP]

lemma normalized_cell_probability {A : Set E} (hA : MeasurableSet A)
    {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    (884/1000:ℝ)*(‖∫ x in A, x ∂stdGaussian E‖/Real.sqrt C)^2 ≤
      (stdGaussian E).real A := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hnum : (81/200:ℝ)*(884/1000) < 9/(8*Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_lt_d4]
  have hCc : (81/200:ℝ)*(884/1000) < C := hnum.trans hC
  have hz := cell_norm_sq_le hA
  rw [div_pow, Real.sq_sqrt hCp.le, ← mul_div_assoc]
  apply (div_le_iff₀ hCp).mpr
  have hm := mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ) ≤ 884/1000)
  have hP : 0 ≤ (stdGaussian E).real A := measureReal_nonneg
  have hc := mul_le_mul_of_nonneg_right hCc.le hP
  nlinarith only [hm,hc]

end GeneralCell
end GaussianPropeller.OneCell

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Mills
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.Mills
open OneCell

lemma tail_pos (x : ℝ) : 0 < tail x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (Real.exp_pos _).le)) density_integrable.integrableOn).mpr
  simp [Function.support, Real.exp_ne_zero]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-density x) x := by
  have heq : tail = fun a => tail 0 - ∫ t in (0:ℝ)..a, density t := by
    funext a
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := 0) (b := a) density_integrable.integrableOn density_integrable.integrableOn
    change tail 0-tail a = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (density_integrable.intervalIntegrable)
    (by exact (show StronglyMeasurable density by unfold density; fun_prop).stronglyMeasurableAtFilter) (hasDerivAt_density x).continuousAt).const_sub _

lemma barrier_pos {x : ℝ} (hx : 0 ≤ x) : 0 < barrier x := by
  unfold barrier
  have : 0 < Real.sqrt (x^2+8) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma tail_le_barrier {x : ℝ} (hx : 0 ≤ x) : tail x ≤ density x / barrier x :=
  gaussian_tail_le_sampford hx

lemma lambda_ge_barrier {x : ℝ} (hx : 0 ≤ x) : barrier x ≤ lambda x := by
  rw [lambda, le_div_iff₀ (tail_pos x)]
  have hh := (le_div_iff₀ (barrier_pos hx)).mp (tail_le_barrier hx)
  linarith only [hh]

lemma lambda_pos (x : ℝ) : 0 < lambda x := div_pos (Real.exp_pos _) (tail_pos x)

lemma hasDerivAt_lambda (x : ℝ) : HasDerivAt lambda (lambda x*(lambda x-x)) x := by
  convert (hasDerivAt_density x).div (hasDerivAt_tail x) (tail_pos x).ne' using 1 <;>
    first | rfl | (unfold lambda; field_simp [(tail_pos x).ne']; ring)

lemma hasDerivAt_G (x : ℝ) : HasDerivAt G
    (lambda x*((lambda x-x)*(2*lambda x-x)-1)) x := by
  convert (hasDerivAt_lambda x).mul ((hasDerivAt_lambda x).sub (hasDerivAt_id x)) using 1 <;>
    first | rfl | (dsimp; ring)

lemma G_monotone : MonotoneOn G (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun x _ => (hasDerivAt_G x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_G x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  apply mul_nonneg (lambda_pos x).le
  have hl := lambda_ge_barrier hx'
  have hs := Real.sq_sqrt (show 0 ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hb : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx']
  have hprod := mul_nonneg (sub_nonneg.mpr hl)
    (show 0 ≤ 2*lambda x+2*barrier x-3*x by unfold barrier at *; linarith only [hl,hb,hx'])
  unfold barrier at hprod
  nlinarith only [hprod,hs]

lemma G_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G x := by
  apply mul_nonneg (lambda_pos x).le
  have hb := lambda_ge_barrier hx
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hh : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx]
  dsimp [barrier] at hb
  linarith only [hb,hh]

lemma G_le_one (x : ℝ) : G x ≤ 1 :=
  inverse_mills_ratio_deriv_le_one x

end GaussianPropeller.Mills

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.Taylor

lemma E_zero (n : ℕ) : E n 0 = 1 := by
  unfold E
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

lemma exp_remainder {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ c : ℝ, Real.exp (-x)-E n x =
      (-1:ℝ)^(n+1)*Real.exp (-c)*x^(n+1)/(Nat.factorial (n+1)) := by
  obtain ⟨c,hc,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun t : ℝ => Real.exp ((-1)*t)) (x₀ := 0) (x := x) (n := n) hx.ne
    (by fun_prop)
  refine ⟨c, ?_⟩
  have he : taylorWithinEval (fun t : ℝ => Real.exp ((-1)*t)) n (uIcc 0 x) 0 x = E n x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.ne)
      (by fun_prop) (by simp), iteratedDeriv_exp_const_mul]
    simp only [mul_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
    ring
  rw [he, iteratedDeriv_exp_const_mul] at h
  simpa only [neg_one_mul, sub_zero, mul_assoc] using h

lemma exp_le_E_even (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ E (2*n) x := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n)
  have hn : (-1:ℝ)^(2*n+1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hn] at h
  have : (-1:ℝ)*Real.exp (-c)*x^(2*n+1)/(Nat.factorial (2*n+1)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.exp_pos (-c)]) (pow_nonneg hx _)
    · positivity
  linarith only [h,this]

lemma E_odd_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : E (2*n+1) x ≤ Real.exp (-x) := by
  obtain rfl | hp := hx.eq_or_lt
  · simp [E_zero]
  obtain ⟨c,h⟩ := exp_remainder hp (2*n+1)
  have hn : (-1:ℝ)^(2*n+1+1) = 1 := by rw [show 2*n+1+1=2*(n+1) by omega, pow_mul]; norm_num
  rw [hn] at h
  have : 0 ≤ (1:ℝ)*Real.exp (-c)*x^(2*n+1+1)/(Nat.factorial (2*n+1+1)) := by positivity
  linarith only [h,this]

lemma hasDerivAt_J (n : ℕ) (x : ℝ) : HasDerivAt (J n) (E n (x^2/2)) x := by
  unfold J E
  convert! HasDerivAt.sum (u := Finset.range (n+1)) (fun k hk =>
    (((hasDerivAt_pow (2*k+1) x).const_mul ((-1:ℝ)^k)).div_const
      ((2:ℝ)^k*(Nat.factorial k)*(2*k+1)))) using 1
  · funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hk' : (2*(k:ℝ)+1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [div_pow, pow_mul]
    field_simp

lemma J_zero (n : ℕ) : J n 0 = 0 := by simp [J]

lemma integral_E (n : ℕ) (x : ℝ) :
    ∫ t in (0:ℝ)..x, E n (t^2/2) = J n x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_J n t)
    (show IntervalIntegrable (fun t : ℝ => E n (t^2/2)) volume 0 x from
      (by unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _))
  simpa only [J_zero, sub_zero] using h

lemma integral_exp_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    J (2*n+1) x ≤ (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ∧
      (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ≤ J (2*n) x := by
  have hi (k : ℕ) : IntervalIntegrable (fun t : ℝ => E k (t^2/2)) volume 0 x := by
    unfold E; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have he : IntervalIntegrable (fun t : ℝ => Real.exp (-t^2/2)) volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  constructor
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx (hi _) he
    intro t ht
    simpa only [neg_div] using E_odd_le_exp n (show (0:ℝ) ≤ t^2/2 by positivity)
  · rw [← integral_E]
    apply intervalIntegral.integral_mono_on hx he (hi _)
    intro t ht
    simpa only [neg_div] using exp_le_E_even n (show (0:ℝ) ≤ t^2/2 by positivity)
end GaussianPropeller.Taylor

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ProbabilityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor

lemma gaussianConst_tight : (398942/1000000:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  refine ⟨?_, gaussianConst_bounds.2⟩
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
  have hh := Real.pi_lt_d6
  nlinarith

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

lemma p_antitone : Antitone p := by
  apply antitone_of_hasDerivAt_nonpos (fun x => hasDerivAt_p x)
  intro x
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [gaussianConst_tight.1]) (Real.exp_pos _).le

lemma p_taylor_lower {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n) x) :
    1/2-(398943/1000000:ℝ)*J (2*n) x ≤ p x := by
  have hh := (integral_exp_bounds n hx).2
  change (∫ t in (0:ℝ)..x, density t) ≤ J (2*n) x at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.2 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma p_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n+1) x) :
    p x ≤ 1/2-(398942/1000000:ℝ)*J (2*n+1) x := by
  have hh := (integral_exp_bounds n hx).1
  change J (2*n+1) x ≤ ∫ t in (0:ℝ)..x, density t at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.1 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma lambda_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hJ : 0 ≤ J (2*n) x)
    (hc : (398943/1000000:ℝ)*E (2*n) (x^2/2) ≤
      L*(1/2-(398943/1000000:ℝ)*J (2*n) x)) : lambda x ≤ L := by
  have he := exp_le_E_even n (show 0 ≤ x^2/2 by positivity)
  rw [← neg_div] at he
  change density x ≤ E (2*n) (x^2/2) at he
  have hd : 0 ≤ density x := (Real.exp_pos _).le
  have hmul := mul_le_mul he gaussianConst_tight.2
    (le_trans (by norm_num) gaussianConst_tight.1) (hd.trans he)
  have ht := mul_le_mul_of_nonneg_left (p_taylor_lower hx n hJ) hL
  have hpos : 0 < gaussianConst := lt_of_lt_of_le (by norm_num) gaussianConst_tight.1
  rw [lambda, div_le_iff₀ (tail_pos x)]
  apply (mul_le_mul_iff_right₀ hpos).mp
  dsimp [p] at ht
  nlinarith only [hmul,hc,ht]

lemma G_upper_of_lambda {x L U : ℝ} (hx : 0 ≤ x) (h : lambda x ≤ L)
    (hLU : L*(L-x) ≤ U) : G x ≤ U := by
  have hl : 0 ≤ lambda x-x := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx)
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ L+lambda x-x by linarith [lambda_pos x])
  unfold G
  nlinarith only [hh,hLU]

lemma certificate_005 : p (2.1) < (0.415+0.15*0.05)*0.05 ∧ G (2.1) ≤ 0.91 := by
  have hj12 : 0 ≤ J 12 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 2.1) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (2.1) < (0.415+0.15*0.05)*0.05 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 2.1) (L := 2.463)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_014 : p (1.6) < (0.415+0.15*0.14)*0.14 ∧ G (1.6) ≤ 0.87 := by
  have hj12 : 0 ≤ J 12 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.6) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.6) < (0.415+0.15*0.14)*0.14 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.6) (L := 2.025)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_024 : p (1.3) < (0.415+0.15*0.24)*0.24 ∧ G (1.3) ≤ 0.836 := by
  have hj12 : 0 ≤ J 12 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.3) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.3) < (0.415+0.15*0.24)*0.24 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.3) (L := 1.771)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_033 : p (1.04) < (0.415+0.15*0.33)*0.33 ∧ G (1.04) ≤ 0.809 := by
  have hj12 : 0 ≤ J 12 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.04) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.04) < (0.415+0.15*0.33)*0.33 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.04) (L := 1.558)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_041 : p (0.87) < (0.415+0.15*0.41)*0.41 ∧ G (0.87) ≤ 0.788 := by
  have hj12 : 0 ≤ J 12 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.87) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.87) < (0.415+0.15*0.41)*0.41 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.87) (L := 1.423)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_048 : p (0.74) < (0.415+0.15*0.48)*0.48 ∧ G (0.74) ≤ 0.771 := by
  have hj12 : 0 ≤ J 12 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.74) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.74) < (0.415+0.15*0.48)*0.48 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.74) (L := 1.322)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_054 : p (0.63) < (0.415+0.15*0.54)*0.54 ∧ G (0.63) ≤ 0.756 := by
  have hj12 : 0 ≤ J 12 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.63) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.63) < (0.415+0.15*0.54)*0.54 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.63) (L := 1.238)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_059 : p (0.55) < (0.415+0.15*0.59)*0.59 ∧ G (0.55) ≤ 0.743 := by
  have hj12 : 0 ≤ J 12 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.55) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.55) < (0.415+0.15*0.59)*0.59 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.55) (L := 1.178)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_064 : p (0.47) < (0.415+0.15*0.64)*0.64 ∧ G (0.47) ≤ 0.73 := by
  have hj12 : 0 ≤ J 12 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.47) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.47) < (0.415+0.15*0.64)*0.64 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.47) (L := 1.120)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma exists_p {P : ℝ} (hP : 0 < P) (hPh : P ≤ 1/2) : ∃ x ≥ (0:ℝ), p x=P := by
  have ht : Tendsto p atTop (𝓝 0) := by
    convert! (tendsto_integral_Ioi_zero (f := density) (μ := volume) tendsto_id).const_mul gaussianConst using 1
    simp only [mul_zero]
  have hh := isPreconnected_Ici.intermediate_value_Ioc (a := (0:ℝ)) self_mem_Ici
    (le_principal_iff.mpr (Ici_mem_atTop (0:ℝ)))
    (show ContinuousOn p (Ici 0) from fun x _ => (hasDerivAt_p x).continuousAt.continuousWithinAt) ht
  have hm : P ∈ Ioc 0 (p 0) := by exact ⟨hP, by simpa [p,tail_zero] using hPh⟩
  exact hh hm

lemma loss_eq (x : ℝ) : loss x=gaussianConst^2*density x*(density x-x*tail x) := by
  unfold loss p G lambda
  field_simp [(tail_pos x).ne']

lemma hasDerivAt_loss (x : ℝ) : HasDerivAt loss
    (gaussianConst^2*density x*(x^2*tail x-x*density x-tail x)) x := by
  have he : loss = fun x => gaussianConst^2*density x*(density x-x*tail x) := funext loss_eq
  rw [he]
  convert ((hasDerivAt_density x).const_mul (gaussianConst^2)).mul
    ((hasDerivAt_density x).sub ((hasDerivAt_id x).mul (hasDerivAt_tail x))) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply, Pi.mul_apply, id_eq]; ring)

lemma loss_antitone : AntitoneOn loss (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun x _ => (hasDerivAt_loss x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_loss x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  have hl : x ≤ lambda x := by
    have hh := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx')
    linarith only [hh]
  rw [lambda, le_div_iff₀ (tail_pos x)] at hl
  apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left hl hx'
  have ht : 0 < tail x := tail_pos x
  have hm : 0 ≤ x*density x := mul_nonneg hx' (Real.exp_pos _).le
  nlinarith only [hh,ht,hm]

lemma G_test_bound {a r x w U : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hx : 0 ≤ x) (hw : 0 ≤ w) (hp : p x=(0.415+0.15*r)*r)
    (hc : p w < (0.415+0.15*a)*a ∧ G w ≤ U) : G x ≤ U := by
  have hpw : p w < p x := by
    rw [hp]
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by linarith)
    nlinarith only [hc.1,har,hm]
  have hxw : x ≤ w := by
    by_contra! hgt
    exact (not_lt_of_ge (p_antitone hgt.le)) hpw
  exact (G_monotone hx hw hxw).trans hc.2

lemma row_margin {a b r x U S : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hrb : r ≤ b)
    (hb : b ≤ 2/3) (hU : 0 ≤ U) (hG : G x ≤ U) (hS : 0 ≤ S)
    (hSsq : 1-a^2 ≤ S^2)
    (hc : U*(0.415+0.15*b)^2 < (9/(8*3.1416:ℝ))/(1+S)) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  have hr : 0 ≤ r := ha.trans har
  have hr2 : r^2 ≤ (1:ℝ) := by nlinarith only [hr,hrb,hb]
  have hs := Real.sq_sqrt (show 0 ≤ 1-r^2 by linarith only [hr2])
  have hsp := Real.sqrt_nonneg (1-r^2)
  have hsq : Real.sqrt (1-r^2) ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by positivity)
    nlinarith only [hs,hsp,hSsq,hS,hm]
  have hbcoef : (0.415+0.15*r)^2 ≤ (0.415+0.15*b)^2 := by
    nlinarith only [hr,hrb, sq_nonneg (b-r)]
  have hh₁ := mul_le_mul_of_nonneg_left hG (sq_nonneg (0.415+0.15*r))
  have hh₂ := mul_le_mul_of_nonneg_right hbcoef hU
  have hB : (9/(8*3.1416:ℝ)) ≤ 9/(8*Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [Real.pi_lt_d4])
  have hd₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9/(8*3.1416))
    (show 0 < 1+Real.sqrt (1-r^2) by positivity) (show 1+Real.sqrt (1-r^2) ≤ 1+S by linarith only [hsq])
  have hd₂ := div_le_div_of_nonneg_right hB (show 0 ≤ 1+Real.sqrt (1-r^2) by positivity)
  have hc' : (0.415+0.15*b)^2*U < (9/(8*3.1416:ℝ))/(1+S) := by simpa only [mul_comm] using hc
  exact lt_of_le_of_lt (hh₁.trans hh₂) (lt_of_lt_of_le hc' (hd₁.trans hd₂))

lemma test_probability {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hp : p x=(0.415+0.15*r)*r) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  by_cases h0 : r ≤ 0.05
  · apply row_margin (a := 0) (b := 0.05) (U := 1) (S := 1)
    · norm_num
    · exact hr.le
    · exact h0
    · norm_num
    · norm_num
    · exact G_le_one x
    · norm_num
    · norm_num
    · norm_num
  by_cases h1 : r ≤ 0.14
  · apply row_margin (a := 0.05) (b := 0.14) (U := 0.91) (S := 0.99875)
    · norm_num
    · exact (lt_of_not_ge h0).le
    · exact h1
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h0).le hx (by norm_num) hp certificate_005
    · norm_num
    · norm_num
    · norm_num
  by_cases h2 : r ≤ 0.24
  · apply row_margin (a := 0.14) (b := 0.24) (U := 0.87) (S := 0.99016)
    · norm_num
    · exact (lt_of_not_ge h1).le
    · exact h2
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h1).le hx (by norm_num) hp certificate_014
    · norm_num
    · norm_num
    · norm_num
  by_cases h3 : r ≤ 0.33
  · apply row_margin (a := 0.24) (b := 0.33) (U := 0.836) (S := 0.97078)
    · norm_num
    · exact (lt_of_not_ge h2).le
    · exact h3
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h2).le hx (by norm_num) hp certificate_024
    · norm_num
    · norm_num
    · norm_num
  by_cases h4 : r ≤ 0.41
  · apply row_margin (a := 0.33) (b := 0.41) (U := 0.809) (S := 0.94399)
    · norm_num
    · exact (lt_of_not_ge h3).le
    · exact h4
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h3).le hx (by norm_num) hp certificate_033
    · norm_num
    · norm_num
    · norm_num
  by_cases h5 : r ≤ 0.48
  · apply row_margin (a := 0.41) (b := 0.48) (U := 0.788) (S := 0.91209)
    · norm_num
    · exact (lt_of_not_ge h4).le
    · exact h5
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h4).le hx (by norm_num) hp certificate_041
    · norm_num
    · norm_num
    · norm_num
  by_cases h6 : r ≤ 0.54
  · apply row_margin (a := 0.48) (b := 0.54) (U := 0.771) (S := 0.87727)
    · norm_num
    · exact (lt_of_not_ge h5).le
    · exact h6
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h5).le hx (by norm_num) hp certificate_048
    · norm_num
    · norm_num
    · norm_num
  by_cases h7 : r ≤ 0.59
  · apply row_margin (a := 0.54) (b := 0.59) (U := 0.756) (S := 0.84167)
    · norm_num
    · exact (lt_of_not_ge h6).le
    · exact h7
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h6).le hx (by norm_num) hp certificate_054
    · norm_num
    · norm_num
    · norm_num
  by_cases h8 : r ≤ 0.64
  · apply row_margin (a := 0.59) (b := 0.64) (U := 0.743) (S := 0.80741)
    · norm_num
    · exact (lt_of_not_ge h7).le
    · exact h8
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h7).le hx (by norm_num) hp certificate_059
    · norm_num
    · norm_num
    · norm_num
  apply row_margin (a := 0.64) (b := (2/3)) (U := 0.73) (S := 0.76838)
  · norm_num
  · exact (lt_of_not_ge h8).le
  · exact hrcap
  · norm_num
  · norm_num
  · exact G_test_bound (by norm_num) (lt_of_not_ge h8).le hx (by norm_num) hp certificate_064
  · norm_num
  · norm_num
  · norm_num

lemma linear_quadratic_of_loss {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hc : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) ≤ loss x) :
    0.415*r+0.15*r^2 < p x := by
  let P₀ := (0.415+0.15*r)*r
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hP₀h : P₀ ≤ 1/2 := by dsimp [P₀]; nlinarith only [hr,hrcap]
  obtain ⟨y,hy,hPy⟩ := exists_p hP₀ hP₀h
  have ht := test_probability hr hrcap hy hPy
  have ht' := mul_lt_mul_of_pos_right ht (sq_pos_of_pos hr)
  have htest : loss y < (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) := by
    unfold loss
    rw [hPy]
    dsimp [P₀] at *
    calc
      _ = (0.415+0.15*r)^2*G y*r^2 := by ring
      _ < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2))*r^2 := ht'
      _ = _ := by ring
  by_contra! hh
  have hpx : p x ≤ p y := by rw [hPy]; dsimp [P₀]; nlinarith only [hh]
  have hyx : y ≤ x := by
    by_contra! hgt
    have hd : StrictAnti p := strictAnti_of_hasDerivAt_neg (fun z => hasDerivAt_p z)
      (fun z => mul_neg_of_neg_of_pos (by linarith [gaussianConst_tight.1]) (Real.exp_pos _))
    exact (not_lt_of_ge hpx) (hd hgt)
  have hh' := loss_antitone hy hx hyx
  exact (not_lt_of_ge (hc.trans hh')) htest

end GaussianPropeller.ProbabilityBounds

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic

theorem integral_pos_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hd (x : ℝ) : HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    apply (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv
    field_simp [hb']
    ring
  have ht : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1
  simp

theorem integral_abs_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, |r| * Real.exp (-b * r ^ 2) = b⁻¹ := by
  let f : ℝ → ℝ := fun r => |r| * Real.exp (-b * r ^ 2)
  have hf : Integrable f := by
    simpa only [f, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).abs
  have hpos : ∫ r in Ioi 0, f r = (2 * b)⁻¹ := by
    rw [← integral_pos_mul_exp hb]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
      simp only [f, abs_of_pos (show (0 : ℝ) < r from hr)])
  have hneg : ∫ r in Iic 0, f r = ∫ r in Ioi 0, f r := by
    calc
      ∫ r in Iic 0, f r = ∫ r in Ioi 0, f (-r) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r in Ioi 0, f r := by simp only [f, abs_neg, neg_sq]
  change (∫ r, f r) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos]
  field_simp
  ring

theorem integral_abs_gaussianReal_std :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
    rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [hfun, integral_const_mul, integral_abs_mul_exp (by norm_num : (0 : ℝ) < 1/2)]
  norm_num
  ring

theorem integral_abs_dual_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    ∫ x, |L x| ∂stdGaussian E = ‖L‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  have hm : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => |x|) ((stdGaussian E).map L)), hm,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul, integral_abs_gaussianReal_std]

theorem integral_abs_inner_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    ∫ x, |⟪v, x⟫| ∂stdGaussian E = ‖v‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  simpa only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.norm_map] using
    integral_abs_dual_stdGaussian (InnerProductSpace.toDual ℝ E v)

end GaussianPropeller.Analytic

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Attainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem integral_comp_neg {d : ℕ} (f : Space d → ℝ) (hf : AEStronglyMeasurable f (gaussian d)) :
    ∫ x, f (-x) ∂gaussian d = ∫ x, f x ∂gaussian d := by
  have hm : (gaussian d).map (fun x => -x) = gaussian d :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rw [← integral_map (by fun_prop) (hm.symm ▸ hf), hm]

theorem centroid_norm_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖ ≤ 1 / Real.sqrt (2 * Real.pi) := by
  let z := centroid A
  let f : Space d → ℝ := fun x => ⟪z, x⟫
  have hi : Integrable f (gaussian d) := (integrable_id_gaussian d).const_inner z
  have he : ∫ x, (A.indicator f) x ∂gaussian d = ‖z‖^2 := by
    rw [integral_indicator hA]
    change (∫ x in A, ⟪z, x⟫ ∂gaussian d) = _
    rw [integral_inner (integrable_id_restrict d A)]
    exact real_inner_self_eq_norm_sq z
  have hz : ∫ x, f x ∂gaussian d = 0 := by
    change (∫ x, ⟪z, x⟫ ∂gaussian d) = 0
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  have hab : ∫ x, |f x| ∂gaussian d = ‖z‖ * (2 / Real.sqrt (2 * Real.pi)) :=
    Analytic.integral_abs_inner_stdGaussian z
  have hp (x : Space d) : A.indicator f x ≤ (|f x| + f x) / 2 := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      linarith only [le_abs_self (f x)]
    · rw [Set.indicator_of_notMem hx]
      linarith only [neg_abs_le (f x)]
  have h := integral_mono_ae (hi.indicator hA) ((hi.abs.add hi).div_const 2)
    (Filter.Eventually.of_forall hp)
  rw [he, integral_div] at h
  change ‖z‖^2 ≤ (∫ x, |f x| + f x ∂gaussian d) / 2 at h
  rw [integral_add hi.abs hi, hab, hz, add_zero] at h
  have hn := norm_nonneg z
  have hq : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hn' : ‖z‖^2 ≤ (1 / Real.sqrt (2 * Real.pi)) * ‖z‖ := by
    convert h using 1; ring
  nlinarith only [hn, hq, hn']

theorem centroid_norm_sq_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖^2 ≤ 1 / (2 * Real.pi) := by
  have h := (sq_le_sq₀ (norm_nonneg (centroid A)) (by positivity :
      0 ≤ 1 / Real.sqrt (2 * Real.pi))).mpr (centroid_norm_le hA)
  simpa only [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)] using h

theorem normalized_centroid_lt_two_thirds {d : ℕ} {A : Set (Space d)}
    (hA : MeasurableSet A) {C : ℝ} (hC : 9 / (8 * Real.pi) < C) :
    ‖centroid A‖ / Real.sqrt C < 2 / 3 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hCp : 0 < C := (by positivity : (0 : ℝ) < 9 / (8 * Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hn := centroid_norm_sq_le hA
  have hC' : 9 < C * (8 * Real.pi) := (div_lt_iff₀ (by positivity)).mp hC
  have hn' : ‖centroid A‖^2 * (2 * Real.pi) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hn
  have hsq : 9 * ‖centroid A‖^2 < 4 * C := by nlinarith only [hC', hn', hp]
  apply (div_lt_iff₀ ht).mpr
  have ht2 := Real.sq_sqrt hCp.le
  have hz := norm_nonneg (centroid A)
  nlinarith only [hsq, ht2, hz, ht]

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CellBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

lemma winning_inner_nonneg (z : Fin k → Space d) (hz : ∑ j,z j=0)
    (i : Fin k) {x : Space d} (hx : x ∈ closedCell z i) : 0 ≤ ⟪z i,x⟫ := by
  have hh : (0:ℝ) ≤ ∑ j : Fin k, (⟪z i,x⟫-⟪z j,x⟫) :=
    Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hx j))
  have hz' : (∑ j,⟪z j,x⟫)=0 := by rw [← sum_inner,hz,inner_zero_left]
  rw [Finset.sum_sub_distrib, hz', sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact nonneg_of_mul_nonneg_right hh (by exact_mod_cast (NeZero.pos k))

lemma active_probability_mem (_hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) : 0 < (gaussian d).real (A i) ∧ (gaussian d).real (A i) ≤ 1/2 := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  have hP : 0 < (gaussian d).real (A i) := ENNReal.toReal_pos hi (measure_ne_top _ _)
  have hzn : centroid (A i) ≠ 0 := active_centroid_ne_zero hA hpos hi
  let e : Space d := - (‖centroid (A i)‖⁻¹ • centroid (A i))
  have he : ‖e‖=1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hmap := OneCell.map_unit_inner_gaussian e he
  have hs : closedCell (fun j => centroid (A j)) i ⊆ {x | ⟪e,x⟫ ≤ 0} := by
    intro x hx
    have hn := winning_inner_nonneg (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i hx
    simp only [Set.mem_ofPred_eq,e,inner_neg_left,real_inner_smul_left]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hn)
  have heq : (gaussian d) {x | ⟪e,x⟫ ≤ 0} = (gaussianReal 0 1) (Iic 0) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  refine ⟨hP, ?_⟩
  have hh := measure_mono (μ:=gaussian d) hs
  rw [← measure_congr (active_eq_closedCell_ae hA hpos hi), heq] at hh
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  change (gaussian d).real (A i) ≤ (gaussianReal 0 1).real (Iic 0) at hh'
  rw [← Φ_eq_gaussianReal, Φ_zero] at hh'
  exact hh'

lemma p_eq_Φ_neg (x : ℝ) : p x=Φ (-x) := by
  rw [Φ_neg, Φ_eq_one_sub_tail]
  simp only [φ, OneCell.gaussianConst, p, OneCell.tail, OneCell.density]
  rw [integral_const_mul]
  ring

lemma loss_eq_quantile {P : ℝ} (_hP : P ∈ Ioo (0:ℝ) 1) {x : ℝ} (hx : p x=P) :
    loss x = φ (q P)*(q P*P+φ (q P)) := by
  have hq : q P = -x := by rw [← hx, p_eq_Φ_neg, q_Φ]
  rw [hq, φ_neg, loss_eq]
  rw [← hx]
  simp only [p, φ, OneCell.gaussianConst, OneCell.density]
  ring

lemma loss_rationalize {C α r L : ℝ} (_hC : 0 < C) (hα : 0 < α)
    (_hr : 0 ≤ r) (hs : 0 ≤ 1-α*r^2)
    (hl : C*(1-Real.sqrt (1-α*r^2)) ≤ α*L) :
    C*r^2/(1+Real.sqrt (1-α*r^2)) ≤ L := by
  have hq := Real.sqrt_nonneg (1-α*r^2)
  have hq2 := Real.sq_sqrt hs
  rw [div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+Real.sqrt (1-α*r^2) by positivity)
  have heq : C*(1-Real.sqrt (1-α*r^2))*(1+Real.sqrt (1-α*r^2)) = α*(C*r^2) := by
    calc
      _ = C*(1-Real.sqrt (1-α*r^2)^2) := by ring
      _ = _ := by rw [hq2]; ring
  rw [heq] at hm
  exact (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_assoc] using hm)

lemma minimal_loss_constraint (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (value A)*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-((k:ℝ)/((k:ℝ)-1))*(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  let C := value A
  let r := ‖centroid (A i)‖/Real.sqrt C
  let α := (k:ℝ)/((k:ℝ)-1)
  have hCp : 0 < C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 0<α := div_pos (by linarith) (by linarith)
  have hP := active_probability_mem hk hA hCp (hall i)
  obtain ⟨x,hx,hpx⟩ := exists_p hP.1 hP.2
  refine ⟨x,hx,hpx,?_⟩
  have hl := (optimal_loss_lower hk hA.1 i).trans (minimal_loss_upper hk hA hCp hall i)
  rw [mul_assoc, ← loss_eq_quantile ⟨hP.1,by linarith [hP.2]⟩ hpx] at hl
  have hsq : ‖centroid (A i)‖^2 = C*r^2 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hCp.le]
    field_simp
  have hnon : 0 ≤ C-α*‖centroid (A i)‖^2 := by
    change 0 ≤ (∑ j, ‖centroid (A j)‖^2) - ((k:ℝ)/((k:ℝ)-1))*‖centroid (A i)‖^2
    rw [← recentered_norm_sq hk (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i]
    positivity
  have hs : 0 ≤ 1-α*r^2 := by
    rw [hsq] at hnon
    nlinarith only [hnon,hCp]
  have hsqrt : Real.sqrt (C-α*‖centroid (A i)‖^2) = Real.sqrt C*Real.sqrt (1-α*r^2) := by
    rw [hsq, show C-α*(C*r^2)=C*(1-α*r^2) by ring, Real.sqrt_mul hCp.le]
  change C-Real.sqrt C*Real.sqrt (C-α*‖centroid (A i)‖^2) ≤ α*loss x at hl
  rw [hsqrt] at hl
  have ht := Real.sq_sqrt hCp.le
  apply loss_rationalize hCp hα (by positivity : 0≤r) hs
  have he : C-Real.sqrt C*(Real.sqrt C*Real.sqrt (1-α*r^2)) = C*(1-Real.sqrt (1-α*r^2)) := by
    rw [←mul_assoc, ←pow_two, ht]; ring
  rwa [he] at hl

lemma minimal_universal_loss (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (9/(8*Real.pi))*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  obtain ⟨x,hx,hp,hl⟩ := minimal_loss_constraint hk hA hC hall i
  refine ⟨x,hx,hp, le_trans ?_ hl⟩
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 1≤(k:ℝ)/((k:ℝ)-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hα) (sq_nonneg (‖centroid (A i)‖/Real.sqrt (value A)))]

lemma minimal_linear_quadratic (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    0.415*(‖centroid (A i)‖/Real.sqrt (value A))+
      0.15*(‖centroid (A i)‖/Real.sqrt (value A))^2 < (gaussian d).real (A i) := by
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨x,hx,hp,hl⟩ := minimal_universal_loss hk hA hC hall i
  rw [← hp]
  exact linear_quadratic_of_loss (div_pos (norm_pos_iff.mpr (active_centroid_ne_zero hA hCp (hall i)))
      (Real.sqrt_pos.mpr hCp)) (normalized_centroid_lt_two_thirds (hA.1.1.1 i) hC).le hx hl

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.GaussianCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic
section FamilyLaw
variable {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u,x⟫, fun x => ⟪v,x⟫; stdGaussian E] = ⟪u,v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

lemma hasGaussianLaw_innerFamily (v : ι → E) :
    HasGaussianLaw (fun x : E => fun i => ⟪v i,x⟫) (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => InnerProductSpace.toDual ℝ E (v i)))

lemma indep_innerFamily (v : ι → E) (hv : Pairwise (fun i j => ⟪v i,v j⟫ = 0)) :
    iIndepFun (fun i x => ⟪v i,x⟫) (stdGaussian E) := by
  exact (hasGaussianLaw_innerFamily v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => (covariance_inner_stdGaussian _ _).trans (hv hij))

lemma map_inner_stdGaussian (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map]

lemma map_orthonormal_stdGaussian (v : ι → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i,x⟫) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  rw [hi.map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [map_inner_stdGaussian, hv.1 i]
  norm_num

end FamilyLaw

end GaussianPropeller.Analytic

namespace GaussianPropeller.Analytic

open scoped ENNReal

section TripleLaw
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_orthonormal_triple_stdGaussian (v : Fin 3 → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => (⟪v 0,x⟫, ⟪v 1,x⟫, ⟪v 2,x⟫)) =
      (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  have hm (i : Fin 3) : (stdGaussian E).map (fun x => ⟪v i,x⟫) = gaussianReal 0 1 := by
    rw [map_inner_stdGaussian, hv.1 i]
    norm_num
  have hp := hi.indepFun_prodMk (fun _ => by fun_prop) 1 2 0 (by decide) (by decide)
  rw [hp.symm.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hm,
    (hi.indepFun (by decide : (1:Fin 3) ≠ 2)).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop), hm, hm]

lemma lintegral_orthonormal_triple (v : Fin 3 → E) (hv : Orthonormal ℝ v)
    (f : ℝ × ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (⟪v 0,x⟫,⟪v 1,x⟫,⟪v 2,x⟫) ∂stdGaussian E =
      ∫⁻ s : ℝ, (∫⁻ u : ℝ, (∫⁻ w : ℝ, f (s,u,w) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
  rw [← lintegral_map hf (by fun_prop), map_orthonormal_triple_stdGaussian v hv,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro s
  exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable

end TripleLaw
end GaussianPropeller.Analytic

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.PairIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairIntegral

lemma integrableOn_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Ici 0) := by
  by_cases hb : 0 ≤ b
  · have hi : IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Icc 0 b) :=
      (by fun_prop : Continuous (fun x : ℝ => (max (b-x) 0)^n)).integrableOn_Icc
    have hz : IntegrableOn (fun x : ℝ => (max (b-x) 0)^n) (Ioi b) := by
      apply integrableOn_zero.congr_fun _ measurableSet_Ioi
      intro x hx
      have hx' : b ≤ x := le_of_lt hx
      simp only [max_eq_right (sub_nonpos.mpr hx'), zero_pow hn]
    simpa [Icc_union_Ioi_eq_Ici hb] using hi.union hz
  · apply integrableOn_zero.congr_fun _ measurableSet_Ici
    intro x hx
    have hx' : 0 ≤ x := hx
    simp only [max_eq_right (by linarith : b-x ≤ 0), zero_pow hn]

lemma integral_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∫ x : ℝ in Ici 0, (max (b-x) 0)^n = (max b 0)^(n+1)/(n+1) := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici (show Icc 0 b ⊆ Ici 0 from fun _ hx => hx.1)]
    · rw [setIntegral_congr_fun measurableSet_Icc (fun x hx =>
        congrArg (fun z : ℝ => z^n) (max_eq_left (by linarith [hx.2] : 0 ≤ b-x)))]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) b]
      simp [integral_pow]
    · intro x hx
      have hxb : b < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1,h⟩)
      simp [max_eq_right (by linarith : b-x ≤ 0), hn]
  · rw [max_eq_right (le_of_not_ge hb)]
    simp only [zero_pow (Nat.succ_ne_zero n), zero_div]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hx' : 0 ≤ x := hx
    simp only [max_eq_right (by linarith : b-x ≤ 0), zero_pow hn]

lemma lintegral_pos_sub_pow (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ x : ℝ in Ici 0, ENNReal.ofReal ((max (b-x) 0)^n) =
      ENNReal.ofReal ((max b 0)^(n+1)/(n+1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_pos_sub_pow b hn)
    (ae_of_all _ (fun _ => pow_nonneg (le_max_right _ _) _)), integral_pos_sub_pow b hn]

lemma lintegral_triangle_shifted (s : ℝ) :
    ∫⁻ a : ℝ in Ici 0, ∫⁻ b : ℝ in Ici 0,
      ENNReal.ofReal (max (3*s-a-b) 0) = ENNReal.ofReal ((max (3*s) 0)^3/6) := by
  have hl (c : ℝ) : ∫⁻ b : ℝ in Ici 0, ENNReal.ofReal (max (c-b) 0) =
      ENNReal.ofReal ((max c 0)^2/2) := by
    simpa only [pow_one, Nat.cast_one, one_add_one_eq_two] using
      lintegral_pos_sub_pow c (by decide : (1:ℕ) ≠ 0)
  simp_rw [hl]
  simp_rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_pos_sub_pow _ (by decide : (2:ℕ) ≠ 0)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num
  ring

lemma gaussianPDF_std_le (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) := by
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have he : Real.exp (-(x^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

lemma lintegral_gaussian_std_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * ∫⁻ x, f x := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:NNReal) ≠ 0),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hf]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * f x :=
      lintegral_mono (fun x => by
        simpa only [mul_comm, Pi.mul_apply] using
          mul_le_mul_right (gaussianPDF_std_le x) (f x))
    _ = _ := lintegral_const_mul _ hf

lemma lintegral_affine_volume (f : ℝ → ℝ≥0∞) (hf : Measurable f) (b : ℝ)
    {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ x : ℝ, f (a*x+b) = ENNReal.ofReal |a⁻¹| * ∫⁻ u, f u := by
  have hm := lintegral_map (μ := (volume : Measure ℝ))
    (f := fun u => f (u+b)) (g := fun x => a*x)
    (by fun_prop) (by fun_prop)
  rw [← hm, Real.map_volume_mul_left ha, lintegral_smul_measure,
    lintegral_add_right_eq_self]
  rfl

lemma lintegral_affine_gaussian_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) (b : ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ x : ℝ, f (a*x+b) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((Real.sqrt (2*Real.pi)*a)⁻¹) * ∫⁻ u, f u := by
  calc
    _ ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) * ∫⁻ x : ℝ, f (a*x+b) :=
      lintegral_gaussian_std_le _ (by fun_prop)
    _ = _ := by
      rw [lintegral_affine_volume f hf b ha.ne', ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      simp only [abs_of_pos (inv_pos.mpr ha), mul_inv_rev, mul_comm]

lemma measurable_triangle : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 p.2.1 p.2.2) := by
  unfold triangle
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
      measurable_const) measurable_const

lemma lintegral_triangle (s : ℝ) :
    ∫⁻ u : ℝ, ∫⁻ v : ℝ, triangle s u v = ENNReal.ofReal ((max (3*s) 0)^3/6) := by
  calc
    _ = ∫⁻ a : ℝ, ∫⁻ b : ℝ, triangle s (s-a) (s-b) := by
      simp only [lintegral_sub_left_eq_self]
      exact (lintegral_sub_left_eq_self (fun u : ℝ => ∫⁻ v : ℝ, triangle s u v) s).symm
    _ = ∫⁻ a : ℝ in Ici 0, ∫⁻ b : ℝ in Ici 0,
        ENNReal.ofReal (max (3*s-a-b) 0) := by
      have hfun (a b : ℝ) : triangle s (s-a) (s-b) =
          (Ici (0:ℝ)).indicator (fun a => (Ici (0:ℝ)).indicator
            (fun b => ENNReal.ofReal (max (3*s-a-b) 0)) b) a := by
        simp only [triangle, Set.indicator, mem_Ici]
        simp only [show s-a ≤ s ↔ 0 ≤ a by constructor <;> intro h <;> linarith,
          show s-b ≤ s ↔ 0 ≤ b by constructor <;> intro h <;> linarith,
          show s+(s-a)+(s-b) = 3*s-a-b by ring]
      simp_rw [hfun]
      have hint (a : ℝ) :
          (∫⁻ b : ℝ, (Ici (0:ℝ)).indicator (fun a => (Ici (0:ℝ)).indicator
            (fun b => ENNReal.ofReal (max (3*s-a-b) 0)) b) a) =
          (Ici (0:ℝ)).indicator (fun a => ∫⁻ b : ℝ in Ici 0,
            ENNReal.ofReal (max (3*s-a-b) 0)) a := by
        by_cases ha : 0 ≤ a
        · simp only [Set.indicator, mem_Ici, ite_eq_left ha]
          simpa only [Set.indicator, mem_Ici] using lintegral_indicator measurableSet_Ici
            (fun b : ℝ => ENNReal.ofReal (max (3*s-a-b) 0))
        · simp only [Set.indicator, mem_Ici, ite_eq_right ha, lintegral_zero]
      simp_rw [hint]
      exact lintegral_indicator measurableSet_Ici _
    _ = _ := lintegral_triangle_shifted s

lemma lintegral_gaussian_pair_le (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f)
    (b : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ x : ℝ, (∫⁻ y : ℝ, f (a*x,b*x+c*y) ∂gaussianReal 0 1) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) * ∫⁻ u : ℝ, ∫⁻ v : ℝ, f (u,v) := by
  let k := ENNReal.ofReal ((Real.sqrt (2*Real.pi)*c)⁻¹)
  have hm : Measurable (fun u : ℝ => ∫⁻ v : ℝ, f (u,v)) := hf.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ x : ℝ, k * (∫⁻ v : ℝ, f (a*x,v)) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro x
      simpa only [add_comm, k] using lintegral_affine_gaussian_le
        (fun v => f (a*x,v)) (by fun_prop) (b*x) hc
    _ = k * (∫⁻ x : ℝ, (∫⁻ v : ℝ, f (a*x,v)) ∂gaussianReal 0 1) :=
      lintegral_const_mul k (hm.comp (by fun_prop))
    _ ≤ k * (ENNReal.ofReal ((Real.sqrt (2*Real.pi)*a)⁻¹) *
        ∫⁻ u : ℝ, ∫⁻ v : ℝ, f (u,v)) := by
      gcongr
      simpa only [add_zero] using lintegral_affine_gaussian_le _ hm 0 ha
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [← mul_inv]
      congr 1
      calc
        _ = (Real.sqrt (2*Real.pi))^2*a*c := by ring
        _ = _ := by rw [Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)]

lemma integral_pos_cube_gaussian :
    ∫ x : ℝ, (max x 0)^3 ∂gaussianReal 0 1 = 2/Real.sqrt (2*Real.pi) := by
  have hc : ∫ x : ℝ in Ioi 0, x^3*Real.exp (-(1/2:ℝ)*x^2) = 2 := by
    have hh := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1/2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.rpow_natCast, Real.rpow_neg, Real.Gamma_nat_eq_factorial] at hh
    simpa only [neg_mul] using hh
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have hf : (fun x : ℝ => gaussianPDFReal 0 1 x • (max x 0)^3) =
      (Real.sqrt (2*Real.pi))⁻¹ • (fun x : ℝ => (max x 0)^3*Real.exp (-(1/2:ℝ)*x^2)) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, Pi.smul_apply,
      smul_eq_mul]
    rw [show -(x^2)/2 = -(1/2:ℝ)*x^2 by ring]
    ring
  rw [hf]
  change (∫ x : ℝ, (Real.sqrt (2*Real.pi))⁻¹ * ((max x 0)^3*Real.exp (-(1/2:ℝ)*x^2))) = _
  rw [integral_const_mul]
  have hs : ∫ x : ℝ, (max x 0)^3*Real.exp (-(1/2:ℝ)*x^2) = 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))]
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
        rw [max_eq_left (le_of_lt hx)])]
      exact hc
    · intro x hx
      have hx' : x ≤ 0 := le_of_not_gt hx
      simp [max_eq_right hx']
  rw [hs]
  ring

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

lemma integrable_pos_cube_gaussian :
    Integrable (fun x : ℝ => (max x 0)^3) (gaussianReal 0 1) := by
  have hi : Integrable (fun x : ℝ => ‖x‖^3) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 3).integrable_norm_pow (by decide : (3:ℕ) ≠ 0)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) _)]
  apply pow_le_pow_left₀ (le_max_right _ _)
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma lintegral_pos_cube_gaussian :
    ∫⁻ x : ℝ, ENNReal.ofReal ((max x 0)^3) ∂gaussianReal 0 1 =
      ENNReal.ofReal (2/Real.sqrt (2*Real.pi)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_pos_cube_gaussian
    (ae_of_all _ (fun _ => pow_nonneg (le_max_right _ _) _)), integral_pos_cube_gaussian]

lemma lintegral_triangle_gaussian {a c : ℝ} (b : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ s : ℝ, (∫⁻ x : ℝ, (∫⁻ y : ℝ, triangle s (a*x) (b*x+c*y)
      ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal ((max (3*s) 0)^3/6)) := by fun_prop
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) *
        ENNReal.ofReal ((max (3*s) 0)^3/6) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro s
      exact (lintegral_gaussian_pair_le (fun p => triangle s p.1 p.2)
        (measurable_triangle.comp (measurable_const.prodMk measurable_id)) b ha hc).trans_eq
          (congrArg (ENNReal.ofReal ((2*Real.pi*a*c)⁻¹) * ·) (lintegral_triangle s))
    _ = _ := by
      have he (s : ℝ) : (max (3*s) 0)^3/6 = (9/2:ℝ)*(max s 0)^3 := by
        rw [show max (3*s) 0 = 3*max s 0 by
          by_cases hs : 0 ≤ s
          · rw [max_eq_left hs, max_eq_left (mul_nonneg (by norm_num) hs)]
          · rw [max_eq_right (le_of_not_ge hs), max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_ge hs)), mul_zero]]
        ring
      rw [lintegral_const_mul _ hm]
      simp_rw [he, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9/2)]
      rw [lintegral_const_mul _ (by fun_prop), lintegral_pos_cube_gaussian,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9/2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

end GaussianPropeller.PairIntegral

namespace GaussianPropeller.PairIntegral

lemma integral_le_of_lintegral_ofReal_le {X : Type uX} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal b) : ∫ x, f x ∂μ ≤ b := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_ofReal hb] at hh
  linarith only [hh, ENNReal.toReal_nonneg (a := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ)]

end GaussianPropeller.PairIntegral

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.PairBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma orthonormal_triple_of_gram_pos (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∃ (f : Fin 3 → E) (a b c : ℝ), Orthonormal ℝ f ∧
      f 0 = e ∧ 0 < a ∧ 0 < c ∧ u = a • f 1 ∧ v = b • f 1 + c • f 2 ∧
      (a*c)^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have hu : u ≠ 0 := by
    intro h
    simp [h] at hd
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let p : E := ‖u‖⁻¹ • u
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, ha.ne']
  have hu' : u = ‖u‖ • p := by simp [p, smul_smul, ha.ne']
  have hep : ⟪e,p⟫ = 0 := by simp [p, inner_smul_right, heu]
  let b : ℝ := ⟪p,v⟫
  let w : E := v-b • p
  have hpw : ⟪p,w⟫ = 0 := by
    simp [w, b, inner_sub_right, inner_smul_right, hp]
  have hew : ⟪e,w⟫ = 0 := by simp [w, inner_sub_right, inner_smul_right, hev, hep]
  have hd' : ‖u‖^2*‖w‖^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    have h : ‖w‖^2 = ‖v‖^2-b^2 := by
      rw [show w = v-b • p from rfl, norm_sub_sq_real, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, hp, one_pow, mul_one, inner_smul_right,
        real_inner_comm p v]
      dsimp [b]
      ring
    rw [h, hu', inner_smul_left, starRingEnd_apply, star_trivial]
    change _ = ‖‖u‖ • p‖^2 * ‖v‖^2 - (‖u‖ * b)^2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hp, mul_one]
    ring
  have hw : w ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero] at hd'
    linarith only [hd, hd']
  have hc : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let q : E := ‖w‖⁻¹ • w
  have hq : ‖q‖ = 1 := by simp [q, norm_smul, hc.ne']
  have hw' : w = ‖w‖ • q := by simp [q, smul_smul, hc.ne']
  have hpq : ⟪p,q⟫ = 0 := by simp [q, inner_smul_right, hpw]
  have heq : ⟪e,q⟫ = 0 := by simp [q, inner_smul_right, hew]
  refine ⟨![e,p,q], ‖u‖, b, ‖w‖, ?_, rfl, ha, hc, hu', ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> simpa using (by assumption : ‖_‖ = 1)
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | exact (hij rfl).elim
        | exact hep
        | exact heq
        | exact hpq
        | exact (real_inner_comm e p).trans hep
        | exact (real_inner_comm e q).trans heq
        | exact (real_inner_comm p q).trans hpq
  · change v = b • p + ‖w‖ • q
    rw [← hw']
    dsimp [w]
    module
  · rw [mul_pow]
    exact hd'

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma triangle_inner_bound (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∫⁻ x, triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ ∂stdGaussian E ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*
        Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2))) := by
  obtain ⟨f,a,b,c,hf,he',ha,hc,hu,hv,hd'⟩ := orthonormal_triple_of_gram_pos e u v he heu hev hd
  have hm : Measurable (fun p : ℝ × ℝ × ℝ => triangle p.1 (a*p.2.1) (b*p.2.1+c*p.2.2)) :=
    measurable_triangle.comp (show Measurable (fun p : ℝ × ℝ × ℝ =>
      (p.1, a*p.2.1, b*p.2.1+c*p.2.2)) from by fun_prop)
  have hs : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) = a*c := by
    rw [← hd', Real.sqrt_sq (mul_nonneg ha.le hc.le)]
  have hfun (x : E) : triangle ⟪e,x⟫ ⟪u,x⟫ ⟪v,x⟫ =
      triangle ⟪f 0,x⟫ (a*⟪f 1,x⟫) (b*⟪f 1,x⟫+c*⟪f 2,x⟫) := by
    rw [← he', hu, hv]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  calc
    _ = ∫⁻ t : ℝ, (∫⁻ w : ℝ, (∫⁻ y : ℝ, triangle t (a*w) (b*w+c*y)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
      simp_rw [hfun]
      exact lintegral_orthonormal_triple f hf _ hm
    _ ≤ ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) :=
      lintegral_triangle_gaussian b ha hc
    _ = _ := by
      rw [hs]
      congr 1
      congr 1
      ring

lemma setIntegral_inner_le_triangle (K : Set E) (hK : MeasurableSet K)
    (e u v : E) (he : ‖e‖ = 1) (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2)
    (huK : ∀ x ∈ K, ⟪u,x⟫ ≤ ⟪e,x⟫) (hvK : ∀ x ∈ K, ⟪v,x⟫ ≤ ⟪e,x⟫)
    (hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0)
    (hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0) :
    ∫ x in K, ⟪e,x⟫ ∂stdGaussian E ≤
      9/(2*Real.pi*Real.sqrt (2*Real.pi)*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2)) := by
  let f : E → ℝ := K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫)
  have hi (w : E) : Integrable (fun x => ⟪w,x⟫) (stdGaussian E) :=
    IsGaussian.integrable_dual _ (InnerProductSpace.toDual ℝ E w)
  have hfi : Integrable f (stdGaussian E) := ((hi e).add (hi u) |>.add (hi v)).indicator hK
  have hfint : ∫ x, f x ∂stdGaussian E = ∫ x in K, ⟪e,x⟫ ∂stdGaussian E := by
    rw [show f = K.indicator (fun x => ⟪e,x⟫+⟪u,x⟫+⟪v,x⟫) from rfl,
      integral_indicator hK, integral_add (f := fun x => ⟪e,x⟫+⟪u,x⟫)
        ((hi e).integrableOn.add (hi u).integrableOn) (hi v).integrableOn,
      integral_add (hi e).integrableOn (hi u).integrableOn, hu0, hv0]
    ring
  rw [← hfint]
  apply integral_le_of_lintegral_ofReal_le hfi (by positivity)
  apply le_trans _ (triangle_inner_bound e u v he heu hev hd)
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ K
  · simp only [f, Set.indicator_of_mem hx, triangle, ite_eq_left (huK x hx), ite_eq_left (hvK x hx)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · simp only [f, Set.indicator_of_notMem hx, ENNReal.ofReal_zero, zero_le]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_inner_eq_inner_integral (K : Set E) (w : E) :
    ∫ x in K, ⟪w,x⟫ ∂stdGaussian E = ⟪w, ∫ x in K, x ∂stdGaussian E⟫ := by
  exact (InnerProductSpace.toDual ℝ E w).integral_comp_comm
    IsGaussian.integrable_id.integrableOn

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sqrt_gram_smul {u v : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (‖a • u‖^2*‖b • v‖^2-⟪a • u,b • v⟫^2) =
      a*b*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [show (a*‖u‖)^2*(b*‖v‖)^2-(b*(a*⟪u,v⟫))^2 =
    (a*b)^2*(‖u‖^2*‖v‖^2-⟪u,v⟫^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg ha hb)]

lemma centroid_residual_pair (K : Set E) (hK : MeasurableSet K)
    (z r s : E) (hz : z ≠ 0) (hzK : ∫ x in K, x ∂stdGaussian E = z)
    (hzr : ⟪z,r⟫ = 0) (hzs : ⟪z,s⟫ = 0)
    {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hrK : ∀ x ∈ K, ⟪r,x⟫ ≤ L*⟪z,x⟫)
    (hsK : ∀ x ∈ K, ⟪s,x⟫ ≤ M*⟪z,x⟫)
    (hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2) :
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*L*M/(2*Real.pi*Real.sqrt (2*Real.pi)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let e := ‖z‖⁻¹ • z
  let u := (L*‖z‖)⁻¹ • r
  let v := (M*‖z‖)⁻¹ • s
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hn.ne']
  have heu : ⟪e,u⟫ = 0 := by simp [e,u,inner_smul_left,inner_smul_right,hzr]
  have hev : ⟪e,v⟫ = 0 := by simp [e,v,inner_smul_left,inner_smul_right,hzs]
  have huv : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    dsimp [u,v]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hL hn)),
      abs_of_pos (inv_pos.mpr (mul_pos hM hn)), inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    nlinarith only [mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hL hn)))
      (mul_pos (sq_pos_of_pos (inv_pos.mpr (mul_pos hM hn))) hd)]
  have huK (x : E) (hx : x ∈ K) : ⟪u,x⟫ ≤ ⟪e,x⟫ := by
    simp only [u,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hrK x hx) (inv_nonneg.mpr (mul_pos hL hn).le)
    calc
      _ ≤ (L*‖z‖)⁻¹*(L*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hvK (x : E) (hx : x ∈ K) : ⟪v,x⟫ ≤ ⟪e,x⟫ := by
    simp only [v,e,inner_smul_left,starRingEnd_apply,star_trivial]
    have hh := mul_le_mul_of_nonneg_left (hsK x hx) (inv_nonneg.mpr (mul_pos hM hn).le)
    calc
      _ ≤ (M*‖z‖)⁻¹*(M*⟪z,x⟫) := hh
      _ = _ := by field_simp
  have hu0 : ∫ x in K, ⟪u,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [u, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z r, hzr, mul_zero]
  have hv0 : ∫ x in K, ⟪v,x⟫ ∂stdGaussian E = 0 := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [v, inner_smul_left, starRingEnd_apply, star_trivial,
      real_inner_comm z s, hzs, mul_zero]
  have heK : ∫ x in K, ⟪e,x⟫ ∂stdGaussian E = ‖z‖ := by
    rw [integral_inner_eq_inner_integral, hzK]
    simp only [e,inner_smul_left,starRingEnd_apply,star_trivial,real_inner_self_eq_norm_sq]
    field_simp
  have hh := setIntegral_inner_le_triangle K hK e u v he heu hev huv huK hvK hu0 hv0
  rw [heK] at hh
  have hsqrt : Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) =
      (L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) :=
    sqrt_gram_smul (by positivity) (by positivity)
  rw [hsqrt] at hh
  have hp : 0 < Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) := Real.sqrt_pos.mpr hd
  have hc : 0 < 2*Real.pi*Real.sqrt (2*Real.pi) := by positivity
  have hh' := (le_div_iff₀ (show 0 < 2*Real.pi*Real.sqrt (2*Real.pi)*
      ((L*‖z‖)⁻¹*(M*‖z‖)⁻¹*Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2)) by positivity)).mp hh
  apply (le_div_iff₀ hc).mpr
  have := mul_le_mul_of_nonneg_right hh' (show 0 ≤ ‖z‖*L*M by positivity)
  convert this using 1 <;> field_simp

end GaussianPropeller.Pair

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

theorem centroid_closedCell {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) :
    centroid (closedCell (fun j => centroid (A j)) i) = centroid (A i) := by
  exact setIntegral_congr_set (active_eq_closedCell_ae hA hpos hi).symm

omit [NeZero k] in
theorem residual_orthogonal {z y : Space d} (hz : z ≠ 0) :
    ⟪z,residualVector z y⟫ = 0 := by
  simp only [residualVector, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    residualCoefficient]
  field_simp
  ring

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

theorem minimal_residual_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := residualVector z (centroid (A j))
    let s := residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l)))/(2*Real.pi*Real.sqrt (2*Real.pi)) := by
  dsimp only
  let z := centroid (A i)
  let r := residualVector z (centroid (A j))
  let s := residualVector z (centroid (A l))
  let a := residualCoefficient z (centroid (A j))
  let b := residualCoefficient z (centroid (A l))
  have ha : 0 < a := residualCoefficient_pos (negative_inner_of_minimal hA hij hi hj)
  have hb : 0 < b := residualCoefficient_pos (negative_inner_of_minimal hA hil hi hl)
  have hz : z ≠ 0 := active_centroid_ne_zero hA hpos hi
  change Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
    9*‖z‖*(1+a)*(1+b)/(2*Real.pi*Real.sqrt (2*Real.pi))
  by_cases hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2
  · apply GaussianPropeller.Pair.centroid_residual_pair
      (closedCell (fun j => centroid (A j)) i) (measurableSet_closedCell _ _)
      z r s hz (centroid_closedCell hA hpos hi)
      (residual_orthogonal hz) (residual_orthogonal hz)
      (by linarith : 0 < 1+a) (by linarith : 0 < 1+b) ?_ ?_ hd
    · intro x hx
      have hh := hx j
      change ⟪centroid (A j),x⟫ ≤ ⟪z,x⟫ at hh
      simp only [r,residualVector,inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial]
      change ⟪centroid (A j),x⟫+a*⟪z,x⟫ ≤ (1+a)*⟪z,x⟫
      linarith
    · intro x hx
      have hh := hx l
      change ⟪centroid (A l),x⟫ ≤ ⟪z,x⟫ at hh
      simp only [s,residualVector,inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial]
      change ⟪centroid (A l),x⟫+b*⟪z,x⟫ ≤ (1+b)*⟪z,x⟫
      linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hd)]
    positivity

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SpanReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

lemma sqrt_value_lower {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    3/(2*Real.sqrt (2*Real.pi)) < Real.sqrt C := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hs2 : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hrel : (3/(2*Real.sqrt (2*Real.pi)))^2 = 9/(8*Real.pi) := by
    rw [div_pow, mul_pow, hs2]
    ring
  have ht2 := Real.sq_sqrt hCp.le
  have hn : 0 ≤ 3/(2*Real.sqrt (2*Real.pi)) := by positivity
  nlinarith only [hrel,hC,ht2,Real.sqrt_nonneg C]

lemma normalize_pair_constant {C z L M D : ℝ} (hC : 9/(8*Real.pi) < C)
    (hz : 0 ≤ z) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hD : D ≤ 9*z*L*M/(2*Real.pi*Real.sqrt (2*Real.pi))) :
    (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹*D ≤ (3/Real.pi)*(z/Real.sqrt C)*L*M := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hq : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hp : 0 < Real.pi := Real.pi_pos
  have hh := le_of_lt (sqrt_value_lower hC)
  have hh' : 3 ≤ Real.sqrt C*(2*Real.sqrt (2*Real.pi)) := (div_le_iff₀ (by positivity)).mp hh
  have hb : 9/(2*Real.pi*Real.sqrt (2*Real.pi)) ≤ (3/Real.pi)*Real.sqrt C := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      9 ≤ 3*(Real.sqrt C*(2*Real.sqrt (2*Real.pi))) := by linarith only [hh']
      _ = _ := by field_simp
  have hDb : D ≤ (3/Real.pi)*Real.sqrt C*z*L*M := by
    calc
      D ≤ (9/(2*Real.pi*Real.sqrt (2*Real.pi)))*z*L*M := by
        convert hD using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hz) hL) hM
  have hm := mul_le_mul_of_nonneg_left hDb
    (show 0 ≤ (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹ by positivity)
  convert hm using 1 <;> first | rfl | field_simp

variable {d k : ℕ} [NeZero k]

theorem minimal_normalized_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hC : 9/(8*Real.pi) < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A j))
    let s := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      (3/Real.pi)*(‖z‖/Real.sqrt (value A))*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l))) := by
  dsimp only
  rw [GaussianPropeller.Pair.sqrt_gram_smul (by positivity) (by positivity)]
  apply normalize_pair_constant hC (norm_nonneg _)
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hij hi hj)))))
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hil hi hl)))))
  exact minimal_residual_pair hA ((by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC) hi hj hl hij hil

omit [NeZero k] in
theorem sum_cell_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i, (gaussian d).real (A i) = 1 := by
  let : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have hsum := integral_congr_ae (sum_indicator_eq hA (fun _ => (1:ℝ)))
  rw [integral_finsetSum] at hsum
  · simpa only [integral_indicator_const (1:ℝ) (hA.1 _), smul_eq_mul, mul_one,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hsum
  · intro i _
    exact (integrable_const (1:ℝ)).indicator (hA.1 i)

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open Metric
namespace GaussianPropeller.Polar
open Translation

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

lemma integral_volume_polar (f : E → ℝ) :
    ∫ x, f x = ∫ p : S × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
      ∂(V).toSphere.prod (Measure.volumeIoiPow (Fintype.card ι - 1)) := by
  have hh := (V).measurePreserving_homeomorphUnitSphereProd.integral_comp
    (homeomorphUnitSphereProd E).measurableEmbedding
    (fun p => f ((homeomorphUnitSphereProd E).symm p).val)
  simp only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
    finrank_euclideanSpace] at hh
  rw [integral_subtype_comap (measurableSet_singleton (0:E)).compl,
    restrict_compl_singleton] at hh
  exact hh

lemma integral_stdGaussian_polar (f : E → ℝ) :
    ∫ x, f x ∂stdGaussian E = (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ p : S × Ioi (0 : ℝ), Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)
        ∂(V).toSphere.prod (Measure.volumeIoiPow (Fintype.card ι - 1)) := by
  rw [stdGaussian_density]
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul measurable_stdDensity.real_toNNReal]
  have heq : (fun x : E => (stdDensity x).toNNReal • f x) =
      fun x => stdDensity x * f x := by
    funext x
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (stdDensity_pos x).le, smul_eq_mul]
  rw [heq, integral_volume_polar, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [stdDensity_eq]
  have hn : ‖p.2.1 • p.1.1‖ = p.2.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2,
      mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
  rw [hn]
  ring

lemma integral_volumeIoiPow (d : ℕ) (g : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), g r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in Ioi (0:ℝ), r^d * g r := by
  rw [Measure.volumeIoiPow]
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const d).real_toNNReal]
  have heq : (fun r : Ioi (0:ℝ) => (r.1^d).toNNReal • g r.1) =
      fun r => r.1^d * g r.1 := by
    funext r
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg r.2.le d), smul_eq_mul]
  rw [heq]
  exact integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^d * g r)

lemma integral_homogeneous (f : E → ℝ) (q : ℕ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r^q * f x) :
    ∫ x, f x ∂stdGaussian E =
      ((Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι - 1 + q) * Real.exp (-r^2/2)) *
      ∫ θ : S, f θ.1 ∂(V).toSphere := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)) =
      fun p => f p.1.1 * (p.2.1^q * Real.exp (-p.2.1^2/2)) := by
    funext p
    rw [hf _ p.2.2]
    ring
  rw [heq, integral_prod_mul (fun θ : S => f θ.1)
    (fun r : Ioi (0:ℝ) => r.1^q * Real.exp (-r.1^2/2)), integral_volumeIoiPow (Fintype.card ι - 1)
      (fun r : ℝ => r^q * Real.exp (-r^2/2))]
  have heq' : (fun r : ℝ => r^(Fintype.card ι-1) * (r^q * Real.exp (-r^2/2))) =
      fun r => r^(Fintype.card ι-1+q) * Real.exp (-r^2/2) := by
    funext r
    rw [pow_add]
    ring
  rw [heq']
  ring

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real

lemma radial_eq (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = b ^ (-((n:ℝ)+1)/2) * (1/2) * Gamma (((n:ℝ)+1)/2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=n) (b:=b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hb
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_mul, radial] using hh

lemma radial_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<radial n b := by
  rw [radial_eq n hb]
  exact mul_pos (mul_pos (rpow_pos_of_pos hb _) (by norm_num))
    (Gamma_pos_of_pos (by positivity))

lemma radial_scale (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = (sqrt (2*b))⁻¹ ^ (n+1) * radial n (1/2) := by
  have hp : 0<sqrt (2*b) := by positivity
  have hs := sq_sqrt (show 0≤2*b by positivity)
  have hh := integral_comp_mul_left_Ioi (fun r : ℝ => r^n*exp (-(1/2:ℝ)*r^2)) 0 hp
  rw [mul_zero] at hh
  have heq : (fun r : ℝ => (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) =
      fun r => sqrt (2*b)^n * (r^n*exp (-b*r^2)) := by
    funext r
    rw [mul_pow, show -(1/2:ℝ)*(sqrt (2*b)*r)^2 = -b*r^2 by rw [mul_pow,hs]; ring]
    ring
  change (∫ r in Ioi (0:ℝ), (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) = _ at hh
  rw [heq, integral_const_mul] at hh
  change sqrt (2*b)^n*radial n b = (sqrt (2*b))⁻¹*radial n (1/2) at hh
  apply (mul_left_cancel₀ (pow_ne_zero n hp.ne'))
  rw [hh, pow_succ, mul_assoc, ← mul_assoc (sqrt (2*b)^n)]
  simp only [inv_pow, mul_inv_cancel₀ (pow_ne_zero n hp.ne'), one_mul]

lemma radial_half_one : radial 1 (1/2) = 1 := by
  rw [radial_eq 1 (by norm_num)]
  norm_num

lemma radial_half_two : radial 2 (1/2) = sqrt (2*Real.pi)/2 := by
  rw [radial_eq 2 (by norm_num)]
  have hg := Gamma_nat_add_one_add_half 0
  norm_num at hg ⊢
  rw [hg]
  rw [show (-((3:ℝ)/2))=-(1+(1/2:ℝ)) by ring, rpow_neg (by norm_num : (0:ℝ)≤1/2),
    rpow_add (by norm_num : (0:ℝ)<1/2), rpow_one, ← sqrt_eq_rpow]
  have h1 := sq_sqrt (by norm_num : (0:ℝ)≤1/2)
  have h2 := sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp1 := sqrt_pos.mpr (by norm_num : (0:ℝ)<1/2)
  have hp2 := sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hh : sqrt (1/2:ℝ)*sqrt 2=1 := by rw [← sqrt_mul (by norm_num : (0:ℝ)≤1/2)]; norm_num
  field_simp
  nlinarith only [hh]

lemma radial_half_three : radial 3 (1/2) = 2 := by
  rw [radial_eq 3 (by norm_num)]
  norm_num [Gamma_nat_eq_factorial, rpow_neg, rpow_natCast]

lemma radial_half_four : radial 4 (1/2) = 3*sqrt (2*Real.pi)/2 := by
  have h2 := radial_half_two
  rw [radial_eq 2 (by norm_num)] at h2
  rw [radial_eq 4 (by norm_num)]
  have hg := Gamma_add_one (s:=(3/2:ℝ)) (by norm_num)
  norm_num at hg h2 ⊢
  rw [hg]
  have he : (1/2:ℝ)^(-((5:ℝ)/2)) = 2*(1/2:ℝ)^(-((3:ℝ)/2)) := by
    rw [show (-((5:ℝ)/2))=-(1:ℝ)+(-((3:ℝ)/2)) by ring, rpow_add (by norm_num : (0:ℝ)<1/2)]
    norm_num
  rw [he]
  nlinarith only [h2]

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

lemma integral_radial (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      ((sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι * ∫ _ : S, (1:ℝ) ∂(volume : Measure E).toSphere) *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => exp (-p.2.1^2/2)*f ‖p.2.1•p.1.1‖) =
      fun p => (1:ℝ)*(exp (-p.2.1^2/2)*f p.2.1) := by
    funext p
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0<p.2.1 from p.2.2),
      mem_sphere_zero_iff_norm.mp p.1.2]
  rw [heq, integral_prod_mul (fun θ : S => (1:ℝ))
    (fun r : Ioi (0:ℝ) => exp (-r.1^2/2)*f r.1), integral_volumeIoiPow (Fintype.card ι-1) (fun r => exp (-r^2/2)*f r)]
  simp_rw [mul_assoc]

lemma integral_radial_normalized (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r) /
      radial (Fintype.card ι-1) (1/2) := by
  have h1 := integral_radial (ι:=ι) (fun _ => (1:ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  have hi : (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)) = radial (Fintype.card ι-1) (1/2) := by
    unfold radial
    congr 1; funext r; congr 2; ring
  rw [hi] at h1
  rw [integral_radial]
  rw [← one_div_mul_eq_div]
  congr 1
  apply (eq_div_iff (radial_pos _ (by norm_num)).ne').mpr
  simpa using h1.symm

lemma integral_norm_pow_exp (q : ℕ) {a : ℝ} (_ha : 0≤a) :
    ∫ x : E, ‖x‖^q*exp (-a*‖x‖^2) ∂stdGaussian E =
      radial (Fintype.card ι-1+q) (a+1/2)/radial (Fintype.card ι-1) (1/2) := by
  rw [integral_radial_normalized (fun r => r^q*exp (-a*r^2))]
  congr 1
  unfold radial
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [pow_add]
  rw [show r^(Fintype.card ι-1)*exp (-r^2/2)*(r^q*exp (-a*r^2)) =
    r^(Fintype.card ι-1)*r^q*(exp (-r^2/2)*exp (-a*r^2)) by ring, ← exp_add]
  congr 2
  ring

end GaussianPropeller.Polar

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma p_eq_integral_indicator (a : ℝ) :
    p a = ∫ x : ℝ, (Ioi a).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun _ => (1:ℝ)) x*density x) =
      (Ioi a).indicator density := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

lemma p_le_one (a : ℝ) : p a ≤ 1 := by
  rw [p_eq_integral_indicator, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one]
  exact measureReal_le_one

lemma density_le_one (a : ℝ) : density a ≤ 1 := by
  unfold density
  rw [Real.exp_le_one_iff]
  linarith [sq_nonneg a]

variable {n : ℕ}

lemma integrable_p_norm (a : ℝ) : Integrable (fun y : CE n => p (a*‖y‖)) (stdGaussian (CE n)) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_p x).continuousAt)).comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with y
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_pos (p_pos _)]
  exact p_le_one _

lemma capP_zero (n : ℕ) : capP n 0 = 1/2 := by
  simp [capP,p,tail_zero]

lemma hasDerivAt_capP (a : ℝ) : HasDerivAt (capP n)
    (-gaussianConst * ∫ y : CE n, ‖y‖*density (a*‖y‖) ∂stdGaussian (CE n)) a := by
  have hc : 0 < gaussianConst := by dsimp [gaussianConst]; positivity
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:= fun y : CE n => gaussianConst*‖y‖)
    (F:= fun s y => p (s*‖y‖))
    (F':=fun s y => -gaussianConst*(‖y‖*density (s*‖y‖)))
    (by simp : univ ∈ 𝓝 a)
    (Filter.Eventually.of_forall (fun s => (integrable_p_norm s).aestronglyMeasurable))
    (integrable_p_norm a)
    (by unfold density; fun_prop : AEStronglyMeasurable (fun y : CE n => -gaussianConst*(‖y‖*density (a*‖y‖))) (stdGaussian (CE n)))
    (by
      filter_upwards [] with y
      intro s _
      simp only [norm_mul,norm_neg,Real.norm_eq_abs,abs_of_pos hc,abs_of_nonneg (norm_nonneg y),abs_of_pos (show 0 < density (s*‖y‖) from Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (by nlinarith only [density_le_one (s*‖y‖),norm_nonneg y] :
        ‖y‖*density (s*‖y‖) ≤ ‖y‖) hc.le)
    (IsGaussian.integrable_id.norm.const_mul gaussianConst)
    (by
      filter_upwards [] with y
      intro s _
      convert (hasDerivAt_p (s*‖y‖)).comp s ((hasDerivAt_id s).mul_const ‖y‖) using 1 <;> first | rfl | ring)
  have hd2 := hd.2
  rw [integral_const_mul] at hd2
  exact hd2

lemma capM_eq (hn : 0<n) (a : ℝ) :
    capM n a = gaussianConst * (Real.sqrt (1+a^2))⁻¹^n := by
  let : NeZero n := ⟨by omega⟩
  have hh := integral_norm_pow_exp (ι:=Fin n) 0 (a:=a^2/2) (by positivity)
  have hs := radial_scale (n-1) (b:=a^2/2+1/2) (by positivity)
  simp only [Fintype.card_fin, add_zero, pow_zero, one_mul] at hh
  unfold capM
  have he : (fun y : CE n => density (a*‖y‖)) = fun y => Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 1; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,
    show n-1+1=n by omega, mul_div_cancel_right₀ _ (radial_pos _ (by norm_num)).ne']

lemma capP_deriv_two (a : ℝ) : HasDerivAt (capP 2)
    (-(1/2:ℝ)*(Real.sqrt (1+a^2))⁻¹^3) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 2) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 2 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one, radial_half_one] at hh
  have hd := hasDerivAt_capP (n:=2) a
  have he : (fun y : CE 2 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,div_one,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_two] at hd
  convert hd using 1
  dsimp [gaussianConst]
  field_simp

lemma capP_two (a : ℝ) : capP 2 a = (1-a/Real.sqrt (1+a^2))/2 := by
  have hp (x : ℝ) : 0 < 1+x^2 := by positivity
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (1-x/Real.sqrt (1+x^2))/2)
      (-(1/2:ℝ)*(Real.sqrt (1+x^2))⁻¹^3) x := by
    convert ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).div
      (((hasDerivAt_pow 2 x).const_add 1).sqrt (hp x).ne') (Real.sqrt_pos.mpr (hp x)).ne')).div_const 2 using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [Real.sq_sqrt (hp x).le])
  have he := is_const_of_deriv_eq_zero (fun x => ((hasDerivAt_capP (n:=2) x).sub (hd x)).differentiableAt)
  have he' : ∀ x, deriv (fun x => capP 2 x-(1-x/Real.sqrt (1+x^2))/2) x=0 := by
    intro x
    have hx := ((capP_deriv_two x).fun_sub (hd x)).deriv
    rw [sub_self] at hx
    exact hx
  have hg := he he' a 0
  simp only [Pi.sub_apply, capP_zero,zero_div,sub_zero,one_div] at hg
  linarith

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords

lemma split_measure (n : ℕ) :
    (stdGaussian (CS (n+1))).map (split n) = (gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).map_eq
  have he : (split n) ∘ WithLp.toLp 2 =
      (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) := by
    funext x
    rfl
  rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_split n).measurable
    (PiLp.continuous_toLp 2 _).measurable, he,
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),hm,
    ← Measure.map_prod_map _ _ measurable_id (PiLp.continuous_toLp 2 _).measurable,
    Measure.map_id,map_pi_eq_stdGaussian]

lemma measurePreserving_split (n : ℕ) : MeasurePreserving (splitEquiv n)
    (stdGaussian (CS (n+1))) ((gaussianReal 0 1).prod (stdGaussian (CS n))) :=
  ⟨(continuous_split n).measurable,split_measure n⟩

lemma integral_split (n : ℕ) (f : CS (n+1) → ℝ) :
    (∫ x, f x ∂stdGaussian (CS (n+1))) =
      ∫ y, f (join n y) ∂(gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  exact ((measurePreserving_split n).symm.integral_comp (splitEquiv n).symm.measurableEmbedding f).symm

lemma norm_join_sq (n : ℕ) (y : ℝ × CS n) : ‖join n y‖^2 = y.1^2+‖y.2‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,join,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]

lemma exists_basis_zero {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E=n+1)
    (e : E) (he : ‖e‖=1) :
    ∃ b : OrthonormalBasis (Fin (n+1)) ℝ E, b 0=e := by
  have ho : Orthonormal ℝ (({0}:Set (Fin (n+1))).domRestrict (fun _ => e)) := by
    constructor
    · intro i; exact he
    · intro i j hij
      have hi : (i:Fin (n+1))=0 := i.2
      have hj : (j:Fin (n+1))=0 := j.2
      exact (hij (Subtype.ext (hi.trans hj.symm))).elim
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (ι:=Fin (n+1)) (by simpa using hn)
  exact ⟨b,hb 0 (by simp)⟩

end GaussianPropeller.Coords

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

lemma measurableSet_coneCap (n : ℕ) (a : ℝ) : MeasurableSet (coneCap n a) := by
  apply isOpen_lt (by exact continuous_const.mul ((continuous_split n).snd.norm)) (by fun_prop) |>.measurableSet

lemma coneCap_smul (a : ℝ) {r : ℝ} (hr : 0<r) (x : CE (n+1)) :
    r•x∈coneCap n a ↔ x∈coneCap n a := by
  have he : (split n (r•x)).2 = r•(split n x).2 := by ext i; rfl
  simp only [coneCap,mem_ofPred_eq,he,norm_smul,Real.norm_eq_abs,abs_of_pos hr,PiLp.smul_apply,smul_eq_mul]
  rw [← mul_assoc, mul_comm a r, mul_assoc, mul_lt_mul_iff_right₀ hr]

lemma integrable_coord : Integrable (fun x : CE (n+1) => x 0) (stdGaussian (CE (n+1))) := by
  apply Integrable.mono' IsGaussian.integrable_id.norm (by fun_prop)
  filter_upwards [] with x
  exact PiLp.norm_apply_le x 0

lemma tail_first_gaussian (a : ℝ) : ∫ x in Ioi a, x ∂gaussianReal 0 1 = gaussianConst*density a := by
  rw [← integral_indicator measurableSet_Ioi,integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun x=>x) x*density x) =
      (Ioi a).indicator (fun x => x*density x) := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi,tail_first_moment]

lemma integral_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun _ => (1:ℝ)) x ∂stdGaussian (CE (n+1)) = capP n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun _ => (1:ℝ)) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      (((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      ((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capP
  apply integral_congr_ae
  filter_upwards [] with y
  rw [p_eq_integral_indicator]
  rfl

lemma moment_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun x => x 0) x ∂stdGaussian (CE (n+1)) = capM n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun x => x 0) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      ((integrable_coord.indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      (integrable_coord.indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capM
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← tail_first_gaussian,← integral_indicator measurableSet_Ioi]
  rfl

lemma integral_cone_norm {d : ℕ} (hd : 0<d) (K : Set (CE d))
    (hK : MeasurableSet K) (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) :
    (∫ x : CE d, K.indicator (fun x => ‖x‖) x ∂stdGaussian (CE d)) =
      radial d (1/2)/radial (d-1) (1/2) * (stdGaussian (CE d)).real K := by
  let : NeZero d := ⟨by omega⟩
  have h0 := integral_homogeneous (ι:=Fin d) (K.indicator (fun _ => (1:ℝ))) 0 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx])
  have h1 := integral_homogeneous (ι:=Fin d) (K.indicator (fun x => ‖x‖)) 1 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx,norm_smul,Real.norm_eq_abs,abs_of_pos hr])
  have he : (fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun x => ‖x‖) θ.1) =
      fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun _ => (1:ℝ)) θ.1 := by
    funext θ
    by_cases hh : θ.1∈K <;> simp [hh, mem_sphere_zero_iff_norm.mp θ.2]
  rw [he] at h1
  simp only [Fintype.card_fin,Nat.add_zero,show d-1+1=d by omega] at h0 h1
  rw [integral_indicator hK,setIntegral_const,smul_eq_mul,mul_one] at h0
  have hr (q:ℕ) : (∫ r in Ioi (0:ℝ), r^q*Real.exp (-r^2/2))=radial q (1/2) := by
    unfold radial
    congr 1
    funext r; congr 2; ring
  rw [hr] at h0 h1
  rw [h1,h0]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (radial_pos (d-1) (b:=1/2) (by norm_num)).ne').mpr
  ring

lemma coneCap_criterion {a : ℝ} (ha : 0≤a) (x : CE (n+1)) :
    x∈coneCap n a ↔ a/Real.sqrt (1+a^2)*‖x‖ < x 0 := by
  have hp : 0 < Real.sqrt (1+a^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1+a^2 by positivity)
  have hn := norm_join_sq n (split n x)
  rw [join_split] at hn
  change ‖x‖^2 = (x 0)^2+‖(split n x).2‖^2 at hn
  change a*‖(split n x).2‖ < x 0 ↔ _
  rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
  constructor
  · intro h
    have hx : 0 < x 0 := lt_of_le_of_lt (by positivity) h
    have hs1 : (a*‖(split n x).2‖)^2 < (x 0)^2 := sq_lt_sq₀ (by positivity) hx.le |>.mpr h
    have hs2 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hs2
  · intro h
    have hx : 0 < x 0 := (mul_pos_iff_of_pos_right hp).mp (lt_of_le_of_lt (by positivity) h)
    have hs1 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
    have hs2 : (a*‖(split n x).2‖)^2 < (x 0)^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) hx.le).mp hs2

lemma moment_rearrange (K : Set (CE (n+1))) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) {a : ℝ} (ha : 0≤a) :
    (∫ x : CE (n+1), K.indicator (fun x=>x 0) x ∂stdGaussian (CE (n+1))) ≤
      capM n a + a/Real.sqrt (1+a^2) * (radial (n+1) (1/2)/radial n (1/2)) *
        ((stdGaussian (CE (n+1))).real K-capP n a) := by
  let b := a/Real.sqrt (1+a^2)
  let C := coneCap n a
  have hn : Integrable (fun x : CE (n+1)=>‖x‖) (stdGaussian (CE (n+1))) := IsGaussian.integrable_id.norm
  have hf : Integrable (fun x : CE (n+1)=> x 0-b*‖x‖) (stdGaussian (CE (n+1))) :=
    integrable_coord.sub (hn.const_mul b)
  have hi := integral_mono (hf.indicator hK) (hf.indicator (measurableSet_coneCap n a)) (fun x => show
      K.indicator (fun x=>x 0-b*‖x‖) x ≤ C.indicator (fun x=>x 0-b*‖x‖) x from by
    by_cases hk : x∈K <;> by_cases hc : x∈C
    · simp [hk,hc]
    · simp only [indicator_of_mem hk,indicator_of_notMem hc]
      exact sub_nonpos.mpr (not_lt.mp (mt (coneCap_criterion ha x).mpr hc))
    · simp only [indicator_of_notMem hk,indicator_of_mem hc]
      exact sub_nonneg.mpr ((coneCap_criterion ha x).mp hc).le
    · simp [hk,hc])
  simp_rw [indicator_sub,indicator_const_mul] at hi
  rw [integral_sub (integrable_coord.indicator hK) ((hn.indicator hK).const_mul b),
    integral_const_mul,
    integral_sub (integrable_coord.indicator (measurableSet_coneCap n a))
      ((hn.indicator (measurableSet_coneCap n a)).const_mul b),integral_const_mul,
    integral_cone_norm (by omega) K hK hcone,
    integral_cone_norm (by omega) C (measurableSet_coneCap n a) (fun r hr x=>coneCap_smul a hr x),
    moment_cap,show n+1-1=n by omega] at hi
  have hp : (stdGaussian (CE (n+1))).real C = capP n a := by
    rw [← integral_cap,integral_indicator (measurableSet_coneCap n a),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
    rfl
  rw [hp] at hi
  dsimp [b] at hi
  linarith only [hi]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

lemma cap_parameter {b : ℝ} (hb : 0≤b) (hb1 : b<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ ∧
    (b/Real.sqrt (1-b^2))/Real.sqrt (1+(b/Real.sqrt (1-b^2))^2)=b := by
  have hpos : 0<1-b^2 := by nlinarith only [hb,hb1]
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr hpos
  have hs := Real.sq_sqrt hpos.le
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp
    nlinarith only [hs]
  refine ⟨?_,?_⟩
  · rw [he,Real.sqrt_sq (by positivity)]
  · rw [he,Real.sqrt_sq (by positivity)]
    field_simp

lemma cone_three (K : Set (CE 3)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : (stdGaussian (CE 3)).real K ∈ Ioo (0:ℝ) 1)
    (hPh : (stdGaussian (CE 3)).real K ≤ 1/2) :
    (∫ x : CE 3, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 3)) ≤
      4*gaussianConst*(stdGaussian (CE 3)).real K*(1-(stdGaussian (CE 3)).real K) := by
  let P := (stdGaussian (CE 3)).real K
  let b := 1-2*P
  have hb : 0≤b := by dsimp [b,P]; linarith only [hPh]
  have hb1 : b<1 := by dsimp [b,P]; linarith only [hP.1]
  have hh := cap_parameter hb hb1
  have hr := moment_rearrange (n:=2) K hK hcone (a:=b/Real.sqrt (1-b^2)) (by positivity)
  rw [capP_two,hh.2,capM_eq (by omega),hh.1,inv_inv] at hr
  have hs : 0≤1-b^2 := by nlinarith only [hb,hb1]
  rw [Real.sq_sqrt hs] at hr
  have he : (1-b)/2=P := by dsimp [b]; ring
  rw [he,show (stdGaussian (CE (2+1))).real K=P from rfl,sub_self,mul_zero,add_zero] at hr
  dsimp [b,P] at hr
  nlinarith only [hr]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma capP_deriv_three (a : ℝ) : HasDerivAt (capP 3)
    (-(2/Real.pi:ℝ)*(Real.sqrt (1+a^2))⁻¹^4) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 3) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 3 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one] at hh
  have hd := hasDerivAt_capP (n:=3) a
  have he : (fun y : CE 3 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_three,radial_half_two] at hd
  convert hd using 1
  have hp : 0<Real.sqrt (2*Real.pi) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  dsimp [gaussianConst]
  field_simp
  nlinarith only [hsq]

lemma sphereTail_zero : sphereTail 0 = Real.pi/4 := by
  have hi : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume (-1) 0 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have he := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hn := intervalIntegral.integral_comp_neg (f:=fun u:ℝ=>Real.sqrt (1-u^2)) (a:=(0:ℝ)) (b:=1)
  simp only [neg_zero,neg_sq] at hn
  rw [integral_sqrt_one_sub_sq] at he
  dsimp [sphereTail]
  linarith only [he,hn]

lemma hasDerivAt_sphereTail (b:ℝ) : HasDerivAt sphereTail (-Real.sqrt (1-b^2)) b := by
  apply intervalIntegral.integral_hasDerivAt_left
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).stronglyMeasurable.stronglyMeasurableAtFilter
  · fun_prop

lemma cap_parameter' {b:ℝ} (hb:b^2<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ := by
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by linarith only [hb])
  have hs := Real.sq_sqrt (show 0≤1-b^2 by linarith only [hb])
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp; nlinarith only [hs]
  rw [he,Real.sqrt_sq (by positivity)]

lemma capP_three_sphere {b:ℝ} (hb:b∈Ioo (-1:ℝ) 1) :
    capP 3 (b/Real.sqrt (1-b^2)) = 2/Real.pi*sphereTail b := by
  have hd (x:ℝ) (hx:x∈Ioo (-1:ℝ) 1) :
      HasDerivAt (fun x=>capP 3 (x/Real.sqrt (1-x^2)))
        (-(2/Real.pi)*Real.sqrt (1-x^2)) x := by
    have hxs : x^2<1 := by nlinarith only [hx.1,hx.2]
    have hp : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by linarith only [hxs])
    have hs' := Real.sq_sqrt (show 0≤1-x^2 by linarith only [hxs])
    have hh := (capP_deriv_three (x/Real.sqrt (1-x^2))).comp x
      ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_sub 1 |>.sqrt (by change 1-x^2≠0; linarith only [hxs])) hp.ne')
    rw [cap_parameter' hxs,inv_inv] at hh
    convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring_nf; try simp only [hs']; ring)
  have he := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun x hx=>(hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx=>((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).differentiableAt.differentiableWithinAt)
    (fun x hx=>by rw [(hd x hx).deriv,((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).deriv]; ring)
    (x:=0) (by norm_num) (by rw [zero_div,capP_zero,sphereTail_zero]; field_simp; ring)
  exact he hb

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.CapNumeric
open Real Set

lemma hasDerivAt_Q (t:ℝ) : HasDerivAt Q (-1/35-2*t/504) t := by
  unfold Q
  convert (((hasDerivAt_id t).div_const 35).const_sub (4/15) |>.sub
    (((hasDerivAt_id t).pow 2).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_R (t:ℝ) : HasDerivAt R (-31/15+67*t/140+11*t^2/168) t := by
  unfold R
  convert ((((hasDerivAt_id t).const_mul 31).div_const 15).const_sub (4/3) |>.add
    ((((hasDerivAt_id t).pow 2).const_mul 67).div_const 280) |>.add
    ((((hasDerivAt_id t).pow 3).const_mul 11).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_U {t:ℝ} (ht:0<t) : HasDerivAt U (Real.sqrt (2*t)*t/2*R t) t := by
  have hs : 0<Real.sqrt (2*t) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*t by positivity)
  unfold U
  convert ((((hasDerivAt_id t).const_sub 1).mul ((hasDerivAt_id t).pow 2)).mul
    (((hasDerivAt_id t).const_mul 2).sqrt (by positivity)) |>.mul (hasDerivAt_Q t)) using 1 <;> first | rfl | (dsimp [Q,R]; field_simp; rw [hsq]; ring)

lemma Q_nonneg {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : 0≤Q t := by
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  unfold Q; linarith only [ht.2,hsq]
lemma Q_antitone : AntitoneOn Q (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold Q; fun_prop)
    (fun t ht=>(hasDerivAt_Q t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_Q t).deriv]
  rw [interior_Icc] at ht
  linarith only [ht.1]
lemma R_antitone : AntitoneOn R (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold R; fun_prop)
    (fun t ht=>(hasDerivAt_R t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_R t).deriv]
  rw [interior_Icc] at ht
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  linarith only [ht.2,hsq]

lemma U_middle {t:ℝ} (ht:t∈Icc (7067/10000:ℝ) (7068/10000:ℝ)) : U t < (428/10000:ℝ) := by
  have ht0 : 0≤t := by linarith only [ht.1]
  have ht1 : t≤1 := by linarith only [ht.2]
  have hq : Q t≤Q (7067/10000) := Q_antitone (by norm_num) ⟨ht0,ht1⟩ ht.1
  have hs : Real.sqrt (2*t)≤1189/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [ht.2]⟩
  have ht2 : t^2≤(7068/10000:ℝ)^2 := (sq_le_sq₀ ht0 (by norm_num)).mpr ht.2
  have hp := mul_le_mul (show 1-t≤2933/10000 by linarith only [ht.1]) ht2 (sq_nonneg t) (by norm_num)
  have hp' := mul_le_mul hp hs (Real.sqrt_nonneg _) (by norm_num)
  have hp'' := mul_le_mul hp' hq (Q_nonneg ⟨ht0,ht1⟩) (by norm_num)
  dsimp [U]
  exact hp''.trans_lt (by norm_num [Q])

lemma U_bound {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : U t < (428/10000:ℝ) := by
  have hl : MonotoneOn U (Icc (0:ℝ) (7067/10000)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; exact hx.1)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_U hx.1).deriv]
    have hR := R_antitone ⟨hx.1.le,by linarith only [hx.2]⟩ (by norm_num) hx.2.le
    have hpos : 0≤R (7067/10000) := by norm_num [R]
    exact mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx.1.le) (by norm_num)) (hpos.trans hR)
  have hu : AntitoneOn U (Icc (7068/10000:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; linarith only [hx.1])).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := by linarith only [hx.1]
    rw [(hasDerivAt_U hx0).deriv]
    have hR := R_antitone (by norm_num) ⟨hx0.le,hx.2.le⟩ hx.1.le
    have hneg : R (7068/10000)≤0 := by norm_num [R]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hR.trans hneg)
  by_cases htl : t≤7067/10000
  · exact (hl ⟨ht.1,htl⟩ (by norm_num) htl).trans_lt (U_middle (by norm_num))
  by_cases htu : 7068/10000≤t
  · exact (hu (by norm_num) ⟨htu,ht.2⟩ htu).trans_lt (U_middle (by norm_num))
  exact U_middle ⟨(lt_of_not_ge htl).le,(lt_of_not_ge htu).le⟩

end GaussianPropeller.CapNumeric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

lemma integral_u_sqrt {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    (∫ u in b..1, u*Real.sqrt (1-u^2)) = (1-b^2)*Real.sqrt (1-b^2)/3 := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.2
    (f:=fun u:ℝ=>-(1-u^2)*Real.sqrt (1-u^2)/3)
    (f':=fun u:ℝ=>u*Real.sqrt (1-u^2)) (by fun_prop) (fun u hu=>?_)
    (by exact (by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
  · simp only [one_pow,sub_self,neg_zero,zero_mul,zero_div,zero_sub] at hh
    rw [hh]; ring
  have hu0 : 0≤u := hb.1.trans hu.1.le
  have hsq : u^2<1 := by nlinarith only [hu0,hu.2]
  have hp : 0<Real.sqrt (1-u^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1-u^2 by linarith only [hsq])
  have hd := ((hasDerivAt_id u).pow 2).const_sub 1
  convert ((hd.neg.mul (hd.sqrt (by change 1-u^2≠0; linarith only [hsq]))).div_const 3) using 1 <;> first | rfl | (dsimp; field_simp; rw [hs]; ring)

lemma sphereGap_eq {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    sphereGap b = (1-b^2)*Real.sqrt (1-b^2)/3-b*sphereTail b := by
  have he : (fun u:ℝ => (u-b)*Real.sqrt (1-u^2)) =
      fun u=> u*Real.sqrt (1-u^2)-b*Real.sqrt (1-u^2) := by funext u; ring
  rw [sphereGap,he,intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u:ℝ=>b*Real.sqrt (1-u^2))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_u_sqrt hb]
  rfl

lemma sqrt_two_upper {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    Real.sqrt (2*s-s^2) ≤ Real.sqrt (2*s)*(1-s/4-s^2/32) := by
  have hs2 : s^2≤1 := by nlinarith only [hs.1,hs.2]
  have hp : 0≤1-s/4-s^2/32 := by linarith only [hs.2,hs2]
  have ha : 0≤2*s-s^2 := by nlinarith only [hs.1,hs.2]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hp)).mp
  rw [mul_pow,Real.sq_sqrt ha,Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hs.1)]
  have he : 2*s*(1-s/4-s^2/32)^2-(2*s-s^2) = s^4/32+s^5/512 := by ring
  nlinarith only [he,pow_nonneg hs.1 4,pow_nonneg hs.1 5]

lemma hasDerivAt_sqrt_two {s:ℝ} (hs:0<s) : HasDerivAt (fun s:ℝ=>Real.sqrt (2*s))
    (Real.sqrt (2*s)/(2*s)) s := by
  have hp : 0<Real.sqrt (2*s) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*s by positivity)
  convert (((hasDerivAt_id s).const_mul 2).sqrt (by positivity)) using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [hsq])

lemma hasDerivAt_gapPrim (t:ℝ) {s:ℝ} (hs:0<s) : HasDerivAt (gapPrim t)
    ((t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32)) s := by
  unfold gapPrim
  convert (hasDerivAt_sqrt_two hs).mul
    (((((hasDerivAt_id s).const_mul (2*t)).div_const 3).sub
      (((hasDerivAt_id s).pow 2).const_mul (2/5+t/10))).add
      (((hasDerivAt_id s).pow 3).const_mul (1/14-t/112)) |>.add
      (((hasDerivAt_id s).pow 4).div_const 144)) using 1 <;> first | rfl | (dsimp; field_simp; ring)

lemma sphereGap_upper {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    b*sphereGap b ≤ U (1-b) := by
  let t := 1-b
  have ht : t∈Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith only [hb.2],by dsimp [t]; linarith only [hb.1]⟩
  have hsub := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=t)
    (fun u:ℝ=>(u-b)*Real.sqrt (1-u^2)) 1
  have he : (fun s:ℝ=>(1-s-b)*Real.sqrt (1-(1-s)^2)) =
      fun s=>(t-s)*Real.sqrt (2*s-s^2) := by funext s; dsimp [t]; rw [show 1-(1-s)^2=2*s-s^2 by ring]; ring
  rw [he,show 1-t=b by dsimp [t]; ring,sub_zero] at hsub
  have hi := intervalIntegral.integral_mono_on (μ:=volume) ht.1
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s-s^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
    (fun s hs=>show (t-s)*Real.sqrt (2*s-s^2)≤(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32) from by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sqrt_two_upper ⟨hs.1,hs.2.trans ht.2⟩) (sub_nonneg.mpr hs.2))
  have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (f:=gapPrim t) (by unfold gapPrim; fun_prop)
    (fun s hs=>hasDerivAt_gapPrim t hs.1)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
  rw [hsub,hj,show gapPrim t 0=0 by simp [gapPrim],sub_zero] at hi
  have hh := mul_le_mul_of_nonneg_left hi hb.1
  change b*sphereGap b≤_ at hh
  convert hh using 1
  dsimp [gapPrim,U,CapNumeric.Q,t]
  ring

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

lemma cone_four (K : Set (CE 4)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : 0<(stdGaussian (CE 4)).real K)
    (hM0 : 0≤∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4)) :
    (∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4))^2 ≤
      (963/2500:ℝ)*(stdGaussian (CE 4)).real K := by
  let P := (stdGaussian (CE 4)).real K
  let M := ∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4)
  let ρ := 3*Real.sqrt (2*Real.pi)/4
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρsq : ρ^2=9*Real.pi/8 := by
    dsimp [ρ]
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
    ring
  have hρrad : radial 4 (1/2)/radial 3 (1/2)=ρ := by
    rw [radial_half_four,radial_half_three]; dsimp [ρ]; ring
  have hφ : gaussianConst=ρ*(2/Real.pi)/3 := by
    have hs := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
    dsimp [gaussianConst,ρ]
    field_simp
    nlinarith only [hs]
  have hm : M≤ρ*P := by
    have hn : Integrable (fun x:CE 4=>‖x‖) (stdGaussian (CE 4)) := IsGaussian.integrable_id.norm
    have hh := integral_mono (integrable_coord.indicator hK) (hn.indicator hK) (fun x=>show
        K.indicator (fun x=>x 0) x≤K.indicator (fun x=>‖x‖) x from by
      by_cases hx:x∈K
      · simp only [indicator_of_mem hx]
        exact (le_abs_self _).trans (PiLp.norm_apply_le x 0)
      · simp [hx])
    rw [integral_cone_norm (by omega) K hK hcone,hρrad] at hh
    exact hh
  let b := M/(2*ρ*P)
  have hb : 0≤b := div_nonneg hM0 (by positivity)
  have hbhalf : b≤1/2 := (div_le_iff₀ (by positivity : 0<2*ρ*P)).mpr (by nlinarith only [hm])
  have hb1 : b<1 := by linarith only [hbhalf]
  have hM : M=2*ρ*P*b := by dsimp [b]; field_simp [ne_of_gt (show 0<P from hP)]
  have hh := cap_parameter hb hb1
  have hr := moment_rearrange (n:=3) K hK hcone (a:=b/Real.sqrt (1-b^2)) (by positivity)
  rw [capM_eq (by omega),hh.2,hh.1,inv_inv,capP_three_sphere ⟨by linarith only [hb],hb1⟩,
    hρrad] at hr
  have hs := Real.sq_sqrt (show 0≤1-b^2 by nlinarith only [hb,hb1])
  have hg := sphereGap_eq ⟨hb,hb1.le⟩
  have he : gaussianConst*Real.sqrt (1-b^2)^3+b*ρ*(P-(2/Real.pi)*sphereTail b) =
      ρ*(b*P+(2/Real.pi)*sphereGap b) := by
    rw [hφ,hg]
    have hs3 : Real.sqrt (1-b^2)^3 = (1-b^2)*Real.sqrt (1-b^2) := by
      rw [pow_succ,hs]
    rw [hs3]; ring
  change M≤gaussianConst*Real.sqrt (1-b^2)^3+b*ρ*(P-(2/Real.pi)*sphereTail b) at hr
  rw [he] at hr
  have hu : b*sphereGap b≤428/10000 :=
    (sphereGap_upper ⟨hb,hb1.le⟩).trans (U_bound ⟨by linarith only [hb1],by linarith only [hb]⟩).le
  have hmb : M*b/2≤ρ*(2/Real.pi)*(b*sphereGap b) := by
    have hh := mul_le_mul_of_nonneg_right hr hb
    have he : ρ*(b*P+(2/Real.pi)*sphereGap b)*b = M*b/2+ρ*(2/Real.pi)*(b*sphereGap b) := by rw [hM]; ring
    rw [he] at hh
    linarith only [hh]
  calc
    M^2 = (4*ρ*P)*(M*b/2) := by rw [hM]; ring
    _ ≤ (4*ρ*P)*(ρ*(2/Real.pi)*(b*sphereGap b)) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _ ≤ (4*ρ*P)*(ρ*(2/Real.pi)*(428/10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
    _ = (963/2500)*P := by
      calc
        _ = (428/10000)*8*ρ^2/Real.pi*P := by ring
        _ = _ := by rw [hρsq]; field_simp; ring

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
open Coords
variable {d k n : ℕ} [NeZero k]

omit [NeZero k] in
lemma closedCell_cone [NeZero k] (z : Fin k → Space d) (i : Fin k) (r:ℝ) (hr:0<r)
    (x:Space d) : r•x ∈ closedCell z i ↔ x∈closedCell z i := by
  simp only [closedCell, mem_ofPred_eq,inner_smul_right]
  exact forall_congr' (fun j => mul_le_mul_iff_right₀ hr)

lemma coordinates_law {V : Submodule ℝ (Space d)}
    (b : OrthonormalBasis (Fin (n+1)) ℝ V) :
    (gaussian d).map (fun x => b.repr (V.orthogonalProjectionOnto x)) = gaussian (n+1) := by
  have ho : Orthonormal ℝ (fun j => (b j : Space d)) := by
    constructor
    · intro j; exact b.orthonormal.1 j
    · intro j l hjl; exact b.orthonormal.2 hjl
  have he : (fun x => b.repr (V.orthogonalProjectionOnto x)) =
      WithLp.toLp 2 ∘ (fun x => fun j => ⟪(b j:Space d),x⟫) := by
    funext x; ext j
    simp only [Function.comp_apply,WithLp.ofLp_toLp,OrthonormalBasis.repr_apply_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold gaussian
  rw [he,← Measure.map_map (PiLp.continuous_toLp 2 _).measurable (by fun_prop),
    Analytic.map_orthonormal_stdGaussian _ ho,map_pi_eq_stdGaussian]

lemma exists_span_cone {z : Fin k → Space d} (hsum : ∑ j,z j=0)
    (hneg : Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hzi:z i≠0)
    (hdim : k-1=n+1) (hcen : centroid (closedCell z i)=z i) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (closedCell z i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖z i‖ := by
  let V := Submodule.span ℝ (range z)
  let zv : Fin k → V := fun j=>⟨z j,Submodule.subset_span (mem_range_self j)⟩
  have hnorm : 0<‖z i‖ := norm_pos_iff.mpr hzi
  let e : V := ‖z i‖⁻¹ • zv i
  have he : ‖e‖=1 := by simp [e,zv,norm_smul,hnorm.ne']
  obtain ⟨b,hb⟩ := exists_basis_zero
    (show Module.finrank ℝ V=n+1 by rw [Gram.finrank_span z hneg hsum i,Fintype.card_fin,hdim]) e he
  let T : Space d → Space (n+1) := fun x=> b.repr (V.orthogonalProjectionOnto x)
  let w : Fin k → Space (n+1) := fun j=>b.repr (zv j)
  let K := closedCell w i
  have hT : Continuous T := b.repr.continuous.comp V.orthogonalProjectionOnto.continuous
  have hm : (gaussian d).map T=gaussian (n+1) := coordinates_law b
  have hs : ∀ j x, ⟪w j,T x⟫=⟪z j,x⟫ := by
    intro j x
    dsimp [w,T]
    rw [b.repr.inner_map_map,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hp : T ⁻¹' K=closedCell z i := by
    ext x
    simp only [K,closedCell,mem_preimage,mem_ofPred_eq,hs]
  refine ⟨K,measurableSet_closedCell w i,closedCell_cone w i,?_,?_⟩
  · rw [← hm,measureReal_def,Measure.map_apply hT.measurable (measurableSet_closedCell w i),hp]
    rfl
  have ht0 : ∀ x, T x 0=‖z i‖⁻¹*⟪z i,x⟫ := by
    intro x
    dsimp [T]
    rw [b.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,hb]
    simp only [e,Submodule.coe_smul,zv,real_inner_smul_left]
  have hi := integral_map (μ:=gaussian d) (φ:=T)
    (f:=K.indicator (fun x:Space (n+1)=>x 0)) hT.aemeasurable
    (((by fun_prop : Continuous (fun x:Space (n+1)=>x 0)).stronglyMeasurable.indicator
      (measurableSet_closedCell w i)).aestronglyMeasurable)
  rw [hm] at hi
  rw [hi]
  have heq : (fun x => K.indicator (fun x:Space (n+1)=>x 0) (T x)) =
      (closedCell z i).indicator (fun x=>‖z i‖⁻¹*⟪z i,x⟫) := by
    funext x
    have hh : T x∈K ↔ x∈closedCell z i := Set.ext_iff.mp hp x
    by_cases hx : x∈closedCell z i
    · simp only [indicator_of_mem hx,indicator_of_mem (hh.mpr hx),ht0]
    · simp only [indicator_of_notMem hx,indicator_of_notMem (mt hh.mp hx)]
  rw [heq,integral_indicator (measurableSet_closedCell z i),integral_const_mul]
  have hinner : (∫ x in closedCell z i, ⟪z i,x⟫ ∂gaussian d) =
      ⟪z i,centroid (closedCell z i)⟫ := Pair.integral_inner_eq_inner_integral _ _
  rw [hinner]
  change ‖z i‖⁻¹*⟪z i,centroid (closedCell z i)⟫=‖z i‖
  rw [hcen,real_inner_self_eq_norm_sq]
  field_simp

lemma minimal_span_cone {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hpos:0<value A) (hactive:∀ j,gaussian d (A j)≠0) (i:Fin k) (hdim:k-1=n+1) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (A i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖centroid (A i)‖ := by
  obtain ⟨K,hK,hcone,hP,hM⟩ := exists_span_cone (sum_centroid_eq_zero hA.1.1)
    (fun j l hjl => negative_inner_of_minimal hA hjl (hactive j) (hactive l))
    i (active_centroid_ne_zero hA hpos (hactive i)) hdim
    (centroid_closedCell hA hpos (hactive i))
  refine ⟨K,hK,hcone,hP.trans ?_,hM⟩
  rw [measureReal_def,measureReal_def,measure_congr (active_eq_closedCell_ae hA hpos (hactive i))]

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_det_nonneg (u v : E) : 0 ≤ ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

end InnerProduct

end GaussianPropeller.Geometry

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.FourReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
variable {d k : ℕ}

lemma residualCoefficient_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualCoefficient (s•z) (s•y)=residualCoefficient z y := by
  simp only [residualCoefficient,real_inner_smul_left,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos hs,mul_pow]
  field_simp

lemma residualVector_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualVector (s•z) (s•y)=s•residualVector z y := by
  rw [residualVector,residualCoefficient_smul hs,residualVector,smul_add,smul_comm]

lemma normalized_tuple_pair [NeZero k] {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0)
    {i j l:Fin k} (hij:i≠j) (hil:i≠l) :
    let z := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
    let u := residualVector (z i) (z j)
    let v := residualVector (z i) (z l)
    ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ (3/Real.pi)^2*‖z i‖^2*
      (1+residualCoefficient (z i) (z j))^2*(1+residualCoefficient (z i) (z l))^2 := by
  dsimp only
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs : 0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  rw [residualVector_smul hs,residualVector_smul hs,residualCoefficient_smul hs,
    residualCoefficient_smul hs]
  have h := minimal_normalized_pair hA hC (hall i) (hall j) (hall l) hij hil
  dsimp only at h
  have hb : 0 ≤ (3/Real.pi)*(‖centroid (A i)‖/Real.sqrt (value A))*
      (1+residualCoefficient (centroid (A i)) (centroid (A j)))*
      (1+residualCoefficient (centroid (A i)) (centroid (A l))) := by
    have hj:=residualCoefficient_pos (negative_inner_of_minimal hA hij (hall i) (hall j))
    have hl:=residualCoefficient_pos (negative_inner_of_minimal hA hil (hall i) (hall l))
    positivity
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mpr h
  rw [Real.sq_sqrt (Geometry.gram_det_nonneg _ _)] at hh
  convert hh using 1 <;> first | rfl | (simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul_pow,div_pow]; ring1)

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SmallCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell
variable {d:ℕ}

lemma sqrt_threshold {C:ℝ} (hC:9/(8*Real.pi)<C) :
    (3/2:ℝ)*gaussianConst < Real.sqrt C := by
  have hCp:0<C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hc0:0≤gaussianConst := by unfold gaussianConst; positivity
  have hc2:gaussianConst^2=1/(2*Real.pi) := by
    rw [gaussianConst,inv_pow,Real.sq_sqrt (by positivity),one_div]
  apply (sq_lt_sq₀ (by positivity : 0≤(3/2:ℝ)*gaussianConst) (Real.sqrt_nonneg C)).mp
  rw [mul_pow,hc2,Real.sq_sqrt hCp.le]
  have he : (3/2:ℝ)^2*(1/(2*Real.pi))=9/(8*Real.pi) := by field_simp; ring
  rwa [he]

lemma minimal_cap_three {A:Fin 4→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) (i:Fin 4) :
    ‖centroid (A i)‖/Real.sqrt (value A) ≤
      (8/3:ℝ)*(gaussian d).real (A i)*(1-(gaussian d).real (A i)) := by
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨K,hK,hcone,hP,hM⟩ := minimal_span_cone (n:=2) hA hCp hall i (by norm_num)
  have hp := active_probability_mem (by norm_num) hA hCp (hall i)
  have hb := Cap.cone_three K hK hcone (by change (gaussian 3).real K∈Set.Ioo (0:ℝ) 1; rw [hP]; exact ⟨hp.1,by linarith only [hp.2]⟩)
    (by change (gaussian 3).real K≤1/2; rw [hP]; exact hp.2)
  change (∫ x, K.indicator (fun x:Space 3=>x 0) x ∂gaussian 3) ≤
    4*gaussianConst*(gaussian 3).real K*(1-(gaussian 3).real K) at hb
  rw [hP,hM] at hb
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hCp)).mpr
  have hs := sqrt_threshold hC
  have hh := mul_le_mul_of_nonneg_right (show 4*gaussianConst ≤ (8/3:ℝ)*Real.sqrt (value A) by linarith only [hs])
    (show 0≤(gaussian d).real (A i)*(1-(gaussian d).real (A i)) by exact mul_nonneg hp.1.le (by linarith only [hp.2]))
  nlinarith only [hb,hh]

lemma minimal_cap_four {A:Fin 5→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) (i:Fin 5) :
    (929/1000:ℝ)*(‖centroid (A i)‖/Real.sqrt (value A))^2 ≤ (gaussian d).real (A i) := by
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨K,hK,hcone,hP,hM⟩ := minimal_span_cone (n:=3) hA hCp hall i (by norm_num)
  have hp := active_probability_mem (by norm_num) hA hCp (hall i)
  have hb := Cap.cone_four K hK hcone (by change 0<(gaussian 4).real K; rw [hP]; exact hp.1)
    (by change 0≤∫ x, K.indicator (fun x:Space 4=>x 0) x ∂gaussian 4; rw [hM]; positivity)
  change (∫ x, K.indicator (fun x:Space 4=>x 0) x ∂gaussian 4)^2 ≤
    (963/2500:ℝ)*(gaussian 4).real K at hb
  rw [hP,hM] at hb
  have hn:(963/2500:ℝ)*(929/1000)<9/(8*Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_lt_d6]
  have hh:=mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤929/1000)
  have hc:=mul_le_mul_of_nonneg_right (hn.trans hC).le hp.1.le
  rw [div_pow,Real.sq_sqrt hCp.le,←mul_div_assoc]
  apply (div_le_iff₀ hCp).mpr
  nlinarith only [hh,hc]

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Configuration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

variable {d k:ℕ} [NeZero k]

lemma exists_configuration_oai (hk:2≤k) {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) :
    Nonempty (Configuration d k) := by
  classical
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs:0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  let v:Fin k→Space d := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
  let σ:=_root_.Tuple.sort (fun j=> -‖v j‖)
  let z:Fin k→Space d := fun j=>v (σ j)
  let P:Fin k→ℝ := fun j=>(gaussian d).real (A (σ j))
  have hr:∀ j,‖v j‖=‖centroid (A j)‖/Real.sqrt (value A) := by
    intro j
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    ring
  have hz:∀ j,‖z j‖=‖centroid (A (σ j))‖/Real.sqrt (value A) := fun j=>hr (σ j)
  refine ⟨{z:=z,P:=P,zero:=?_,norm:=?_,pos:=?_,order:=?_,obtuse:=?_,cap:=?_,
            probability:=?_,half:=?_,quadratic:=?_,linear:=?_,pair:=?_,cap3:=?_,loss4:=?_}⟩
  · dsimp [z]
    rw [Equiv.sum_comp σ]
    simp only [v,←Finset.smul_sum,sum_centroid_eq_zero hA.1.1,smul_zero]
  · dsimp [z]
    rw [Equiv.sum_comp σ (fun j => ‖v j‖^2)]
    simp_rw [hr,div_pow,Real.sq_sqrt hCp.le]
    rw [←Finset.sum_div]
    change value A/value A=1
    exact div_self hCp.ne'
  · intro j
    exact smul_ne_zero hs.ne' (active_centroid_ne_zero hA hCp (hall (σ j)))
  · intro i j hij
    have hh:=_root_.Tuple.monotone_sort (fun j=> -‖v j‖) hij
    exact neg_le_neg_iff.mp hh
  · intro i j hij
    change ⟪(Real.sqrt (value A))⁻¹•centroid (A (σ i)),(Real.sqrt (value A))⁻¹•centroid (A (σ j))⟫<0
    rw [real_inner_smul_left,real_inner_smul_right]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg hs
      (negative_inner_of_minimal hA (σ.injective.ne hij) (hall _) (hall _)))
  · intro j
    rw [hz]
    exact (normalized_centroid_lt_two_thirds (hA.1.1.1 _) hC).le
  · dsimp [P]
    rw [Equiv.sum_comp σ (fun j => (gaussian d).real (A j))]
    exact sum_cell_probability hA.1.1
  · intro j
    exact (active_probability_mem hk hA hCp (hall (σ j))).2
  · intro j
    rw [hz]
    by_cases hk5:k=5
    · subst k
      convert minimal_cap_four hA hC hall (σ j) using 1
      norm_num [P]
    · simp only [ite_eq_right hk5]
      convert normalized_cell_probability (hA.1.1.1 (σ j)) hC using 1 <;>
        norm_num [P,centroid,gaussian]
  · intro j
    rw [hz]
    exact (minimal_linear_quadratic hk hA hC hall (σ j)).le
  · intro i j l hij hil
    exact normalized_tuple_pair hA hC hall (σ.injective.ne hij) (σ.injective.ne hil)
  · intro hk4 j
    subst k
    rw [hz]
    exact minimal_cap_three hA hC hall (σ j)
  · intro hk4 j
    subst k
    rw [hz]
    obtain ⟨x,hx,hpx,hl⟩:=minimal_loss_constraint (by norm_num) hA hC hall (σ j)
    refine ⟨x,hx,hpx,le_trans ?_ hl⟩
    norm_num only [Nat.cast_ofNat] at hl ⊢
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)

end GaussianPropeller.Reduction

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.Reduction.exists_configuration_oai := @OAI.GaussianPropeller.Reduction.exists_configuration_oai
