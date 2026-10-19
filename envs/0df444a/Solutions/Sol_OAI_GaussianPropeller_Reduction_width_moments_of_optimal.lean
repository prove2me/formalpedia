-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.width_moments_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:17:20.672281+00:00
-- url     : https://prove2.me/submissions/4fa3298a-ffe7-4e29-9871-f500a73b87ad

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_integrable_id (d : ℕ) : Integrable (fun x : Space d => x) (gaussian d) := by
  unfold gaussian; exact IsGaussian.integrable_id

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_integrable_inner {d : ℕ} (w : Space d) :
    Integrable (fun x : Space d => ⟪w, x⟫) (gaussian d) :=
  (hn2_integrable_id d).const_inner w

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreMax_integrable {d k : ℕ} [NeZero k] (v : Fin k → Space d) :
    Integrable (fun x => scoreMax v x) (gaussian d) := by
  refine Integrable.mono' (g := fun x => ∑ i, |⟪v i, x⟫|)
    (integrable_finsetSum _ (fun i _ => (hn2_integrable_inner (v i)).abs)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold scoreMax
    apply Continuous.finset_sup'_apply
    intro i _; fun_prop
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h0 := Finset.le_sup' (fun i => ⟪v i, x⟫) (Finset.mem_univ (0 : Fin k))
      have h1 := Finset.single_le_sum (f := fun i => |⟪v i, x⟫|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ (0 : Fin k))
      have h2 := neg_abs_le ⟪v 0, x⟫
      change ⟪v 0, x⟫ ≤ scoreMax v x at h0
      linarith
    · apply Finset.sup'_le
      intro i _
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |⟪v i, x⟫|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i))

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_pair_eq {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (v : Tuple d k) : ⟪v, moments A⟫ =
      ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
  classical
  have hcent : ∀ i, ⟪v.ofLp i, centroid (A i)⟫ = ∫ x, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
    intro i
    rw [integral_indicator (hA i), centroid, integral_inner ((hn2_integrable_id d).integrableOn)]
  rw [PiLp.inner_apply]
  change ∑ i, ⟪v.ofLp i, centroid (A i)⟫ = _
  simp_rw [hcent]
  rw [← integral_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA i))]

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_unique {d k : ℕ} [NeZero k] (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ⟪v j, x⟫) Finset.univ_nonempty
  have hS : (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).Nonempty := ⟨m, by simp⟩
  set i := (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).min' hS with hi
  have hiS : i ∈ Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫) := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiS
  refine ⟨i, ⟨fun j => hiS ▸ hm j (Finset.mem_univ _), fun j hj => ?_⟩, ?_⟩
  · rcases lt_or_eq_of_le (hm j (Finset.mem_univ _)) with h | h
    · rw [hiS]; exact h
    · exfalso
      have : i ≤ j := Finset.min'_le _ _ (by simp [h])
      exact absurd hj (not_lt.mpr this)
  · rintro i' ⟨h1, h2⟩
    have e' : ⟪v i', x⟫ = ⟪v m, x⟫ := le_antisymm (hm i' (Finset.mem_univ _)) (h1 m)
    rcases lt_trichotomy i' i with h | h | h
    · exfalso
      have : i ≤ i' := Finset.min'_le _ _ (by simp [e'])
      exact absurd h (not_lt.mpr this)
    · exact h
    · exfalso
      have := h2 i h
      rw [hiS, e'] at this
      exact lt_irrefl _ this

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_measurable {d k : ℕ} [NeZero k] (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  have : scoreCell v i = (⋂ j, {x | ⟪v j, x⟫ ≤ ⟪v i, x⟫}) ∩ ⋂ j, ⋂ (_ : j < i), {x | ⟪v j, x⟫ < ⟪v i, x⟫} := by
    ext x; simp [scoreCell]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_) (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_width_eq_pair {d k : ℕ} [NeZero k] (v : Tuple d k) :
    width v = ⟪v, moments (scoreCell v.ofLp)⟫ := by
  classical
  rw [hn2_pair_eq (hn2_scoreCell_measurable _), width]
  congr 1; funext x
  obtain ⟨i, hi, hu⟩ := hn2_scoreCell_unique v.ofLp x
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => hi.1 j)
    · exact Finset.le_sup' (fun i => ⟪v.ofLp i, x⟫) (Finset.mem_univ i)
  · intro j _ hj
    exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
  · simp

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_partition {d k : ℕ} [NeZero k] (v : Fin k → Space d) :
    IsPartition (scoreCell v) :=
  ⟨hn2_scoreCell_measurable v, Filter.Eventually.of_forall (hn2_scoreCell_unique v)⟩

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_norm_moments_sq {d k : ℕ} [NeZero k] (A : Fin k → Set (Space d)) :
    ‖moments A‖ ^ 2 = value A := by
  rw [PiLp.norm_sq_eq_of_L2]; rfl

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_pair_le_width {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  have hcent : ∀ i, ⟪v.ofLp i, centroid (A i)⟫ = ∫ x, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
    intro i
    rw [integral_indicator (hA.1 i), centroid, integral_inner ((hn2_integrable_id d).integrableOn)]
  rw [PiLp.inner_apply]
  change ∑ i, ⟪v.ofLp i, centroid (A i)⟫ ≤ width v
  simp_rw [hcent]
  rw [← integral_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA.1 i))]
  unfold width
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA.1 i)))
    (hn2_scoreMax_integrable _)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, hu⟩ := hx
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
    exact Finset.le_sup' (fun i => ⟪v.ofLp i, x⟫) (Finset.mem_univ i)
  · intro j _ hj
    exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
  · simp

theorem solution {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by
  have hv := hn2_norm_moments_sq A
  apply le_antisymm
  · rw [hn2_width_eq_pair]
    set B := scoreCell (moments A).ofLp
    have hB := hA.2 B (hn2_scoreCell_partition _)
    have hw := hn2_norm_moments_sq B
    have h1 := real_inner_le_norm (moments A) (moments B)
    have h2 : ‖moments B‖ ≤ ‖moments A‖ := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, hw, hv]; exact hB
    nlinarith [norm_nonneg (moments A), norm_nonneg (moments B)]
  · have := hn2_pair_le_width hA.1 (moments A)
    rw [real_inner_self_eq_norm_sq, hv] at this
    exact this

