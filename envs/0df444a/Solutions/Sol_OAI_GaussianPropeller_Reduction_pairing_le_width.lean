-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.pairing_le_width
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:13:49.726851+00:00
-- url     : https://prove2.me/submissions/65b1faf5-ef79-4f86-b0cc-b9c61a23028f

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

theorem solution {A : Fin k → Set (Space d)} (hA : IsPartition A)
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

