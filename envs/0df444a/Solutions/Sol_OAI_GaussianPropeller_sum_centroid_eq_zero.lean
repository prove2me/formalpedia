-- Prove2me | solution 1 for OAI.GaussianPropeller.sum_centroid_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:12:26.655979+00:00
-- url     : https://prove2.me/submissions/fd840415-fc3c-49a9-bc78-e00046feca13

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments

open OAI OAI.GaussianPropeller
universe uF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  classical
  have hint : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian; exact IsGaussian.integrable_id
  have h1 : ∀ i, centroid (A i) = ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := fun i =>
    (integral_indicator (hA.1 i)).symm
  simp_rw [h1]
  rw [← integral_finsetSum _ (fun i _ => hint.indicator (hA.1 i))]
  have h2 : (fun x => ∑ i, (A i).indicator (fun x : Space d => x) x) =ᵐ[gaussian d] fun x => x := by
    filter_upwards [hA.2] with x hx
    obtain ⟨i, hi, hu⟩ := hx
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hj
      exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
    · simp
  rw [integral_congr_ae h2]
  unfold gaussian
  exact integral_id_stdGaussian

