-- Prove2me | solution 1 for GlobalTheory.JR.FourUnit.fourU_unitU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:11.552595+00:00
-- url     : https://prove2.me/submissions/60645356-1b86-48f9-b4ee-855cc35a4cfe

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicator
import Theorems.Thm_GlobalTheory_JR_FourUnit_addChar_sum
import Theorems.Thm_GlobalTheory_JR_FourUnit_integral_ball_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.FourUnit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.FourUnit
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
    (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ htr hu
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  funext X
  simp only [fourU]
  by_cases h0 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1
  · have hint : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) =
        ∏ i, (Metric.closedBall (0 : E) 1).indicator
          (fun z => ψ (Algebra.trace F E (star z * X.2.1 i))) (c i) := by
      intro c
      by_cases hc : ∀ i, ‖c i‖ ≤ 1
      · have e1 : unitU r F E (X.1, c, X.2.2) = 1 := by
          simp only [unitU]; rw [Set.indicator_of_mem (by exact ⟨h0.1, hc, h0.2⟩)]; rfl
        rw [e1, one_mul]
        simp only [dotProduct, Pi.star_apply, map_sum, addChar_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hc i))]
      · push_neg at hc
        obtain ⟨i, hi⟩ := hc
        have e1 : unitU r F E (X.1, c, X.2.2) = 0 := by
          simp only [unitU]
          exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (h.2.1 i)) _
        rw [e1, zero_mul]
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (mem_closedBall_zero_iff.1 h)) _
    simp_rw [hint]
    rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_ball_char hU M.μE M.volE ψ hψ htr hu]
    rw [Finset.prod_boole]
    simp only [unitU, Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_univ, true_implies, Pi.one_apply]
    simp [h0.1, h0.2]
  · have e : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) = 0 := fun c => by
      simp only [unitU]
      exact Set.indicator_of_notMem (fun h => h0 ⟨h.1, h.2.2⟩) _
    simp_rw [e, zero_mul, integral_zero]
end GlobalTheory.JR.FourUnit
