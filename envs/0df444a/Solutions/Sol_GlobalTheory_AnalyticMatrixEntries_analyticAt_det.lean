-- Prove2me | solution 1 for GlobalTheory.AnalyticMatrixEntries.analyticAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:25.627154+00:00
-- url     : https://prove2.me/submissions/039d2063-6323-49d7-946c-e9aa9f4ac6fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticMatrixEntries
universe u_1 u_2
namespace GlobalTheory.AnalyticMatrixEntries
theorem _root_.solution {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : X → E →L[ℂ] E} {a : X} (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z : X ↦ LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  let b := Module.finBasis ℂ E
  have hfun : (fun z : X => LinearMap.det (A z : E →ₗ[ℂ] E)) =
      fun z => ∑ σ : Equiv.Perm (Fin (Module.finrank ℂ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, b.repr (A z (b i)) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
  exact analyticAt_entry b hA (σ i) i
end GlobalTheory.AnalyticMatrixEntries
