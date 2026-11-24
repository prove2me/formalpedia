-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:09.018441+00:00
-- url     : https://prove2.me/submissions/ad6c6475-6c55-4d59-bb02-62544a167180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Theorems.Thm_GlobalTheory_JR_Spec_isIntegral_or_isIntegral_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  first | exact @GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | exact GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | (intros; apply GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv <;> assumption)
end _root_.GlobalTheory.T
