-- Prove2me | solution 1 for GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:13.512611+00:00
-- url     : https://prove2.me/submissions/a17c75e7-e4a5-40b6-8436-1682101e646d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportJacquetRallisOrbitalIntegrand
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportJacquetRallisOrbitalIntegrandStatement
import Theorems.Thm_GlobalTheory_JR_orbG_integrand_hasCompactSupport


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
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  first | exact @GlobalTheory.JR.orbG_integrand_hasCompactSupport | exact GlobalTheory.JR.orbG_integrand_hasCompactSupport | (intros; apply GlobalTheory.JR.orbG_integrand_hasCompactSupport <;> assumption)
end _root_.GlobalTheory.T
