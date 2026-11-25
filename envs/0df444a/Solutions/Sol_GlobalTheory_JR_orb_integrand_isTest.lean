-- Prove2me | solution 1 for GlobalTheory.JR.orb_integrand_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:48.520567+00:00
-- url     : https://prove2.me/submissions/c6836b00-5cde-4d2f-bb49-688a0edd60e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Theorems.Thm_GlobalTheory_JR_OrbTest_isTest_orbG_integrand
import Theorems.Thm_GlobalTheory_JR_OrbTest_isTest_orbU_integrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.OrbTest
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
end GlobalTheory.JR
