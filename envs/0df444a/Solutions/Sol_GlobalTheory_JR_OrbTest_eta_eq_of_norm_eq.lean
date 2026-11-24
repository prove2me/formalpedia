-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.eta_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:42.71668+00:00
-- url     : https://prove2.me/submissions/62da1161-1f11-4121-9d39-676b55aa1258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbTest
namespace GlobalTheory.JR.OrbTest
theorem _root_.solution {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]
end GlobalTheory.JR.OrbTest
