-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.continuous_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:41.088661+00:00
-- url     : https://prove2.me/submissions/0ee60ffd-5f9f-4716-b52f-47a07feeee58

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
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv
end GlobalTheory.JR.OrbTest
