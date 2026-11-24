-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.continuous_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:41.911801+00:00
-- url     : https://prove2.me/submissions/a65df978-3a1e-4c5e-bb2f-2e888eb2212a

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
theorem _root_.solution {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const
end GlobalTheory.JR.OrbTest
