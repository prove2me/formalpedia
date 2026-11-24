-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.actU_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:15.085505+00:00
-- url     : https://prove2.me/submissions/fae56831-851e-4185-9d13-e9a658ce2a67

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
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]
end GlobalTheory.JR.OrbTest
