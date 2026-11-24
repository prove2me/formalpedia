-- Prove2me | solution 1 for GlobalTheory.JR.Step.UNormal.full_ll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:10:52.636327+00:00
-- url     : https://prove2.me/submissions/1723ddd3-efd4-46b2-a7ba-228fb230a70e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant

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
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.UNormal
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step.UNormal
theorem _root_.solution (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]
end GlobalTheory.JR.Step.UNormal
