-- Prove2me | solution 1 for GlobalTheory.JR.Step.UNormal.full_cl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:19.586211+00:00
-- url     : https://prove2.me/submissions/400f3688-9281-42f5-89ee-59a49a9777f3

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
theorem _root_.solution (Y : Gl r k) (i : Fin r) : full Y (Fin.castSucc i) (Fin.last r) = Y.2.1 i := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]
end GlobalTheory.JR.Step.UNormal
