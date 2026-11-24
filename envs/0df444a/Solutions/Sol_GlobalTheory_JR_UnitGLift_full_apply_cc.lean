-- Prove2me | solution 1 for GlobalTheory.JR.UnitGLift.full_apply_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:41.227546+00:00
-- url     : https://prove2.me/submissions/b3f79b14-84ae-44c9-8fac-ff5fb9784282

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitGLift
variable {k : Type} [CommRing k] {r : ℕ}
namespace GlobalTheory.JR.UnitGLift
theorem _root_.solution (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]
end GlobalTheory.JR.UnitGLift
