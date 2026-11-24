-- Prove2me | solution 1 for GlobalTheory.JR.UnitGLift.full_apply_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:44.816825+00:00
-- url     : https://prove2.me/submissions/b10b9444-ceef-488d-b7a7-0a7c0928fbad

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
theorem _root_.solution (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]
end GlobalTheory.JR.UnitGLift
