-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mul_rowOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:18.730898+00:00
-- url     : https://prove2.me/submissions/c20dac3d-3067-4167-ad01-3da8a821071a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (A * rowOp k c) i j = A i j + A i k * c j := by
  rw [rowOp, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
