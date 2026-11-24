-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.colOp_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:17.065791+00:00
-- url     : https://prove2.me/submissions/9a1e6468-e896-4d2e-b9ae-5046940046ca

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
    (colOp k c * A) i j = A i j + c i * A k j := by
  rw [colOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
