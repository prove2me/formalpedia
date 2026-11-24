-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.rowOp_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:19.915103+00:00
-- url     : https://prove2.me/submissions/61be25f8-5f27-4d66-9b01-ff8488f1dfc2

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
    (rowOp k c * A) i j = A i j + if i = k then ∑ l, c l * A l j else 0 := by
  rw [rowOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : i = k <;> simp [h]
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
