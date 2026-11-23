-- Prove2me | solution 1 for GlobalTheory.WeilM.norm_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:00.978832+00:00
-- url     : https://prove2.me/submissions/e83790d7-51fc-4488-9d38-a180e9bfbf24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
namespace GlobalTheory.WeilM
theorem _root_.solution (x : R × R) : Algebra.norm R x = x.1 * x.2 := by
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd R), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul]
end GlobalTheory.WeilM
