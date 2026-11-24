-- Prove2me | solution 1 for GlobalTheory.MatrixBall.dotProduct_mulVec_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:42.831032+00:00
-- url     : https://prove2.me/submissions/6dbf6e73-13fe-4f4d-a962-7ccea84026e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
open GlobalTheory
open GlobalTheory.MatrixBall
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GlobalTheory.MatrixBall
theorem _root_.solution (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl
end GlobalTheory.MatrixBall
