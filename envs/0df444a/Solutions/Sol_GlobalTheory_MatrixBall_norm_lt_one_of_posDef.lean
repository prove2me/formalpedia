-- Prove2me | solution 1 for GlobalTheory.MatrixBall.norm_lt_one_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:20.332674+00:00
-- url     : https://prove2.me/submissions/ec2979b4-57b6-4485-9890-63b75c806cd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
import Theorems.Thm_GlobalTheory_MatrixBall_dotProduct_mulVec_eq_inner
import Theorems.Thm_GlobalTheory_MatrixBall_inner_one_sub

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
theorem _root_.solution {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)
end GlobalTheory.MatrixBall
