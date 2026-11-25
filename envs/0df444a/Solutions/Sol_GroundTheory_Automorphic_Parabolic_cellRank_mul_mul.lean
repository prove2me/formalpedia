-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:25.103228+00:00
-- url     : https://prove2.me/submissions/ab22eaff-9209-426d-8538-da9ae966e591

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_submatrix_mul_of_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_submatrix_of_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {p q : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hq : q ∈ blockUpper F n γ) (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ (p * g * q) a b = cellRank β γ g a b := by
  classical
  unfold cellRank
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, submatrix_mul_of_mem_blockUpper hp,
    mul_submatrix_of_mem_blockUpper hq,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_submatrix_of_mem_blockUpper hp a),
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_submatrix_of_mem_blockUpper' hq b)]
end GroundTheory.Automorphic.Parabolic
