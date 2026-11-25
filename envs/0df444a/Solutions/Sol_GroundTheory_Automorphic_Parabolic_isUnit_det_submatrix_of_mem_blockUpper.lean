-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isUnit_det_submatrix_of_mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:47.721474+00:00
-- url     : https://prove2.me/submissions/bd9a4b89-e0c9-4993-9fb2-a768d31b5db5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_submatrix_mul_of_mem_blockUpper

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
theorem _root_.solution {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (a : ℕ) :
    IsUnit ((p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
      (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))).det := by
  classical
  apply Matrix.isUnit_det_of_right_inverse (B := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)))
  rw [← submatrix_mul_of_mem_blockUpper hp, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective
end GroundTheory.Automorphic.Parabolic
