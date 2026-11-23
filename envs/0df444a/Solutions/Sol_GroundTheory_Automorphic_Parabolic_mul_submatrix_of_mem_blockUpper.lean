-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mul_submatrix_of_mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:19.824844+00:00
-- url     : https://prove2.me/submissions/3b25bce8-7a9a-4ccd-83fd-19538bd0dabf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



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
theorem _root_.solution {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (r : ι → Fin n) (b : ℕ) :
    (M * (q : Matrix (Fin n) (Fin n) F)).submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) =
      M.submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) *
        (q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
          (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => γ k ≤ b)]
  have h0 : ∑ k : {k : Fin n // ¬ γ k ≤ b}, M (r i) k * (q : Matrix (Fin n) (Fin n) F) k j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have hk : γ j < γ k := lt_of_le_of_lt j.2 (not_le.1 k.2)
      rw [hq hk, mul_zero]
  rw [h0, add_zero]
end GroundTheory.Automorphic.Parabolic
