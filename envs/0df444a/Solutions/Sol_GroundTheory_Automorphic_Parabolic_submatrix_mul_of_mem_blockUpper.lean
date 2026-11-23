-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.submatrix_mul_of_mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:25.107705+00:00
-- url     : https://prove2.me/submissions/39117dad-0b31-4332-b3f8-aed9b07c1aa7

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
theorem _root_.solution {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (c : ι → Fin n) (a : ℕ) :
    ((p : Matrix (Fin n) (Fin n) F) * M).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c =
      (p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
          (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) *
        M.submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => a ≤ β k)]
  have h0 : ∑ k : {k : Fin n // ¬ a ≤ β k}, (p : Matrix (Fin n) (Fin n) F) i k * M k (c j) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have hk : β k < β i := lt_of_lt_of_le (not_le.1 k.2) i.2
      rw [hp hk, zero_mul]
  rw [h0, add_zero]
end GroundTheory.Automorphic.Parabolic
