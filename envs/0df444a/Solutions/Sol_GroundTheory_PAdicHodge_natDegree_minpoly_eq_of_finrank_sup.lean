-- Prove2me | solution 1 for GroundTheory.PAdicHodge.natDegree_minpoly_eq_of_finrank_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:06.88106+00:00
-- url     : https://prove2.me/submissions/ef52f582-526a-44f6-88f1-ae1e7af83b1c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_mul_le
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_adjoin_simple
import Theorems.Thm_GroundTheory_PAdicHodge_finiteDimensional_of_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTraceFₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTraceₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k A B : IntermediateField B₀ Ω} (hA : k ≤ A)
    (hB : k ≤ B) [FiniteDimensional B₀ A] [FiniteDimensional B₀ B]
    (h : finrank B₀ ↥(A ⊔ B) * finrank B₀ k = finrank B₀ A * finrank B₀ B) {z : Ω} (hz : z ∈ A) :
    (minpoly B z).natDegree = (minpoly k z).natDegree := by
  haveI := finiteDimensional_of_le hA
  have hz0 : IsIntegral B₀ z := by
    have := IsIntegral.of_finite B₀ (⟨z, hz⟩ : A)
    exact this.map (IsScalarTower.toAlgHom B₀ A Ω)
  have hzk : IsIntegral k z := hz0.tower_top
  have hzB : IsIntegral B z := hz0.tower_top
  have hz' : adjoin B₀ {z} ≤ A := by
    rw [adjoin_le_iff]; simpa using hz
  have ek := finrank_sup_adjoin_simple k hzk
  have eB := finrank_sup_adjoin_simple B hzB
  have c1 := finrank_sup_mul_le (k := k ⊔ adjoin B₀ {z}) (X := A) (Y := B ⊔ adjoin B₀ {z})
    (sup_le hA hz') (sup_le_sup_right hB _)
  have s1 : A ⊔ (B ⊔ adjoin B₀ {z}) = A ⊔ B :=
    le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hz'.trans le_sup_left)))
      (sup_le_sup_left le_sup_left _)
  rw [s1, ek, eB] at c1
  have c2 := finrank_sup_mul_le (k := k) (X := B) (Y := k ⊔ adjoin B₀ {z}) hB le_sup_left
  have s2 : B ⊔ (k ⊔ adjoin B₀ {z}) = B ⊔ adjoin B₀ {z} := by
    rw [← sup_assoc, sup_eq_left.2 hB]
  rw [s2, ek, eB] at c2
  have pA : 0 < finrank B₀ A := Module.finrank_pos
  have pB : 0 < finrank B₀ B := Module.finrank_pos
  have pk : 0 < finrank B₀ k := Module.finrank_pos
  have pAB : 0 < finrank B₀ A * finrank B₀ B := Nat.mul_pos pA pB
  have pBk : 0 < finrank B₀ B * finrank B₀ k := Nat.mul_pos pB pk
  apply le_antisymm
  · have : finrank B₀ B * finrank B₀ k * (minpoly B z).natDegree ≤
        finrank B₀ B * finrank B₀ k * (minpoly k z).natDegree := by
      calc _ = finrank B₀ B * (minpoly B z).natDegree * finrank B₀ k := by ring
        _ ≤ finrank B₀ B * (finrank B₀ k * (minpoly k z).natDegree) := c2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this pBk
  · have : finrank B₀ A * finrank B₀ B * (minpoly k z).natDegree ≤
        finrank B₀ A * finrank B₀ B * (minpoly B z).natDegree := by
      calc _ = finrank B₀ ↥(A ⊔ B) * finrank B₀ k * (minpoly k z).natDegree := by rw [h]
        _ = finrank B₀ ↥(A ⊔ B) * (finrank B₀ k * (minpoly k z).natDegree) := by ring
        _ ≤ finrank B₀ A * (finrank B₀ B * (minpoly B z).natDegree) := c1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this pAB
end GroundTheory.PAdicHodge
