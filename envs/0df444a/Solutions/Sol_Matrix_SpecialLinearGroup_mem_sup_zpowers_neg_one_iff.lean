-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2b387276-1e9a-51b5-bf23-6ca0418db291

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff

set_option autoImplicit false

open scoped MatrixGroups

namespace Matrix
p2m_export "Matrix" "J SpecialLinearGroup of"
namespace SpecialLinearGroup
namespace MemSupNegOne
p2m_open "Matrix.SpecialLinearGroup Matrix"

def pmSubgroup (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Γ.mul_mem ha hb)
    · right
      have : -(a * b) = a * -b := by rw [mul_neg]
      rw [this]
      exact Γ.mul_mem ha hb
    · right
      have : -(a * b) = -a * b := by rw [neg_mul]
      rw [this]
      exact Γ.mul_mem ha hb
    · left
      have : a * b = -a * -b := by rw [neg_mul_neg]
      rw [this]
      exact Γ.mul_mem ha hb
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (Γ.inv_mem ha)
    · right
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        apply inv_eq_of_mul_eq_one_right
        rw [neg_mul_neg, mul_inv_cancel]
      have : -a⁻¹ ∈ Γ := by
        rw [← hinv]
        exact Γ.inv_mem ha
      exact this

theorem mem_pmSubgroup_iff (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ pmSubgroup Γ ↔ g ∈ Γ ∨ -g ∈ Γ := Iff.rfl

end Matrix.SpecialLinearGroup.MemSupNegOne

open Matrix.SpecialLinearGroup.MemSupNegOne in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ := by
  constructor
  · intro hg
    have hle : Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ pmSubgroup Γ := by
      refine sup_le (fun x hx => Or.inl hx) ?_
      rw [Subgroup.zpowers_le, mem_pmSubgroup_iff]
      right
      rw [neg_neg]
      exact Γ.one_mem
    exact (mem_pmSubgroup_iff Γ g).mp (hle hg)
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have : g = -g * -1 := by rw [neg_mul_neg, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff (solution)
