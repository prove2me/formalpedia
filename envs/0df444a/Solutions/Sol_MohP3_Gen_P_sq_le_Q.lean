-- Prove2me | solution 1 for MohP3.Gen.P_sq_le_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:29.664102+00:00
-- url     : https://prove2.me/submissions/f104efce-cba6-4e93-b269-a7bad6e7009f

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_f1f1_mem_Q
public import Theorems.Thm_MohP3_Gen_f1f2_mem_Q
public import Theorems.Thm_MohP3_Gen_f1f3_mem_Q
public import Theorems.Thm_MohP3_Gen_f1f4_mem_Q
public import Theorems.Thm_MohP3_Gen_f2f2_mem_Q
public import Theorems.Thm_MohP3_Gen_f2f3_mem_Q
public import Theorems.Thm_MohP3_Gen_f2f4_mem_Q
public import Theorems.Thm_MohP3_Gen_f3f3_mem_Q
public import Theorems.Thm_MohP3_Gen_f3f4_mem_Q
public import Theorems.Thm_MohP3_Gen_f4f4_mem_Q

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]
namespace MohP3.Gen
theorem _root_.solution : P x y z ^ 2 ≤ Q x y z := by
  rw [pow_two, P, Ideal.span_mul_span, Ideal.span_le]
  rintro g ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  show a * b ∈ Q x y z
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  all_goals first
    | exact f1f1_mem_Q x y z | exact f1f2_mem_Q x y z | exact f1f3_mem_Q x y z
    | exact f1f4_mem_Q x y z | exact f2f2_mem_Q x y z | exact f2f3_mem_Q x y z
    | exact f2f4_mem_Q x y z | exact f3f3_mem_Q x y z | exact f3f4_mem_Q x y z
    | exact f4f4_mem_Q x y z
    | (rw [mul_comm]; first
        | exact f1f2_mem_Q x y z | exact f1f3_mem_Q x y z | exact f1f4_mem_Q x y z
        | exact f2f3_mem_Q x y z | exact f2f4_mem_Q x y z | exact f3f4_mem_Q x y z)
end MohP3.Gen
