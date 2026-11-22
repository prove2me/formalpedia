-- Prove2me | solution 1 for HardyFLocal.regional_outcome_summability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:53:03.243588+00:00
-- url     : https://prove2.me/submissions/6eb30519-b5dc-440f-80a7-02ea87440171

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_elementary_coordinates_summable
open HardyCausaloid
namespace HardyFLocal
open scoped Matrix Kronecker ComplexOrder
private theorem summable_product_assignments {ι : Type} [Fintype ι] (f : ι → ℕ → ℝ)
    (hf : ∀ i, Summable (f i)) : Summable fun y : ι → ℕ => ∏ i, f i (y i) := by
  classical
  apply Summable.of_norm
  simp only [norm_prod, Real.norm_eq_abs]
  apply summable_of_sum_le (fun _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (c := ∏ i, ∑' j, |f i j|)
  intro s
  let b (i : ι) := s.image fun y => y i
  calc
    _ ≤ ∑ y ∈ Fintype.piFinset b, ∏ i, |f i (y i)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        exact Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hy
      · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _
    _ = ∏ i, ∑ j ∈ b i, |f i j| := (Finset.prod_univ_sum b (fun i j => |f i j|)).symm
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      fun i _ => (hf i).abs.sum_le_tsum _ (fun _ _ => abs_nonneg _)


open HardyCausaloid

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    {O₁ O₂ : Finset (X m n)} (h : Disjoint O₁ O₂)
    (α : Lab (Setting m n) (Outcome m n) O₁)
    (F : ∀ x : O₂, Setting m n x.1) :
    Summable fun y : O₂ → ℕ => (actualCausaloid S L).r (O₁ ∪ O₂) (joinLab α (labOf F y)) := by
  classical
  let C := actualCausaloid S L
  let e := Equiv.Finset.union O₁ O₂ h
  apply Pi.summable.mpr
  intro k
  apply summable_sum
  intro l _
  apply Summable.mul_right
  let g₁ (x : O₁) := C.Λ₁ x.1 (α x) (l (e (.inl x)))
  let g₂ (x : O₂) (z : ℕ) := C.Λ₁ x.1 ⟨F x,z⟩ (l (e (.inr x)))
  have hs (x : O₂) : Summable (g₂ x) :=
    Pi.summable.mp (elementary_coordinates_summable S (F x)) _
  apply ((summable_product_assignments g₂ hs).mul_left (∏ x, g₁ x)).congr
  intro y
  let f (x : ↥(O₁ ∪ O₂)) := C.Λ₁ x.1 (joinLab α (labOf F y) x) (l x)
  change _ = ∏ x, f x
  rw [← e.prod_comp f, Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro x _
    change C.Λ₁ x.1 (α x) _ = C.Λ₁ x.1 (joinLab α (labOf F y) (e (.inl x))) _
    simp [e,joinLab,x.property]
  · apply Finset.prod_congr rfl
    intro x _
    have hx : x.val ∉ O₁ := fun hh => Finset.disjoint_left.mp h hh x.property
    change C.Λ₁ x.1 ⟨F x,y x⟩ _ = C.Λ₁ x.1 (joinLab α (labOf F y) (e (.inr x))) _
    simp [e,joinLab,labOf,hx]

