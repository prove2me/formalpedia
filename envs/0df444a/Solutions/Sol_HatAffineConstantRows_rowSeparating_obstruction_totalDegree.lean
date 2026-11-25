-- Prove2me | solution 1 for HatAffineConstantRows.rowSeparating_obstruction_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:21:41.668226+00:00
-- url     : https://prove2.me/submissions/9a9d3d21-0a08-4bae-bd8f-6194f61fcc8b

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_ne_zero
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_totalDegree
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card


section
open scoped BigOperators
namespace HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
private lemma totalDegree_finsetProd_eq_of_nonzero
    {K : Type u} [Field K] {σ ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ K)
    (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨hfa, hfs⟩ := h
      simp [ha, MvPolynomial.totalDegree_mul_of_isDomain hfa
        (by rw [Finset.prod_ne_zero_iff]; exact hfs), ih hfs]
end HatAffineConstantRows
end

set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b : I → K) :
    (affineObstruction A b (rowSeparatingOffset A b)).totalDegree =
      nonzeroRowCount A := by
  classical
  calc
    (affineObstruction A b (rowSeparatingOffset A b)).totalDegree =
        ∑ i : I,
          (affineObstructionFactor A b (rowSeparatingOffset A b) i).totalDegree := by
      simpa [affineObstruction] using
        (totalDegree_finsetProd_eq_of_nonzero Finset.univ
          (fun i => affineObstructionFactor A b (rowSeparatingOffset A b) i)
          (fun i hi => affineObstructionFactor_rowSeparating_ne_zero A b i))
    _ = ∑ i : I, rowDegree (A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact affineObstructionFactor_rowSeparating_totalDegree A b i
    _ = nonzeroRowCount A := by
      rw [nonzeroRowCount, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hAi : A i = 0 <;> simp [rowDegree, hAi]
end HatAffineConstantRows
