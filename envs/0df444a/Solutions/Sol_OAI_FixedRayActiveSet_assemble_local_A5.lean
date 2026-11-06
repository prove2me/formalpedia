-- Prove2me | solution 1 for OAI.FixedRayActiveSet.assemble_local_A5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:26.496415+00:00
-- url     : https://prove2.me/submissions/36a88d57-2306-42db-872c-1d09e1f82798

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_FixedRayActiveSet_product_sum_by_active_set
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end
section
open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT
end
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
end ActualEisensteinCubic
namespace ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
end ConcreteBreveE
namespace FixedRayActiveSet
open scoped BigOperators
private theorem branch_zero_outside_admissible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) (scalar dual inactive : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → inactive i = 0)
    (A : Finset ι)
    (hnot : ¬ (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A) :
    (∏ i ∈ A, scalar i * dual i) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A, inactive i) = 0 := by
  obtain ⟨i, hiM, hiA⟩ := Finset.not_subset.mp hnot
  have hj : j i ≠ 0 := (Finset.mem_filter.mp hiM).2
  have hi : i ∈ (Finset.univ : Finset ι) \ A := by simp [hiA]
  have hprod : (∏ k ∈ (Finset.univ : Finset ι) \ A, inactive k) = 0 :=
    Finset.prod_eq_zero hi (hzero i hj)
  rw [hprod, mul_zero]
end FixedRayActiveSet
namespace CubeInversion
end CubeInversion
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.FixedRayActiveSet
open scoped BigOperators
namespace OAI.FixedRayActiveSet
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (j : ι → ℕ) (f : ∀ i, F i → ℂ)
    (scalar dual : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → f i 0 = 0)
    (hactive : ∀ i, (∑ u : (F i)ˣ, f i (u : F i)) =
      scalar i * dual i) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, scalar i * dual i) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  rw [product_sum_by_active_set]
  have hreplace : ∀ A : Finset ι,
      (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) =
        ∏ i ∈ A, scalar i * dual i := by
    intro A
    apply Finset.prod_congr rfl
    intro i _
    exact hactive i
  conv_lhs =>
    arg 2
    ext A
    rw [hreplace A]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hAdmissible : (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A
  · simp [hAdmissible]
  · simp [hAdmissible,
      branch_zero_outside_admissible j scalar dual (fun i => f i 0)
        (fun i hj => hzero i hj)
        A hAdmissible]
end OAI.FixedRayActiveSet
