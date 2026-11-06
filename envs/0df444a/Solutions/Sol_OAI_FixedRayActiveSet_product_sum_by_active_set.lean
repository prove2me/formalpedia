-- Prove2me | solution 1 for OAI.FixedRayActiveSet.product_sum_by_active_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:29.52997+00:00
-- url     : https://prove2.me/submissions/01784e30-b9aa-4bed-8675-f73196407b64

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
private theorem sum_zero_and_units {F : Type*} [Field F] [Fintype F]
    (f : F → ℂ) :
    (∑ x : F, f x) = f 0 + ∑ u : Fˣ, f (u : F) := by
  classical
  calc
    (∑ x : F, f x) = f 0 +
        ∑ x ∈ (Finset.univ : Finset F).erase 0, f x := by
          simpa only [add_comm] using
            (Finset.sum_erase_add (Finset.univ : Finset F) f
              (Finset.mem_univ (0 : F))).symm
    _ = f 0 + ∑ x : {x : F // x ≠ 0}, f x := by
      congr 1
      apply Finset.sum_subtype
      intro x
      simp
    _ = f 0 + ∑ u : Fˣ, f (u : F) := by
      congr 1
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun u : Fˣ => f (u : F))
        (fun x : {x : F // x ≠ 0} => f x) ?_).symm
      intro u
      rfl
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
    (f : ∀ i, F i → ℂ) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ (Finset.univ : Finset ι).powerset,
        (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  calc
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
        ∏ i, ∑ h : F i, f i h := by
          simpa using (Fintype.prod_sum (fun i (h : F i) => f i h)).symm
    _ = ∏ i, ((∑ u : (F i)ˣ, f i (u : F i)) + f i 0) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [sum_zero_and_units]
      ring
    _ = _ := Finset.prod_add
      (fun i => ∑ u : (F i)ˣ, f i (u : F i))
      (fun i => f i 0) Finset.univ
end OAI.FixedRayActiveSet
