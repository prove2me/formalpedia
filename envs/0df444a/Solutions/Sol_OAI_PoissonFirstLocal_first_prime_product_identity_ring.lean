-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_prime_product_identity_ring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:18:34.501724+00:00
-- url     : https://prove2.me/submissions/d1f108d6-b1ce-4dd7-a19c-53575c914131

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_PoissonFirstLocal_first_local_identity_ring
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
namespace TraceLambdaPhase
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate
end TraceLambdaPhase
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
end ActualEisensteinCubic
namespace PoissonFirstLocal
open scoped Classical
private theorem quotientUnitMask_mul {R : Type*} [CommRing R]
    (a b : R) :
    quotientUnitMask (a * b) =
      quotientUnitMask a * quotientUnitMask b := by
  classical
  by_cases ha : IsUnit a <;> by_cases hb : IsUnit b <;>
    simp [quotientUnitMask, (Commute.all a b).isUnit_mul_iff, ha, hb]
end PoissonFirstLocal
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
end
end ActualEisensteinCubic
namespace AnalyticBridge
end AnalyticBridge
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
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
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution
    {R : Type*} [CommRing R]
    (side : Bool) (P : Finset R)
    (parityBit ε₁ ε₂ : R → Bool)
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      (χ (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      quotientUnitMask
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  classical
  calc
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      ∏ z ∈ P, newFactorRing (parityBit z) (ε₁ z) (ε₂ z) z χ := by
        apply Finset.prod_congr rfl
        intro z hz
        exact first_local_identity_ring side (parityBit z) (ε₁ z) (ε₂ z) z χ hχ
    _ = (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z),
          (χ z) ^ 4) *
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z),
          quotientUnitMask z) := by
        simp only [newFactorRing]
        exact Finset.prod_ite _ _
    _ = _ := by
      have hchar (S : Finset R) :
          (∏ z ∈ S, (χ z) ^ 4) = (χ (∏ z ∈ S, z)) ^ 4 := by
        induction S using Finset.induction_on with
        | empty => simp
        | @insert z S hz ih => simp [hz, ih, map_mul, mul_pow]
      have hmask (S : Finset R) :
          (∏ z ∈ S, quotientUnitMask z) =
            quotientUnitMask (∏ z ∈ S, z) := by
        induction S using Finset.induction_on with
        | empty => simp [quotientUnitMask]
        | @insert z S hz ih =>
            simp [hz, ih, quotientUnitMask_mul]
      rw [hchar, hmask]
end OAI.PoissonFirstLocal
