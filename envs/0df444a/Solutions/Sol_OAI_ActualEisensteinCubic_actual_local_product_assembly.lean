-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_local_product_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:32.829468+00:00
-- url     : https://prove2.me/submissions/d224c36d-5d70-4b8b-9e2b-238eb4d0854e

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jfour
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jzero_active
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_nonexceptional
import Theorems.Thm_OAI_FixedRayActiveSet_assemble_local_A5
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_ne_one
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
open ConcreteTraceCRT
open scoped ComplexConjugate
end ActualEisensteinCubic
namespace FourierBridge
open scoped ContDiff FourierTransform SchwartzMap
end FourierBridge
namespace AnalyticBridge
end AnalyticBridge
namespace FourierBridge
open scoped FourierTransform SchwartzMap
end FourierBridge
namespace AnalyticBridge
open scoped FourierTransform SchwartzMap
end AnalyticBridge
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
section
open AddChar MulChar
private theorem localA5Kernel_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    localA5Kernel P hgood ψ j σ ε x 0 =
      if j = 0 then 1 - (Nat.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  simp [localA5Kernel]
private theorem localA5Kernel_active_eq_raw (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ u : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P,
          (canonicalSextic P hgood ^ j) t * ψ (-(u * t))) *
        (((canonicalSextic P hgood)⁻¹) ^ 2) (σ * u) *
        ψ ((ε * x) * ((u⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hu : (u : O ⧸ P) ≠ 0 := Units.ne_zero u
  simp only [localA5Kernel, if_neg hu,
    Units.val_inv_eq_inv_val]
  ring
private theorem localA5Kernel_active_eq_output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (j : ℕ) (hj6 : j < 6)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
      localA5Output P hgood ψ j σ ε x := by
  rw [localA5Kernel_active_eq_raw]
  by_cases hj0 : j = 0
  · subst j
    simpa only [localA5Output, ite_true] using
      canonical_A5_jzero_active P hgood hchar ψ hψ σ ε x
  by_cases hj4 : j = 4
  · subst j
    simpa [localA5Output] using
      canonical_A5_jfour P hgood hchar ψ hψ σ ε x
  simpa only [localA5Output, if_neg hj0, if_neg hj4] using
    canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
end
end ActualEisensteinCubic
namespace PoissonFirstLocal
end PoissonFirstLocal
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
open OAI.ActualEisensteinCubic
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    (∑ h : ∀ i, O ⧸ Ideal.span {p i},
      ∏ i, localA5Kernel (Ideal.span {p i}) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (Ideal.span {p i}) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (Ideal.span {p i}) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let f : ∀ i, (O ⧸ Ideal.span {p i}) → ℂ := fun i h =>
    localA5Kernel (Ideal.span {p i}) (hgood i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (j i) (σ i) (ε i) (x i) h
  let D : ι → ℂ := fun i => localA5Output (Ideal.span {p i}) (hgood i)
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
    (j i) (σ i) (ε i) (x i)
  have hzero : ∀ i, j i ≠ 0 → f i 0 = 0 := by
    intro i hj
    simp only [f, localA5Kernel_zero, if_neg hj]
  have hactive : ∀ i, (∑ u : (O ⧸ Ideal.span {p i})ˣ,
      f i (u : O ⧸ Ideal.span {p i})) = 1 * D i := by
    intro i
    simp only [one_mul, f, D]
    exact localA5Kernel_active_eq_output (Ideal.span {p i})
      (hgood i) (hchar i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (PrimitiveTrace.eisTraceModChar_breveE_ne_one
        (Ideal.span {p i}) (p i) rfl (hp i))
      (j i) (hj6 i) (σ i) (ε i) (x i)
  have h := FixedRayActiveSet.assemble_local_A5
    (fun i => O ⧸ Ideal.span {p i}) j f (fun _ => 1) D hzero hactive
  simpa only [f, D, one_mul] using h
end OAI.ActualEisensteinCubic
