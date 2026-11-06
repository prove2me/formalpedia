-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_crt_product_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:16:29.565138+00:00
-- url     : https://prove2.me/submissions/d5e0d168-7e18-41f3-a65f-1bb8563c91b6

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_local_product_assembly
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
    [Fintype (O ⧸ ⨅ i, Ideal.span {p i})]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (fun i k => IsCoprime (P i) (P k)) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
    Ideal.quotientInfRingEquivPiQuotient P hcop
  have hsum :
      (∑ z : O ⧸ ⨅ i, P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ h : ∀ i, O ⧸ P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (h i) := by
    apply Fintype.sum_equiv e.toEquiv
    intro z
    rfl
  dsimp only
  rw [hsum]
  exact actual_local_product_assembly p hp hgood hchar j hj6 σ ε x
end OAI.ActualEisensteinCubic
