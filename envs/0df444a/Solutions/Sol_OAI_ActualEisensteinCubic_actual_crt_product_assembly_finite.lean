-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_crt_product_assembly_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:52.243196+00:00
-- url     : https://prove2.me/submissions/aeee67d4-3051-44d7-b582-1630a48c4aca

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_crt_product_assembly

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
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    letI : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
      crtIntersectionFintype p hdistinct
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
  let : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
    crtIntersectionFintype p hdistinct
  exact actual_crt_product_assembly p hdistinct hp hgood hchar j hj6 σ ε x
end OAI.ActualEisensteinCubic
