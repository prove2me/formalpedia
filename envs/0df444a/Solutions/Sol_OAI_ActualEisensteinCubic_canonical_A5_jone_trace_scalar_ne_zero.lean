-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone_trace_scalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:20.055192+00:00
-- url     : https://prove2.me/submissions/9b7599dd-82ce-4075-bf70-9a1fabb77bab

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct_scalar_ne_zero
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive


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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open OAI.ActualEisensteinCubic
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    let ψ : AddChar (O ⧸ P) ℂ := hP.symm ▸
      ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  subst P
  exact canonical_A5_jone_direct_scalar_ne_zero (Ideal.span {p}) hgood hchar
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)
    ε hε
end OAI.ActualEisensteinCubic
