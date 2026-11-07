-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_p_sq_fiber_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:48.773306+00:00
-- url     : https://prove2.me/submissions/8b212fbe-e242-4661-915d-d313d19ce473

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_split
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_p_sq_split_factors

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
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      {I : Ideal O | ∃ P Q : Ideal O,
        P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        I = P * Q} := by
  ext I
  constructor
  · exact norm_p_sq_split_factors hp hmod I
  · rintro ⟨P, Q, hP, hQ, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, absNorm_split hp hmod P, absNorm_split hp hmod Q, pow_two]
end OAI.ShortDraftHeckeBridge
