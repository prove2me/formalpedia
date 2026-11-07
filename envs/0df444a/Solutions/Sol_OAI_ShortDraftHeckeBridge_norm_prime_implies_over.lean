-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_prime_implies_over
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:52:53.731505+00:00
-- url     : https://prove2.me/submissions/73972fca-e45a-44c5-a021-9a367268b67a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [hI]
      exact (Nat.irreducible_iff_nat_prime p).2 hp)
  have hover : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def, algebraMap_int_eq]
    simpa [hI] using Ideal.span_singleton_absNorm (I := I) (hI ▸ hp)
  exact ⟨hprime, hover⟩
end OAI.ShortDraftHeckeBridge
