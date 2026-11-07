-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChangeWeight_zero_of_norm_prime_pow_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:09.364169+00:00
-- url     : https://prove2.me/submissions/42bd0c71-0140-41cb-b476-16ac901f5508

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
namespace ShortDraftHeckeBridge
private theorem base_ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank ActualEisensteinSieve.K,
    IsCyclotomicExtension.Rat.finrank 3 ActualEisensteinSieve.K]
  decide
end ShortDraftHeckeBridge
namespace NormSplitArithmetic
end NormSplitArithmetic
namespace NormFiberCRT
end NormFiberCRT
namespace NormFiberMult
end NormFiberMult
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Filter Asymptotics
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
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
theorem _root_.solution {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ k) :
    baseChangeWeight χ I = 0 := by
  by_cases hμ : UniqueFactorizationMonoid.moebius I = 0
  · simp [baseChangeWeight, hμ]
  have hsq : Squarefree I := by
    by_contra hnsq
    exact hμ (UniqueFactorizationMonoid.moebius_of_not_squarefree hnsq)
  have hmem : ((p ^ k : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hspanle : Ideal.span {((p : O) ^ k)} ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmem)
  have hpowdiv : I ∣ (Ideal.span {(p : O)}) ^ k := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr hspanle
  have hdiv : I ∣ Ideal.span {(p : O)} :=
    (hsq.dvd_pow_iff_dvd (by omega : k ≠ 0)).mp hpowdiv
  have hnormdiv := map_dvd Ideal.absNorm hdiv
  rw [hI, Ideal.absNorm_span_natCast, base_ring_rank_two] at hnormdiv
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnormdiv
  omega
end OAI.ShortDraftHeckeBridge
