-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pairAF_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:51.502198+00:00
-- url     : https://prove2.me/submissions/f11852bd-60e8-4272-9743-1e8770b0a164

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_invCharAF_apply
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
namespace ShortDraftLocal
end ShortDraftLocal
open MulChar AddChar
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
private theorem invCharAF_mult {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)
end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ p = -(χ p + ψ p) := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]
end OAI.ShortDraftHeckeBridge
