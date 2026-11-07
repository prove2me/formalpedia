-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.split_count_of_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:07.793432+00:00
-- url     : https://prove2.me/submissions/3096ac7c-d228-4b85-b3c2-0e650bd8003a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open MulChar AddChar
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]
private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide
private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two
private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega
end OAI.ShortDraftHeckeBridge
