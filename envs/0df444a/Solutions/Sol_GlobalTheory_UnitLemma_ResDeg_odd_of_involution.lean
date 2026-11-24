-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ResDeg.odd_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:06.38283+00:00
-- url     : https://prove2.me/submissions/0d0cc4e3-86b4-4521-9fc0-0c21a5d9603d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.ResDeg
theorem _root_.solution {k₀ k : Type} [Field k₀] [Field k] [Fintype k₀] [Finite k] (ι : k₀ →+* k) (q d : ℕ)
    (h0 : Fintype.card k₀ = q ^ 2) (hk : Nat.card k = q ^ (2 * d)) (τ : k ≃+* k) (hτ : ∀ z, τ (τ z) = z)
    (x y : k₀) (hxy : τ (ι x) = ι y) (hne : x ≠ y) : Odd d := by
  classical
  have hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m)) := by
    intro m h
    rw [← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy] at h
    exact hne (ι.injective h).symm
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τA : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun r => by
    have := RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact DFunLike.congr_fun this r)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsq : τA ^ 2 = 1 := AlgEquiv.ext fun z => hτ z
  have hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1 := by
    have := orderOf_dvd_iff_pow_eq_one.2
      (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by
        rw [pow_mul']; exact (congrArg (· ^ 2) hn).trans hsq)
    rwa [hord] at this
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hτz : ∀ z, τ z = z ^ (p ^ n.1) := by
    intro z
    have h1 := DFunLike.congr_fun hn z
    simp only at h1
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
    exact h1.symm
  have hN := n.2
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases c
  · exfalso
    have hn0 : n.1 = 0 := by omega
    apply hfix 0
    rw [hτz, hn0]; simp
  · have hpq : p ^ n.1 = q ^ d := by
      have e1 : p ^ (2 * n.1) = q ^ (2 * d) := by
        rw [← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]
      have e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]; exact e1
      exact Nat.pow_left_injective two_ne_zero e
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    apply hfix m
    rw [hτz, hpq, hm, two_mul]
end GlobalTheory.UnitLemma.ResDeg
