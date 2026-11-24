-- Prove2me | solution 1 for GlobalTheory.exists_generator_sq_eq_of_sq_mem_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:42.159948+00:00
-- url     : https://prove2.me/submissions/bf663c59-4174-47a9-9db4-9b9bc7f7af15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsGeneratorSqEqOfSqMemZpowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by
  intro p hp a ha
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgn : orderOf g = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : 0 < Nat.card (ZMod p)ˣ := Nat.card_pos
  have gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤ :=
    fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])
  have hdn : orderOf a ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard a
  have hd0 : 0 < orderOf a := orderOf_pos a
  have key : orderOf (g ^ 2) ∣ orderOf (a ^ 2) := orderOf_dvd_of_mem_zpowers (ha g)
  rw [orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn] at key
  generalize Nat.card (ZMod p)ˣ = n at *
  generalize hd : orderOf a = d at *
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd
  · rcases Nat.even_or_odd d with ⟨e, he⟩ | hd_odd
    · refine ⟨a, gen a ?_, rfl⟩
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      have h2 : d.gcd 2 = 2 := Nat.gcd_eq_right ⟨e, by omega⟩
      rw [h1, h2, show n / 2 = m by omega, show d / 2 = e by omega] at key
      have h3 : e ∣ m := by
        rw [he, hm, ← two_mul, ← two_mul] at hdn
        exact Nat.dvd_of_mul_dvd_mul_left two_pos hdn
      have := Nat.dvd_antisymm key h3
      omega
    · have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hd_odd
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      rw [h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega] at key
      have h3 : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])
      have hdm : d = m := Nat.dvd_antisymm h3 key
      have hgm : orderOf (g ^ m) = 2 := by
        have := orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)
        rwa [show orderOf g / 2 = m by omega] at this
      refine ⟨a * g ^ m, gen _ ?_, ?_⟩
      · rw [(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]
        omega
      · have hg1 : g ^ n = 1 := hgn ▸ pow_orderOf_eq_one g
        rw [mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]
  · have hd_odd : Odd d := hn_odd.of_dvd_nat hdn
    refine ⟨a, gen a ?_, rfl⟩
    rw [(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one,
      Nat.div_one, Nat.div_one] at key
    rw [hd]
    exact Nat.dvd_antisymm hdn key
end GlobalTheory
