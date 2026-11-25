-- Prove2me | solution 1 for KStar.Tree.exists_sq_unit_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:38.05984+00:00
-- url     : https://prove2.me/submissions/653ec29c-e415-49ad-a858-b3ecced9514f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Tree
variable (l : ℕ) [Fact l.Prime]
private theorem nsa_isUnit {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  by_contra hu
  have : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact hc this
private theorem nsa_dvd_iff (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
end KStar.Tree
end

set_option autoImplicit false
open KStar KStar.Tree
variable (l : ℕ) [Fact l.Prime]
namespace KStar.Tree
theorem _root_.solution (n : ℕ) (hn : ¬ (l - 1) / 2 ∣ n) (hl : l ≠ 2) :
    ∃ u : ℤ_[l]ˣ, ¬ (l : ℤ_[l]) ^ (0 + 1) ∣ ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hx : PadicInt.toZMod ((((g : ZMod l).val : ℕ)) : ℤ_[l]) = (g : ZMod l) := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hU : IsUnit ((((g : ZMod l).val : ℕ)) : ℤ_[l]) := by
    apply nsa_isUnit
    rw [nsa_dvd_iff, hx]
    exact g.ne_zero
  refine ⟨hU.unit, fun h => hn ?_⟩
  rw [zero_add, pow_one, nsa_dvd_iff, map_sub, map_one, map_pow, Units.val_pow_eq_pow_val, map_pow,
    IsUnit.unit_spec, hx, sub_eq_zero, ← pow_mul] at h
  have h1 : g ^ (2 * n) = 1 := by
    apply Units.ext
    simpa using h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hl
  have e1 : l - 1 = 2 * k := by omega
  rw [e1] at h2 ⊢
  rw [Nat.mul_div_cancel_left k two_pos]
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h2
end KStar.Tree
