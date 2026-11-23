-- Prove2me | solution 1 for GlobalTheory.UnramValue.pow_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:02.556751+00:00
-- url     : https://prove2.me/submissions/aae51e4a-1ce9-4d35-8736-07ef307c2dd4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
namespace GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
private lemma exists_pow_prime_pow_eq_add_prime_mul (k : ℕ) (a : ℤ_[l]) : ∃ c : ℤ_[l], a ^ (l ^ k) = a + l * c := by
  have h : a ^ (l ^ k) - a ∈ Ideal.span {(l : ℤ_[l])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card_pow, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨c, by linear_combination -hc⟩
private lemma pow_prime_pow_totient_eq_self_of_pow_eq_one {m : ℕ} (hl : ¬ l ∣ m) {x : Om l} (hx : x ^ m = 1) :
    x ^ (l ^ m.totient) = x := by
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
  have hmod : l ^ m.totient % m = 1 % m := Nat.ModEq.pow_totient hcop
  have key : ∀ n, x ^ n = x ^ (n % m) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hx, one_pow, mul_one]
  rw [key, hmod, ← key, pow_one]
end GlobalTheory.UnramValue
end
end

set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m : ℕ} (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m) :
    ∃ z ∈ rootRing l m, y ^ (l ^ m.totient) = y + l * z := by
  have hp : l.Prime := Fact.out
  suffices H : ∃ z : rootRing l m,
      (⟨y, hy⟩ : rootRing l m) ^ (l ^ m.totient) = ⟨y, hy⟩ + (l : rootRing l m) * z by
    obtain ⟨z, hz⟩ := H
    refine ⟨z, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  refine Algebra.adjoin_induction
    (p := fun y hy => ∃ z : rootRing l m,
      (⟨y, hy⟩ : rootRing l m) ^ (l ^ m.totient) = ⟨y, hy⟩ + (l : rootRing l m) * z)
    ?_ ?_ ?_ ?_ hy
  · intro x hx
    refine ⟨0, Subtype.ext ?_⟩
    simp [pow_prime_pow_totient_eq_self_of_pow_eq_one hl hx]
  · intro r
    obtain ⟨c, hc⟩ := exists_pow_prime_pow_eq_add_prime_mul (l := l) m.totient r
    refine ⟨algebraMap ℤ_[l] (rootRing l m) c, ?_⟩
    show (algebraMap ℤ_[l] (rootRing l m) r) ^ (l ^ m.totient) =
      algebraMap ℤ_[l] (rootRing l m) r + (l : rootRing l m) * algebraMap ℤ_[l] (rootRing l m) c
    rw [← map_pow, hc, map_add, map_mul, map_natCast]
  · rintro x y hx hy ⟨z1, h1⟩ ⟨z2, h2⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x, hx⟩ : rootRing l m) ⟨y, hy⟩ m.totient
    refine ⟨z1 + z2 + ⟨x, hx⟩ * ⟨y, hy⟩ * r, ?_⟩
    show ((⟨x, hx⟩ : rootRing l m) + ⟨y, hy⟩) ^ (l ^ m.totient) = (⟨x, hx⟩ + ⟨y, hy⟩) + _
    rw [hr, h1, h2]
    ring
  · rintro x y hx hy ⟨z1, h1⟩ ⟨z2, h2⟩
    refine ⟨⟨x, hx⟩ * z2 + z1 * ⟨y, hy⟩ + (l : rootRing l m) * z1 * z2, ?_⟩
    show ((⟨x, hx⟩ : rootRing l m) * ⟨y, hy⟩) ^ (l ^ m.totient) = (⟨x, hx⟩ * ⟨y, hy⟩) + _
    rw [mul_pow, h1, h2]
    ring
end GlobalTheory.UnramValue
