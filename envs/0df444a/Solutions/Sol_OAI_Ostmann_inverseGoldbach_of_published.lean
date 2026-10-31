-- Prove2me | solution 1 for OAI.Ostmann.inverseGoldbach_of_published
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:41:20.955166+00:00
-- url     : https://prove2.me/submissions/c0f172c5-0800-4084-8120-a251e08dd21d

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D002
import Definitions.Def_OAIQ095D003
import Theorems.Thm_OAI_Ostmann_twoInfiniteSummandsImpossible_of_published

section
-- module Solutions.OAIQ095_OS.Ostmann_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

theorem sumset_comm (A B : Set ℕ) : sumset A B = sumset B A := by
  ext n
  simp only [mem_sumset]
  constructor <;> rintro ⟨a, ha, b, hb, hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩

theorem EventuallyPrimeSumset.symm {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) : EventuallyPrimeSumset B A := by
  simpa only [EventuallyPrimeSumset, sumset_comm B A] using h

open scoped symmDiff

/-- The manuscript's finite symmetric difference and threshold formulations agree. -/
theorem finite_symmDiff_iff (A B : Set ℕ) :
    (sumset A B ∆ primes).Finite ↔ EventuallyPrimeSumset A B := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := Set.finite_iff_bddAbove.mp h
    refine ⟨M + 1, ?_⟩
    intro n hn
    have hout : n ∉ sumset A B ∆ primes := by
      intro hin
      have := hM hin
      omega
    simp only [Set.mem_symmDiff, primes, Set.mem_ofPred_eq] at hout
    tauto
  · rintro ⟨N, hN⟩
    apply (Set.finite_Iio N).subset
    intro n hn
    by_contra hlt
    have heq := hN n (Nat.le_of_not_gt hlt)
    simp only [Set.mem_symmDiff, primes, Set.mem_ofPred_eq, heq,
      and_not_self, or_self] at hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Endpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

theorem eventual_sumset_iff (A B : Set ℕ) :
    EventuallyEqual (A+B) primes ↔ ∃ N : ℕ,
      (∀ a ∈ A, ∀ b ∈ B, N ≤ a+b → Nat.Prime (a+b)) ∧
      (∀ p : ℕ, N ≤ p → Nat.Prime p → ∃ a ∈ A, ∃ b ∈ B, a+b=p) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_, ?_⟩
    · intro a ha b hb hab
      exact (hN (a+b) hab).mp (Set.add_mem_add ha hb)
    · intro p hp hprime
      exact Set.mem_add.mp ((hN p hp).mpr hprime)
  · rintro ⟨N, hexclude, hcover⟩
    refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
    · intro hs
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
      exact hexclude a ha b hb hn
    · intro hp
      exact Set.mem_add.mpr (hcover n hn hp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_FiniteCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

theorem shifted_difference_coprime {q a b : ℕ} (hq : q.Prime)
    (ha : a < q) (hb : b < q) (hab : a ≠ b) : (q + a - b).Coprime q := by
  apply Nat.Coprime.symm
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  have he : q + a - b + b = q + a := Nat.sub_add_cancel (by omega)
  have hm := (Nat.modEq_zero_iff_dvd.mpr hd).add_right b
  rw [he] at hm
  simp only [Nat.ModEq, Nat.add_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
  exact hab hm

theorem separatingPrime_prime (M a : ℕ) : (separatingPrime M a).Prime :=
  Nat.prime_nth_prime (M+a)

theorem lt_separatingPrime (M a : ℕ) : M < separatingPrime M a := by
  have h := Nat.add_two_le_nth_prime (M+a)
  dsimp [separatingPrime]
  omega

theorem separatingPrime_injective (M : ℕ) : Function.Injective (separatingPrime M) := by
  intro a b h
  have hab := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
  exact Nat.add_left_cancel hab

theorem exists_reduced_class (t : Finset ℕ) (f : ℕ → ℕ) (M : ℕ)
    (ha : ∀ a ∈ t, a ≤ M) (hf : ∀ a ∈ t, f a ≤ M)
    (hne : ∀ a ∈ t, a ≠ f a) :
    ∃ Q r : ℕ, Q ≠ 0 ∧ r.Coprime Q ∧
      ∀ a ∈ t, r ≡ separatingPrime M a + a - f a [MOD separatingPrime M a] ∧
        separatingPrime M a ∣ Q := by
  classical
  let q := separatingPrime M
  let c := fun a => q a + a - f a
  have hq : ∀ a, (q a).Prime := separatingPrime_prime M
  have hnonzero : ∀ a ∈ t, q a ≠ 0 := fun a _ => (hq a).ne_zero
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun a b => (q a).Coprime (q b)) := by
    intro a _ b _ hab
    exact (Nat.coprime_primes (hq a) (hq b)).mpr
      (fun h => hab (separatingPrime_injective M h))
  let r := Nat.chineseRemainderOfFinset c q t hnonzero hpair
  have hr : ∀ a ∈ t, (r : ℕ) ≡ c a [MOD q a] := r.property
  have hc : ∀ a ∈ t, (c a).Coprime (q a) := by
    intro a hat
    exact shifted_difference_coprime (hq a)
      ((ha a hat).trans_lt (lt_separatingPrime M a))
      ((hf a hat).trans_lt (lt_separatingPrime M a)) (hne a hat)
  refine ⟨∏ a ∈ t, q a, r, Finset.prod_ne_zero_iff.mpr hnonzero, ?_, ?_⟩
  · apply Nat.coprime_prod_right_iff.mpr
    intro a hat
    have hmod := hr a hat
    change (r : ℕ) % q a = c a % q a at hmod
    rw [← ZMod.coprime_mod_iff_coprime, hmod, ZMod.coprime_mod_iff_coprime]
    exact hc a hat
  · intro a hat
    exact ⟨hr a hat, Finset.dvd_prod_of_mem q hat⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_FiniteFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

theorem finite_factor_impossible (A B : Set ℕ) (hfin : A.Finite)
    (hA : A.Nontrivial) : ¬ EventuallyEqual (A+B) primes := by
  classical
  intro h
  obtain ⟨N, hexclude, hcover⟩ := (eventual_sumset_iff A B).mp h
  obtain ⟨a₀, ha₀, a₁, ha₁, hdistinct⟩ := hA
  let f : ℕ → ℕ := fun a => if a = a₀ then a₁ else a₀
  have hf : ∀ a, f a ∈ A := by
    intro a
    dsimp [f]
    split_ifs
    · exact ha₁
    · exact ha₀
  have hne : ∀ a, a ≠ f a := by
    intro a
    dsimp [f]
    split_ifs with heq
    · simpa only [heq] using hdistinct
    · exact heq
  obtain ⟨M, hM⟩ := hfin.bddAbove
  let t := hfin.toFinset
  have ht : ∀ a, a ∈ t ↔ a ∈ A := fun a => hfin.mem_toFinset
  obtain ⟨Q, r, hQ, hr, hres⟩ := exists_reduced_class t f M
    (fun a ha => hM ((ht a).mp ha))
    (fun a _ => hM (hf a)) (fun a _ => hne a)
  let K := t.sup (separatingPrime M)
  obtain ⟨p, hpbound, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (N+M+K) hQ hr
  obtain ⟨a, ha, b, hb, hab⟩ := hcover p (by omega) hp
  have hat : a ∈ t := (ht a).mpr ha
  have ham : a ≤ M := hM ha
  have haq : separatingPrime M a ≤ K := Finset.le_sup (f := separatingPrime M) hat
  have hbgt : N+K < b := by omega
  obtain ⟨hares, haQ⟩ := hres a hat
  have hpa : p ≡ separatingPrime M a + a - f a [MOD separatingPrime M a] :=
    (hpmod.of_dvd haQ).trans hares
  have hfa : f a ≤ separatingPrime M a + a :=
    (hM (hf a)).trans (Nat.le_add_right_of_le (lt_separatingPrime M a).le)
  have hshift := hpa.add_right (f a)
  rw [Nat.sub_add_cancel hfa] at hshift
  have he : p + f a = a + (f a+b) := by omega
  rw [he] at hshift
  have hqzero : separatingPrime M a + a ≡ a + 0 [MOD separatingPrime M a] := by
    simp [Nat.ModEq]
  have hd : separatingPrime M a ∣ f a+b := Nat.modEq_zero_iff_dvd.mp
    (Nat.ModEq.add_left_cancel' a (hshift.trans hqzero))
  have hp' : (f a+b).Prime := hexclude (f a) (hf a) b hb (by omega)
  have heq := (Nat.prime_dvd_prime_iff_eq (separatingPrime_prime M a) hp').mp hd
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_FiniteSummands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-summand reduction follows from Dirichlet's theorem and the Chinese remainder theorem. -/

namespace Ostmann

/-- A finite nontrivial summand is incompatible with eventual equality to the
primes. The only analytic input is Dirichlet's theorem for one reduced residue
class, provided by `Nat.forall_exists_prime_gt_and_modEq`. -/
theorem not_eventuallyPrimeSumset_of_finite_left {A B : Set ℕ}
    (hA : A.Nontrivial) (hfin : A.Finite) : ¬ EventuallyPrimeSumset A B := by
  intro h
  exact finite_factor_impossible A B hfin hA h

/-- The finite-summand reduction is symmetric. -/
theorem not_eventuallyPrimeSumset_of_finite_right {A B : Set ℕ}
    (hB : B.Nontrivial) (hfin : B.Finite) : ¬ EventuallyPrimeSumset A B := by
  intro h
  exact not_eventuallyPrimeSumset_of_finite_left hB hfin h.symm

/-- Lemma 2.2: both summands of an eventual decomposition are infinite. -/
theorem infinite_summands {A B : Set ℕ} (hA : A.Nontrivial) (hB : B.Nontrivial)
    (h : EventuallyPrimeSumset A B) : A.Infinite ∧ B.Infinite := by
  constructor
  · exact fun hfin => not_eventuallyPrimeSumset_of_finite_left hA hfin h
  · exact fun hfin => not_eventuallyPrimeSumset_of_finite_right hB hfin h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_InverseGoldbach
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ostmann's inverse Goldbach theorem, conditional on the published inputs -/
namespace Ostmann

/-- Theorem 1.1: every sum of two nontrivial sets has infinite symmetric
difference with the primes. The finite-summand reduction uses Mathlib's
Dirichlet theorem; the infinite-summand theorem carries the listed published
analytic inputs explicitly. -/
theorem inverseGoldbach_of_published_oai
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) : InverseGoldbach := by
  intro A B hA hB hfinite
  have hsum := (finite_symmDiff_iff A B).mp hfinite
  obtain ⟨hAinf, hBinf⟩ := infinite_summands hA hB hsum
  exact twoInfiniteSummandsImpossible_of_published P0 ls hsize hBonami Hreal hSiegel sieve
    CM CH hM hMH Z hD hR Pexplicit hPNT A B hAinf hBinf hsum

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.inverseGoldbach_of_published_oai := @OAI.Ostmann.inverseGoldbach_of_published_oai
