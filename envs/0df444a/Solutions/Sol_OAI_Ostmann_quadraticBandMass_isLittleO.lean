-- Prove2me | solution 1 for OAI.Ostmann.quadraticBandMass_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:47:16.083458+00:00
-- url     : https://prove2.me/submissions/bdd94c53-fee8-4d41-bc95-06355a54fa0d

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D004
import Definitions.Def_OAIQ095D005
import Theorems.Thm_OAI_Ostmann_common_center_biased_populations_impossible
import Theorems.Thm_OAI_Ostmann_eventual_original_tail_commonCenter
import Theorems.Thm_OAI_Ostmann_exists_selected_small_primes

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

open scoped symmDiff

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

theorem negTailResidues_nonempty {B : Set ℕ} (hB : B.Infinite) (N p : ℕ) :
    (negTailResidues B N p).Nonempty := by
  have hnot : ¬ BddAbove B := fun h => hB (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨b, hb, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨-(b : ZMod p), b, ⟨hb, hlarge⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Exact squared distance from uniform probability on a finite support. -/
theorem collision_sub_uniform {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
      (∑ x ∈ s, μ x ^ 2) - 1 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, (μ x ^ 2 - (2 / (s.card : ℝ)) * μ x +
          (1 / (s.card : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ s, μ x ^ 2) -
          2 * (∑ x ∈ s, μ x) / (s.card : ℝ) +
          (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [hmass]; field_simp; ring

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

/-- The collision budget for a pair in the initial interval `[0,X]`. -/
theorem sum_log_congruent_primes_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hy : y ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) :=
  sum_log_congruent_primes_le_of_sub_le P hxy ((Nat.sub_le y x).trans hy) hprime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

theorem primeCollisionWeight_le_log {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (ha : a ≤ X) (hb : b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact sum_log_congruent_primes_le P hab hb hP
  · rw [primeCollisionWeight_symm]
    exact sum_log_congruent_primes_le P hba ha hP

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- Weighted larger-sieve pair bound on the interval `[0,X]`. -/
theorem weighted_prime_collision_bound (P S : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log hab (hS a ha) (hS b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The quantitative weighted collision bound for projected probabilities. -/
theorem residue_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound P s μ X m hX hP hs hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

/-- The weighted pair bound applies on any chosen residue support, including
the negative residue support of the second summand. -/
theorem fiber_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ)
    (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m)
    (hf : ∀ p ∈ P, ∀ a ∈ s, f p a ∈ t p)
    (hcongr : ∀ p ∈ P, ∀ a ∈ s, ∀ b ∈ s, f p a = f p b ↔ a ≡ b [MOD p]) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ t p, (fiberMass s μ (f p) r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  convert residue_collision_bound P s μ X m hX hP hs hμ hmass hatom using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  rw [fiberMass_sq_eq_residueMass_sq s (t p) μ (f p) (hP p hp).pos
    (hf p hp) (hcongr p hp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Stability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite collision-stability inequality

This is the finite quantitative calculation in Lemma 2.5 of the manuscript.
The final theorem takes the exact numerical consequences of Chebyshev's
bound and Mertens' first theorem at the chosen cutoff as explicit hypotheses.
No main theorem of the manuscript is assumed here.
-/

namespace Ostmann

open scoped BigOperators

theorem collisionDefect_nonneg {p : ℕ} (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hcard : s.card + t.card ≤ p) :
    0 ≤ collisionDefect p s t μ ν := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hcard' : (s.card : ℝ) + t.card ≤ p := by exact_mod_cast hcard
  have hgap := four_div_le_inverse_add_inverse hspos htpos hcard'
  have hμ : 0 ≤ ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hν : 0 ≤ ∑ r ∈ t, (ν r - 1 / (t.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold collisionDefect
  linarith

theorem collisionDefect_eq (p : ℕ) (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hμ : ∑ r ∈ s, μ r = 1) (hν : ∑ r ∈ t, ν r = 1) :
    collisionDefect p s t μ ν =
      (∑ r ∈ s, μ r ^ 2) + (∑ r ∈ t, ν r ^ 2) - 4 / (p : ℝ) := by
  unfold collisionDefect
  rw [collision_sub_uniform s μ hs hμ, collision_sub_uniform t ν ht hν]
  ring

/-- The sum of stability defects is the sum of the collision energies minus
the universal baseline `4 ∑ log p / p`. -/
theorem weighted_collisionDefect_eq (P : Finset ℕ) (s t : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) =
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
      4 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
  calc
    _ = ∑ p ∈ P,
        ((Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
        (Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
        4 * (Real.log (p : ℝ) / (p : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [collisionDefect_eq p (s p) (t p) (μ p) (ν p)
        (hs p hp) (ht p hp) (hμ p hp) (hν p hp)]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite, explicit form of collision stability. The two energy bounds
come from `residue_collision_bound`; the last two hypotheses are exactly
the prime-sum estimates needed at the cutoff, rather than full asymptotic
theories. Mertens' first theorem (1874) supplies the lower prime sum. -/
theorem collision_stability_of_prime_sums (P : Finset ℕ)
    (s t : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (X Q : ℕ) (m K C : ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1)
    (hm : 0 ≤ m)
    (henergyμ : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (henergyν : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  rw [weighted_collisionDefect_eq P s t μ ν hs ht hμ hν]
  have hweight := mul_le_mul_of_nonneg_left hchebyshev hm
  nlinarith

/-- Apply the stability inequality to two actual finite measures on integers.
The maps `f` and `g` label their residue classes; allowing a relabeling is
needed for the negative second summand. The prime-sum hypotheses are the
finite specializations of the published inputs used here. -/
theorem finite_measure_collision_stability (P A B : Finset ℕ)
    (μ ν : ℕ → ℝ) (s t : ℕ → Finset ℕ) (f g : ℕ → ℕ → ℕ)
    (X Q : ℕ) (m K C : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ a ∈ A, a ≤ X) (hB : ∀ b ∈ B, b ≤ X)
    (hμ : ∀ a ∈ A, 0 ≤ μ a) (hν : ∀ b ∈ B, 0 ≤ ν b)
    (hmassμ : ∑ a ∈ A, μ a = 1) (hmassν : ∑ b ∈ B, ν b = 1)
    (hatomμ : ∀ a ∈ A, μ a ≤ m) (hatomν : ∀ b ∈ B, ν b ≤ m)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hf : ∀ p ∈ P, ∀ a ∈ A, f p a ∈ s p)
    (hg : ∀ p ∈ P, ∀ b ∈ B, g p b ∈ t p)
    (hcongrf : ∀ p ∈ P, ∀ a ∈ A, ∀ b ∈ A, f p a = f p b ↔ a ≡ b [MOD p])
    (hcongrg : ∀ p ∈ P, ∀ a ∈ B, ∀ b ∈ B, g p a = g p b ↔ a ≡ b [MOD p])
    (hm : 0 ≤ m)
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (s p) (t p) (fiberMass A μ (f p)) (fiberMass B ν (g p))) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  apply collision_stability_of_prime_sums P s t
    (fun p => fiberMass A μ (f p)) (fun p => fiberMass B ν (g p))
    X Q m K C hs ht
  · intro p hp
    rw [sum_fiberMass A (s p) μ (f p) (hf p hp)]
    exact hmassμ
  · intro p hp
    rw [sum_fiberMass B (t p) ν (g p) (hg p hp)]
    exact hmassν
  · exact hm
  · exact fiber_collision_bound P A μ s f X m hX hP hA hμ hmassμ hatomμ hf hcongrf
  · exact fiber_collision_bound P B ν t g X m hX hP hB hν hmassν hatomν hg hcongrg
  · exact hchebyshev
  · exact hmertens

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

theorem negativeResidue_eq_iff {p a b : ℕ} (hp : 0 < p) :
    negativeResidue p a = negativeResidue p b ↔ a ≡ b [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  unfold negativeResidue
  rw [(ZMod.val_injective p).eq_iff, neg_inj, ZMod.natCast_eq_natCast_iff]

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

theorem negativeResidue_mem_complement {A B : Set ℕ} {N p b : ℕ}
    (hp : 0 < p) (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hb : b ∈ B) (hlarge : N + p < b) :
    negativeResidue p b ∈ Finset.range p \ tailSupport A N p := by
  classical
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  intro hmem
  have ha := (Finset.mem_filter.mp hmem).2
  change ((-(b : ZMod p)).val : ZMod p) ∈ tailResidues A N p at ha
  rw [ZMod.natCast_zmod_val] at ha
  exact Set.disjoint_left.mp hdisjoint ha ⟨b, ⟨hb, hlarge⟩, rfl⟩

theorem tailSupport_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    {N p : ℕ} (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.range p \ tailSupport A N p).Nonempty := by
  obtain ⟨_, b, ⟨hb, hlarge⟩, rfl⟩ := negTailResidues_nonempty hB N p
  exact ⟨negativeResidue p b, negativeResidue_mem_complement hp hdisjoint hb hlarge⟩

theorem tailSupport_card_add_complement (A : Set ℕ) (N p : ℕ) :
    (tailSupport A N p).card + (Finset.range p \ tailSupport A N p).card = p := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card (tailSupport_subset A N p)]
  exact Finset.card_range p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimeSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A prime block with retained logarithmic weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_dyadic_prime_block (P : Finset ℕ) (M : ℕ)
    (hM : ∀ p ∈ P, p ≤ M) (w : ℕ → ℝ) :
    ∃ j ≤ Nat.log 2 M, (∑ p ∈ P, w p) / (Nat.log 2 M + 1 : ℝ) ≤
      ∑ p ∈ dyadicPrimeBlock P j, w p := by
  let J := Finset.range (Nat.log 2 M + 1)
  have hJ : J.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hsum : (∑ j ∈ J, ∑ p ∈ dyadicPrimeBlock P j, w p) = ∑ p ∈ P, w p := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM p hp)))) w
  have hconst : (∑ _j ∈ J, (∑ p ∈ P, w p) / (Nat.log 2 M + 1 : ℝ)) = ∑ p ∈ P, w p := by
    simp only [J, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  obtain ⟨j, hj, hlarge⟩ := Finset.exists_le_of_sum_le hJ (hconst.trans hsum.symm).le
  exact ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), hlarge⟩

theorem dyadicPrimeBlock_bounds (P : Finset ℕ) (j : ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ dyadicPrimeBlock P j) :
    2 ^ j ≤ p ∧ p < 2 * 2 ^ j := by
  obtain ⟨hpP, he⟩ := Finset.mem_filter.mp hp
  have hlo := Nat.pow_log_le_self 2 (hP p hpP).ne_zero
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [he] at hlo hhi
  rw [pow_succ] at hhi
  exact ⟨hlo, by omega⟩

theorem dyadicPrimeBlock_weight_le (P : Finset ℕ) (j : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ dyadicPrimeBlock P j, Real.log (p : ℝ) / p) ≤
      (dyadicPrimeBlock P j).card * (Real.log (2 * (2 : ℝ) ^ j) / (2 : ℝ) ^ j) := by
  calc
    _ ≤ ∑ _p ∈ dyadicPrimeBlock P j, Real.log (2 * (2 : ℝ) ^ j) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro p hp
      have hb := dyadicPrimeBlock_bounds P j hP hp
      have hpp := hP p (Finset.mem_filter.mp hp).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlo : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hb.1
      have hhi : (p : ℝ) ≤ 2 * (2 : ℝ) ^ j := by exact_mod_cast hb.2.le
      calc
        Real.log (p : ℝ) / p ≤ Real.log (p : ℝ) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) hlo
        _ ≤ _ := div_le_div_of_nonneg_right (Real.log_le_log hp0 hhi) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem exists_weighted_dyadic_prime_block (P : Finset ℕ) (M : ℕ) (W : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ p ∈ P, p ≤ M)
    (hW : 0 < W) (hmass : W ≤ ∑ p ∈ P, Real.log (p : ℝ) / p) :
    ∃ (Z : ℕ) (R : Finset ℕ), 1 ≤ Z ∧ R ⊆ P ∧ R.Nonempty ∧
      (∀ p ∈ R, Z ≤ p ∧ p < 2 * Z) ∧
      W * Z ≤ (Nat.log 2 M + 1 : ℝ) * Real.log (2 * (Z : ℝ)) * R.card := by
  obtain ⟨j, hj, hweight⟩ := exists_dyadic_prime_block P M hM (fun p => Real.log (p : ℝ) / p)
  let Z := 2 ^ j
  let R := dyadicPrimeBlock P j
  have hJ : (0 : ℝ) < Nat.log 2 M + 1 := by positivity
  have hweight' : W / (Nat.log 2 M + 1 : ℝ) ≤ ∑ p ∈ R, Real.log (p : ℝ) / p :=
    (div_le_div_of_nonneg_right hmass hJ.le).trans hweight
  have hR : R.Nonempty := by
    by_contra hn
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty] at hweight'
    exact (div_pos hW hJ).not_ge hweight'
  refine ⟨Z, R, one_le_pow₀ (by norm_num), Finset.filter_subset _ _, hR,
    fun p hp => dyadicPrimeBlock_bounds P j hP hp, ?_⟩
  have hb := hweight'.trans (dyadicPrimeBlock_weight_le P j hP)
  have hZ : (0 : ℝ) < Z := by dsimp [Z]; positivity
  have hZcast : (Z : ℝ) = (2 : ℝ) ^ j := by simp [Z]
  rw [← hZcast] at hb
  have hb' := (div_le_iff₀ hJ).mp hb
  have hb'' := mul_le_mul_of_nonneg_right hb' hZ.le
  convert hb'' using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicShellBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The number of dyadic shells is negligible at the kernel scale -/

namespace Ostmann

open Filter Asymptotics

theorem dyadic_shell_count_bound (C T : ℝ) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (M : ℕ) (hM : (M : ℝ) ≤ Real.exp (C * T)) :
    (Nat.log 2 M + 1 : ℝ) ≤ (2 + C / Real.log 2) * T := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hM0 : M = 0
  · subst M
    simp only [Nat.log_zero_right, Nat.cast_zero, zero_add]
    have hdiv : 0 ≤ C / Real.log 2 := div_nonneg hC hl2.le
    nlinarith
  · have hp : (2 : ℝ) ^ (Nat.log 2 M) ≤ M := by exact_mod_cast Nat.pow_log_le_self 2 hM0
    have hlog : (Nat.log 2 M : ℝ) * Real.log 2 ≤ C * T := by
      calc
        _ = Real.log ((2 : ℝ) ^ (Nat.log 2 M)) := (Real.log_pow _ _).symm
        _ ≤ Real.log M := Real.log_le_log (by positivity) hp
        _ ≤ C * T := (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hM0)).mpr hM
    have hh : (Nat.log 2 M : ℝ) ≤ (C / Real.log 2) * T := by
      apply (le_div_iff₀ hl2).mpr at hlog
      convert hlog using 1
      all_goals try with_reducible_and_instances rfl
      ring
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimePopulation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted biased primes give a block of the required population size -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_populated_prime_block (P : Finset ℕ) (M : ℕ) (T d : ℝ)
    (hT : 1 ≤ T) (hd : 0 < d) (hP : ∀ p ∈ P, p.Prime)
    (hM : ∀ p ∈ P, p ≤ M) (hMexp : (M : ℝ) ≤ Real.exp (2 * T))
    (hmass : d * T ≤ ∑ p ∈ P, Real.log (p : ℝ) / p) :
    ∃ (Z : ℕ) (R : Finset ℕ), 2 ≤ Z ∧ R ⊆ P ∧ R.Nonempty ∧
      (∀ p ∈ R, Z ≤ p ∧ p < 2 * Z) ∧
      (Z : ℝ) ≤ ((4 + 4 / Real.log 2) / d) * Real.log Z * R.card := by
  have hTp : 0 < T := by linarith
  obtain ⟨Z, R, hZ, hRP, hR, hrange, hb⟩ := exists_weighted_dyadic_prime_block P M (d * T)
    hP hM (mul_pos hd hTp) hmass
  have hZ2 : 2 ≤ Z := by
    obtain ⟨p, hp⟩ := hR
    have := (hP p (hRP hp)).two_le
    have := (hrange p hp).2
    omega
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hZ2)
  have hlogZ : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg (by exact_mod_cast hZ)
  have hlog2 : Real.log 2 ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hZ2)
  have hlog : Real.log (2 * (Z : ℝ)) ≤ 2 * Real.log Z := by
    rw [Real.log_mul (by norm_num) hZR.ne']
    linarith
  have hK := dyadic_shell_count_bound 2 T (by norm_num) hT M hMexp
  have hD : 0 ≤ 2 + 2 / Real.log 2 := by positivity
  have hupper : (Nat.log 2 M + 1 : ℝ) * Real.log (2 * (Z : ℝ)) * R.card ≤
      ((2 + 2 / Real.log 2) * T) * (2 * Real.log Z) * R.card := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
    exact mul_le_mul hK hlog (Real.log_nonneg (by linarith)) (mul_nonneg hD hTp.le)
  have hcancel : d * (Z : ℝ) ≤ (4 + 4 / Real.log 2) * Real.log Z * R.card := by
    apply (mul_le_mul_iff_right₀ hTp).mp
    first | (convert hb.trans hupper using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((hb.trans hupper).trans (le_of_eq (by ring)))
  refine ⟨Z, R, hZ2, hRP, hR, hrange, ?_⟩
  have hh : (Z : ℝ) ≤ ((4 + 4 / Real.log 2) * Real.log Z * R.card) / d :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hcancel)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

theorem summandPrefix_card_split (A : Set ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (summandPrefix A hi).card = (summandPrefix A lo).card + (summandTail A lo hi).card := by
  have hlo : (summandPrefix A hi).filter (fun n => n ≤ lo) = summandPrefix A lo := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hn⟩; exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩; exact ⟨⟨ha, hn.trans hle⟩, hn⟩
  have hhi : (summandPrefix A hi).filter (fun n => ¬ n ≤ lo) = summandTail A lo hi := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    constructor
    · rintro ⟨⟨ha, hh⟩, hn⟩; exact ⟨ha, Nat.lt_of_not_ge hn, hh⟩
    · rintro ⟨ha, hn, hh⟩; exact ⟨⟨ha, hh⟩, Nat.not_le_of_lt hn⟩
  have hh := Finset.card_filter_add_card_filter_not (s := summandPrefix A hi) (fun n => n ≤ lo)
  rw [hlo, hhi] at hh
  exact hh.symm

theorem positiveSummandTail_bounds (A : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ positiveSummandTail A lo hi) : (lo : ℤ) < x ∧ x ≤ hi := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail A lo hi n).mp hn
  exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

theorem negativeSummandTail_bounds (B : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ negativeSummandTail B lo hi) : -(hi : ℤ) ≤ x ∧ x < -(lo : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail B lo hi n).mp hn
  constructor <;> omega

theorem EventuallyPrimeSumset.tail_prime_differences {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ lo hi : ℕ, N ≤ lo →
      ∀ x ∈ positiveSummandTail A lo hi, ∀ y ∈ negativeSummandTail B lo hi,
        (x - y).natAbs.Prime ∧ (lo : ℤ) < x - y := by
  obtain ⟨N, hN⟩ := h.prime_add
  refine ⟨N, ?_⟩
  intro lo hi hNlo x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  obtain ⟨hbB, _, _⟩ := (mem_summandTail B lo hi b).mp hb
  have hab : (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; ring
  rw [hab, Int.natAbs_natCast]
  exact ⟨hN a haA b hbB (by omega), by exact_mod_cast (by omega : lo < a + b)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OppositeBiasTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Opposite empirical biases from complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

theorem paired_test_means (S T : Finset ℕ) (f : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hsum : (∑ r ∈ S, f r) + (∑ r ∈ T, f r) = 0) :
    residueTestMean T f = -((S.card : ℝ) / T.card) * residueTestMean S f := by
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have ht0 : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_ne_zero
  unfold residueTestMean
  field_simp
  nlinarith only [hsum]

/-- The same orientation gives positive empirical bias on one side and
negative empirical bias on the complementary side. -/
theorem exists_opposite_bias_orientation (u v x y r δ : ℝ)
    (hδ : 0 < δ) (hr : 1 / 2 ≤ r) (hu : δ ≤ |u|) (hv : v = -r * u)
    (hx : |x - u| ≤ δ / 8) (hy : |y - v| ≤ δ / 8) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ δ / 4 ≤ ε * x ∧ δ / 4 ≤ -ε * y := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  by_cases hu0 : 0 ≤ u
  · have hud : δ ≤ u := by simpa only [abs_of_nonneg hu0] using hu
    have hru : δ / 2 ≤ r * u := by
      have hh := mul_le_mul_of_nonneg_right hr hu0
      linarith
    refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · nlinarith
    · rw [hv] at hy'
      nlinarith
  · have hud : u ≤ -δ := by
      rw [abs_of_neg (lt_of_not_ge hu0)] at hu
      linarith
    have hru : r * u ≤ -δ / 2 := by
      have hh := mul_le_mul_of_nonpos_right hr (le_of_lt (lt_of_not_ge hu0))
      linarith
    refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · nlinarith
    · rw [hv] at hy'
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CollisionTestTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision stability controls every chosen bounded residue test -/

namespace Ostmann

open scoped BigOperators Classical

theorem residueTestError_eq (S : Finset ℕ) (μ f : ℕ → ℝ) :
    residueTestError S μ f = ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) * f r := by
  simp only [residueTestError, residueTestMean, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem residueTestError_sq_le (S : Finset ℕ) (μ f : ℕ → ℝ) (p : ℕ)
    (hcard : S.card ≤ p) (hf : ∀ r ∈ S, |f r| ≤ 1) :
    residueTestError S μ f ^ 2 ≤ (p : ℝ) * ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2 := by
  rw [residueTestError_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun r => μ r - 1 / (S.card : ℝ)) f
  have henergy : (∑ r ∈ S, f r ^ 2) ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun r hr => by
        have hh := hf r hr
        have ha := abs_nonneg (f r)
        nlinarith [sq_abs (f r)])
      _ = (S.card : ℝ) := by simp
      _ ≤ p := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_left henergy
    (Finset.sum_nonneg (s := S) (fun r _ => sq_nonneg (μ r - 1 / (S.card : ℝ))))
  exact hCS.trans (by simpa only [mul_comm] using hm)

theorem collisionDefect_controls_tests (p : ℕ) (S T : Finset ℕ) (μ ν f g : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card ≤ p)
    (hf : ∀ r ∈ S, |f r| ≤ 1) (hg : ∀ r ∈ T, |g r| ≤ 1) :
    residueTestError S μ f ^ 2 + residueTestError T ν g ^ 2 ≤
      (p : ℝ) * collisionDefect p S T μ ν := by
  have hs := residueTestError_sq_le S μ f p (by omega) hf
  have ht := residueTestError_sq_le T ν g p (by omega) hg
  have hgap := four_div_le_inverse_add_inverse
    (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card)
    (by exact_mod_cast hT.card_pos : (0 : ℝ) < T.card)
    (by exact_mod_cast hcard : (S.card : ℝ) + T.card ≤ p)
  have hpgap := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr hgap)
  unfold collisionDefect
  nlinarith only [hs, ht, hpgap]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedPrimeSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite weighted deletion estimates for selecting the biased prime block -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_good_mass (P : Finset ℕ) (w : ℕ → ℝ) (good : ℕ → Prop)
    [DecidablePred good] (M E : ℝ)
    (htotal : M ≤ ∑ p ∈ P, w p)
    (hbad : (∑ p ∈ P.filter (fun p => ¬good p), w p) ≤ E) :
    M - E ≤ ∑ p ∈ P.filter good, w p := by
  have hsum := Finset.sum_filter_add_sum_filter_not P good w
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDefectSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small collision defect forces balanced supports and accurate tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem reciprocal_gap_forces_thirds (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b = p) (hgap : p * (1 / a + 1 / b - 4 / p) ≤ 1 / 4) :
    p / 3 ≤ a ∧ a ≤ 2 * p / 3 := by
  have hp : 0 < p := by linarith
  have hab : 0 < a * b := mul_pos ha hb
  have hid : p * (1 / a + 1 / b - 4 / p) = (a - b) ^ 2 / (a * b) := by
    field_simp
    rw [← hsum]
    ring
  have hsq : (a - b) ^ 2 ≤ (1 / 4 : ℝ) * (a * b) := by
    apply (div_le_iff₀ hab).mp
    rwa [← hid]
  constructor
  · by_contra! h
    have hba : 0 ≤ b - 2 * a := by linarith
    have hab' : 0 ≤ 2 * b - a := by linarith
    nlinarith [mul_nonneg hba hab']
  · by_contra! h
    have hab' : 0 ≤ a - 2 * b := by linarith
    have hba : 0 ≤ 2 * a - b := by linarith
    nlinarith [mul_nonneg hab' hba]

theorem small_defect_balances_supports (p : ℕ) (S T : Finset ℕ) (μ ν : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card = p)
    (hsmall : (p : ℝ) * collisionDefect p S T μ ν ≤ 1 / 4) :
    (p : ℝ) / 3 ≤ S.card ∧ (S.card : ℝ) ≤ 2 * p / 3 := by
  apply reciprocal_gap_forces_thirds (S.card : ℝ) T.card p
    (by exact_mod_cast hS.card_pos) (by exact_mod_cast hT.card_pos) (by exact_mod_cast hcard)
  have henergy : 0 ≤ (∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2) +
      ∑ r ∈ T, (ν r - 1 / (T.card : ℝ)) ^ 2 := by positivity
  have hm := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) henergy
  unfold collisionDefect at hsmall
  nlinarith only [hsmall, hm]

theorem small_defect_controls_test_errors (p : ℕ) (S T : Finset ℕ) (μ ν f g : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card ≤ p)
    (hf : ∀ r ∈ S, |f r| ≤ 1) (hg : ∀ r ∈ T, |g r| ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (p : ℝ) * collisionDefect p S T μ ν ≤ δ ^ 2 / 64) :
    |residueTestError S μ f| ≤ δ / 8 ∧ |residueTestError T ν g| ≤ δ / 8 := by
  have hh := (collisionDefect_controls_tests p S T μ ν f g hS hT hcard hf hg).trans hsmall
  have hs := sq_nonneg (residueTestError S μ f)
  have ht := sq_nonneg (residueTestError T ν g)
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

/-- Weighted Markov bound, used with cost `p * collisionDefect`. -/
theorem weighted_cost_exception_bound (P : Finset ℕ) (w cost : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hcost : ∀ p ∈ P, 0 ≤ cost p) :
    δ * (∑ p ∈ P.filter (fun p => δ < cost p), w p) ≤ ∑ p ∈ P, w p * cost p := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => δ < cost p), w p * cost p := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp'.2.le (hw p hp'.1)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => mul_nonneg (hw p hp) (hcost p hp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_StablePrimeSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting stable primes directly from the total collision budget -/

namespace Ostmann

open scoped BigOperators Classical

theorem stableBiasPrimes_weight (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (δ E : ℝ) (hδ : 0 < δ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ p ∈ P, (S p).Nonempty)
    (hT : ∀ p ∈ P, (T p).Nonempty) (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * E / δ ^ 2 ≤
      ∑ p ∈ stableBiasPrimes P S T μ ν δ, Real.log (p : ℝ) / p := by
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let cost := fun p : ℕ => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hc (p : ℕ) (hp : p ∈ P) : 0 ≤ cost p :=
    mul_nonneg (Nat.cast_nonneg _) (collisionDefect_nonneg (S p) (T p) (μ p) (ν p)
      (hS p hp) (hT p hp) (hcard p hp))
  have hsum : (∑ p ∈ P, w p * cost p) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    dsimp [w, cost]
    field_simp
  have hb := weighted_cost_exception_bound P w cost (δ ^ 2 / 64) hw hc
  rw [hsum] at hb
  have hbad : (∑ p ∈ P.filter (fun p => ¬ cost p ≤ δ ^ 2 / 64), w p) ≤ 64 * E / δ ^ 2 := by
    apply (le_div_iff₀ (pow_pos hδ 2)).mpr
    have hb' : δ ^ 2 / 64 * (∑ p ∈ P.filter (fun p => ¬ cost p ≤ δ ^ 2 / 64), w p) ≤ E := by
      simpa only [not_le] using hb.trans hbudget
    nlinarith only [hb']
  exact weighted_good_mass P w (fun p => cost p ≤ δ ^ 2 / 64) _ _ le_rfl hbad

theorem stableBiasPrimes_pointwise (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν f g : ℕ → ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδU : δ ≤ 1)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hf : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hg : ∀ p ∈ P, ∀ r ∈ T p, |g p r| ≤ 1) :
    ∀ p ∈ stableBiasPrimes P S T μ ν δ,
      (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 ∧
      |residueTestError (S p) (μ p) (f p)| ≤ δ / 8 ∧
      |residueTestError (T p) (ν p) (g p)| ≤ δ / 8 := by
  intro p hp
  obtain ⟨hpP, hsmall⟩ := Finset.mem_filter.mp hp
  have hsmall' : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    linarith
  have hbalanced := small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall'
  have herrors := small_defect_controls_test_errors p (S p) (T p) (μ p) (ν p) (f p) (g p)
    (hS p hpP) (hT p hpP) (hcard p hpP).le (hf p hpP) (hg p hpP) δ hδ hsmall
  exact ⟨hbalanced.1, hbalanced.2, herrors.1, herrors.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_StableBiasOrientation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained stable primes have compatible opposite orientations -/

namespace Ostmann

open scoped BigOperators Classical

theorem stable_prime_bias_orientations (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν f : ℕ → ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hfS : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hfT : ∀ p ∈ P, ∀ r ∈ T p, |f p r| ≤ 1)
    (hsum : ∀ p ∈ P, (∑ r ∈ S p, f p r) + (∑ r ∈ T p, f p r) = 0)
    (hbias : ∀ p ∈ P, δ ≤ |residueTestMean (S p) (f p)|) :
    ∃ ε : ℕ → ℝ, ∀ p ∈ stableBiasPrimes P S T μ ν δ,
      (ε p = 1 ∨ ε p = -1) ∧
      δ / 4 ≤ ε p * (∑ r ∈ S p, μ p r * f p r) ∧
      δ / 4 ≤ -(ε p) * (∑ r ∈ T p, ν p r * f p r) := by
  let R := stableBiasPrimes P S T μ ν δ
  have hpoint (p : ℕ) (hp : p ∈ R) : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      δ / 4 ≤ e * (∑ r ∈ S p, μ p r * f p r) ∧
      δ / 4 ≤ -e * (∑ r ∈ T p, ν p r * f p r) := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hstable := stableBiasPrimes_pointwise P S T μ ν f f δ hδ.le hδU hS hT hcard hfS hfT p hp
    have hc : (0 : ℝ) < (T p).card := by exact_mod_cast (hT p hpP).card_pos
    have hsplit : ((S p).card : ℝ) + (T p).card = p := by exact_mod_cast hcard p hpP
    have hratio : (1 / 2 : ℝ) ≤ ((S p).card : ℝ) / (T p).card := by
      apply (le_div_iff₀ hc).mpr
      linarith [hstable.1]
    apply exists_opposite_bias_orientation (residueTestMean (S p) (f p))
      (residueTestMean (T p) (f p)) _ _ (((S p).card : ℝ) / (T p).card) δ
      hδ hratio (hbias p hpP) (paired_test_means (S p) (T p) (f p) (hS p hpP) (hT p hpP) (hsum p hpP))
      hstable.2.2.1 hstable.2.2.2
  let ε : ℕ → ℝ := fun p => if hp : p ∈ R then Classical.choose (hpoint p hp) else 1
  refine ⟨ε, ?_⟩
  intro p hp
  have hpR : p ∈ R := hp
  simpa [ε, hpR] using Classical.choose_spec (hpoint p hpR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

theorem jacobiCharacter_prime_ne_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    jacobiCharacter p ≠ 1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  intro he
  have hev := congrArg (fun χ : DirichletCharacter ℝ p => χ a) he
  have hneg : jacobiCharacter p a = -1 := by
    simp only [jacobiCharacter, MulChar.ringHomComp_apply, jacobiCharacterInt_prime]
    rw [ha]
    norm_num
  rw [hneg, MulChar.one_apply a.isUnit] at hev
  norm_num at hev

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic tests on complementary residue supports -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticResidueTest_abs_le (p : ℕ) (t : ℤ) (r : ℕ) :
    |quadraticResidueTest p t r| ≤ 1 := by
  rcases jacobiSym.trichotomy ((r : ℤ) - t) p with h | h | h <;>
    simp [quadraticResidueTest, h]

theorem quadraticResidueTest_eq_character (p : ℕ) [NeZero p] (t : ℤ) (r : ℕ) :
    quadraticResidueTest p t r = jacobiCharacter p ((r : ZMod p) - (t : ZMod p)) := by
  rw [quadraticResidueTest, ← jacobiCharacter_intCast]
  simp only [Int.cast_sub, Int.cast_natCast]

theorem quadraticResidueTest_sum_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ) :
    ∑ r ∈ Finset.range p, quadraticResidueTest p t r = 0 := by
  have heq : (∑ r ∈ Finset.range p, quadraticResidueTest p t r) =
      ∑ a : ZMod p, jacobiCharacter p a := by
    apply Finset.sum_bij (fun (r : ℕ) _ => (r : ZMod p) - (t : ZMod p))
    · intro r hr
      exact Finset.mem_univ _
    · intro r hr s hs he
      have hm := (ZMod.natCast_eq_natCast_iff' r s p).mp (sub_left_injective he)
      simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hs)] using hm
    · intro a _
      refine ⟨(a + (t : ZMod p)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      rw [ZMod.natCast_zmod_val, add_sub_cancel_right]
    · intro r hr
      exact quadraticResidueTest_eq_character p t r
  rw [heq]
  exact MulChar.sum_eq_zero_of_ne_one (jacobiCharacter_prime_ne_one p hp2)

theorem quadraticResidueTest_complement_sum_zero (A : Set ℕ) (N p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (t : ℤ) :
    (∑ r ∈ tailSupport A N p, quadraticResidueTest p t r) +
      (∑ r ∈ Finset.range p \ tailSupport A N p, quadraticResidueTest p t r) = 0 := by
  rw [add_comm, Finset.sum_sdiff (tailSupport_subset A N p)]
  exact quadraticResidueTest_sum_zero p hp2 t

theorem quadraticResidueTest_mod (p : ℕ) [NeZero p] (t : ℤ) (a : ℕ) :
    quadraticResidueTest p t (a % p) = (jacobiSym ((a : ℤ) - t) p : ℝ) := by
  rw [quadraticResidueTest_eq_character, ZMod.natCast_mod,
    ← Int.cast_natCast a, ← Int.cast_sub, jacobiCharacter_intCast]

theorem quadraticResidueTest_negative (p : ℕ) [NeZero p] (t : ℤ) (a : ℕ) :
    quadraticResidueTest p t (negativeResidue p a) = (jacobiSym (-(a : ℤ) - t) p : ℝ) := by
  rw [quadraticResidueTest_eq_character]
  change jacobiCharacter p (((-(a : ZMod p)).val : ZMod p) - (t : ZMod p)) = _
  rw [ZMod.natCast_zmod_val]
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast] using
    jacobiCharacter_intCast p (-(a : ℤ) - t)

theorem quadratic_positive_projection (A₀ S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ)
    (hS : ∀ a ∈ A₀, a % p ∈ S) :
    (∑ r ∈ S, residueMass A₀ (fun _ => 1 / (A₀.card : ℝ)) p r * quadraticResidueTest p t r) =
      (∑ a ∈ A₀, (jacobiSym ((a : ℤ) - t) p : ℝ)) / A₀.card := by
  change (∑ r ∈ S, fiberMass A₀ (fun _ => 1 / (A₀.card : ℝ)) (fun a => a % p) r *
    quadraticResidueTest p t r) = _
  rw [sum_fiberMass_mul A₀ S _ _ _ hS]
  simp only [quadraticResidueTest_mod]
  rw [← Finset.mul_sum]
  ring

theorem quadratic_negative_projection (B₀ S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ)
    (hS : ∀ b ∈ B₀, negativeResidue p b ∈ S) :
    (∑ r ∈ S, fiberMass B₀ (fun _ => 1 / (B₀.card : ℝ)) (negativeResidue p) r * quadraticResidueTest p t r) =
      (∑ b ∈ B₀, (jacobiSym (-(b : ℤ) - t) p : ℝ)) / B₀.card := by
  rw [sum_fiberMass_mul B₀ S _ _ _ hS]
  simp only [quadraticResidueTest_negative]
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BiasedTailSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting actual oppositely biased endpoint tails -/

namespace Ostmann

open scoped BigOperators Classical

theorem positiveSummandTail_character_sum (A : Set ℕ) (lo hi p : ℕ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) :
    (∑ n ∈ positiveSummandTail A lo hi, orientedQuadraticValue ε t n p) =
      ε p * ∑ a ∈ summandTail A lo hi, (jacobiSym ((a : ℤ) - t p) p : ℝ) := by
  rw [positiveSummandTail, Finset.sum_image]
  · simp only [orientedQuadraticValue, Finset.mul_sum]
  · intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab

theorem negativeSummandTail_character_sum (B : Set ℕ) (lo hi p : ℕ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) :
    (∑ n ∈ negativeSummandTail B lo hi, orientedQuadraticValue ε t n p) =
      ε p * ∑ b ∈ summandTail B lo hi, (jacobiSym (-(b : ℤ) - t p) p : ℝ) := by
  rw [negativeSummandTail, Finset.sum_image]
  · simp only [orientedQuadraticValue, Finset.mul_sum]
  · intro a ha b hb hab
    exact_mod_cast neg_injective hab

theorem stable_tail_quadratic_bias {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (P : Finset ℕ) (δ E : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, p ≠ 2)
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hlo : ∀ p ∈ P, N + p ≤ lo)
    (hA₀ : (summandTail A lo hi).Nonempty) (hB₀ : (summandTail B lo hi).Nonempty)
    (t : ℕ → ℤ)
    (hbias : ∀ p ∈ P, δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ E) :
    ∃ ε : ℕ → ℝ,
      (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * E / δ ^ 2 ≤
        ∑ p ∈ stableTailPrimes A B N lo hi P δ, Real.log (p : ℝ) / p ∧
      ∀ p ∈ stableTailPrimes A B N lo hi P δ,
        (ε p = 1 ∨ ε p = -1) ∧
        (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
        ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
        (positiveSummandTail A lo hi).card * (δ / 4) ≤
          ∑ n ∈ positiveSummandTail A lo hi, orientedQuadraticValue ε t n p ∧
        (negativeSummandTail B lo hi).card * (δ / 4) ≤
          ∑ n ∈ negativeSummandTail B lo hi, orientedQuadraticValue (fun p => -ε p) t n p := by
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)
  have hS : ∀ p ∈ P, (S p).Nonempty := fun p hp => tailSupport_nonempty hA N p (hP p hp).pos
  have hT : ∀ p ∈ P, (T p).Nonempty := fun p hp => tailSupport_complement_nonempty hB (hP p hp).pos (hdis p hp)
  have hcard : ∀ p ∈ P, (S p).card + (T p).card = p := fun p _ => tailSupport_card_add_complement A N p
  have hf : ∀ p ∈ P, ∀ r ∈ S p, |quadraticResidueTest p (t p) r| ≤ 1 :=
    fun p _ r _ => quadraticResidueTest_abs_le p (t p) r
  have hg : ∀ p ∈ P, ∀ r ∈ T p, |quadraticResidueTest p (t p) r| ≤ 1 :=
    fun p _ r _ => quadraticResidueTest_abs_le p (t p) r
  have hsum : ∀ p ∈ P, (∑ r ∈ S p, quadraticResidueTest p (t p) r) +
      (∑ r ∈ T p, quadraticResidueTest p (t p) r) = 0 := by
    intro p hp
    let : Fact p.Prime := ⟨hP p hp⟩
    exact quadraticResidueTest_complement_sum_zero A N p (hodd p hp) (t p)
  obtain ⟨ε, hε⟩ := stable_prime_bias_orientations P S T μ ν
    (fun p => quadraticResidueTest p (t p)) δ hδ hδU hS hT hcard hf hg hsum hbias
  refine ⟨ε, stableBiasPrimes_weight P S T μ ν δ E hδ hP hS hT
    (fun p hp => (hcard p hp).le) hbudget, ?_⟩
  intro p hp
  have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
  let : Fact p.Prime := ⟨hP p hpP⟩
  have hst := stableBiasPrimes_pointwise P S T μ ν
    (fun p => quadraticResidueTest p (t p)) (fun p => quadraticResidueTest p (t p))
    δ hδ.le hδU hS hT hcard hf hg p hp
  have he := hε p hp
  refine ⟨he.1, hst.1, hst.2.1, ?_, ?_⟩
  · have hm : ∀ a ∈ summandTail A lo hi, a % p ∈ S p := by
      intro a ha
      obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
      exact mod_mem_tailSupport (hP p hpP).pos haA (lt_of_le_of_lt (hlo p hpP) halo)
    have hx := he.2.1
    rw [quadratic_positive_projection (summandTail A lo hi) (S p) p (t p) hm,
      ← mul_div_assoc] at hx
    have hc : (0 : ℝ) < (summandTail A lo hi).card := by exact_mod_cast hA₀.card_pos
    rw [positiveSummandTail_card, positiveSummandTail_character_sum]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hx
  · have hm : ∀ b ∈ summandTail B lo hi, negativeResidue p b ∈ T p := by
      intro b hb
      obtain ⟨hbB, hblo, _⟩ := (mem_summandTail B lo hi b).mp hb
      exact negativeResidue_mem_complement (hP p hpP).pos (hdis p hpP) hbB
        (lt_of_le_of_lt (hlo p hpP) hblo)
    have hx := he.2.2
    rw [quadratic_negative_projection (summandTail B lo hi) (T p) p (t p) hm,
      ← mul_div_assoc] at hx
    have hc : (0 : ℝ) < (summandTail B lo hi).card := by exact_mod_cast hB₀.card_pos
    rw [negativeSummandTail_card, negativeSummandTail_character_sum]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hx

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCountingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the short initial segment preserves the square-root lower bound -/

namespace Ostmann

open Filter

theorem eventual_tail_counting_budget (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Set ℕ) (lo hi : ℕ), lo ≤ hi → 1 ≤ lo →
      (lo : ℝ) ≤ Real.exp (9 * L / 10) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A hi).card →
      (summandPrefix A lo).card ≤ C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 →
      (a / 2) * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 20 by norm_num)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL A lo hi hlo h1 hupper hsize hsmall
  have hLp : 0 < L := by linarith
  have hloR : (1 : ℝ) ≤ lo := by exact_mod_cast h1
  have hloPos : (0 : ℝ) < lo := by linarith
  have hlog0 : 0 ≤ Real.log (lo : ℝ) := Real.log_nonneg hloR
  have hlog : Real.log (lo : ℝ) ≤ L := by
    have hh := Real.log_le_log hloPos hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * L / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * L / 10) = (Real.exp (9 * L / 20)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hsmall' : (summandPrefix A lo).card ≤ C * Real.exp (9 * L / 20) * L ^ 2 := by
    apply hsmall.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
      (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)
  have hpoly' : (2 * C / a) * L ^ 5 ≤ Real.exp (L / 20) := by
    have he : Real.exp ((1 / 20 : ℝ) * L) = Real.exp (L / 20) := by congr 1; ring
    rw [he] at hpoly
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdiscard : C * Real.exp (9 * L / 20) * L ^ 2 ≤ (a / 2) * Real.exp (L / 2) / L ^ 3 := by
    apply (le_div_iff₀ (pow_pos hLp 3)).mpr
    have hh : C * L ^ 5 ≤ (a / 2) * Real.exp (L / 20) := by
      have hm := mul_le_mul_of_nonneg_right hpoly' (show 0 ≤ a / 2 by positivity)
      have hcancel : (2 * C / a) * L ^ 5 * (a / 2) = C * L ^ 5 := by
        calc
          _ = (C * L ^ 5) * (a * a⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ ha.ne', mul_one]
      rw [hcancel] at hm
      linarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (9 * L / 20))
    have he : Real.exp (9 * L / 20) * Real.exp (L / 20) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = Real.exp (9 * L / 20) * (C * L ^ 5) := by ring
      _ ≤ Real.exp (9 * L / 20) * ((a / 2) * Real.exp (L / 20)) := hm
      _ = _ := by rw [mul_left_comm, he]
  have hsplit : (summandPrefix A hi).card =
      (summandPrefix A lo).card + (summandTail A lo hi).card := summandPrefix_card_split A lo hi hlo
  have hsplitR : ((summandPrefix A hi).card : ℝ) =
      (summandPrefix A lo).card + (summandTail A lo hi).card := by exact_mod_cast hsplit
  have hh := hsmall'.trans hdiscard
  ring_nf at hh hsize ⊢
  linarith only [hh, hsize, hsplitR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LargeSummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large actual tails from the published summand counting bounds -/

namespace Ostmann

open Filter
open scoped Classical

theorem exists_large_summand_tails (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, (N : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) N).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) N).card ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ N) ∧
      (∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        -(N : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        ∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        (x - y).natAbs.Prime ∧ Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) := by
  obtain ⟨a, C, ha, hC, N₀, hcounts⟩ := hsize A B hA hB h
  obtain ⟨N₁, hprime⟩ := h.tail_prime_differences
  let K := max N₀ (max N₁ 2)
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [eventual_tail_counting_budget a C ha hC.le,
    eventually_ge_atTop (2 * ((K : ℝ) + 2))] with L hbudget hL N hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hKexp : (K : ℝ) ≤ Real.exp (9 * L / 10) := by
    have he := Real.add_one_le_exp (9 * L / 10)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith
  have hKcut : K ≤ summandTailCutoff L := Nat.le_floor hKexp
  have hcutupper : (summandTailCutoff L : ℝ) ≤ Real.exp (9 * L / 10) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hcutN : summandTailCutoff L ≤ N := by
    have he : Real.exp (9 * L / 10) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have hh := hcutupper.trans he
    rw [← hN] at hh
    exact_mod_cast hh
  have hN₀cut : N₀ ≤ summandTailCutoff L := (le_max_left _ _).trans hKcut
  have hN₁cut : N₁ ≤ summandTailCutoff L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hKcut)
  have h2cut : 2 ≤ summandTailCutoff L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hKcut)
  have hcntN := hcounts N (hN₀cut.trans hcutN) (h2cut.trans hcutN)
  have hcntCut := hcounts (summandTailCutoff L) hN₀cut h2cut
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (L / 2) := by
    rw [hN]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hlog : Real.log (N : ℝ) = L := by rw [hN, Real.log_exp]
  have hsa : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A N).card := by
    simpa only [hsqrt, hlog] using hcntN.1
  have hsb : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix B N).card := by
    simpa only [hsqrt, hlog] using hcntN.2.2.1
  have htailA := hbudget A (summandTailCutoff L) N hcutN (by omega) hcutupper hsa hcntCut.2.1
  have htailB := hbudget B (summandTailCutoff L) N hcutN (by omega) hcutupper hsb hcntCut.2.2.2
  refine ⟨by simpa only [positiveSummandTail_card] using htailA,
    by simpa only [negativeSummandTail_card] using htailB, ?_, ?_, ?_⟩
  · intro x hx
    have hb := positiveSummandTail_bounds A _ _ hx
    have hx0 : (0 : ℤ) ≤ x := by omega
    exact ⟨by exact_mod_cast hx0, by exact_mod_cast hb.2⟩
  · intro y hy
    have hb := negativeSummandTail_bounds B _ _ hy
    have hy0 : y ≤ (0 : ℤ) := by omega
    exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hy0⟩
  · intro x hx y hy
    have hp := hprime (summandTailCutoff L) N hN₁cut x hx y hy
    refine ⟨hp.1, ?_⟩
    have hd : 0 ≤ x - y := by omega
    have he : ((x - y).natAbs : ℤ) = x - y := by rw [Int.natCast_natAbs, abs_of_nonneg hd]
    have hn : summandTailCutoff L < (x - y).natAbs := by omega
    exact (Nat.floor_lt (Real.exp_nonneg _)).mp hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem tailCollisionCutoff_bounds (L : ℝ) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) :
    1 ≤ tailCollisionCutoff L ∧
    (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) / L ^ 5 ∧
    L / 2 - 5 * Real.log L - Real.log 2 ≤ Real.log (tailCollisionCutoff L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hrp : 0 < Real.exp (L / 2) / L ^ 5 := by positivity
  have hQ : 1 ≤ tailCollisionCutoff L := (Nat.one_le_floor_iff _).mpr (show (1 : ℝ) ≤ _ by linarith)
  have hhalf : (Real.exp (L / 2) / L ^ 5) / 2 ≤ (tailCollisionCutoff L : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (L / 2) / L ^ 5)
    change Real.exp (L / 2) / L ^ 5 - 1 < (tailCollisionCutoff L : ℝ) at hh
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have hh := Real.log_le_log (show 0 < (Real.exp (L / 2) / L ^ 5) / 2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hrp) (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'),
    Real.log_exp, Real.log_pow] at hh
  exact hh

theorem eventual_tailCollisionCutoff (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 ≤ Real.exp (L / 2) / L ^ 5 ∧
      N + tailCollisionCutoff L ≤ summandTailCutoff L := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 2).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hb hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hLp : 0 < L := by linarith
  have hpoly : 2 * L ^ 5 ≤ Real.exp (L / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hr : 2 ≤ Real.exp (L / 2) / L ^ 5 := (le_div_iff₀ (pow_pos hLp 5)).mpr hpoly
  have hQ := (tailCollisionCutoff_bounds L hL1 hr).2.1
  have hQ' : (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) := hQ.trans
    (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hL1))
  have he : (1 : ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hN : (N : ℝ) + 3 ≤ Real.exp (2 * L / 5) := by
    have := Real.add_one_le_exp (2 * L / 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (L / 2))
  have hexp : Real.exp (L / 2) * Real.exp (2 * L / 5) = Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hmul
  have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr he) hN0
  have hfloor := Nat.sub_one_lt_floor (Real.exp (9 * L / 10))
  change Real.exp (9 * L / 10) - 1 < (summandTailCutoff L : ℝ) at hfloor
  have hfinal : (N : ℝ) + tailCollisionCutoff L ≤ (summandTailCutoff L : ℝ) := by
    nlinarith only [hmul, hprod, hfloor, hQ']
  exact ⟨hL1, hr, by exact_mod_cast hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_UniformTailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic collision defect bound for the actual uniform tails -/

namespace Ostmann

open scoped BigOperators Classical

private theorem uniform_atom_bound (s : Finset ℕ) (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (hsize : a * Real.exp (L / 2) / L ^ 3 ≤ (s.card : ℝ)) :
    s.Nonempty ∧ 1 / (s.card : ℝ) ≤ L ^ 3 / (a * Real.exp (L / 2)) := by
  have hp : 0 < a * Real.exp (L / 2) / L ^ 3 := by positivity
  have hc : (0 : ℝ) < s.card := hp.trans_le hsize
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hc), ?_⟩
  calc
    1 / (s.card : ℝ) ≤ 1 / (a * Real.exp (L / 2) / L ^ 3) := one_div_le_one_div_of_le hp hsize
    _ = _ := by field_simp

theorem uniform_tail_collision_bound {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (a L C : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) (hhi : (hi : ℝ) = Real.exp L)
    (hlo : N + tailCollisionCutoff L ≤ lo)
    (hdis : ∀ p ∈ Nat.primesLE (tailCollisionCutoff L),
      Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hsizeA : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card)
    (hsizeB : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B lo hi).card)
    (hM : MertensLowerBound C) :
    (∑ p ∈ Nat.primesLE (tailCollisionCutoff L), Real.log (p : ℝ) *
      tailCollisionDefect A N p (summandTail A lo hi) (summandTail B lo hi)
        (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
        (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤
      20 * Real.log L + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a := by
  let Q := tailCollisionCutoff L
  let P := Nat.primesLE Q
  let s := summandTail A lo hi
  let t := summandTail B lo hi
  let m := L ^ 3 / (a * Real.exp (L / 2))
  have hLp : 0 < L := by linarith
  have hs := uniform_atom_bound s a L ha hLp hsizeA
  have ht := uniform_atom_bound t a L ha hLp hsizeB
  have hQ := tailCollisionCutoff_bounds L hL hr
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE hp
  have hps (p : ℕ) (hp : p ∈ P) : p ≤ Q := Nat.le_of_mem_primesLE hp
  have hmapA (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ s) : x % p ∈ tailSupport A N p := by
    obtain ⟨hxA, hxlo, _⟩ := (mem_summandTail A lo hi x).mp hx
    apply mod_mem_tailSupport (hp p hpP).pos hxA
    have := hps p hpP
    omega
  have hmapB (p : ℕ) (hpP : p ∈ P) (x : ℕ) (hx : x ∈ t) :
      negativeResidue p x ∈ Finset.range p \ tailSupport A N p := by
    obtain ⟨hxB, hxlo, _⟩ := (mem_summandTail B lo hi x).mp hx
    apply negativeResidue_mem_complement (hp p hpP).pos (hdis p hpP) hxB
    have := hps p hpP
    omega
  have hX : 1 ≤ hi := by
    have he := Real.one_le_exp hLp.le
    rw [← hhi] at he
    exact_mod_cast he
  have hraw := finite_measure_collision_stability P s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p x => x % p) negativeResidue hi Q m (Real.log 4) C hX hp
    (fun x hx => ((mem_summandTail A lo hi x).mp hx).2.2)
    (fun x hx => ((mem_summandTail B lo hi x).mp hx).2.2)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (sum_uniform_mass s hs.1) (sum_uniform_mass t ht.1)
    (fun _ _ => hs.2) (fun _ _ => ht.2)
    (fun p hpP => tailSupport_nonempty hA N p (hp p hpP).pos)
    (fun p hpP => tailSupport_complement_nonempty hB (hp p hpP).pos (hdis p hpP))
    hmapA hmapB (fun _ _ _ _ _ _ => Iff.rfl)
    (fun p hpP _ _ _ _ => negativeResidue_eq_iff (hp p hpP).pos)
    (by positivity) (prime_log_weight_le Q) (hM Q hQ.1)
  change (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p s t
    (fun _ => 1 / (s.card : ℝ)) (fun _ => 1 / (t.card : ℝ))) ≤ _ at hraw
  rw [hhi, Real.log_exp] at hraw
  have hmQ : m * Q ≤ 1 / a := by
    calc
      m * Q ≤ m * (Real.exp (L / 2) / L ^ 5) :=
        mul_le_mul_of_nonneg_left hQ.2.1 (by positivity)
      _ = 1 / (a * L ^ 2) := by dsimp [m]; field_simp
      _ ≤ 1 / a := one_div_le_one_div_of_le ha
        (le_mul_of_one_le_right ha.le (one_le_pow₀ hL))
  have herr := mul_le_mul_of_nonneg_left hmQ (show 0 ≤ 2 * Real.log 4 by positivity)
  dsimp only [Q] at herr
  have herr' : 2 * m * Real.log 4 * (tailCollisionCutoff L : ℝ) ≤ 2 * Real.log 4 / a := by
    first | (convert herr using 1 <;> ring) | exact (le_of_eq (by ring)).trans (herr.trans (le_of_eq (by ring)))
  have hlogQ := hQ.2.2
  dsimp only [P, Q, s, t] at hraw
  linarith only [hraw, herr', hlogQ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_StableSummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable biased primes for the actual large summand tails -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_eventual_stable_summand_tails_at (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) hi).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) hi).card ∧
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (tailCollisionCutoff L) →
      (∀ p ∈ P, p ≠ 2) → ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (t : ℕ → ℤ),
      (∀ p ∈ P, δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) →
      ∃ ε : ℕ → ℝ,
        (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * tailDefectBudget a C L / δ ^ 2 ≤
          ∑ p ∈ stableTailPrimes A B N (summandTailCutoff L) hi P δ, Real.log (p : ℝ) / p ∧
        ∀ p ∈ stableTailPrimes A B N (summandTailCutoff L) hi P δ,
          (ε p = 1 ∨ ε p = -1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
          (positiveSummandTail A (summandTailCutoff L) hi).card * (δ / 4) ≤
            ∑ n ∈ positiveSummandTail A (summandTailCutoff L) hi, orientedQuadraticValue ε t n p ∧
          (negativeSummandTail B (summandTailCutoff L) hi).card * (δ / 4) ≤
            ∑ n ∈ negativeSummandTail B (summandTailCutoff L) hi, orientedQuadraticValue (fun p => -ε p) t n p := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨a, ha, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  refine ⟨hsa, hsb, ?_⟩
  intro P hPsub hodd δ hδ hδU t hbias
  let lo := summandTailCutoff L
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE (hPsub hp)
  have hlo (p : ℕ) (hp : p ∈ P) : N + p ≤ lo :=
    (Nat.add_le_add_left (Nat.le_of_mem_primesLE (hPsub hp)) N).trans hcut.2.2
  have hLp : 0 < L := by linarith [hcut.1]
  have hsa' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
    simpa only [positiveSummandTail_card] using hsa
  have hsb' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B lo hi).card := by
    simpa only [negativeSummandTail_card] using hsb
  have hA₀ : (summandTail A lo hi).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < (summandTail A lo hi).card := (by positivity : 0 < a * Real.exp (L / 2) / L ^ 3).trans_le hsa'
    exact_mod_cast hp
  have hB₀ : (summandTail B lo hi).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < (summandTail B lo hi).card := (by positivity : 0 < a * Real.exp (L / 2) / L ^ 3).trans_le hsb'
    exact_mod_cast hp
  have hbudgetAll := uniform_tail_collision_bound hA hB N lo hi a L C ha hcut.1 hcut.2.1
    hhi hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) hsa' hsb' hM
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ tailDefectBudget a C L := by
    apply le_trans _ hbudgetAll
    apply Finset.sum_le_sum_of_subset_of_nonneg hPsub
    intro p hp _
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  exact stable_tail_quadratic_bias hA hB N lo hi P δ (tailDefectBudget a C L)
    hδ hδU hP hodd (fun p hp => hN p (hP p hp)) hlo hA₀ hB₀ t hbias hbudget

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailBudgetNegligible
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The discarded collision weight is negligible in both prime bands -/

namespace Ostmann

open Filter

theorem eventual_affine_log_le_rpow (A B d κ : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, A * Real.log T + B ≤ d * T ^ κ := by
  have hl := ((isLittleO_log_rpow_atTop hκ).const_mul_left A).bound (show 0 < d / 2 by positivity)
  have hp := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * max B 0 / d)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hl hp hT
  have hlog : A * Real.log T ≤ d / 2 * T ^ κ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Real.log_nonneg hT)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) κ)] using hl
  have hb : B ≤ d / 2 * T ^ κ := by
    have hh := (div_le_iff₀ hd).mp hp
    linarith [le_max_left B 0]
  linarith

theorem eventual_tailDefectBudget_negligible (a C δ d κ : ℝ)
    (hδ : 0 < δ) (hd : 0 < d) (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, 1 ≤ L → L ≤ 2 * T ^ 2 →
      64 * tailDefectBudget a C L / δ ^ 2 ≤ d * T ^ κ := by
  let B := 24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a
  have hh := eventual_affine_log_le_rpow (2560 / δ ^ 2) (64 * B / δ ^ 2) d κ
    (by positivity) hd hκ
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with T hh hT L hL hLT
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := by linarith
  have hlog : Real.log L ≤ Real.log 2 + 2 * Real.log T := by
    have h := Real.log_le_log hLp hLT
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hTp.ne'), Real.log_pow] at h
    exact h
  have hE : tailDefectBudget a C L ≤ 40 * Real.log T + B := by
    dsimp [tailDefectBudget, B]
    linarith
  calc
    64 * tailDefectBudget a C L / δ ^ 2 ≤ 64 * (40 * Real.log T + B) / δ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) (sq_nonneg _)
    _ = (2560 / δ ^ 2) * Real.log T + 64 * B / δ ^ 2 := by ring
    _ ≤ _ := hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.lower {C : ℝ} (h : MertensEstimate C) : MertensLowerBound C := by
  intro Q hQ
  have hh := (abs_le.mp (h Q hQ)).1
  linarith

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

theorem floor_exp_log_bounds (T : ℝ) (hT : 1 ≤ T) :
    1 ≤ ⌊Real.exp T⌋₊ ∧ T - Real.log 2 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
  have he : 2 ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor : (1 : ℕ) ≤ ⌊Real.exp T⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hfp : (0 : ℝ) < ⌊Real.exp T⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hfloor)
  have hhalf : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hlo := Real.log_le_log (show 0 < Real.exp T / 2 by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlo
  have hhi := Real.log_le_log hfp (Nat.floor_le (Real.exp_nonneg T))
  rw [Real.log_exp] at hhi
  exact ⟨hfloor, hlo, hhi⟩

theorem logPrimeBand_mem {T : ℝ} {p : ℕ} (hp : p ∈ logPrimeBand T) :
    p.Prime ∧ T < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp T⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp T < (p : ℝ) := (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (2 * T) :=
    (by exact_mod_cast Nat.le_of_mem_primesLE hhi : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans
      (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

theorem logPrimeBand_weight_bounds (T C : ℝ) (hT : 1 ≤ T) (hM : MertensEstimate C) :
    T - Real.log 2 - 2 * C ≤ (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ∧
      (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ≤ T + Real.log 2 + 2 * C := by
  have hT0 : 0 ≤ T := by linarith
  have hlo := floor_exp_log_bounds T hT
  have hhi := floor_exp_log_bounds (2 * T) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp T⌋₊ ⊆ Nat.primesLE ⌊Real.exp (2 * T)⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))), Nat.prime_of_mem_primesLE hp⟩
  rw [logPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  constructor
  · have h1 := hM.lower _ hhi.1
    have h2 := hM.upper _ hlo.1
    linarith [hhi.2.1, hlo.2.2]
  · have h1 := hM.upper _ hhi.1
    have h2 := hM.lower _ hlo.1
    linarith [hhi.2.2, hlo.2.1]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both logarithmic prime bands lie inside the collision cutoff -/

namespace Ostmann

open scoped Classical

theorem exp_prime_band_le_tail_cutoff (T L : ℝ) (hT : 4096 ≤ T)
    (hTL : T ^ (3 / 2 : ℝ) ≤ L) (hLU : L ≤ 2 * T ^ 2) :
    Real.exp (2 * T) ≤ Real.exp (L / 2) / L ^ 5 := by
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hsqrt : (64 : ℝ) ≤ Real.sqrt T := by
    have hh := Real.sqrt_le_sqrt hT
    have he : Real.sqrt (4096 : ℝ) = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [he] using hh
  have hpow : 64 * T ≤ T ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hTp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith
  have hLp : 0 < L := by linarith
  have hlog : Real.log L ≤ 2 + 2 * T := by
    have hh := Real.log_le_log hLp hLU
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hTp.ne'), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have htlog := Real.log_le_self hTp.le
    have h2log : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith
  apply (Real.le_log_iff_exp_le (show 0 < Real.exp (L / 2) / L ^ 5 by positivity)).mp
  rw [Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'), Real.log_exp, Real.log_pow]
  linarith

theorem logPrimeBand_subset_tailCollisionCutoff (T L U : ℝ) (hT : 4096 ≤ T)
    (hTL : T ^ (3 / 2 : ℝ) ≤ L) (hLU : L ≤ 2 * T ^ 2) (hU : U ≤ T) :
    logPrimeBand U ⊆ Nat.primesLE (tailCollisionCutoff L) := by
  intro p hp
  have hpp := (logPrimeBand_mem hp).1
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, hpp⟩
  have hpbound := Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  apply hpbound.trans
  apply Nat.floor_mono
  exact (Real.exp_le_exp.mpr (by linarith : 2 * U ≤ 2 * T)).trans
    (exp_prime_band_le_tail_cutoff T L hT hTL hLU)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBiasSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting a fixed quadratic bias from a large weighted mean -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem residueTestMean_abs_le_one (S : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ r ∈ S, |f r| ≤ 1) : |residueTestMean S f| ≤ 1 := by
  by_cases hs : S.Nonempty
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hs.card_pos
    rw [residueTestMean, abs_div, abs_of_pos hc]
    apply (div_le_one hc).mpr
    calc
      |∑ r ∈ S, f r| ≤ ∑ r ∈ S, |f r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum hf
      _ = _ := by simp
  · simp [residueTestMean, Finset.not_nonempty_iff_eq_empty.mp hs]

theorem weighted_bias_threshold (P : Finset ℕ) (w b : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hw : ∀ p ∈ P, 0 ≤ w p) (hb : ∀ p ∈ P, b p ≤ 1) :
    (∑ p ∈ P, w p * b p) - δ * (∑ p ∈ P, w p) ≤
      ∑ p ∈ P.filter (fun p => δ ≤ b p), w p := by
  have hp (p : ℕ) (hp : p ∈ P) :
      w p * b p ≤ δ * w p + if δ ≤ b p then w p else 0 := by
    split_ifs with h
    · nlinarith [mul_le_mul_of_nonneg_left (hb p hp) (hw p hp), mul_nonneg hδ (hw p hp)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (hw p hp)
      linarith
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hh
  linarith only [hh]

theorem biasedPrimeBand_weight (A : Set ℕ) (N : ℕ) (T δ C : ℝ) (t : ℕ → ℤ)
    (hT : 1 ≤ T) (hC : Real.log 2 + 2 * C ≤ T) (hM : MertensEstimate C)
    (hδ : 0 ≤ δ)
    (hbias : δ * T ≤ ∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
      |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) :
    δ * T / 2 ≤ ∑ p ∈ biasedPrimeBand A N T (δ / 4) t, Real.log (p : ℝ) / p := by
  have htotal : (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ≤ 2 * T := by
    linarith [(logPrimeBand_weight_bounds T C hT hM).2]
  have hw (p : ℕ) (hp : p ∈ logPrimeBand T) : 0 ≤ Real.log (p : ℝ) / p :=
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
  have hh := weighted_bias_threshold (logPrimeBand T) (fun p => Real.log (p : ℝ) / p)
    (fun p => |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|)
    (δ / 4) (by positivity) hw
    (fun p _ => residueTestMean_abs_le_one _ _ (fun r _ => quadraticResidueTest_abs_le p (t p) r))
  change _ ≤ ∑ p ∈ biasedPrimeBand A N T (δ / 4) t, Real.log (p : ℝ) / p at hh
  nlinarith only [hh, hbias, mul_nonneg hδ (sub_nonneg.mpr htotal)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BiasedPrimeBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A populated dyadic block with actual biases on both summand tails -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_eventual_biased_prime_block (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensEstimate C) (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1) :
    ∃ a Cpop L₀ : ℝ, 0 < a ∧ 500 ≤ Cpop ∧
      ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, L₀ ≤ L → L ≤ 2 * T ^ 2 →
      T ^ (3 / 2 : ℝ) ≤ L → ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ t : ℕ → ℤ,
      δ * T ≤ (∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
        |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) →
      ∃ (Z : ℕ) (P : Finset ℕ) (ε : ℕ → ℝ),
        2 ≤ Z ∧ P.Nonempty ∧ P ⊆ logPrimeBand T ∧
        (∀ p ∈ P, Z ≤ p ∧ p < 2 * Z) ∧
        (Z : ℝ) ≤ Cpop * Real.log Z * P.card ∧
        a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) hi).card ∧
        a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) hi).card ∧
        (∀ p ∈ P, (ε p = 1 ∨ ε p = -1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
          (positiveSummandTail A (summandTailCutoff L) hi).card * (δ / 16) ≤
            ∑ n ∈ positiveSummandTail A (summandTailCutoff L) hi, orientedQuadraticValue ε t n p ∧
          (negativeSummandTail B (summandTailCutoff L) hi).card * (δ / 16) ≤
            ∑ n ∈ negativeSummandTail B (summandTailCutoff L) hi, orientedQuadraticValue (fun p => -ε p) t n p) := by
  obtain ⟨a, ha, hstable⟩ := exists_eventual_stable_summand_tails_at hsize hA hB h N hN C hM.lower
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hstable
  let Cpop := max 500 ((4 + 4 / Real.log 2) / (δ / 4))
  let L₀ := max 1 L₁
  refine ⟨a, Cpop, L₀, ha, le_max_left _ _, ?_⟩
  filter_upwards [eventual_tailDefectBudget_negligible a C (δ / 4) (δ / 4) 1
      (by positivity) (by positivity) (by norm_num),
    eventually_ge_atTop (max 4096 (Real.log 2 + 2 * C))] with T hloss hT
  intro L hL hLU hTL hi hhi t hbias
  have hTbig : 4096 ≤ T := (le_max_left _ _).trans hT
  have hband := logPrimeBand_subset_tailCollisionCutoff T L T hTbig hTL hLU le_rfl
  have hT2 : 2 ≤ T := by linarith
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hdata := hL₁ L ((le_max_right _ _).trans hL) hi hhi
  obtain ⟨hsa, hsb, hselect⟩ := hdata
  let Q := biasedPrimeBand A N T (δ / 4) t
  have hQband : Q ⊆ logPrimeBand T := Finset.filter_subset _ _
  have hQcut : Q ⊆ Nat.primesLE (tailCollisionCutoff L) := hQband.trans hband
  have hodd : ∀ p ∈ Q, p ≠ 2 := by
    intro p hp he
    have hlog := (logPrimeBand_mem (hQband hp)).2.1
    rw [he] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith
  have hQbias : ∀ p ∈ Q, δ / 4 ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))| :=
    fun p hp => (Finset.mem_filter.mp hp).2
  obtain ⟨ε, hweight, hpoint⟩ := hselect Q hQcut hodd (δ / 4) (by positivity) (by linarith) t hQbias
  let R := stableTailPrimes A B N (summandTailCutoff L) hi Q (δ / 4)
  have hRQ : R ⊆ Q := Finset.filter_subset _ _
  have hRband : R ⊆ logPrimeBand T := hRQ.trans hQband
  have hmassQ := biasedPrimeBand_weight A N T δ C t (by linarith)
    ((le_max_right _ _).trans hT) hM hδ.le hbias
  have hlossL := hloss L hL1 hLU
  rw [Real.rpow_one] at hlossL
  have hmassR : (δ / 4) * T ≤ ∑ p ∈ R, Real.log (p : ℝ) / p := by
    linarith only [hweight, hmassQ, hlossL]
  obtain ⟨Z, P, hZ, hP, hPne, hrange, hpop⟩ := exists_populated_prime_block R
    ⌊Real.exp (2 * T)⌋₊ T (δ / 4) (by linarith) (by positivity)
    (fun p hp => (logPrimeBand_mem (hRband hp)).1)
    (fun p hp => Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp (hRband hp)).1)
    (Nat.floor_le (Real.exp_nonneg _)) hmassR
  refine ⟨Z, P, ε, hZ, hPne, hP.trans hRband, hrange, ?_, hsa, hsb, ?_⟩
  · apply hpop.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Z)))
  · intro p hp
    have hh := hpoint p (hP hp)
    simpa only [div_div, show (4 : ℝ) * 4 = 16 by norm_num] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeBlockLogBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the base parameter with both constructed prime blocks -/

namespace Ostmann

open scoped Classical

theorem primeBlock_log_bounds (P : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 2 ≤ z) (hne : P.Nonempty) (hP : P ⊆ logPrimeBand T)
    (hrange : ∀ p ∈ P, z ≤ p ∧ p < 2 * z) :
    T - Real.log 2 < Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ 2 * T := by
  obtain ⟨p, hp⟩ := hne
  have hb := logPrimeBand_mem (hP hp)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
  have hlow := Real.log_le_log hz0 (show (z : ℝ) ≤ p by exact_mod_cast (hrange p hp).1)
  have hhigh := Real.log_lt_log hp0 (show (p : ℝ) < 2 * z by exact_mod_cast (hrange p hp).2)
  rw [Real.log_mul (by norm_num) hz0.ne'] at hhigh
  constructor <;> linarith [hb.2.1, hb.2.2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmallPrimeSubset
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the original small-prime amplification modulus -/

namespace Ostmann

open scoped BigOperators Classical

theorem separated_prime_products_coprime (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hsep : ∀ p ∈ Q, ∀ q ∈ P, p < q) (k M : ℕ) (hM : M ∈ primeSubsetProducts P k) :
    Q.toList.prod.Coprime M := by
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hM
  have hRP := (Finset.mem_powersetCard.mp hR).1
  have he : Q.toList.prod = ∏ p ∈ Q, p := by simp
  rw [he]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Nat.coprime_primes (hQ p hp) (hP q (hRP hq))).mpr (ne_of_lt (hsep p hp q (hRP hq)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalParameterChoice
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete integer choices for the original moment parameters -/

namespace Ostmann

theorem originalMomentOrder_even (L V : ℝ) : Even (originalMomentOrder L V) := by
  refine ⟨⌈L / (2 * V)⌉₊ + 5, ?_⟩
  dsimp [originalMomentOrder]
  omega

theorem originalMomentOrder_scale (L V : ℝ) (hL : 0 ≤ L) (hV : 0 < V) :
    10 ≤ originalMomentOrder L V ∧
      L ≤ ((originalMomentOrder L V - 10 : ℕ) : ℝ) * V ∧
      (originalMomentOrder L V : ℝ) * V ≤ L + 12 * V := by
  let k := ⌈L / (2 * V)⌉₊
  have hceil := Nat.le_ceil (L / (2 * V))
  have hceilU := (Nat.ceil_lt_add_one (div_nonneg hL (by positivity : 0 ≤ 2 * V))).le
  have hlo := (div_le_iff₀ (show 0 < 2 * V by positivity)).mp hceil
  have hhi := (le_div_iff₀ (show 0 < 2 * V by positivity)).mp
    (show (k : ℝ) - 1 ≤ L / (2 * V) by dsimp [k]; linarith)
  have hsub : originalMomentOrder L V - 10 = 2 * k := by dsimp [originalMomentOrder, k]; omega
  refine ⟨by dsimp [originalMomentOrder]; omega, ?_, ?_⟩
  · rw [hsub]
    push_cast
    nlinarith only [hlo]
  · dsimp [originalMomentOrder]
    push_cast
    dsimp [k] at hhi
    nlinarith only [hhi]

theorem originalMomentOrder_size (L V : ℝ) (hV : 0 < V)
    (hlo : V ^ (8 / 5 : ℝ) / 2 ≤ L) (hhi : L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ))
    (hlarge : 60 ≤ V ^ (3 / 5 : ℝ)) :
    V ^ (3 / 5 : ℝ) / 2 ≤ (originalMomentOrder L V : ℝ) ∧
      (originalMomentOrder L V : ℝ) ≤ 2 * V ^ (3 / 5 : ℝ) := by
  have hpow : V ^ (8 / 5 : ℝ) = V * V ^ (3 / 5 : ℝ) := by
    rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add hV, Real.rpow_one]
  have hL : 0 ≤ L := (by positivity : 0 ≤ V ^ (8 / 5 : ℝ) / 2).trans hlo
  obtain ⟨hk, hlow, hupp⟩ := originalMomentOrder_scale L V hL hV
  have hsub : ((originalMomentOrder L V - 10 : ℕ) : ℝ) = (originalMomentOrder L V : ℝ) - 10 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hpow] at hlo hhi
  rw [hsub] at hlow
  constructor
  · apply (mul_le_mul_iff_right₀ hV).mp
    nlinarith only [hlow, hlo, hV.le]
  · apply (mul_le_mul_iff_right₀ hV).mp
    nlinarith only [hupp, hhi, mul_nonneg hV.le (sub_nonneg.mpr hlarge)]

theorem originalHolderOrder_bounds (V : ℝ) (hV : 0 ≤ V)
    (hlarge : 2 ≤ V ^ (1 / 1000000 : ℝ)) :
    1 ≤ originalHolderOrder V ∧
      V ^ (1 / 1000000 : ℝ) / 2 ≤ (originalHolderOrder V : ℝ) ∧
      (originalHolderOrder V : ℝ) ≤ V ^ (1 / 1000000 : ℝ) := by
  refine ⟨(Nat.one_le_floor_iff _).mpr (by linarith), ?_, Nat.floor_le (Real.rpow_nonneg hV _)⟩
  have hh := Nat.sub_one_lt_floor (V ^ (1 / 1000000 : ℝ))
  change V ^ (1 / 1000000 : ℝ) - 1 < (originalHolderOrder V : ℝ) at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalProductScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product and frequency ranges for the concrete moment parameters -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetProducts_log_bounds (P : Finset ℕ) (k z M : ℕ)
    (hz : 0 < z) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z) (hM : M ∈ primeSubsetProducts P k) :
    (k : ℝ) * Real.log z ≤ Real.log (M : ℝ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) * (Real.log z + Real.log 2) := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hM
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hlog : Real.log ((∏ p ∈ Q, p : ℕ) : ℝ) = ∑ p ∈ Q, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hP p (hQP hp)).ne_zero
  rw [hlog]
  constructor
  · have hh := Finset.sum_le_sum (s := Q) (fun (p : ℕ) hp =>
      Real.log_le_log (show (0 : ℝ) < z by exact_mod_cast hz)
        (show (z : ℝ) ≤ p by exact_mod_cast (hrange p (hQP hp)).1))
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard] using hh
  · have hh := Finset.sum_le_sum (s := Q) (fun (p : ℕ) hp =>
      Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast (hP p (hQP hp)).pos)
        (show (p : ℝ) ≤ 2 * z by exact_mod_cast (hrange p (hQP hp)).2))
    have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
    rw [Real.log_mul (by norm_num) hz0] at hh
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard, add_comm] using hh

theorem original_prime_product_scale (P : Finset ℕ) (z : ℕ) (L V : ℝ)
    (hz : 0 < z) (hV : 0 < V) (hLV : Real.log (z : ℝ) = V) (hL : 0 ≤ L)
    (hP : ∀ p ∈ P, p.Prime) (hrange : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z)
    (hklog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V) :
    ∀ M ∈ primeSubsetProducts P (originalMomentOrder L V),
      Real.exp (10 * V) ≤ (M : ℝ) / Real.exp L ∧
      (M : ℝ) / Real.exp L ≤ Real.exp (13 * V) := by
  intro M hM
  have hb := primeSubsetProducts_log_bounds P (originalMomentOrder L V) z M hz hP hrange hM
  rw [hLV] at hb
  have hMpos : 0 < M := by
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hM
    exact Finset.prod_pos (fun p hp => (hP p ((Finset.mem_powersetCard.mp hQ).1 hp)).pos)
  have hratio : 0 < (M : ℝ) / Real.exp L := div_pos (by exact_mod_cast hMpos) (Real.exp_pos _)
  obtain ⟨hk, hlo, hhi⟩ := originalMomentOrder_scale L V hL hV
  have hsub : ((originalMomentOrder L V - 10 : ℕ) : ℝ) = (originalMomentOrder L V : ℝ) - 10 := by
    rw [Nat.cast_sub hk]; norm_num
  rw [hsub] at hlo
  constructor
  · apply (Real.le_log_iff_exp_le hratio).mp
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt hMpos)) (Real.exp_ne_zero _), Real.log_exp]
    nlinarith only [hb.1, hlo]
  · apply (Real.log_le_iff_le_exp hratio).mp
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt hMpos)) (Real.exp_ne_zero _), Real.log_exp]
    nlinarith only [hb.2, hhi, hklog]

theorem originalFrequencyCutoff_bounds (V : ℝ) (hV : 2 ≤ V) :
    1 ≤ originalFrequencyCutoff V ∧ (originalFrequencyCutoff V : ℝ) ≤ Real.exp (14 * V) := by
  have hpos : 0 < Real.exp (27 * V / 2) := Real.exp_pos _
  refine ⟨(Nat.one_le_ceil_iff).mpr hpos, ?_⟩
  have hceil := (Nat.ceil_lt_add_one hpos.le).le
  have he : 1 ≤ Real.exp (27 * V / 2) := Real.one_le_exp (by linarith)
  have h2 : 2 ≤ Real.exp (V / 2) := by linarith [Real.add_one_le_exp (V / 2)]
  have hh := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg (27 * V / 2))
  have heq : Real.exp (27 * V / 2) * Real.exp (V / 2) = Real.exp (14 * V) := by
    rw [← Real.exp_add]; congr 1; ring
  change (originalFrequencyCutoff V : ℝ) ≤ _
  change (⌈Real.exp (27 * V / 2)⌉₊ : ℝ) ≤ _
  rw [heq] at hh
  linarith

theorem originalFrequencyCutoff_covers (V B R Q : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hRU : R ≤ Real.exp (13 * V))
    (hQU : Q ≤ Real.exp (V / 50)) (hB : B ^ 2 ≤ Real.exp (12 * V / 25)) :
    B ^ 2 * R * Q ≤ (originalFrequencyCutoff V : ℝ) := by
  apply le_trans _ (Nat.le_ceil (Real.exp (27 * V / 2)))
  have hh := mul_le_mul (mul_le_mul hB hRU hR (Real.exp_nonneg _)) hQU hQ
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  have heq : Real.exp (12 * V / 25) * Real.exp (13 * V) * Real.exp (V / 50) =
      Real.exp (27 * V / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact heq ▸ hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalEndpointTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring the chosen tails and dyadic block to the original theorem's bounds -/

namespace Ostmann

open scoped BigOperators Classical

theorem local_tail_size_transfer (a L V : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (hLU : L ≤ 2 * V ^ 2) :
    (a / 8) * Real.exp (L / 2) / V ^ 6 ≤ a * Real.exp (L / 2) / L ^ 3 := by
  have hp : L ^ 3 ≤ 8 * V ^ 6 := by
    have hh := pow_le_pow_left₀ hL.le hLU 3
    nlinarith only [hh]
  calc
    (a / 8) * Real.exp (L / 2) / V ^ 6 = a * Real.exp (L / 2) / (8 * V ^ 6) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hp

theorem dyadic_block_card_le (P : Finset ℕ) (z : ℕ)
    (hP : ∀ p ∈ P, z ≤ p ∧ p < 2 * z) : P.card ≤ z := by
  have hsub : P ⊆ Finset.Ico z (2 * z) := fun p hp => Finset.mem_Ico.mpr (hP p hp)
  have hh := Finset.card_le_card hsub
  simp only [Nat.card_Ico] at hh
  omega

theorem doubled_prime_endpoint_le_exp (z : ℕ) (hz : 0 < z) :
    ((2 * z : ℕ) : ℝ) ≤ Real.exp (Real.log z + 1) := by
  rw [Real.exp_add, Real.exp_log (by exact_mod_cast hz)]
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (Nat.cast_nonneg (α := ℝ) z)]

theorem original_upper_endpoint_power (z : ℕ) (L V : ℝ)
    (hz : 0 < z) (hV : 0 < V) (hLV : Real.log (z : ℝ) = V) (hL : 0 ≤ L)
    (hklog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V) (h13 : 13 * V ≤ L) :
    (((2 * z : ℕ) : ℝ) ^ originalMomentOrder L V) ≤ Real.exp (2 * L) := by
  have hzpos : 0 < 2 * (z : ℝ) := by positivity
  have he : Real.log (2 * (z : ℝ)) = V + Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (Nat.ne_of_gt hz)), hLV, add_comm]
  push_cast
  rw [← Real.exp_log hzpos, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [he]
  have hu := (originalMomentOrder_scale L V hL hV).2.2
  nlinarith only [hu, hklog, h13]

theorem original_tail_weight_cutoff (L V B Q : ℝ) (hV : 0 < V)
    (h13 : 13 * V ≤ L) (hQ : 0 < Q) (hQU : Q ≤ Real.exp (V / 50))
    (hB : B ^ 2 ≤ Real.exp (12 * V / 25)) : B ^ 2 < Real.exp L / Q := by
  apply (lt_div_iff₀ hQ).mpr
  have hh := mul_le_mul hB hQU hQ.le (Real.exp_nonneg _)
  have he : Real.exp (12 * V / 25) * Real.exp (V / 50) = Real.exp (V / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hh
  exact hh.trans_lt (Real.exp_lt_exp.mpr (by linarith))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalLocalScaleBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete choices meet the local scale inequalities -/

namespace Ostmann

open Filter

theorem eventual_original_local_scales :
    ∀ᶠ V : ℝ in atTop, ∀ L : ℝ,
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      V ^ (3 / 2 : ℝ) ≤ L ∧ L ≤ 2 * V ^ 2 ∧ 13 * V ≤ L ∧
      V ^ (3 / 5 : ℝ) / 2 ≤ (originalMomentOrder L V : ℝ) ∧
      (originalMomentOrder L V : ℝ) ≤ 2 * V ^ (3 / 5 : ℝ) ∧
      (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V ∧
      1 ≤ originalHolderOrder V ∧
      V ^ (1 / 1000000 : ℝ) / 2 ≤ (originalHolderOrder V : ℝ) ∧
      (originalHolderOrder V : ℝ) ≤ V ^ (1 / 1000000 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).eventually_ge_atTop 4,
    (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).eventually_ge_atTop 60,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 1000000 by norm_num)).eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with V h10 h25 h35 hμ hV L hLlo hLhi
  have hVp : 0 < V := by linarith
  have hsize := originalMomentOrder_size L V hVp hLlo hLhi h35
  have hholder := originalHolderOrder_bounds V hVp.le hμ
  have hpow32 : V ^ (8 / 5 : ℝ) = V ^ (3 / 2 : ℝ) * V ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hVp]; congr 1; norm_num
  have hpow1 : V ^ (8 / 5 : ℝ) = V * V ^ (3 / 5 : ℝ) := by
    rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add hVp, Real.rpow_one]
  have hpow2 : V ^ (8 / 5 : ℝ) ≤ V ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hV (show (8 / 5 : ℝ) ≤ 2 by norm_num)
  have hpowlog : V = V ^ (3 / 5 : ℝ) * V ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hVp, show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num, Real.rpow_one]
  have h32 : V ^ (3 / 2 : ℝ) ≤ L := by
    have hm := mul_le_mul_of_nonneg_left h10 (Real.rpow_nonneg hVp.le (3 / 2 : ℝ))
    rw [← hpow32] at hm
    linarith
  have h13 : 13 * V ≤ L := by
    have hm := mul_le_mul_of_nonneg_left h35 hVp.le
    rw [← hpow1] at hm
    linarith
  have hlog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V := by
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h25 (Real.rpow_nonneg hVp.le (3 / 5 : ℝ))
    rw [← hpowlog] at hm
    have hk := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (originalMomentOrder L V))
    nlinarith only [hm, hk, hsize.2]
  exact ⟨h32, by nlinarith, h13, hsize.1, hsize.2, hlog, hholder.1, hholder.2.1, hholder.2.2⟩

theorem eventual_originalMomentOrder_population (C : ℝ) (hC : 0 < C) :
    ∀ᶠ V : ℝ in atTop, ∀ (L : ℝ) (J : ℕ),
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      Real.exp V ≤ C * V * J → 2 * (originalMomentOrder L V) ^ 2 ≤ J := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 3 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (8 * C)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hpoly, eventual_original_local_scales, eventually_ge_atTop (1 : ℝ)]
    with V hpoly hsc hV L J hLlo hLhi hpop
  have hnum : 8 * C * V ^ 3 ≤ Real.exp V := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (8 * C) * V ^ 3),
      one_mul, abs_of_pos (Real.exp_pos _)] using hpoly
  have hJ : 8 * V ^ 2 ≤ (J : ℝ) := by
    have hp := hnum.trans hpop
    have hCV : 0 < C * V := mul_pos hC (by linarith)
    apply (mul_le_mul_iff_left₀ hCV).mp
    nlinarith only [hp]
  have hk := (hsc L hLlo hLhi).2.2.2.2.1
  have hpow : V ^ (3 / 5 : ℝ) ≤ V := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hV (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkV : (originalMomentOrder L V : ℝ) ≤ 2 * V := by linarith
  have hk0 : (0 : ℝ) ≤ originalMomentOrder L V := Nat.cast_nonneg _
  have hh : 2 * (originalMomentOrder L V : ℝ) ^ 2 ≤ (J : ℝ) := by nlinarith
  exact_mod_cast hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical scales for common-center extraction -/

namespace Ostmann

open Filter

theorem commonCenter_denominator_lt_primes (T : ℝ) (Amax p : ℕ)
    (hT : 3 ≤ T) (hA : (Amax : ℝ) ≤ 2 * Real.exp (T / 5))
    (hp : Real.exp T ≤ (p : ℝ)) : Amax < p := by
  have hf : (2 : ℝ) < Real.exp (4 * T / 5) := by linarith [Real.add_one_le_exp (4 * T / 5)]
  have hh : (Amax : ℝ) < p := calc
    _ ≤ 2 * Real.exp (T / 5) := hA
    _ < Real.exp (4 * T / 5) * Real.exp (T / 5) := mul_lt_mul_of_pos_right hf (Real.exp_pos _)
    _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ p := hp
  exact_mod_cast hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cutoffs for the original rational-center extraction -/

namespace Ostmann

theorem commonCenter_original_cutoffs (T X : ℝ) (r : ℕ) (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXU : X ≤ Real.exp ((r - 10 : ℕ) * T)) :
    0 < ⌈Real.exp (13 * T / 100)⌉₊ ∧
    (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) ∧
    (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) ∧
    0 < ⌊Real.exp T⌋₊ ∧ Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hE : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hE' : Real.exp (13 * T / 100) ≤ Real.exp (T / 5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hA : (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) := by
    have hh := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
    linarith
  have hXE : 0 ≤ X * Real.exp (13 * T / 100) := by positivity
  have hH : (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) := by
    have hh := Nat.ceil_lt_add_one hXE
    have hbound : X * Real.exp (13 * T / 100) ≤ Real.exp ((r - 10 : ℕ) * T + T / 5) := by
      rw [Real.exp_add]
      exact mul_le_mul hXU hE' (Real.exp_nonneg _) (Real.exp_nonneg _)
    have h1 : 1 ≤ X * Real.exp (13 * T / 100) := by nlinarith
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor := Nat.lt_floor_add_one (Real.exp T)
  have hfloorpos : 0 < ⌊Real.exp T⌋₊ := by
    have hh : (1 : ℝ) ≤ ⌊Real.exp T⌋₊ := by linarith
    exact_mod_cast hh
  exact ⟨Nat.ceil_pos.mpr (Real.exp_pos _), hA, hH, hfloorpos, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelCountFromCenter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quadratic sieve counts the kernels of the actual common-center bias -/

namespace Ostmann

open Filter

theorem eventual_kernel_count_prefactor (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, T ^ (3 / 2 : ℝ) ≤ L →
      2 * C * Real.exp (4 * T) ≤ Real.exp (ε * L) := by
  let D := |Real.log (2 * C)| + 4
  have hD : 0 < D := by dsimp [D]; positivity
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (D / ε)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpow hT L hL
  have hTpos : 0 < T := by linarith
  have hd : D * T ≤ ε * T ^ (3 / 2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hpow) hTpos.le
    have he : T ^ (1 / 2 : ℝ) * T = T ^ (3 / 2 : ℝ) := by
      calc
        _ = T ^ (1 / 2 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = T ^ (1 / 2 + 1 : ℝ) := (Real.rpow_add hTpos _ _).symm
        _ = _ := by norm_num
    rw [mul_right_comm, he] at hh
    nlinarith only [hh]
  have hl : Real.log (2 * C) + 4 * T ≤ ε * L := by
    have hh := mul_le_mul_of_nonneg_left hT (abs_nonneg (Real.log (2 * C)))
    have hll := mul_le_mul_of_nonneg_left hL hε.le
    dsimp [D] at hd
    nlinarith [le_abs_self (Real.log (2 * C))]
  calc
    _ = Real.exp (Real.log (2 * C) + 4 * T) := by rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr hl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterEndpointBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The extracted rational center fits the original endpoint cutoffs -/

namespace Ostmann

open Filter

theorem eventual_commonCenter_denominator (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, T ^ (3 / 2 : ℝ) ≤ L →
      (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ Real.exp (η * L) := by
  filter_upwards [eventual_kernel_count_prefactor 1 η (by norm_num) hη,
    eventually_ge_atTop (1 : ℝ)] with T hbound hT L hL
  have he : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
  have hcmp : Real.exp (13 * T / 100) ≤ Real.exp (4 * T) := Real.exp_le_exp.mpr (by linarith)
  have hh := hbound L hL
  nlinarith only [hc, he, hcmp, hh]

theorem commonCenter_endpoint_power_bound (T X : ℝ) (k Z m : ℕ) (h x : ℤ)
    (hT : 3 ≤ T) (hX : 1 ≤ X) (hk : 10 ≤ k)
    (hXU : X ≤ Real.exp ((k - 10 : ℕ) * T))
    (hm : m ≤ ⌈Real.exp (13 * T / 100)⌉₊)
    (hh : |h| ≤ ⌈X * Real.exp (13 * T / 100)⌉₊)
    (hx : |(x : ℝ)| ≤ X) (hZ : Real.exp T ≤ (Z : ℝ)) :
    |(m : ℤ) * x - h| ≤ (Z ^ k : ℕ) := by
  have hT0 : 0 ≤ T := by linarith
  have hE : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hEcmp : Real.exp (13 * T / 100) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have hmR : (m : ℝ) ≤ 2 * Real.exp T := by
    have hc := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
    have hm' : (m : ℝ) ≤ ⌈Real.exp (13 * T / 100)⌉₊ := by exact_mod_cast hm
    linarith
  have hhR : |(h : ℝ)| ≤ 2 * X * Real.exp T := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ X * Real.exp (13 * T / 100) by positivity)
    have hh' : |(h : ℝ)| ≤ ⌈X * Real.exp (13 * T / 100)⌉₊ := by exact_mod_cast hh
    have heX : 1 ≤ X * Real.exp (13 * T / 100) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hEcmp (show 0 ≤ X by linarith)
    nlinarith only [hc, hh', heX, hmul]
  have hfour : (4 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hbound : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ (Z : ℝ) ^ k := by
    push_cast
    calc
      |(m : ℝ) * x - h| ≤ |(m : ℝ) * x| + |(h : ℝ)| := abs_sub _ _
      _ = (m : ℝ) * |(x : ℝ)| + |(h : ℝ)| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      _ ≤ (2 * Real.exp T) * X + 2 * X * Real.exp T :=
        add_le_add (mul_le_mul hmR hx (abs_nonneg _) (by positivity)) hhR
      _ = 4 * X * Real.exp T := by ring
      _ ≤ Real.exp T * Real.exp ((k - 10 : ℕ) * T) * Real.exp T := by gcongr
      _ = Real.exp (((k - 10 : ℕ) : ℝ) * T + 2 * T) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((k : ℝ) * T) := by
        apply Real.exp_le_exp.mpr
        rw [Nat.cast_sub hk, Nat.cast_ofNat]
        nlinarith
      _ = (Real.exp T) ^ k := Real.exp_nat_mul T k
      _ ≤ (Z : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_nonneg _) hZ k
  exact_mod_cast hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalTwoTailContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original biased tails lead to a contradiction

The Fourier and inverse-phase step produces the center used by the actual
large-sieve and population argument. Only the cited published inputs remain.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_original_two_tail_contradiction (hBonami : PublishedBonamiBound)
    (P₀ : PublishedProgressionInput) (H : PublishedRealZeroInput P₀)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (C₀ : ℝ) (hMertens : MertensLowerBound C₀)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      ∀ _hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (L X : ℝ),
      X = Real.exp L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
      1 ≤ X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) → (Z : ℝ) ^ k ≤ Real.exp (2 * L) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      ∀ (U : Finset ℤ), (∀ n ∈ U, -X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 0) →
      a * Real.sqrt X / T ^ 6 ≤ (U.card : ℝ) →
      ∀ δ : ℕ → ℝ, (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
      (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ n ∈ U, orientedQuadraticValue δ t n p) →
      (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
        Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := common_center_biased_populations_impossible
    P₀ H hSiegel sieve C hC C₀ hMertens a c ha hc
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [hno, eventual_original_tail_commonCenter hBonami cψ a c C B hcψ ha hc
    hC hB ψ hreal hψ0 hψ1 hsupp hCψ, eventual_commonCenter_denominator η hη,
    eventually_ge_atTop (3 : ℝ)] with T hnoT hcenter hdenom hT
  intro Q P hQ hP hodd D L X hXeq hTL hLU hL hX hBX S hS hsize hD hSD ε t hε hbias
    k l N Z hk heven hksize hkL hkU hK hK3 hKU hlarge hQprod hQ2 hpop hPU hXU
    hcop hPZ hmin hZ hZU hZL hl hlL hlU hN1 hN hscale U hU hUsize δ hδ hUbias hcross
  obtain ⟨b, hb, n, hn, h, m, hm, hmcut, hred, hhn, hbig, hrel, ht⟩ := hcenter Q P hQ hP
    hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z hk heven hksize hkL hkU
    hK hK3 hKU hlarge hQprod hQ2 hpop hPU hXU hcop hPZ hmin hZ hZU hl hlL hlU hN1 hN hscale
  let R := matchingPrimes P b t n
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hRprime : ∀ p ∈ R, p.Prime := fun p hp => hP p (hRP hp)
  have hRpos : 0 < R.card := by exact_mod_cast (Real.exp_pos _).trans_le hbig
  have hPpos : 0 < (P.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hRpos (Finset.card_le_card hRP))
  have hmprime : ∀ p ∈ R, m < p := by
    intro p hp
    apply lt_of_le_of_lt hmcut
    exact commonCenter_denominator_lt_primes T ⌈Real.exp (13 * T / 100)⌉₊ p hT
      (commonCenter_original_cutoffs T X k (by linarith) hX hXU).2.1 (hmin p (hRP hp))
  have hnabs : |n| ≤ (⌈X * Real.exp (13 * T / 100)⌉₊ : ℕ) := by
    have hn' := Finset.mem_Ico.mp hn
    apply abs_le.mpr
    constructor <;> omega
  have hhabs : |h| ≤ (⌈X * Real.exp (13 * T / 100)⌉₊ : ℕ) := hhn.trans hnabs
  have hexpZ : Real.exp T ≤ (Z : ℝ) := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hRpos
    exact (hmin p (hRP hp)).trans (by exact_mod_cast hPZ p (hRP hp))
  have hLgeT : T ≤ L := by
    have hp : T ≤ T ^ (3 / 2 : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ T by linarith)
        (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    exact hp.trans hTL
  have hLpos : 0 < L := by linarith
  have hsqrt : Real.sqrt X = Real.exp (L / 2) := by
    rw [hXeq]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsizeTransfer : a * Real.exp (L / 2) / L ^ 6 ≤ a * Real.sqrt X / T ^ 6 := by
    rw [hsqrt]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by linarith) hLgeT 6)
  apply hnoT L P.card R k Z (Z ^ k) m h ε δ t S U hTL hLU hL (by omega) hkU
    hPpos hpop hrel hbig hZU hZ (one_le_pow₀ hZ) le_rfl hZL hRprime
    (fun p hp => hodd p (hRP hp)) (fun p hp => hPZ p (hRP hp))
    (fun p hp => hε p (hRP hp)) (fun p hp => hδ p (hRP hp))
    (fun p hp => (Real.le_log_iff_exp_le (by exact_mod_cast (hRprime p hp).pos)).mpr (hmin p (hRP hp)))
    hmprime ht hm ((by exact_mod_cast hmcut : (m : ℝ) ≤ ⌈Real.exp (13 * T / 100)⌉₊).trans (hdenom L hTL)) hred
    _ _ (fun p hp => hbias p (hRP hp)) (fun p hp => hUbias p (hRP hp))
    _ _ _ (hsizeTransfer.trans hsize) (hsizeTransfer.trans hUsize)
  · intro x hx
    apply commonCenter_endpoint_power_bound T X k Z m h x hT hX hk hXU hmcut hhabs
    · rw [abs_of_nonneg (hS x hx).1]; exact (hS x hx).2
    · exact hexpZ
  · intro x hx
    apply commonCenter_endpoint_power_bound T X k Z m h x hT hX hk hXU hmcut hhabs
    · rw [abs_of_nonpos (hU x hx).2]; linarith [(hU x hx).1]
    · exact hexpZ
  · intro x hx y hy
    rw [Int.cast_sub, hXeq] at *
    apply abs_le.mpr
    constructor <;> linarith [(hS x hx).1, (hS x hx).2, (hS y hy).1, (hS y hy).2]
  · intro x hx y hy
    rw [Int.cast_sub, hXeq] at *
    apply abs_le.mpr
    constructor <;> linarith [(hU x hx).1, (hU x hx).2, (hU y hy).1, (hU y hy).2]
  · intro x hx y hy
    refine ⟨(hcross x hx y hy).1, ?_⟩
    have hcut : (kernelSplitCutoff η L : ℝ) ≤ Real.exp (9 * L / 10) := by
      apply (Nat.floor_le (Real.exp_nonneg _)).trans
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hη.le hLpos.le]
    exact_mod_cast hcut.trans_lt (hcross x hx y hy).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicTwoTailContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original contradiction with its integer parameters constructed

The endpoint scale, moment orders and Fourier cutoff are chosen explicitly.
Only the actual two tails, populated dyadic prime block and small-prime masks
remain as geometric data.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_dyadic_two_tail_contradiction (hBonami : PublishedBonamiBound)
    (P₀ : PublishedProgressionInput) (H : PublishedRealZeroInput P₀)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (C₀ : ℝ) (hMertens : MertensLowerBound C₀)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∃ L₀ : ℝ, ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, L₀ ≤ L →
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      ∀ (z : ℕ) (Q P : Finset ℕ), 2 ≤ z → Real.log (z : ℝ) = V →
      (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p) →
      (∀ p ∈ P, p.Prime ∧ Odd p) →
      (∀ p ∈ P, z ≤ p ∧ p < 2 * z) → (z : ℝ) ≤ C * V * P.card →
      V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) →
      2 ≤ Q.toList.prod → (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) →
      (∀ p ∈ Q, ∀ q ∈ P, p < q) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (S U : Finset ℤ),
      (∀ x ∈ S, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ Real.exp L) →
      (∀ y ∈ U, -Real.exp L ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (S.card : ℝ) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (U.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε δ : ℕ → ℝ) (t : ℕ → ℤ),
      (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
      (∀ p ∈ P, S.card * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      (∀ p ∈ P, U.card * c ≤ ∑ n ∈ U, orientedQuadraticValue δ t n p) →
      (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
        Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) → False := by
  obtain ⟨η, L₀, _, _, _, hno⟩ := eventual_original_two_tail_contradiction
    hBonami P₀ H hSiegel sieve C₀ hMertens cψ (a / 8) c C B hcψ (by positivity) hc
    hC hB ψ hreal hψ0 hψ1 hsupp hCψ
  refine ⟨L₀, ?_⟩
  filter_upwards [hno, eventual_original_local_scales,
    eventual_originalMomentOrder_population C (by linarith),
    eventually_ge_atTop (max 2 (25 * B ^ 2 / 12))] with V hnoV hlocal hpopulation hV
  intro L hL hLlo hLhi z Q P hz hlog hQ hP hrange hpop hKlo hK3 hKhi hQ2 hQprod
    hsep D S U hS hU hSsize hUsize hD hSD ε δ t hε hδ hSbias hUbias hcross
  have hV2 : 2 ≤ V := (le_max_left _ _).trans hV
  have hVp : 0 < V := by linarith
  obtain ⟨hVL, hLV, h13, hklo, hkhi, hklog, hl, hllo, hlhi⟩ := hlocal L hLlo hLhi
  have hLp : 0 < L := by linarith
  have hBexp : B ^ 2 ≤ Real.exp (12 * V / 25) := by
    have hv := (le_max_right _ _).trans hV
    linarith [Real.add_one_le_exp (12 * V / 25)]
  have hzpos : 0 < z := by omega
  have hpr : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hqr : ∀ p ∈ Q, p.Prime := fun p hp => (hQ p hp).1
  have hrange' : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z := fun p hp =>
    ⟨(hrange p hp).1, (hrange p hp).2.le⟩
  have hprod := original_prime_product_scale P z L V hzpos hVp hlog hLp.le hpr hrange' hklog
  have hQpos : (0 : ℝ) < Q.toList.prod := by exact_mod_cast (show 0 < Q.toList.prod by omega)
  have hsqrt : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsize (W : Finset ℤ) (hW : a * Real.exp (L / 2) / L ^ 3 ≤ (W.card : ℝ)) :
      (a / 8) * Real.sqrt (Real.exp L) / V ^ 6 ≤ (W.card : ℝ) := by
    rw [hsqrt]
    exact (local_tail_size_transfer a L V ha.le hLp hLV).trans hW
  have hZ := doubled_prime_endpoint_le_exp z hzpos
  rw [hlog] at hZ
  have hcardz : (P.card : ℝ) ≤ z := by exact_mod_cast dyadic_block_card_le P z hrange
  have hz2 : (z : ℝ) ≤ (2 * z : ℕ) := by exact_mod_cast (show z ≤ 2 * z by omega)
  have hPcard : (P.card : ℝ) ≤ Real.exp (V + 1) := hcardz.trans (hz2.trans hZ)
  have hexpz : Real.exp V = (z : ℝ) := by
    rw [← hlog, Real.exp_log (by exact_mod_cast hzpos)]
  have hpop' : Real.exp V ≤ C * V * P.card := by rw [hexpz]; exact hpop
  have hmin : ∀ p ∈ P, Real.exp V ≤ (p : ℝ) := by
    intro p hp
    rw [← hlog, Real.exp_log (by exact_mod_cast hzpos)]
    exact_mod_cast (hrange p hp).1
  have hX : Real.exp L ≤ Real.exp (((originalMomentOrder L V - 10 : ℕ) : ℝ) * V) :=
    Real.exp_le_exp.mpr (originalMomentOrder_scale L V hLp.le hVp).2.1
  exact hnoV Q P hqr hpr (fun p hp => (hP p hp).2) D L (Real.exp L) rfl hVL hLV hL
    (Real.one_le_exp hLp.le) (original_tail_weight_cutoff L V B _ hVp h13 hQpos hQprod hBexp)
    S hS (hsize S hSsize) hD hSD ε t hε hSbias
    (originalMomentOrder L V) (originalHolderOrder V) (originalFrequencyCutoff V) (2 * z)
    (originalMomentOrder_scale L V hLp.le hVp).1 (originalMomentOrder_even L V)
    (hpopulation L P.card hLlo hLhi hpop')
    hklo hkhi hKlo hK3 hKhi (fun p hp => (hQ p hp).2) hQprod hQ2
    hpop'
    hPcard hX (separated_prime_products_coprime Q P hqr hpr hsep _)
    (fun p hp => (hrange p hp).2.le) hmin (by omega) hZ
    (original_upper_endpoint_power z L V hzpos hVp hlog hLp.le hklog h13)
    hl hllo hlhi (originalFrequencyCutoff_bounds V hV2).1 (originalFrequencyCutoff_bounds V hV2).2
    (fun M hM => ⟨originalFrequencyCutoff_covers V B _ _ (by positivity) (by positivity)
      (hprod M hM).2 hQprod hBexp, (hprod M hM).1,
      (hprod M hM).2.trans (Real.exp_le_exp.mpr (by linarith))⟩)
    U hU (hsize U hUsize) δ hδ hUbias hcross

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointBaseScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integer endpoint scale compatible with every selected dyadic block -/

namespace Ostmann

open Filter

private theorem two_rpow_three_fifths_le : (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 8 / 5 := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    (by norm_num : (0 : ℝ) < 5)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem eventual_endpoint_scale :
    ∀ᶠ T : ℝ in atTop, 1 ≤ endpointSize T ∧
      Real.exp (endpointLogScale T) = (endpointSize T : ℝ) ∧
      T ≤ endpointLogScale T ∧ T ^ (3 / 2 : ℝ) ≤ endpointLogScale T ∧
      endpointLogScale T ≤ 2 * T ^ 2 ∧
      ∀ V : ℝ, T - Real.log 2 ≤ V → V ≤ 2 * T →
        T / 2 ≤ V ∧ 0 < V ∧
        V ^ (8 / 5 : ℝ) / 2 ≤ endpointLogScale T ∧
        endpointLogScale T ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 8 / 5 by norm_num)).eventually_ge_atTop
      (20 * Real.log 2), eventually_ge_atTop (max 1 (100 * Real.log 2))] with T hbig hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := by linarith
  have hp1 : 1 ≤ T ^ (8 / 5 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hs1 : 1 ≤ endpointBaseScale T := by dsimp [endpointBaseScale]; linarith
  have hbounds := floor_exp_log_bounds (endpointBaseScale T) hs1
  have hLlo : (17 / 10 : ℝ) * T ^ (8 / 5 : ℝ) ≤ endpointLogScale T := by
    have hh := hbounds.2.1
    change endpointBaseScale T - Real.log 2 ≤ endpointLogScale T at hh
    dsimp [endpointBaseScale] at hh
    linarith
  have hLhi : endpointLogScale T ≤ (7 / 4 : ℝ) * T ^ (8 / 5 : ℝ) := by
    have hh := hbounds.2.2
    change endpointLogScale T ≤ endpointBaseScale T at hh
    dsimp [endpointBaseScale] at hh
    linarith
  have hTpow : T ≤ T ^ (8 / 5 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
      (show (1 : ℝ) ≤ 8 / 5 by norm_num)
  have hT32 : T ^ (3 / 2 : ℝ) ≤ T ^ (8 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hT2 : T ^ (8 / 5 : ℝ) ≤ T ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hT1 (show (8 / 5 : ℝ) ≤ 2 by norm_num)
  have hsize0 : (0 : ℝ) < endpointSize T := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hbounds.1)
  refine ⟨hbounds.1, Real.exp_log hsize0, by linarith, by linarith, by nlinarith, ?_⟩
  intro V hVlo hVhi
  have hTbig := (le_max_right _ _).trans hT
  have hV99 : (99 / 100 : ℝ) * T ≤ V := by linarith
  have hVhalf : T / 2 ≤ V := by linarith
  have hVp : 0 < V := by linarith
  have hVupper : V ^ (8 / 5 : ℝ) ≤ (16 / 5 : ℝ) * T ^ (8 / 5 : ℝ) := by
    calc
      _ ≤ (2 * T) ^ (8 / 5 : ℝ) := Real.rpow_le_rpow hVp.le hVhi (by norm_num)
      _ = (2 : ℝ) ^ (8 / 5 : ℝ) * T ^ (8 / 5 : ℝ) := Real.mul_rpow (by norm_num) hTp.le
      _ ≤ _ := by
        rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        nlinarith [mul_nonneg (sub_nonneg.mpr two_rpow_three_fifths_le) (Real.rpow_nonneg hTp.le (8 / 5 : ℝ))]
  have hVlower : (9801 / 10000 : ℝ) * T ^ (8 / 5 : ℝ) ≤ V ^ (8 / 5 : ℝ) := by
    have hc : (9801 / 10000 : ℝ) ≤ (99 / 100 : ℝ) ^ (8 / 5 : ℝ) := by
      have hh := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 99 / 100)
        (by norm_num : (99 / 100 : ℝ) ≤ 1) (show (8 / 5 : ℝ) ≤ 2 by norm_num)
      norm_num at hh ⊢
      exact hh
    calc
      _ ≤ (99 / 100 : ℝ) ^ (8 / 5 : ℝ) * T ^ (8 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hTp.le _)
      _ = ((99 / 100 : ℝ) * T) ^ (8 / 5 : ℝ) := (Real.mul_rpow (by norm_num) hTp.le).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hV99 (by norm_num)
  refine ⟨hVhalf, hVp, ?_, ?_⟩ <;> nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBiasSmallness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform smallness of translated quadratic biases

The residue partition is fixed before the error tolerance. The proof constructs
both prime blocks, all integer parameters and the positive and reflected tails.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_small_prime_separation :
    ∀ᶠ T : ℝ in atTop, 2 * T ^ (1 / 10000000 : ℝ) < T := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 9999999 / 10000000 by norm_num)).eventually_ge_atTop 4,
    eventually_gt_atTop (0 : ℝ)] with T hpow hT
  have he : T ^ (1 / 10000000 : ℝ) * T ^ (9999999 / 10000000 : ℝ) = T := by
    rw [← Real.rpow_add hT]; norm_num
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hT.le (1 / 10000000 : ℝ))
  rw [he] at hh
  nlinarith [Real.rpow_pos_of_pos hT (1 / 10000000 : ℝ)]

theorem eventual_translated_quadratic_bias_lt
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℕ → ℤ,
      (∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
        |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) < δ * T := by
  obtain ⟨a, Cpop, Lbig, ha, hCpop, hblocks⟩ :=
    exists_eventual_biased_prime_block hsize hA hB h N hN C₀ hM δ hδ hδU
  let C := max Cpop (𝓕 ψ 0).re
  have hC : 500 ≤ C := hCpop.trans (le_max_left _ _)
  obtain ⟨Lno, hno⟩ := eventual_dyadic_two_tail_contradiction hBonami P₀ H hSiegel sieve
    C₀ hM.lower cψ a (δ / 16) C Bψ hcψ ha (by positivity) hC hBψ ψ hreal hψ0 hψ1 hsupp
    (le_max_right _ _)
  obtain ⟨Vno, hVno⟩ := eventually_atTop.mp hno
  obtain ⟨Nsmall, Lsmall, hsmall⟩ := exists_selected_small_primes hsize hA hB h C₀ hM
  obtain ⟨_, _, htails⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Ltails, hLtails⟩ := eventually_atTop.mp htails
  filter_upwards [hblocks, hsmall, eventual_endpoint_scale, eventual_small_prime_separation,
    eventually_ge_atTop (max 2 (max Lbig (max Lsmall (max Lno (max Ltails (2 * Vno))))))]
    with T hblock hsm hend hsep hT t
  by_contra hnot
  have hbias := le_of_not_gt hnot
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hmax : max Lbig (max Lsmall (max Lno (max Ltails (2 * Vno)))) ≤ T :=
    (le_max_right _ _).trans hT
  obtain ⟨hX1, hXL, hTL, hT32, hL2, hsc⟩ := hend
  let L := endpointLogScale T
  let X := endpointSize T
  have hXL' : (X : ℝ) = Real.exp L := hXL.symm
  have hLbig : Lbig ≤ L := (le_max_left _ _).trans (hmax.trans hTL)
  have hsmallmax : max Lsmall (max Lno (max Ltails (2 * Vno))) ≤ T :=
    (le_max_right _ _).trans hmax
  have hLsmall : Lsmall ≤ L := (le_max_left _ _).trans (hsmallmax.trans hTL)
  have hnomax : max Lno (max Ltails (2 * Vno)) ≤ T := (le_max_right _ _).trans hsmallmax
  have hLno : Lno ≤ L := (le_max_left _ _).trans (hnomax.trans hTL)
  have htailmax : max Ltails (2 * Vno) ≤ T := (le_max_right _ _).trans hnomax
  have hLtail : Ltails ≤ L := (le_max_left _ _).trans (htailmax.trans hTL)
  have hVcut : 2 * Vno ≤ T := (le_max_right _ _).trans htailmax
  obtain ⟨z, P, ε, hz, hPne, hPband, hrange, hpop, hsa, hsb, hpoint⟩ :=
    hblock L hLbig hL2 hT32 X hXL' t hbias
  have hlogs := primeBlock_log_bounds P z T hz hPne hPband hrange
  let V := Real.log (z : ℝ)
  obtain ⟨hTV, hVp, hLVlo, hLVhi⟩ := hsc V hlogs.1.le hlogs.2
  have hVlarge : Vno ≤ V := by linarith
  obtain ⟨Q, hQ, hK3, hKlo, hKhi, hQ2, hQprod, hD, hSD⟩ :=
    hsm L hLsmall hT32 hL2 X hXL' V hTV hlogs.2
  have hprime : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    have hh := logPrimeBand_mem (hPband hp)
    refine ⟨hh.1, hh.1.odd_of_ne_two ?_⟩
    intro he
    rw [he] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith [hh.2.1]
  have hsepQP : ∀ p ∈ Q, ∀ q ∈ P, p < q := by
    intro p hp q hq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).1.pos
    have hlogsPQ : Real.log (p : ℝ) < Real.log (q : ℝ) :=
      (hQ p hp).2.2.trans_lt (hsep.trans (logPrimeBand_mem (hPband hq)).2.1)
    exact_mod_cast (Real.log_lt_log_iff hp0 (by exact_mod_cast (hprime q hq).1.pos)).mp hlogsPQ
  have hpopC : (z : ℝ) ≤ C * V * P.card := by
    apply hpop.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hVp.le) (Nat.cast_nonneg _)
  obtain ⟨_, _, hSbounds, hUbounds, hcross⟩ := hLtails L hLtail X hXL'
  have hSbounds' : ∀ x ∈ positiveSummandTail A (summandTailCutoff L) X,
      0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ Real.exp L := by simpa only [hXL'] using hSbounds
  have hUbounds' : ∀ y ∈ negativeSummandTail B (summandTailCutoff L) X,
      -Real.exp L ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0 := by simpa only [hXL'] using hUbounds
  exact hVno V hVlarge L hLno hLVlo hLVhi z Q P hz rfl
    (fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.1⟩) hprime hrange hpopC hKlo hK3 hKhi hQ2 hQprod
    hsepQP (tailDensityMask A Nsmall) (positiveSummandTail A (summandTailCutoff L) X)
    (negativeSummandTail B (summandTailCutoff L) X) hSbounds' hUbounds' hsa hsb hD hSD
    ε (fun p => -ε p) t (fun p hp => (hpoint p hp).1)
    (fun p hp => by rcases (hpoint p hp).1 with hh | hh <;> simp [hh])
    (fun p hp => (hpoint p hp).2.2.2.1) (fun p hp => (hpoint p hp).2.2.2.2) hcross

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_MaximalQuadraticBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem maximalQuadraticBias_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ maximalQuadraticBias S p :=
  abs_nonneg _

theorem quadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) : 0 ≤ quadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (logPrimeBand_mem hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

theorem quadraticBandMass_isLittleO_oai
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0) :
    (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hδ : 0 < min c 1 := lt_min hc (by norm_num)
  have hh := eventual_translated_quadratic_bias_lt hBonami P₀ H hSiegel sieve hsize
    hA hB h N hN C₀ hM cψ Bψ hcψ hBψ ψ hreal hψ0 hψ1 hsupp (min c 1) hδ (min_le_right _ _)
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with T hh hT
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hT]
  exact (hh (fun p => maximizingQuadraticTranslate (tailSupport A N p) p)).le.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hT)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadraticBandMass_isLittleO_oai := @OAI.Ostmann.quadraticBandMass_isLittleO_oai
