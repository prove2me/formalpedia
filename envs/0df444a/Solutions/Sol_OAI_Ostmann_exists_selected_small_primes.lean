-- Prove2me | solution 1 for OAI.Ostmann.exists_selected_small_primes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:32:53.073613+00:00
-- url     : https://prove2.me/submissions/02a274bc-5c63-4335-ba88-434c56d8d863

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D005

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

/-- Large sums in an eventual prime decomposition have no smaller prime divisor. -/
theorem EventuallyPrimeSumset.prime_not_dvd_large_sum {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, ∀ b ∈ B,
      N ≤ a + b → p < a + b → ¬ p ∣ a + b := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro p hp a ha b hb hn hlt hdvd
  have hab : (a + b).Prime := (hN _ hn).mp ⟨a, ha, b, hb, rfl⟩
  have heq : a + b = p := (hab.dvd_iff_eq (ne_of_gt hp.one_lt)).mp hdvd
  omega

/-- The two tails have disjoint images modulo every prime (§2). -/
theorem EventuallyPrimeSumset.disjoint_tail_residues {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p) := by
  obtain ⟨N, hN⟩ := h.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ⟨ha, hna⟩, rfl⟩ ⟨b, ⟨hb, hnb⟩, hz⟩
  apply hN p hp a ha b hb (by omega) (by omega)
  apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
  change -(b : ZMod p) = (a : ZMod p) at hz
  rw [Nat.cast_add, ← hz]
  simp

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TailDensityMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

theorem tailDensityMask_card (A : Set ℕ) (N p : ℕ) :
    (tailDensityMask A N p).card = (tailSupport A N p).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs he
  have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
  have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
  have hmod := (ZMod.natCast_eq_natCast_iff' r s p).mp he
  simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hmod

theorem positiveSummandTail_mem_mask (A : Set ℕ) (N lo hi p : ℕ) (hp : 0 < p)
    (hlo : N + p ≤ lo) {x : ℤ} (hx : x ∈ positiveSummandTail A lo hi) :
    (x : ZMod p) ∈ tailDensityMask A N p := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  apply Finset.mem_image.mpr
  refine ⟨a % p, mod_mem_tailSupport hp haA (lt_of_le_of_lt hlo halo), ?_⟩
  simp

theorem tailDensityMask_density (A : Set ℕ) (N p : ℕ) (hp : 0 < p)
    (hcard : ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) :
    (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3 := by
  rw [tailDensityMask_card]
  apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
  linarith

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityPrimeBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A populated small-prime block with balanced residue masks -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_density_prime_block {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (U C E : ℝ) (hU : 1 ≤ U)
    (hUC : 4 * (Real.log 2 + 2 * C) ≤ U) (hM : MertensEstimate C)
    (hdis : ∀ p ∈ logPrimeBand U, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hbudget : (∑ p ∈ logPrimeBand U, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ E)
    (hE : 64 * E ≤ U / 4) :
    ∃ (z : ℕ) (P : Finset ℕ), 2 ≤ z ∧ P.Nonempty ∧ P ⊆ logPrimeBand U ∧
      (∀ p ∈ P, z ≤ p ∧ p < 2 * z) ∧
      (z : ℝ) ≤ (8 + 8 / Real.log 2) * Real.log z * P.card ∧
      (∀ p ∈ P, (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
        ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)
  have hprime (p : ℕ) (hp : p ∈ logPrimeBand U) : p.Prime := (logPrimeBand_mem hp).1
  have hS : ∀ p ∈ logPrimeBand U, (S p).Nonempty := fun p hp => tailSupport_nonempty hA N p (hprime p hp).pos
  have hT : ∀ p ∈ logPrimeBand U, (T p).Nonempty := fun p hp =>
    tailSupport_complement_nonempty hB (hprime p hp).pos (hdis p hp)
  have hc : ∀ p ∈ logPrimeBand U, (S p).card + (T p).card = p := fun p _ =>
    tailSupport_card_add_complement A N p
  let R := stableTailPrimes A B N lo hi (logPrimeBand U) 1
  have hRsub : R ⊆ logPrimeBand U := Finset.filter_subset _ _
  have hw := stableBiasPrimes_weight (logPrimeBand U) S T μ ν 1 E (by norm_num) hprime hS hT
    (fun p hp => (hc p hp).le) hbudget
  change (∑ p ∈ logPrimeBand U, Real.log (p : ℝ) / p) - 64 * E / 1 ^ 2 ≤
    ∑ p ∈ R, Real.log (p : ℝ) / p at hw
  norm_num only [one_pow, div_one] at hw
  have hmass : (1 / 2 : ℝ) * U ≤ ∑ p ∈ R, Real.log (p : ℝ) / p := by
    linarith [(logPrimeBand_weight_bounds U C hU hM).1]
  obtain ⟨z, P, hz, hP, hPne, hrange, hpop⟩ := exists_populated_prime_block R
    ⌊Real.exp (2 * U)⌋₊ U (1 / 2) hU (by norm_num)
    (fun p hp => hprime p (hRsub hp))
    (fun p hp => Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp (hRsub hp)).1)
    (Nat.floor_le (Real.exp_nonneg _)) hmass
  refine ⟨z, P, hz, hPne, hP.trans hRsub, hrange, ?_, ?_⟩
  · convert hpop using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro p hp
    have hh := stableBiasPrimes_pointwise (logPrimeBand U) S T μ ν
      (fun _ _ => 0) (fun _ _ => 0) 1 (by norm_num) (by norm_num) hS hT hc
      (fun _ _ _ _ => by norm_num) (fun _ _ _ _ => by norm_num) p (hP hp)
    exact ⟨hh.1, hh.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_EventualDensityPrimeBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small-prime block at the manuscript's scale -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_eventual_density_prime_block (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
      L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      N + tailCollisionCutoff L ≤ summandTailCutoff L ∧
      ∃ (z : ℕ) (P : Finset ℕ), 2 ≤ z ∧ P.Nonempty ∧
        P ⊆ logPrimeBand (T ^ (1 / 10000000 : ℝ)) ∧
        (∀ p ∈ P, z ≤ p ∧ p < 2 * z) ∧
        (z : ℝ) ≤ (8 + 8 / Real.log 2) * Real.log z * P.card ∧
        (∀ p ∈ P, (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hlarge
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff N)
  refine ⟨N, max L₁ L₂, ?_⟩
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  filter_upwards [eventual_tailDefectBudget_negligible a C 1 (1 / 4) (1 / 10000000)
      (by norm_num) (by norm_num) hγ,
    (tendsto_rpow_atTop hγ).eventually_ge_atTop (max 1 (4 * (Real.log 2 + 2 * C))),
    eventually_ge_atTop (4096 : ℝ)] with T hloss hU hT
  intro L hL hTL hLU hi hhi
  have hcut := hL₂ L ((le_max_right _ _).trans hL)
  refine ⟨hcut.2.2, ?_⟩
  let U := T ^ (1 / 10000000 : ℝ)
  have hU1 : 1 ≤ U := (le_max_left _ _).trans hU
  have hUC : 4 * (Real.log 2 + 2 * C) ≤ U := (le_max_right _ _).trans hU
  have hUT : U ≤ T := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using hh
  have hband := logPrimeBand_subset_tailCollisionCutoff T L U hT hTL hLU hUT
  obtain ⟨hsa, hsb, _, _, _⟩ := hL₁ L ((le_max_left _ _).trans hL) hi hhi
  have hsa' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A (summandTailCutoff L) hi).card := by
    simpa only [positiveSummandTail_card] using hsa
  have hsb' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B (summandTailCutoff L) hi).card := by
    simpa only [negativeSummandTail_card] using hsb
  have hfull := uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
    ha hcut.1 hcut.2.1 hhi hcut.2.2
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) hsa' hsb' hM.lower
  apply exists_density_prime_block hA hB N (summandTailCutoff L) hi U C (tailDefectBudget a C L)
    hU1 hUC hM (fun p hp => hN p (logPrimeBand_mem hp).1)
  · apply le_trans _ hfull
    apply Finset.sum_le_sum_of_subset_of_nonneg hband
    intro p hp _
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  · have hh := hloss L hcut.1 hLU
    simpa only [one_pow, div_one, one_div_mul_eq_div] using hh

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

theorem small_primeBlock_log_bounds (T V : ℝ) (z : ℕ) (hT : 0 < T)
    (hVlo : T / 2 ≤ V) (hVhi : V ≤ 2 * T)
    (hU : Real.log 2 ≤ T ^ (1 / 10000000 : ℝ))
    (hz : 0 < z)
    (hlo : T ^ (1 / 10000000 : ℝ) - Real.log 2 < Real.log (z : ℝ))
    (hhi : Real.log (z : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) :
    V ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) ∧
      Real.log (2 * (z : ℝ)) ≤ 8 * V ^ (1 / 10000000 : ℝ) := by
  have hV : 0 < V := by linarith
  have hγ : (0 : ℝ) ≤ 1 / 10000000 := by norm_num
  have h2 : (2 : ℝ) ^ (1 / 10000000 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
  have hv : V ^ (1 / 10000000 : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ) := by
    calc
      _ ≤ (2 * T) ^ (1 / 10000000 : ℝ) := Real.rpow_le_rpow hV.le hVhi hγ
      _ = (2 : ℝ) ^ (1 / 10000000 : ℝ) * T ^ (1 / 10000000 : ℝ) := Real.mul_rpow (by norm_num) hT.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT.le _)
  have ht : T ^ (1 / 10000000 : ℝ) ≤ 2 * V ^ (1 / 10000000 : ℝ) := by
    calc
      _ ≤ (2 * V) ^ (1 / 10000000 : ℝ) := Real.rpow_le_rpow hT.le (by linarith) hγ
      _ = (2 : ℝ) ^ (1 / 10000000 : ℝ) * V ^ (1 / 10000000 : ℝ) := Real.mul_rpow (by norm_num) hV.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hV.le _)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Real.log_mul (by norm_num) hz0.ne']
  constructor <;> nlinarith [Real.rpow_nonneg hV.le (1 / 10000000 : ℝ)]

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

theorem primeSet_prod_le_exp (Q : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 0 < z) (hQ : ∀ p ∈ Q, p ≤ 2 * z)
    (hlog : (Q.card : ℝ) * Real.log (2 * (z : ℝ)) ≤ T) :
    (Q.toList.prod : ℝ) ≤ Real.exp T := by
  have hp := Finset.prod_le_pow_card Q (fun p : ℕ => p) (2 * z) hQ
  have hpR : (Q.toList.prod : ℝ) ≤ (2 * (z : ℝ)) ^ Q.card := by
    have hh : Q.toList.prod = ∏ p ∈ Q, p := by simp
    rw [hh]
    exact_mod_cast hp
  apply hpR.trans
  have hzR : 0 < 2 * (z : ℝ) := by positivity
  rw [← Real.exp_log hzR, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hlog

theorem two_le_primeSet_prod (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hne : Q.Nonempty) :
    2 ≤ Q.toList.prod := by
  have hp := Finset.pow_card_le_prod Q (fun p : ℕ => p) 2 (fun p hp => (hQ p hp).two_le)
  have he : Q.toList.prod = ∏ p ∈ Q, p := by simp
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hne.card_pos).trans hp

theorem exists_amplification_prime_subset (P : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 2 ≤ z) (hT : 0 ≤ T) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, p < 2 * z)
    (hcount : amplificationPrimeCount T z ≤ P.card)
    (hK : 1 ≤ amplificationPrimeCount T z) :
    ∃ Q ⊆ P, Q.card = amplificationPrimeCount T z ∧
      (∀ p ∈ Q, p.Prime) ∧ 2 ≤ Q.toList.prod ∧
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) := by
  obtain ⟨Q, hQP, hcard⟩ := Finset.exists_subset_card_eq hcount
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨Q, hQP, hcard, hQ, two_le_primeSet_prod Q hQ hne, ?_⟩
  apply primeSet_prod_le_exp Q z (T / 50) (by omega)
    (fun p hp => (hrange p (hQP hp)).le)
  have hlog : 0 < Real.log (2 * (z : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * z))
  have hfloor : (amplificationPrimeCount T z : ℝ) ≤ T / (50 * Real.log (2 * (z : ℝ))) :=
    Nat.floor_le (div_nonneg hT (by positivity))
  rw [hcard]
  have hh := (le_div_iff₀ (show 0 < 50 * Real.log (2 * (z : ℝ)) by positivity)).mp hfloor
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationCountBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise number of small primes required for amplification -/

namespace Ostmann

private theorem original_scale_power_quotient (T : ℝ) (hT : 0 < T) :
    T / T ^ (1 / 10000000 : ℝ) = T ^ (9999999 / 10000000 : ℝ) := by
  rw [show (9999999 / 10000000 : ℝ) = 1 - 1 / 10000000 by norm_num,
    Real.rpow_sub hT, Real.rpow_one]

theorem amplificationPrimeCount_bounds (T : ℝ) (z : ℕ) (hT : 0 < T)
    (hlo : T ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)))
    (hhi : Real.log (2 * (z : ℝ)) ≤ 8 * T ^ (1 / 10000000 : ℝ))
    (hlarge : 3000000 ≤ T ^ (9999999 / 10000000 : ℝ)) :
    3000 ≤ amplificationPrimeCount T z ∧
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (amplificationPrimeCount T z : ℝ) ∧
      (amplificationPrimeCount T z : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) := by
  let R := T ^ (9999999 / 10000000 : ℝ)
  let u := T ^ (1 / 10000000 : ℝ)
  let b := Real.log (2 * (z : ℝ))
  have hu : 0 < u := Real.rpow_pos_of_pos hT _
  have hb : 0 < b := lt_of_lt_of_le (by positivity) hlo
  have hratio : T / u = R := original_scale_power_quotient T hT
  have hrlo : R / 400 ≤ T / (50 * b) := by
    calc
      R / 400 = T / (400 * u) := by rw [← hratio]; ring
      _ ≤ T / (50 * b) := div_le_div_of_nonneg_left hT.le (by positivity) (by dsimp [b, u]; linarith)
  have hrhi : T / (50 * b) ≤ R / 25 := by
    calc
      T / (50 * b) ≤ T / (25 * u) := div_le_div_of_nonneg_left hT.le (by positivity) (by dsimp [b, u]; linarith)
      _ = R / 25 := by rw [← hratio]; ring
  have hfloorlo := Nat.sub_one_lt_floor (T / (50 * b))
  change T / (50 * b) - 1 < (amplificationPrimeCount T z : ℝ) at hfloorlo
  have hfloorhi : (amplificationPrimeCount T z : ℝ) ≤ T / (50 * b) :=
    Nat.floor_le (by positivity)
  have hR : 3000000 ≤ R := hlarge
  have hKlo : R / 1000 ≤ (amplificationPrimeCount T z : ℝ) := by linarith
  refine ⟨?_, hKlo, ?_⟩
  · have hh : (3000 : ℝ) ≤ (amplificationPrimeCount T z : ℝ) := by linarith
    exact_mod_cast hh
  · linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmallPrimeSupply
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A populated small-prime block contains enough distinct amplifying primes -/

namespace Ostmann

open Filter
open scoped Classical

theorem eventual_small_prime_population (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, ∀ (z : ℕ) (P : Finset ℕ),
      T ^ (1 / 10000000 : ℝ) / 4 ≤ Real.log (z : ℝ) →
      Real.log (z : ℝ) ≤ 8 * T ^ (1 / 10000000 : ℝ) →
      (z : ℝ) ≤ D * Real.log z * P.card → T ≤ (P.card : ℝ) := by
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  have hnum := eventual_affine_log_le_rpow (1 + 1 / 10000000) (Real.log (8 * D)) (1 / 4)
    (1 / 10000000) (by norm_num) (by norm_num) hγ
  filter_upwards [hnum, eventually_ge_atTop (1 : ℝ)] with T hnum hT z P hlo hhi hpop
  have hTp : 0 < T := by linarith
  have hu : 0 < T ^ (1 / 10000000 : ℝ) := Real.rpow_pos_of_pos hTp _
  have hzpos : 0 < (z : ℝ) := by
    by_contra hn
    have hz0 : z = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg z))
    subst z
    simp only [Nat.cast_zero, Real.log_zero] at hlo
    linarith
  have hnum' : 8 * D * T ^ (1 / 10000000 : ℝ) * T ≤ Real.exp (T ^ (1 / 10000000 : ℝ) / 4) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_mul (by positivity) hTp.ne', Real.log_mul (by positivity) hu.ne',
      Real.log_rpow hTp]
    linarith only [hnum]
  have hnumz : 8 * D * T ^ (1 / 10000000 : ℝ) * T ≤ (z : ℝ) :=
    hnum'.trans ((Real.le_log_iff_exp_le hzpos).mp hlo)
  have hpbound : (z : ℝ) ≤ 8 * D * T ^ (1 / 10000000 : ℝ) * P.card := by
    apply hpop.trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hD.le) (Nat.cast_nonneg P.card)
    nlinarith only [hh]
  exact (mul_le_mul_iff_right₀ (show 0 < 8 * D * T ^ (1 / 10000000 : ℝ) by positivity)).mp
    (by nlinarith only [hnumz, hpbound])

theorem eventual_amplification_prime_count_available (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, ∀ (z : ℕ) (P : Finset ℕ), 0 < z →
      T ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) →
      Real.log (2 * (z : ℝ)) ≤ 8 * T ^ (1 / 10000000 : ℝ) →
      (z : ℝ) ≤ D * Real.log z * P.card → amplificationPrimeCount T z ≤ P.card := by
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  have hκ : (0 : ℝ) < 9999999 / 10000000 := by norm_num
  filter_upwards [eventual_small_prime_population D hD,
    (tendsto_rpow_atTop hγ).eventually_ge_atTop (4 * Real.log 2),
    (tendsto_rpow_atTop hκ).eventually_ge_atTop 3000000,
    eventually_ge_atTop (1 : ℝ)] with T hpop hU hK hT z P hz hlo hhi hsize
  have hTp : 0 < T := by linarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz
  have hlo' : T ^ (1 / 10000000 : ℝ) / 4 ≤ Real.log (z : ℝ) := by
    rw [Real.log_mul (by norm_num) hzpos.ne'] at hlo
    linarith
  have hhi' : Real.log (z : ℝ) ≤ 8 * T ^ (1 / 10000000 : ℝ) := by
    rw [Real.log_mul (by norm_num) hzpos.ne'] at hhi
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hcard := hpop z P hlo' hhi' hsize
  have hcount := (amplificationPrimeCount_bounds T z hTp hlo hhi hK).2.2
  have hpower : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
  exact_mod_cast hcount.trans (hpower.trans hcard)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedSmallPrimes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting the actual small-prime amplification data -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_selected_small_primes_oai (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
      L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L → ∀ V : ℝ, T / 2 ≤ V → V ≤ 2 * T →
      ∃ Q : Finset ℕ,
        (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p ∧ Real.log (p : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) ∧
        3000 ≤ Q.card ∧ V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) ∧
        (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) ∧
        2 ≤ Q.toList.prod ∧ (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) ∧
        (∀ p ∈ Q, (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3) ∧
        (∀ n ∈ positiveSummandTail A (summandTailCutoff L) hi,
          ∀ p ∈ Q, (n : ZMod p) ∈ tailDensityMask A N p) := by
  obtain ⟨N, L₀, hblocks⟩ := exists_eventual_density_prime_block hsize hA hB h C hM
  let D := 8 + 8 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : ∀ᶠ V : ℝ in atTop,
      (∀ (z : ℕ) (P : Finset ℕ), 0 < z →
        V ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) →
        Real.log (2 * (z : ℝ)) ≤ 8 * V ^ (1 / 10000000 : ℝ) →
        (z : ℝ) ≤ D * Real.log z * P.card → amplificationPrimeCount V z ≤ P.card) ∧
      3000000 ≤ V ^ (9999999 / 10000000 : ℝ) ∧ 0 < V := by
    filter_upwards [eventual_amplification_prime_count_available D hD,
      (tendsto_rpow_atTop (show (0 : ℝ) < 9999999 / 10000000 by norm_num)).eventually_ge_atTop 3000000,
      eventually_gt_atTop (0 : ℝ)] with V hs hp hV
    exact ⟨hs, hp, hV⟩
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hnum
  refine ⟨N, L₀, ?_⟩
  filter_upwards [hblocks,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10000000 by norm_num)).eventually_ge_atTop
      (max 1000000 (Real.log 2)), eventually_ge_atTop (max 4096 (2 * V₀))]
    with T hblock hU hT
  intro L hL hTL hLU hi hhi V hVlo hVhi
  have hTbig : 4096 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := by linarith
  have hVlarge : V₀ ≤ V := by have := (le_max_right _ _).trans hT; linarith
  obtain ⟨hsupply, hpower, hVp⟩ := hV₀ V hVlarge
  obtain ⟨hNlo, z, P, hz, hPne, hPband, hrange, hpop, hbal⟩ := hblock L hL hTL hLU hi hhi
  have hlogs := primeBlock_log_bounds P z (T ^ (1 / 10000000 : ℝ)) hz hPne hPband hrange
  have hlogbounds := small_primeBlock_log_bounds T V z hTp hVlo hVhi
    ((le_max_right _ _).trans hU) (by omega) hlogs.1 hlogs.2
  have hcounts := amplificationPrimeCount_bounds V z hVp hlogbounds.1 hlogbounds.2 hpower
  have hcount := hsupply z P (by omega) hlogbounds.1 hlogbounds.2 hpop
  obtain ⟨Q, hQP, hcard, hQprime, hprod2, hprod⟩ := exists_amplification_prime_subset P z V hz hVp.le
    (fun p hp => (logPrimeBand_mem (hPband hp)).1) (fun p hp => (hrange p hp).2) hcount (by omega)
  have hQband : Q ⊆ logPrimeBand (T ^ (1 / 10000000 : ℝ)) := hQP.trans hPband
  have hUT : T ^ (1 / 10000000 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
  have hQcut : Q ⊆ Nat.primesLE (tailCollisionCutoff L) := hQband.trans
    (logPrimeBand_subset_tailCollisionCutoff T L _ hTbig hTL hLU hUT)
  refine ⟨Q, ?_, by omega, ?_, ?_, hprod2, hprod, ?_, ?_⟩
  · intro p hp
    have hb := logPrimeBand_mem (hQband hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
    have he := (Real.lt_log_iff_exp_lt hp0).mp hb.2.1
    have hm : (1000000 : ℝ) ≤ p := by
      have hu := (le_max_left _ _).trans hU
      linarith [Real.add_one_le_exp (T ^ (1 / 10000000 : ℝ))]
    exact ⟨hQprime p hp, by exact_mod_cast hm, hb.2.2⟩
  · simpa only [hcard] using hcounts.2.1
  · simpa only [hcard] using hcounts.2.2
  · intro p hp
    exact tailDensityMask_density A N p (hQprime p hp).pos (hbal p (hQP hp)).2
  · intro n hn p hp
    apply positiveSummandTail_mem_mask A N (summandTailCutoff L) hi p (hQprime p hp).pos _ hn
    exact (Nat.add_le_add_left (Nat.le_of_mem_primesLE (hQcut hp)) N).trans hNlo

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.exists_selected_small_primes_oai := @OAI.Ostmann.exists_selected_small_primes_oai
