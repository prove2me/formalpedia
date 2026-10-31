-- Prove2me | solution 1 for OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:56:37.385043+00:00
-- url     : https://prove2.me/submissions/4ce7fa7d-5cb6-40bf-93b6-cef375bb389e

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_all_character_decorrelation
import Theorems.Thm_OAI_Ostmann_quadraticBandMass_isLittleO

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      (Complex.ofReal (∑ q ∈ Q, (q : ℝ)⁻¹))⁻¹ * ∑ q ∈ Q, ((q : ℝ)⁻¹ : ℂ) * F q := by
  unfold primeSubsetPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (∑ q ∈ Q, (q : ℝ)⁻¹ : ℝ) * F p else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Complex.ofReal_inv]
  ring

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.instDecidableEqMulCharZModComplex_solutions
/-- A multiplicative character has modulus one at each unit. -/
theorem norm_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖ = 1 := by
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two local Fourier bounds in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_twice {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (additiveFourier f) a = (q : ℂ)⁻¹ * f (-a) := by
  rw [additiveFourier_apply]
  congr 1
  have hi := additiveFourier_inversion f (-a)
  simpa only [mul_neg] using hi.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive Fourier coefficients of multiplicative characters

The Gauss identity already proved in Mathlib gives the exact normalized
squared modulus needed for the two-bad quartet estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem gaussSum_norm_sq {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  rw [← star_gaussSum_eq] at h
  change gaussSum χ ZMod.stdAddChar * conj (gaussSum χ ZMod.stdAddChar) = _ at h
  rw [Complex.mul_conj', ZMod.card] at h
  exact_mod_cast h

theorem additiveFourier_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) :
    additiveFourier χ (a : ZMod p) =
      (p : ℂ)⁻¹ * χ⁻¹ (-(a : ZMod p)) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  rw [additiveFourier_apply]
  have hsum : (∑ x : ZMod p, χ x * ZMod.stdAddChar (-(x * (a : ZMod p)))) =
      gaussSum χ ((ZMod.stdAddChar (N := p)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm (a : ZMod p) x]
  have hshift := gaussSum_mulShift_eq χ (ZMod.stdAddChar (N := p)) (-a)
  simp only [Units.val_neg] at hshift
  rw [hsum, hshift]
  ring

/-- A nonprincipal character has zero additive Fourier coefficient at zero. -/
theorem additiveFourier_mulChar_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) : additiveFourier χ 0 = 0 := by
  simp [additiveFourier_apply, χ.sum_eq_zero_of_ne_one hχ]

theorem additiveFourier_mulChar {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier χ a =
      (p : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  by_cases ha : a = 0
  · subst a
    simp only [additiveFourier_mulChar_zero χ hχ, neg_zero, MulChar.map_zero, mul_zero,
      zero_mul]
  · exact additiveFourier_mulChar_unit χ (Units.mk0 a ha)

/-- The Fourier transform exchanges pointwise multiplication and convolution. -/
theorem additiveFourier_pointwise_mul {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * g x) a =
      ∑ b : ZMod p, additiveFourier f b * additiveFourier g (a - b) := by
  rw [additiveFourier_apply]
  conv_lhs =>
    enter [2, 2, x]
    rw [additiveFourier_inversion f x]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_apply g (a - b)]
  simp only [Finset.mul_sum]
  have hphase (x : ZMod p) :
      ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a)) =
        ZMod.stdAddChar (-(x * (a - b))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (p : ℂ)⁻¹ * additiveFourier f b * g x *
        (ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a))) := by ring
    _ = _ := by rw [hphase]; ring

/-- Exact Gauss convolution formula, including the vanishing zero term. -/
theorem additiveFourier_mul_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => f x * χ x) a =
      ((p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))) *
        ∑ b : ZMod p, additiveFourier f b * χ⁻¹ (-(a - b)) := by
  rw [additiveFourier_pointwise_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_mulChar χ hχ]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkDeletionCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleted-atom costs in the actual original bulk prior -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_deleted_reciprocal_mass_le (S D : Finset ℕ) (T : ℝ)
    (hlow : ∀ q ∈ S, Real.exp T ≤ (q : ℝ)) :
    (∑ q ∈ S ∩ D, (q : ℝ)⁻¹) ≤ (D.card : ℝ) * Real.exp (-T) := by
  calc
    _ ≤ ∑ _q ∈ S ∩ D, Real.exp (-T) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos T)
        (hlow q (Finset.mem_inter.mp hq).1)
    _ = ((S ∩ D).card : ℝ) * Real.exp (-T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      (Real.exp_nonneg _)

end Ostmann

end OAI
end

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
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SignedQuadraticFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

/-- Reality of the original physical cutoff supplies Hermitian symmetry of
its Fourier transform without any additional analytic input. -/
theorem fourier_real_conj (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 2
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveFourierCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

private theorem narrowSchwartz_apply (x : ℝ) : narrowSchwartz x = (narrowBump x : ℂ) := rfl

private theorem narrowSchwartz_even (x : ℝ) : narrowSchwartz (-x) = narrowSchwartz x := by
  simp only [narrowSchwartz_apply, narrowBump.neg]

private theorem narrow_fourier_real (x : ℝ) :
    conj (𝓕 narrowSchwartz x) = 𝓕 narrowSchwartz x := by
  have hr := fourier_real_conj narrowSchwartz (by intro y; simp [narrowSchwartz_apply]) x
  change conj (𝓕 (narrowSchwartz : ℝ → ℂ) x) = 𝓕 (narrowSchwartz : ℝ → ℂ) x
  rw [← hr]
  have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
    (narrowSchwartz : ℝ → ℂ) x
  have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
    funext y
    exact narrowSchwartz_even y
  rw [hh] at he
  exact he.symm

private theorem narrow_fourier_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y : ℝ, narrowBump y) / 2 ≤ (𝓕 narrowSchwartz x).re := by
  let phase : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * x : ℝ) * Complex.I)
  have hc : HasCompactSupport (fun y : ℝ => narrowSchwartz y) := by
    change HasCompactSupport (Complex.ofReal ∘ (narrowBump : ℝ → ℝ))
    exact narrowBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by simp)
  have hi : Integrable (fun y : ℝ => phase y * narrowSchwartz y) :=
    (by fun_prop : Continuous (fun y : ℝ => phase y * narrowSchwartz y)).integrable_of_hasCompactSupport hc.mul_left
  have hu : Integrable (narrowBump : ℝ → ℝ) :=
    narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport
  have hphase (y : ℝ) : (phase y * narrowSchwartz y).re =
      Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    simp only [phase, narrowSchwartz_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hire := hi.re
  change Integrable (fun y => (phase y * narrowSchwartz y).re) at hire
  have hint : Integrable (fun y => Real.cos (-2 * Real.pi * y * x) * narrowBump y) := by
    simpa only [hphase] using hire
  have he : (𝓕 narrowSchwartz x).re = ∫ y : ℝ, Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    change (∫ y : ℝ, phase y * narrowSchwartz y).re = _
    have hh := integral_re hi
    change (∫ y : ℝ, (phase y * narrowSchwartz y).re) = (∫ y : ℝ, phase y * narrowSchwartz y).re at hh
    rw [← hh]
    simp only [hphase]
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_mono (hu.mul_const _) hint
  · intro y
    by_cases hy : narrowBump y = 0
    · simp [hy]
    have hylt : |y| < 1 / 100 := by
      have hm : y ∈ Function.support narrowBump := hy
      rw [narrowBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
      exact hm
    have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hang : |(-2 * Real.pi * y * x)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
      have hh := mul_le_mul (le_of_lt hylt) hxabs (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (-2 * Real.pi * y * x) := by
      have hs := (abs_le.mp hang)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * y * x)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hcos (narrowBump.nonneg' y)

private theorem narrow_integral_pos : 0 < ∫ y : ℝ, narrowBump y := by
  apply integral_pos_of_integrable_nonneg_nonzero narrowBump.continuous
    (narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport)
    narrowBump.nonneg'
  have hh : narrowBump (0 : ℝ) = 1 := narrowBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]; exact narrowBump.rIn_pos.le)
  rw [hh]
  norm_num

private theorem schwartz_fourier_twice (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at hh
  exact hh

private theorem narrow_convolution_zero (x : ℝ) (hx : 1 ≤ |x|) :
    SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz x = 0 := by
  rw [SchwartzMap.convolution_apply, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : 1 / 100 ≤ |y|
  · have hz : narrowBump y = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hy)
    simp [narrowSchwartz_apply, hz]
  · have hxy : 1 / 100 ≤ |x - y| := by
      have hh := abs_add_le (x - y) y
      rw [sub_add_cancel] at hh
      linarith
    have hz : narrowBump (x - y) = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hxy)
    simp [narrowSchwartz_apply, hz]

/-- The cutoff needed by the original amplified moment argument exists. -/
theorem exists_positive_even_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) ∧
      (∀ x : ℝ, 𝓕 ψ (-x) = 𝓕 ψ x) := by
  let f := 𝓕 narrowSchwartz
  let ψ := SchwartzMap.pairing (.mul ℂ ℂ) f f
  let c := ((∫ y : ℝ, narrowBump y) / 2) ^ 2
  have hfreal (x : ℝ) : (f x).im = 0 := by
    have hh := congrArg Complex.im (narrow_fourier_real x)
    simp only [Complex.conj_im] at hh
    change -(f x).im = (f x).im at hh
    linarith
  have hψ (x : ℝ) : ψ x = f x * f x := rfl
  have hcpos := narrow_integral_pos
  refine ⟨c, ψ, by dsimp [c]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hψ, map_mul] using congrArg (fun z : ℂ => z * z) (narrow_fourier_real x)
  · intro x
    rw [hψ, Complex.mul_re, hfreal]
    nlinarith
  · intro x hx
    rw [hψ, Complex.mul_re, hfreal]
    have hl := narrow_fourier_lower x hx
    change (∫ y : ℝ, narrowBump y) / 2 ≤ (f x).re at hl
    dsimp [c]
    nlinarith [narrow_integral_pos]
  · intro x hx
    have he : ψ = 𝓕 (SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz) :=
      (SchwartzMap.fourier_convolution _ _ _).symm
    rw [he, schwartz_fourier_twice]
    exact narrow_convolution_zero (-x) (by rw [abs_neg]; linarith)

  · intro x
    have hfEven (y : ℝ) : f (-y) = f y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have hψEven : (ψ : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = ψ := by
      funext y
      change f (-y) * f (-y) = f y * f y
      rw [hfEven]
    have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (ψ : ℝ → ℂ) x
    rw [hψEven] at he
    exact he.symm

/-- A positive Fourier cutoff with bounded derivatives and compact Fourier support. -/
theorem exists_positive_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) := by
  obtain ⟨c, ψ, hc, hr, hp, hl, hs, _⟩ := exists_positive_even_fourier_cutoff
  exact ⟨c, ψ, hc, hr, hp, hl, hs⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected shells give the actual character prime ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_of_loglog_lower (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : a ≤ Real.log (Real.log (p : ℝ))) : Real.exp (Real.exp a) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem prime_of_loglog_upper (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : Real.log (Real.log (p : ℝ)) ≤ a) : (p : ℝ) ≤ Real.exp (Real.exp a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRoundedEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral endpoints with the original character product scale -/
namespace Ostmann
open scoped Classical

theorem characterEndpointFactor_pos (k : ℕ) : 0 < characterEndpointFactor k := by
  unfold characterEndpointFactor
  positivity

theorem character_rounded_endpoint_bounds (k : ℕ) (v U : ℝ) (hv : 2 ≤ v) (hUv : U + 1 ≤ v) :
    let X := characterRoundedEndpoint k v
    let τ := characterRoundedTau k v
    1 ≤ X ∧ (X : ℝ) = Real.exp (characterEndpointFactor k * τ) ∧
      2 ≤ τ ∧ (19 / 20 : ℝ) * Real.exp v ≤ τ ∧ τ ≤ Real.exp v ∧
      U ≤ Real.log τ ∧ Real.log τ ≤ v ∧
      Real.log (Real.log (X : ℝ)) ≤ v + Real.log (characterEndpointFactor k) := by
  intro X τ
  have hC := characterEndpointFactor_pos k
  have hCbig : 1000 ≤ characterEndpointFactor k := by
    have hp : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    unfold characterEndpointFactor
    linarith
  have he : 3 ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have hT : 1 ≤ characterEndpointFactor k * Real.exp v := by nlinarith
  have hf := floor_exp_log_bounds (characterEndpointFactor k * Real.exp v) hT
  have hXp : (0 : ℝ) < X := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hf.1
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have htlo : (19 / 20 : ℝ) * Real.exp v ≤ τ := by
    apply (le_div_iff₀ hC).mpr
    have hlow := hf.2.1
    change characterEndpointFactor k * Real.exp v - Real.log 2 ≤ Real.log (X : ℝ) at hlow
    nlinarith only [hlow, hCbig, he, hlog2]
  have hthi : τ ≤ Real.exp v := by
    apply (div_le_iff₀ hC).mpr
    exact hf.2.2.trans_eq (mul_comm _ _)
  have ht2 : 2 ≤ τ := by linarith
  have hτ : 0 < τ := by linarith
  have hidentity : characterEndpointFactor k * τ = Real.log (X : ℝ) := by
    dsimp [τ, characterRoundedTau, X]
    exact mul_div_cancel₀ _ hC.ne'
  have hU : U ≤ Real.log τ := by
    apply (Real.le_log_iff_exp_le hτ).mpr
    have hexp : Real.exp U * Real.exp 1 ≤ Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hUv
    have h2 : 2 * Real.exp U ≤ Real.exp U * Real.exp 1 := by
      nlinarith only [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 : ℝ)) (Real.exp_nonneg U)]
    nlinarith only [hexp, h2, htlo, Real.exp_nonneg v]
  refine ⟨hf.1, ?_, ht2, htlo, hthi, hU, ?_, ?_⟩
  · rw [hidentity, Real.exp_log hXp]
  · exact (Real.log_le_iff_le_exp hτ).mpr hthi
  · have hlogp : 0 < Real.log (X : ℝ) := by rw [← hidentity]; positivity
    apply (Real.log_le_iff_le_exp hlogp).mpr
    rw [Real.exp_add, Real.exp_log hC]
    exact hf.2.2.trans_eq (mul_comm _ _)

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointTestScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff used to test all large endpoint subsets -/

namespace Ostmann

open Filter

theorem eventual_endpointTestCutoff :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 2 ≤ Real.exp (t / 2) / t ^ 12 := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with t hb ht
  have htp : 0 < t := by linarith
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  exact ⟨ht, (le_div_iff₀ (pow_pos htp 12)).mpr hpow⟩

theorem endpointTestCutoff_le_tailCollisionCutoff (t : ℝ) (ht : 1 ≤ t) :
    endpointTestCutoff t ≤ tailCollisionCutoff t := by
  apply Nat.floor_mono
  have htp : 0 < t := by linarith
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (pow_pos htp 5)
  exact pow_le_pow_right₀ ht (by decide : 5 ≤ 12)

theorem eventual_endpointTestCutoff_quarter :
    ∀ᶠ t : ℝ in atTop, Real.exp (t / 4) ≤ (endpointTestCutoff t : ℝ) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventual_endpointTestCutoff] with t hb ht
  have htp : 0 < t := by linarith [ht.1]
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 4) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hexp : Real.exp (t / 4) * Real.exp (t / 4) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (t / 4))
  rw [hexp] at hmul
  have hratio : 2 * Real.exp (t / 4) ≤ Real.exp (t / 2) / t ^ 12 := by
    apply (le_div_iff₀ (pow_pos htp 12)).mpr
    nlinarith only [hmul]
  have hf := Nat.sub_one_lt_floor (Real.exp (t / 2) / t ^ 12)
  change Real.exp (t / 2) / t ^ 12 - 1 < (endpointTestCutoff t : ℝ) at hf
  have hone : 1 ≤ Real.exp (t / 4) := Real.one_le_exp (by positivity)
  linarith

theorem eventual_endpoint_test_error_small (α β D C δ c : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, Real.log t ≤ β * L + D →
      4 * ((48 * Real.log t + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L)) < δ ^ 2 * c := by
  have hlin : Tendsto (fun L : ℝ => L * Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 α hα
  have hconst : Tendsto (fun L : ℝ => Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 α hα
  have hbound : Tendsto (fun L : ℝ =>
      4 * ((48 * (β * L + D) + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L))) atTop (nhds 0) := by
    have h := (hlin.const_mul (192 * β)).add
      (hconst.const_mul (192 * D + 16 * C + 16 * Real.log 2 + 8 * Real.log 4))
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro L
    rw [div_eq_mul_inv, ← Real.exp_neg]
    simp only [neg_mul]
    ring
  filter_upwards [hbound.eventually_lt_const (by positivity : (0 : ℝ) < δ ^ 2 * c)] with L hL t ht
  apply lt_of_le_of_lt _ hL
  gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHigherBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform translated higher-order character bias of the actual residue supports -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem translatedResidueCharacterMean_norm_le_one (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ 1 := by
  unfold translatedResidueCharacterMean
  rw [norm_div, Complex.norm_natCast]
  have hs : ‖∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)‖ ≤ (tailSupport A N p).card := by
    calc
      _ ≤ ∑ r ∈ tailSupport A N p, ‖χ ((r : ZMod p) - t)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ tailSupport A N p, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => χ.norm_le_one _)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)).trans (div_self_le_one _)

theorem higherCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ higherCharacterBias A N p := by
  apply le_csSup _ (Set.mem_insert 0 _)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HigherCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proposition 4.1: maximal translated higher-order bias has harmonic mass o(L) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem mem_closedLogLogPrimeBand_iff (α β L : ℝ) (p : ℕ) :
    p ∈ closedLogLogPrimeBand α β L ↔ p.Prime ∧
      α * L ≤ Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L := by
  simp only [closedLogLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, ?_⟩
    have hpp : (p : ℝ) ≤ Real.exp (Real.exp (β * L)) :=
      (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans
        (Nat.floor_le (Real.exp_nonneg _))
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
    apply (Real.log_le_iff_le_exp (Real.log_pos hp1)).mpr
    exact (Real.log_le_iff_le_exp hp0).mpr hpp
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor (prime_of_loglog_upper p hprime _ hhi), hprime⟩, hlo⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem residueVariance_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) : 0 < residueVariance S := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : 0 < residueDensity S := div_pos (by exact_mod_cast hS.card_pos) hp
  have hd1 : residueDensity S < 1 := (div_lt_one hp).mpr (by exact_mod_cast hSp)
  exact mul_pos hd (sub_pos.mpr hd1)

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

/-- On the balanced supports used in the construction, the physical function
has a fixed pointwise bound. -/
theorem normalizedResidueIndicator_norm_le_three {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (x : ZMod p) :
    ‖normalizedResidueIndicator S x‖ ≤ 3 := by
  have hv : (1 / 9 : ℝ) ≤ residueVariance S := by
    dsimp [residueVariance]
    nlinarith
  have hs : (1 / 3 : ℝ) ≤ Real.sqrt (residueVariance S) := by
    have hh := Real.sq_sqrt (show 0 ≤ residueVariance S by linarith)
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  have hsp : 0 < Real.sqrt (residueVariance S) := by linarith
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hsp]
  apply (div_le_iff₀ hsp).mpr
  have hb := centeredDensity_abs_le S x
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedMixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixed Fourier coefficients of the normalized residue transform

The principal coefficient is controlled by Fourier inversion. Nonprincipal
coefficients are exactly the translated residue bias times its density factor.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem additiveFourier_densityFourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (densityFourier f) a =
      (Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ * f (-a) := by
  change additiveFourier (fun x => (Real.sqrt (p : ℝ) : ℂ) * additiveFourier f x) a = _
  rw [additiveFourier_const_mul, additiveFourier_twice]
  ring

theorem normalizedResidueTransform_principal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (a : ZMod p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) a‖ =
      ‖normalizedResidueIndicator S (-a)‖ / Real.sqrt (p : ℝ) := by
  have he : (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) =
      normalizedResidueTransform S := by
    funext x
    by_cases hx : x = 0
    · simp [hx, normalizedResidueTransform_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), mul_one]
  rw [he, normalizedResidueTransform, additiveFourier_densityFourier,
    norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

theorem densityFourier_mixed_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => densityFourier f x * χ x) a =
      ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
  rw [additiveFourier_mul_character _ χ hχ]
  simp_rw [additiveFourier_densityFourier]
  have he : (∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b))) =
      ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
    have hh := (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => f x * χ⁻¹ (-a - x))
    simpa only [Equiv.neg_apply, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using hh
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [he]

theorem normalizedResidueIndicator_character_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    (∑ x : ZMod p, normalizedResidueIndicator S x * χ⁻¹ (-a - x)) =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x) := by
  have hsum : (∑ x : ZMod p, χ⁻¹ (-a - x)) = 0 := by
    have hh := (Equiv.subLeft (-a)).bijective.sum_comp (fun x => χ⁻¹ x)
    change (∑ x : ZMod p, χ⁻¹ (-a - x)) = ∑ x : ZMod p, χ⁻¹ x at hh
    rw [hh]
    exact MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ)
  have hf (x : ZMod p) : normalizedResidueIndicator S x =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ *
        ((if x ∈ S then 1 else 0) - (residueDensity S : ℂ)) := by
    simp only [normalizedResidueIndicator, centeredDensity, residueDensity,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    split <;> push_cast <;> ring
  simp_rw [hf, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  simp

theorem normalizedResidueTransform_nonprincipal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p)
    (hS : S.Nonempty) (hSp : S.card < p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * χ x) a‖ =
      residueDensity S / Real.sqrt (residueVariance S) *
        ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ := by
  rw [normalizedResidueTransform, densityFourier_mixed_character _ χ hχ,
    normalizedResidueIndicator_character_sum S χ hχ a]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hv := residueVariance_pos S hS hSp
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hsv : 0 < Real.sqrt (residueVariance S) := Real.sqrt_pos.mpr hv
  have hgauss : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ = Real.sqrt (p : ℝ) := by
    have hh := gaussSum_norm_sq χ hχ
    have he := Real.sq_sqrt hp.le
    nlinarith [norm_nonneg (gaussSum χ (ZMod.stdAddChar (N := p))), Real.sqrt_nonneg (p : ℝ)]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hsv, hgauss, residueDensity]
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

/-- The exact Gauss identity supplies the local mixed bound used by the tree
comparison once the translated character means have been bounded. -/
theorem normalizedResidueTransform_mixedBound {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (β : ℝ)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    MixedFourierBound (normalizedResidueTransform S)
      (max (3 / Real.sqrt (p : ℝ)) (2 * β)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < S.card := by
      have hh : 0 < residueDensity S := by linarith
      exact (div_pos_iff_of_pos_right hp).mp hh
    exact_mod_cast hpos
  have hSp : S.card < p := by
    have hh : residueDensity S < 1 := by linarith
    exact_mod_cast (div_lt_one hp).mp hh
  have hv : (1 / 9 : ℝ) ≤ residueVariance S := by
    dsimp [residueVariance]
    nlinarith
  have hs : (1 / 3 : ℝ) ≤ Real.sqrt (residueVariance S) := by
    have hh := Real.sq_sqrt (show 0 ≤ residueVariance S by linarith)
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  have hsv : 0 < Real.sqrt (residueVariance S) := by linarith
  have hratio : residueDensity S / Real.sqrt (residueVariance S) ≤ 2 :=
    (div_le_iff₀ hsv).mpr (by linarith)
  intro χ a
  by_cases hχ : χ = 1
  · subst χ
    rw [normalizedResidueTransform_principal]
    exact (div_le_div_of_nonneg_right (normalizedResidueIndicator_norm_le_three S hlo hhi (-a))
      (Real.sqrt_nonneg _)).trans (le_max_left _ _)
  · rw [normalizedResidueTransform_nonprincipal S χ hχ a hS hSp]
    exact (mul_le_mul hratio (hbias χ hχ a) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (le_max_right _ _)

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One total Fourier-mass function for the actual tail masks -/
namespace Ostmann
open scoped Classical BigOperators

theorem tailDensityMask_balanced_iff (A : Set ℕ) (N p : ℕ) (hp : 0 < p) :
    ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
      residueDensity (tailDensityMask A N p) ≤ 2 / 3) ↔
    ((p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  unfold residueDensity
  rw [tailDensityMask_card]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hp'] at hl
    rw [div_le_iff₀ hp'] at hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    constructor
    · apply (le_div_iff₀ hp').mpr
      linarith
    · apply (div_le_iff₀ hp').mpr
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
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem quadraticResidueTest_translate_congr (p : ℕ) [NeZero p] (t u : ℤ)
    (htu : (t : ZMod p) = (u : ZMod p)) :
    quadraticResidueTest p t = quadraticResidueTest p u := by
  funext r
  rw [quadraticResidueTest_eq_character, quadraticResidueTest_eq_character, htu]

theorem translated_quadratic_bias_le_maximal (S : Finset ℕ) (p : ℕ) [NeZero p] (t : ℤ) :
    |residueTestMean S (quadraticResidueTest p t)| ≤ maximalQuadraticBias S p := by
  have hm := (Classical.choose_spec (Finset.exists_max_image (Finset.range (p + 1))
    (fun t : ℕ => |residueTestMean S (quadraticResidueTest p t)|)
    (Finset.nonempty_range_iff.mpr (by omega)))).2
  have he : (t : ZMod p) = (((t : ZMod p).val : ℕ) : ℤ) := by simp
  rw [quadraticResidueTest_translate_congr p t _ he]
  exact hm _ (Finset.mem_range.mpr (by have := ZMod.val_lt (t : ZMod p); omega))

theorem maximalQuadraticBias_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ maximalQuadraticBias S p :=
  abs_nonneg _

theorem maximalQuadraticBias_le_one (S : Finset ℕ) (p : ℕ) : maximalQuadraticBias S p ≤ 1 :=
  residueTestMean_abs_le_one S _ (fun r _ => quadraticResidueTest_abs_le p _ r)

theorem quadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) : 0 ≤ quadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (logPrimeBand_mem hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeQuadraticUniqueness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The only nonprincipal quadratic character at a prime -/
namespace Ostmann

theorem prime_character_eq_of_square_eq_one {p : ℕ} [Fact p.Prime]
    (χ ψ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχ2 : χ ^ 2 = 1) (hψ2 : ψ ^ 2 = 1) : χ = ψ := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective (ZMod p)ˣ
  have hext (φ θ : DirichletCharacter ℂ p) (heq : φ g = θ g) : φ = θ := by
    apply MulChar.equivToUnitHom.injective
    apply MonoidHom.ext
    intro u
    obtain ⟨z, rfl⟩ := hg u
    change φ.toUnitHom (g ^ z) = θ.toUnitHom (g ^ z)
    rw [map_zpow, map_zpow]
    congr 1
    exact Units.ext heq
  have hneg (φ : DirichletCharacter ℂ p) (hφ : φ ≠ 1) (hφ2 : φ ^ 2 = 1) : φ g = -1 := by
    have hs : φ g ^ 2 = 1 := by
      have hh := congrArg (fun θ : DirichletCharacter ℂ p => θ g) hφ2
      simpa only [MulChar.pow_apply_coe, MulChar.one_apply g.isUnit] using hh
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact (hφ (hext φ 1 (by simpa only [MulChar.one_apply g.isUnit] using hh))).elim
    · exact hh
  exact hext χ ψ ((hneg χ hχ hχ2).trans (hneg ψ hψ hψ2).symm)

theorem complexJacobiCharacter_square {p : ℕ} [Fact p.Prime] :
    complexJacobiCharacter p ^ 2 = 1 := by
  apply MulChar.IsQuadratic.sq_eq_one
  change ((jacobiCharacterInt p).ringHomComp (Int.castRingHom ℂ)).IsQuadratic
  rw [jacobiCharacterInt_prime]
  exact (quadraticChar_isQuadratic (ZMod p)).comp _

theorem complexJacobiCharacter_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    complexJacobiCharacter p ≠ 1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  intro he
  have hev := congrArg (fun χ : DirichletCharacter ℂ p => χ a) he
  have hneg : complexJacobiCharacter p a = -1 := by
    simp only [complexJacobiCharacter, MulChar.ringHomComp_apply, jacobiCharacterInt_prime]
    rw [ha]
    norm_num
  rw [hneg, MulChar.one_apply a.isUnit] at hev
  norm_num at hev

theorem prime_quadratic_character_unique {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    χ = complexJacobiCharacter p :=
  prime_character_eq_of_square_eq_one χ _ hχ (complexJacobiCharacter_ne_one hp2)
    hχ2 complexJacobiCharacter_square

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TailCharacterBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both character orders control the actual tail transform -/
namespace Ostmann
open scoped Classical BigOperators

theorem translated_complexJacobi_mean (A : Set ℕ) (N p : ℕ) [NeZero p] (t : ZMod p) :
    translatedResidueCharacterMean A N p (complexJacobiCharacter p) t =
      (residueTestMean (tailSupport A N p) (quadraticResidueTest p (t.val : ℤ)) : ℂ) := by
  have ht : ((t.val : ℤ) : ZMod p) = t := by simp
  have he (r : ℕ) : complexJacobiCharacter p ((r : ZMod p) - t) =
      (quadraticResidueTest p (t.val : ℤ) r : ℂ) := by
    rw [quadraticResidueTest_eq_character, ht]
    simp only [complexJacobiCharacter, jacobiCharacter, MulChar.ringHomComp_apply]
    norm_cast
  simp only [translatedResidueCharacterMean, he, residueTestMean,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

theorem translatedResidueCharacterMean_norm_le_higher (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (hχ : χ ^ 2 ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ higherCharacterBias A N p := by
  unfold higherCharacterBias
  refine le_csSup ?_ (Or.inr ⟨χ, hχ, t, rfl⟩)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨ψ, _, u, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p ψ u

theorem translated_tail_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  by_cases hχ2 : χ ^ 2 = 1
  · rw [prime_quadratic_character_unique hp2 χ hχ hχ2, translated_complexJacobi_mean,
      Complex.norm_real, Real.norm_eq_abs]
    exact (translated_quadratic_bias_le_maximal (tailSupport A N p) p (t.val : ℤ)).trans
      (le_add_of_nonneg_right (higherCharacterBias_nonneg A N p))
  · exact (translatedResidueCharacterMean_norm_le_higher A N p χ hχ2 t).trans
      (le_add_of_nonneg_left (maximalQuadraticBias_nonneg (tailSupport A N p) p))

theorem tailDensityMask_character_mean (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ (x - t)) = translatedResidueCharacterMean A N p χ t := by
  rw [tailDensityMask_card]
  have hi : Set.InjOn (fun r : ℕ => (r : ZMod p)) (tailSupport A N p) := by
    intro r hr s hs he
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
    have hm := (ZMod.natCast_eq_natCast_iff' r s p).mp he
    simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hm
  rw [tailDensityMask, Finset.sum_image hi]
  exact (div_eq_inv_mul _ _).symm

theorem tailDensityMask_reverse_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ⁻¹ (-a - x))‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  have he (x : ZMod p) : χ⁻¹ (-a - x) = χ⁻¹ (-1) * χ⁻¹ (x - (-a)) := by
    rw [← map_mul]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ (χ⁻¹ (-1)), mul_assoc,
    tailDensityMask_character_mean, norm_mul]
  have hunit : ‖χ⁻¹ (-1 : ZMod p)‖ = 1 := by
    exact norm_mulChar_unit χ⁻¹ (-1 : (ZMod p)ˣ)
  rw [hunit, one_mul]
  exact translated_tail_character_mean_bound A N p hp2 χ⁻¹ (inv_ne_one.mpr hχ) (-a)

theorem tail_transform_mixed_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p))
    (hhi : residueDensity (tailDensityMask A N p) ≤ 2 / 3) :
    MixedFourierBound (normalizedResidueTransform (tailDensityMask A N p))
      (max (3 / Real.sqrt (p : ℝ))
        (2 * (maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p))) :=
  normalizedResidueTransform_mixedBound _ hlo hhi _
    (tailDensityMask_reverse_character_mean_bound A N p hp2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ClosedQuadraticBand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed prime band used in the manuscript's quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem mem_closedLogPrimeBand_iff (T : ℝ) (p : ℕ) :
    p ∈ closedLogPrimeBand T ↔ p.Prime ∧ T ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  simp only [closedLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, (Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mpr ?_⟩
    exact (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hhi), hprime⟩, hlo⟩

theorem logPrimeBand_subset_closed (T : ℝ) : logPrimeBand T ⊆ closedLogPrimeBand T := by
  intro p hp
  have hh := logPrimeBand_mem hp
  exact (mem_closedLogPrimeBand_iff T p).mpr ⟨hh.1, hh.2.1.le, hh.2.2⟩

private theorem deleted_log_eq (T : ℝ) {p : ℕ}
    (hp : p ∈ closedLogPrimeBand T \ logPrimeBand T) : Real.log (p : ℝ) = T := by
  obtain ⟨hclosed, hnot⟩ := Finset.mem_sdiff.mp hp
  have hc := (mem_closedLogPrimeBand_iff T p).mp hclosed
  have hup : p ∈ Nat.primesLE ⌊Real.exp (2 * T)⌋₊ := (Finset.mem_filter.mp hclosed).1
  have hlo : p ∈ Nat.primesLE ⌊Real.exp T⌋₊ := by
    by_contra hn
    exact hnot (Finset.mem_sdiff.mpr ⟨hup, hn⟩)
  have hple : (p : ℝ) ≤ Real.exp T :=
    (by exact_mod_cast Nat.le_of_mem_primesLE hlo : (p : ℝ) ≤ ⌊Real.exp T⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  exact le_antisymm ((Real.log_le_iff_le_exp (by exact_mod_cast hc.1.pos)).mpr hple) hc.2.1

theorem closedQuadraticBandMass_le (A : Set ℕ) (N : ℕ) (T : ℝ) :
    closedQuadraticBandMass A N T ≤ quadraticBandMass A N T + 1 := by
  let E := closedLogPrimeBand T \ logPrimeBand T
  have hcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpprime := ((mem_closedLogPrimeBand_iff T p).mp (Finset.mem_sdiff.mp hp).1).1
    have hqprime := ((mem_closedLogPrimeBand_iff T q).mp (Finset.mem_sdiff.mp hq).1).1
    have he := congrArg Real.exp ((deleted_log_eq T hp).trans (deleted_log_eq T hq).symm)
    rw [Real.exp_log (by exact_mod_cast hpprime.pos), Real.exp_log (by exact_mod_cast hqprime.pos)] at he
    exact_mod_cast he
  have hsum : (∑ p ∈ E, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) ≤ 1 := by
    calc
      _ ≤ ∑ _p ∈ E, (1 : ℝ) := Finset.sum_le_sum (fun p hp => by
        have hprime := ((mem_closedLogPrimeBand_iff T p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
        have hweight : 0 ≤ Real.log (p : ℝ) / p :=
          div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hp0.le
        have hweightU : Real.log (p : ℝ) / p ≤ 1 :=
          (div_le_one hp0).mpr (Real.log_le_self hp0.le)
        exact (mul_le_mul_of_nonneg_left (maximalQuadraticBias_le_one _ _) hweight).trans
          (by simpa using hweightU))
      _ = (E.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  have he := Finset.sum_sdiff (f := fun (p : ℕ) => (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p)
    (logPrimeBand_subset_closed T)
  change _ + quadraticBandMass A N T = closedQuadraticBandMass A N T at he
  linarith

theorem closedQuadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) :
    0 ≤ closedQuadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := ((mem_closedLogPrimeBand_iff T p).mp hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

theorem closedQuadraticBandMass_isLittleO_of_halfopen (A : Set ℕ) (N : ℕ)
    (h : (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T)) :
    (fun T => closedQuadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [h.bound (show 0 < c / 2 by positivity), eventually_ge_atTop (2 / c)] with T hh hT
  have hTpos : 0 ≤ T := (by positivity : (0 : ℝ) ≤ 2 / c).trans hT
  have hone : 1 ≤ c / 2 * T := by have := (div_le_iff₀ hc).mp hT; nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (closedQuadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hTpos]
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hTpos] at hh
  linarith [closedQuadraticBandMass_le A N T]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AllCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining quadratic and higher-order translated decorrelation -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem tailCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ tailCharacterBias A N p :=
  add_nonneg (maximalQuadraticBias_nonneg _ _) (higherCharacterBias_nonneg _ _ _)

/-- Markov's bound is uniform in subsets of the whole closed band. -/
theorem eventual_bad_tail_character_mass (A : Set ℕ) (N : ℕ) (α β δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε)
    (hsmall : (fun L => tailCharacterBandMass A N α β L) =o[atTop] (fun L : ℝ => L)) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) ≤ ε * L := by
  have hh := hsmall.bound (mul_pos hδ hε)
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with L hh hL P hP
  have hnonneg : 0 ≤ tailCharacterBandMass A N α β L :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (tailCharacterBias_nonneg _ _ _))
  have hmass : tailCharacterBandMass A N α β L ≤ δ * ε * L := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hL] using hh
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    δ * (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) =
        ∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), δ * (p : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p),
        (p : ℝ)⁻¹ * tailCharacterBias A N p := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2.le
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (show 0 ≤ (p : ℝ)⁻¹ by positivity)
    _ ≤ tailCharacterBandMass A N α β L :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => hP (Finset.mem_filter.mp hp).1)
        (fun p _ _ => mul_nonneg (by positivity) (tailCharacterBias_nonneg A N p))
    _ ≤ δ * (ε * L) := by simpa only [mul_assoc] using hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CollisionPrimeCellBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good cells from the proved collision-stability budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem collisionExceptionalPrimes_log_mass (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ collisionExceptionalPrimes P S T μ ν, Real.log (p : ℝ) / p) ≤ 4 * E := by
  have h := weighted_cost_exception_bound P (fun p => Real.log (p : ℝ) / p)
    (fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) (1 / 4)
    (fun p hp => div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
      (Nat.cast_nonneg _))
    (fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp)))
  have heq : (∑ p ∈ P, Real.log (p : ℝ) / p *
      ((p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  rw [heq] at h
  change (1 / 4 : ℝ) * (∑ p ∈ collisionExceptionalPrimes P S T μ ν,
    Real.log (p : ℝ) / p) ≤ _ at h
  linarith

theorem collision_retained_prime_balanced (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (p : ℕ) (hp : p ∈ P \ collisionExceptionalPrimes P S T μ ν) :
    (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 := by
  obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
  have hsmall : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    by_contra! hh
    exact hpnot (Finset.mem_filter.mpr ⟨hpP, hh⟩)
  exact small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CollisionBalancedPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced mass under the unconditioned harmonic prime prior -/
namespace Ostmann
open scoped Classical BigOperators

theorem primeSubsetPrior_real_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (f : ℕ → ℝ) :
    (∑ p : P, primeSubsetPrior P Q p * f p) =
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * ∑ q ∈ Q, (q : ℝ)⁻¹ * f q := by
  have h := congrArg Complex.re (primeSubsetPrior_mean P Q hQP (fun p => (f p : ℂ)))
  simpa only [← Complex.ofReal_inv, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using h

theorem primeSubsetPrior_balanced_mass (P Q R : Finset ℕ) (hQP : Q ⊆ P) (hRQ : R ⊆ Q)
    (good : ℕ → Prop) [DecidablePred good] (hgood : ∀ p ∈ R, good p)
    (hM : 0 < ∑ p ∈ Q, (p : ℝ)⁻¹)
    (hR : (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 ≤ ∑ p ∈ R, (p : ℝ)⁻¹) :
    (1 / 2 : ℝ) ≤ ∑ p : P, if good p then primeSubsetPrior P Q p else 0 := by
  have he := primeSubsetPrior_real_mean P Q hQP (fun p => if p ∈ R then 1 else 0)
  have hfilter : Q.filter (fun p => p ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hRQ h, h⟩⟩
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter] at he
  rw [Finset.sum_filter] at he
  have hnorm : (1 / 2 : ℝ) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ * ∑ p ∈ R, (p : ℝ)⁻¹ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hM]
    linarith
  apply (hnorm.trans_eq he.symm).trans
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : (p : ℕ) ∈ R
  · simpa only [hp, ite_true, if_true, hgood p hp] using (le_rfl : primeSubsetPrior P Q p ≤ primeSubsetPrior P Q p)
  · simp only [hp, ite_false, if_false]
    split_ifs
    · exact primeSubsetPrior_nonneg P Q p
    · exact le_rfl

theorem collision_harmonic_prior_balanced_mass (P Q ambient : Finset ℕ)
    (hQP : Q ⊆ P) (hQA : Q ⊆ ambient)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (D G : ℝ) (hG : 0 < G)
    (hprime : ∀ p ∈ ambient, p.Prime)
    (hS : ∀ p ∈ ambient, (S p).Nonempty) (hT : ∀ p ∈ ambient, (T p).Nonempty)
    (hcard : ∀ p ∈ ambient, (S p).card + (T p).card = p)
    (hlog : ∀ p ∈ ambient, G ≤ Real.log (p : ℝ))
    (hbudget : (∑ p ∈ ambient, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D)
    (hM : 0 < ∑ p ∈ Q, (p : ℝ)⁻¹)
    (hsmall : 4 * D / G ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) / 2) :
    (1 / 2 : ℝ) ≤ ∑ p : P, if (p : ℝ) / 3 ≤ (S p).card ∧
      ((S p).card : ℝ) ≤ 2 * p / 3 then primeSubsetPrior P Q p else 0 := by
  let E := collisionExceptionalPrimes ambient S T μ ν
  have hEA : E ⊆ ambient := Finset.filter_subset _ _
  have hbad := collisionExceptionalPrimes_log_mass ambient S T μ ν D hprime hS hT
    (fun p hp => (hcard p hp).le) hbudget
  have hbadmass : (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 4 * D / G := by
    apply (le_div_iff₀ hG).mpr
    calc
      _ = ∑ p ∈ E, G * (p : ℝ)⁻¹ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
          (hlog p (hEA hp)) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hbad
  have hint : (∑ p ∈ Q ∩ E, (p : ℝ)⁻¹) ≤ ∑ p ∈ E, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => by positivity)
  apply primeSubsetPrior_balanced_mass P Q (Q \ E) hQP Finset.sdiff_subset
    (fun p : ℕ => (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3) ?_ hM ?_
  · intro p hp
    have hh := Finset.mem_sdiff.mp hp
    exact collision_retained_prime_balanced ambient S T μ ν hS hT hcard p
      (Finset.mem_sdiff.mpr ⟨hQA hh.1, hh.2⟩)
  · have he := Finset.sum_inter_add_sum_sdiff Q E (fun p : ℕ => (p : ℝ)⁻¹)
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothLogCellProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth partition profile for the original logarithmic cells -/

namespace Ostmann
open Filter
open scoped Classical

/-- The two nonzero translates telescope to one on a unit logarithmic cell. -/
theorem logCellProfile_partition (x : ℝ) (hlo : 0 ≤ x) (hhi : x ≤ 1) :
    logCellProfile x + logCellProfile (x - 1) = 1 := by
  unfold logCellProfile
  rw [Real.smoothTransition.one_of_one_le (x := x + 1) (by linarith),
    Real.smoothTransition.zero_of_nonpos (x := x - 1) (by linarith), sub_add_cancel]
  ring

/-- The full integer partition of unity specified for the logarithmic cells.
Only the two translates adjacent to `floor x` can be nonzero. -/
theorem logCellProfile_partition_unity (x : ℝ) :
    (∑' n : ℤ, logCellProfile (x - n)) = 1 := by
  let z := ⌊x⌋
  have hzlo : (z : ℝ) ≤ x := Int.floor_le x
  have hzhi : x < (z : ℝ) + 1 := Int.lt_floor_add_one x
  have hzero (n : ℤ) (hn : n ∉ ({z, z + 1} : Finset ℤ)) :
      logCellProfile (x - n) = 0 := by
    have hne : n ≠ z ∧ n ≠ z + 1 := by simpa only [Finset.mem_insert,
      Finset.mem_singleton, not_or] using hn
    apply logCellProfile_zero_outside
    by_cases hle : n ≤ z
    · have hi : n + 1 ≤ z := by omega
      have hr : (n : ℝ) + 1 ≤ z := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ x - n by linarith).trans (le_abs_self _)
    · have hi : z + 2 ≤ n := by omega
      have hr : (z : ℝ) + 2 ≤ n := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ -(x - n) by linarith).trans (neg_le_abs _)
  rw [tsum_eq_sum hzero, Finset.sum_pair (by omega : z ≠ z + 1)]
  have hp := logCellProfile_partition (x - z) (by linarith) (by linarith)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  rw [Int.cast_add, Int.cast_one]
  congr 2
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic cutoff weights in the initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every nonzero translate on this bounded range is retained, including
both boundary centers. -/
theorem logCellProfile_sum_centers (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hN : x ≤ N) :
    (∑ c ∈ Finset.Icc (0 : ℤ) N, logCellProfile (x - c)) = 1 := by
  have h := logCellProfile_partition_unity x
  rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) N) (fun c hc => ?_)] at h
  · exact h
  · apply logCellProfile_zero_outside
    have hc' : c < 0 ∨ (N : ℤ) < c := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hc
    rcases hc' with hc' | hc'
    · have hi : c ≤ -1 := by omega
      have hr : (c : ℝ) ≤ -1 := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ x - c by linarith).trans (le_abs_self _)
    · have hi : (N : ℤ) + 1 ≤ c := by omega
      have hr : (N : ℝ) + 1 ≤ c := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ -(x - c) by linarith).trans (neg_le_abs _)

/-- Pigeonholing selects a weight, without changing the underlying law. -/
theorem exists_weighted_log_sum_center {A : Type*} [Fintype A]
    (weight score : A → ℝ) (N : ℕ) (β : ℝ)
    (hmass : β ≤ ∑ a, weight a)
    (hscore : ∀ a, 0 ≤ score a ∧ score a ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      β / (N + 1) ≤ ∑ a, weight a * logCellProfile (score a - c) := by
  have hcard : ((Finset.Icc (0 : ℤ) N).card : ℝ) = N + 1 := by
    simp
  have hsum : (∑ c ∈ Finset.Icc (0 : ℤ) N,
      ∑ a, weight a * logCellProfile (score a - c)) = ∑ a, weight a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum, logCellProfile_sum_centers N (score a)
      (hscore a).1 (hscore a).2, mul_one]
  apply Finset.exists_le_of_sum_le (s := Finset.Icc (0 : ℤ) N)
    (Finset.nonempty_Icc.mpr (by omega))
  rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_div_cancel₀ _ (by positivity), hsum]
  exact hmass

theorem balancedTupleSet_mass {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0) :
    δ ^ n ≤ ∑ x ∈ balancedTupleSet n good, productPrior μ x := by
  have he (x : Fin n → A) :
      (∏ i, if good i (x i) then μ i (x i) else 0) =
        if ∀ i, good i (x i) then productPrior μ x else 0 := by
    by_cases h : ∀ i, good i (x i)
    · simp [h, productPrior]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have hs : (∑ x ∈ balancedTupleSet n good, productPrior μ x) =
      ∏ i, ∑ a, if good i a then μ i a else 0 := by
    simp only [balancedTupleSet, Finset.sum_filter]
    simp_rw [← he]
    exact (Fintype.prod_sum (fun i a => if good i a then μ i a else 0)).symm
  rw [hs]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun _ _ => hδ) (fun i _ => hmass i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform exponential mass of the chosen broad-band cutoff -/

namespace Ostmann
open scoped Classical BigOperators

theorem logSumCenter_count_bound (n m : ℕ) (T : ℝ)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m) :
    (⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) + 1 ≤ Real.exp (2 * m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
  have he : (m : ℝ) + 1 ≤ Real.exp m := by
    linarith [Real.add_one_le_exp (m : ℝ)]
  have he2 : (2 : ℝ) ≤ Real.exp m := by linarith
  calc
    _ ≤ (n : ℝ) * Real.exp T + 2 := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) * Real.exp T by positivity)
      linarith
    _ ≤ (m : ℝ) * Real.exp m + 2 := by gcongr
    _ ≤ ((m : ℝ) + 1) * Real.exp m := by nlinarith
    _ ≤ Real.exp m * Real.exp m := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem halfPower_div_logSumCenters (n m : ℕ) (T : ℝ)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m) :
    Real.exp (-(Real.log 2 + 2) * m) ≤
      (1 / 2 : ℝ) ^ n / ((⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) + 1) := by
  have hcount := logSumCenter_count_bound n m T hm hn hT
  have hpow : Real.exp (-(Real.log 2) * m) ≤ (1 / 2 : ℝ) ^ n := by
    have he : Real.exp (-(Real.log 2) * n) = (1 / 2 : ℝ) ^ n := by
      rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [one_div, inv_pow]
    rw [← he]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
    nlinarith
  have hform : Real.exp (-(Real.log 2 + 2) * m) =
      Real.exp (-(Real.log 2) * m) / Real.exp (2 * m) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hform]
  exact div_le_div₀ (by positivity) hpow (by positivity) hcount

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedTailScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer endpoints for a whole harmonic prime band at every real scale -/
namespace Ostmann
open Filter

/-- Choose a literal integer endpoint above the band, while retaining a
linear bound on the logarithm of its logarithm. -/
theorem eventual_rounded_tail_scale (β : ℝ) (hβ : 0 < β) (T₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∃ (X : ℕ) (T : ℝ), T₀ ≤ T ∧
      (X : ℝ) = Real.exp T ∧
      Real.log T ≤ (β + 1) * L + Real.log 1000 ∧
      Real.exp (β * L) ≤ T / 4 := by
  have hg := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith only [hβ] : 0 < β + 1))
  filter_upwards [hg.eventually (eventually_ge_atTop T₀), eventually_ge_atTop (4 : ℝ)]
    with L hlarge hL
  let v := (β + 1) * L
  have hv : 2 ≤ v := by dsimp [v]; nlinarith only [hL, hβ]
  obtain ⟨hX1, hX, _, hτlo, _, _, _, hlog⟩ :=
    character_rounded_endpoint_bounds 0 v 0 hv (by linarith only [hv])
  let X := characterRoundedEndpoint 0 v
  let T := characterEndpointFactor 0 * characterRoundedTau 0 v
  have hf : characterEndpointFactor 0 = 1000 := by norm_num [characterEndpointFactor]
  have hT : Real.exp v ≤ T := by
    dsimp only [T]
    rw [hf]
    nlinarith only [hτlo, Real.exp_pos v]
  refine ⟨X, T, hlarge.trans hT, hX, ?_, ?_⟩
  · rw [hX, Real.log_exp, hf] at hlog
    simpa only [T, hf] using hlog
  · have he : 4 ≤ Real.exp L := by linarith only [Real.add_one_le_exp L, hL]
    have hh := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (β * L))
    have heq : Real.exp (β * L) * Real.exp L = Real.exp v := by
      rw [← Real.exp_add]
      congr 1
      dsimp [v]
      ring
    rw [heq] at hh
    linarith only [hh, hT]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailCellWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected small cells lie below the actual collision cutoff -/

namespace Ostmann
open Filter

theorem eventual_tail_cell_window (a C H : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      Real.exp ((1 / 100 : ℝ) * L) ≤ target →
      target ≤ Real.exp ((11 / 1000 : ℝ) * L) →
      H ≤ target ∧
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.log (tailCollisionCutoff X : ℝ) ∧
      target + 64 * tailDefectBudget a C X + 1 ≤ Real.exp (L / 2) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + Real.log 2 + 2
  let K := 1290 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (4 / 100) 0 K (1 / 2) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (11 / 1000) (1 / 2) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop X₀),
    (ht (1 / 100) (by norm_num)).eventually (eventually_ge_atTop H),
    eventually_ge_atTop (1 : ℝ)] with L hgap hlarge hX0 hH hL
  intro X target hXlo hXhi htlo hthi
  have hcut := hX₀ X (hX0.trans hXlo)
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log (by linarith [hcut.1] : 0 < X) hXhi
    rwa [Real.log_exp] at h
  have htail := (tailCollisionCutoff_bounds X hcut.1 hcut.2.1).2.2
  have hlinear : 1285 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((11 / 1000 : ℝ) * L) ≤
      K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    have hKL : 1 ≤ K * L := hL.trans (le_mul_of_one_le_left (by linarith) hK)
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hKL
  have hbound : target + 64 * tailDefectBudget a C X + 2 +
      5 * Real.log X + Real.log 2 ≤ K * L + K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    calc
      _ = target + 1285 * Real.log X + D := by dsimp [tailDefectBudget, D]; ring
      _ ≤ Real.exp ((11 / 1000 : ℝ) * L) + 1285 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, zero_mul, Real.exp_zero] at hgap hlarge
  refine ⟨hH.trans htlo, ?_, ?_⟩
  · nlinarith only [hbound, hgap, htail, hXlo]
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hcut.1
    have hexp : Real.exp ((1 / 2 : ℝ) * L) = Real.exp (L / 2) := by congr 1; ring
    rw [hexp] at hlarge
    nlinarith only [hbound, hlarge, hlog2, hlogX0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCellGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailCellLinearRate_nonneg (a C : ℝ) : 0 ≤ tailCellLinearRate a C := by
  unfold tailCellLinearRate
  positivity

theorem tailDefectBudget_linear (a C L X : ℝ) (hL : 1 ≤ L)
    (hX : 0 < X) (hXupper : X ≤ Real.exp L) :
    tailDefectBudget a C X ≤ tailCellLinearRate a C * L := by
  have hlog : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXupper
    rwa [Real.log_exp] at h
  have hc := le_abs_self (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a)
  have hcl := mul_le_mul_of_nonneg_left hL
    (abs_nonneg (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a))
  unfold tailDefectBudget tailCellLinearRate
  nlinarith only [hlog, hc, hcl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedInitialLogSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial logarithmic cutoffs on the support of the original priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The score only needs to be bounded where its weight is nonzero. This
allows all prime roles to share the same large ambient container. -/
theorem exists_supported_log_sum_center {A : Type*} [Fintype A]
    (weight score : A → ℝ) (N : ℕ) (β : ℝ)
    (hmass : β ≤ ∑ a, weight a)
    (hscore : ∀ a, weight a ≠ 0 → 0 ≤ score a ∧ score a ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      β / (N + 1) ≤ ∑ a, weight a * logCellProfile (score a - c) := by
  let score' : A → ℝ := fun a => if weight a = 0 then 0 else score a
  have hs (a : A) : 0 ≤ score' a ∧ score' a ≤ N := by
    by_cases ha : weight a = 0
    · simp only [score', ite_eq_left ha]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
    · simpa only [score', ite_eq_right ha] using hscore a ha
  obtain ⟨c, hc, h⟩ := exists_weighted_log_sum_center weight score' N β hmass hs
  refine ⟨c, hc, ?_⟩
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : weight a = 0
  · simp only [ha, zero_mul]
  · simp only [score', ite_eq_right ha]

theorem exists_supported_balanced_log_sum_center {A : Type*} [Fintype A]
    (n : ℕ) (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (score : (Fin n → A) → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0)
    (hscore : ∀ x, productPrior μ x ≠ 0 → 0 ≤ score x ∧ score x ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      δ ^ n / (N + 1) ≤ ∑ x ∈ balancedTupleSet n good,
        productPrior μ x * logCellProfile (score x - c) := by
  have hb := balancedTupleSet_mass n μ good δ hδ hmass
  have hm : δ ^ n ≤ ∑ x, if ∀ i, good i (x i) then productPrior μ x else 0 := by
    simpa only [balancedTupleSet, Finset.sum_filter] using hb
  obtain ⟨c, hc, h⟩ := exists_supported_log_sum_center
    (fun x => if ∀ i, good i (x i) then productPrior μ x else 0) score N (δ ^ n) hm (by
      intro x hx
      have hprod : productPrior μ x ≠ 0 := by
        intro he
        by_cases hg : ∀ i, good i (x i) <;> simp [hg, he] at hx
      exact hscore x hprod)
  refine ⟨c, hc, ?_⟩
  simpa only [balancedTupleSet, Finset.sum_filter, ite_mul, zero_mul] using h

/-- The cutoff remains in the true bulk or spectator range although its
prior is represented on a container that also contains the giant primes. -/
theorem exists_supported_prime_log_sum_center (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n m : ℕ) (T : ℝ)
    (μ : Fin n → P → ℝ) (good : Fin n → P → Prop)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m)
    (hlog : ∀ i (p : P), μ i p ≠ 0 → Real.log (p : ℝ) ≤ Real.exp T)
    (hmass : ∀ i, (1 / 2 : ℝ) ≤ ∑ p, if good i p then μ i p else 0) :
    ∃ c ∈ Finset.Icc (0 : ℤ) ⌈(n : ℝ) * Real.exp T⌉₊,
      Real.exp (-(Real.log 2 + 2) * m) ≤
        ∑ x ∈ balancedTupleSet n good, productPrior μ x *
          logCellProfile ((∑ i, Real.log (x i : ℝ)) - c) := by
  have hscore (x : Fin n → P) (hx : productPrior μ x ≠ 0) :
      0 ≤ ∑ i, Real.log (x i : ℝ) ∧
        (∑ i, Real.log (x i : ℝ)) ≤ (⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) := by
    constructor
    · exact Finset.sum_nonneg fun i _ => Real.log_nonneg
        (by exact_mod_cast (hP (x i) (x i).property).one_lt.le)
    · calc
        _ ≤ ∑ _i : Fin n, Real.exp T := by
          apply Finset.sum_le_sum
          intro i hi
          apply hlog i (x i)
          intro hz
          apply hx
          exact Finset.prod_eq_zero hi hz
        _ = (n : ℝ) * Real.exp T := by simp
        _ ≤ _ := Nat.le_ceil _
  obtain ⟨c, hc, h⟩ := exists_supported_balanced_log_sum_center n μ good
    (fun x => ∑ i, Real.log (x i : ℝ)) ⌈(n : ℝ) * Real.exp T⌉₊
    (1 / 2) (by norm_num) hmass hscore
  exact ⟨c, hc, (halfPower_div_logSumCenters n m T hm hn hT).trans h⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailBandBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unbalanced tail supports have negligible mass on each harmonic band -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.eventual_unbalanced_band_mass
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      (∑ p ∈ P.filter (fun p => ¬((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3)), (p : ℝ)⁻¹) ≤ ε * L := by
  classical
  obtain ⟨a, ha, hcounts⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (hcounts.and ((eventual_tailCollisionCutoff N).and eventual_endpointTestCutoff_quarter))
  have herr := eventual_endpoint_test_error_small α (β + 1) (Real.log 1000)
    (C + Real.log 4 / (2 * a)) 1 ε hα (by norm_num) hε
  filter_upwards [eventual_rounded_tail_scale β hβ T₀, herr, eventually_ge_atTop (1 : ℝ)]
    with L hround herr hL P hP
  obtain ⟨X, T, hT, hX, hlogT, hrange⟩ := hround
  obtain ⟨hcounts, hcut, hquarter⟩ := hT₀ T hT
  obtain ⟨hEA, hEB, _, _, _⟩ := hcounts X hX
  let EA := summandTail A (summandTailCutoff T) X
  let EB := summandTail B (summandTailCutoff T) X
  let S := tailSupport A N
  let V := fun p => Finset.range p \ S p
  let μ := fun p => residueMass EA (fun _ => 1 / (EA.card : ℝ)) p
  let ν := fun p => fiberMass EB (fun _ => 1 / (EB.card : ℝ)) (negativeResidue p)
  let D := 20 * Real.log T + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    ((mem_closedLogLogPrimeBand_iff α β L p).mp (hP hp)).1
  have hPcut : P ⊆ Nat.primesLE (tailCollisionCutoff T) := by
    intro p hp
    have hpband := (mem_closedLogLogPrimeBand_iff α β L p).mp (hP hp)
    have hpupper := prime_of_loglog_upper p hpband.1 _ hpband.2.2
    have hcutupper : Real.exp (Real.exp (β * L)) ≤ tailCollisionCutoff T :=
      (Real.exp_le_exp.mpr hrange).trans (hquarter.trans (by exact_mod_cast
        (endpointTestCutoff_le_tailCollisionCutoff T hcut.1)))
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpupper.trans hcutupper, hpband.1⟩
  have hS (p : ℕ) (hp : p ∈ P) : (S p).Nonempty := tailSupport_nonempty hA N p (hprime p hp).pos
  have hV (p : ℕ) (hp : p ∈ P) : (V p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p : ℕ) : (S p).card + (V p).card = p := tailSupport_card_add_complement A N p
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (V p) (μ p) (ν p)) ≤ D := by
    have hh := uniform_tail_collision_bound hA hB N (summandTailCutoff T) X a T C ha hcut.1
      hcut.2.1 hX hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
      (by simpa only [positiveSummandTail_card] using hEA)
      (by simpa only [negativeSummandTail_card] using hEB) hM
    apply le_trans _ hh
    exact Finset.sum_le_sum_of_subset_of_nonneg hPcut (fun p hp _ =>
      mul_nonneg (Real.log_natCast_nonneg p)
        (collisionDefect_nonneg _ _ _ _
          (tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
          (tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
            (hN p (Nat.prime_of_mem_primesLE hp))) (hcard p).le))
  let E := collisionExceptionalPrimes P S V μ ν
  let Bad := P.filter (fun p => ¬((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
    residueDensity (tailDensityMask A N p) ≤ 2 / 3))
  have hBad : Bad ⊆ E := by
    intro p hp
    obtain ⟨hpP, hnot⟩ := Finset.mem_filter.mp hp
    by_contra hpE
    have hbal := collision_retained_prime_balanced P S V μ ν hS hV (fun p _ => hcard p) p
      (Finset.mem_sdiff.mpr ⟨hpP, hpE⟩)
    exact hnot ((tailDensityMask_balanced_iff A N p (hprime p hpP).pos).mpr hbal)
  have hmass : (∑ p ∈ Bad, (p : ℝ)⁻¹) ≤ 4 * D / Real.exp (α * L) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hlogmass := collisionExceptionalPrimes_log_mass P S V μ ν D hprime hS hV
      (fun p _ => (hcard p).le) hbudget
    calc
      _ = ∑ p ∈ Bad, Real.exp (α * L) * (p : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ ∑ p ∈ Bad, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        have hb := (mem_closedLogLogPrimeBand_iff α β L p).mp
          (hP (Finset.mem_filter.mp hp).1)
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast hb.1.one_lt
        have hh := (Real.le_log_iff_exp_le (Real.log_pos hp1)).mp hb.2.1
        simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hBad (fun p _ _ =>
          div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      _ ≤ _ := hlogmass
  have hD : D ≤ 48 * Real.log T + 4 * (C + Real.log 4 / (2 * a)) +
      4 * Real.log 2 + 2 * Real.log 4 := by
    have hlog0 := Real.log_nonneg hcut.1
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp only [D]
    have he : 4 * (Real.log 4 / (2 * a)) = 2 * Real.log 4 / a := by ring
    rw [mul_add, he]
    linarith only [hlog0, hlog4]
  have he := herr T hlogT
  norm_num only [one_pow, one_mul] at he
  have hfinal : 4 * D / Real.exp (α * L) < ε := by
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hD (Real.exp_nonneg (α * L))) (show (0 : ℝ) ≤ 4 by norm_num)
    calc
      _ = 4 * (D / Real.exp (α * L)) := by ring
      _ ≤ _ := hh
      _ < ε := he
  exact hmass.trans (hfinal.le.trans (le_mul_of_one_le_right hε.le hL))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellLinearMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear harmonic mass in the full original bulk shell -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logPrimeBand_mass_quarter {C : ℝ} (hM : MertensEstimate C)
    (u : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u) :
    (1 / 4 : ℝ) ≤ ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
  have hw := (logPrimeBand_weight_bounds u C hu hM).1
  have hb : (∑ p ∈ logPrimeBand u, Real.log (p : ℝ) / p) ≤
      (2 * u) * ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (logPrimeBand_mem hp).2.2 (by positivity : 0 ≤ (p : ℝ)⁻¹)
  nlinarith

theorem whole_shell_geometric_mass {C : ℝ} (hM : MertensEstimate C)
    (u v : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u)
    (N : ℕ) (hN : (2 : ℝ) ^ N * u ≤ v) :
    (N : ℝ) / 4 ≤ ∑ p ∈ primeLogCellSet 1 0 u v, (p : ℝ)⁻¹ := by
  let B := fun i : Fin N => logPrimeBand ((2 : ℝ) ^ i.val * u)
  have hpow (i : ℕ) : u ≤ (2 : ℝ) ^ i * u :=
    le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  have hband (i : Fin N) : (1 / 4 : ℝ) ≤ ∑ p ∈ B i, (p : ℝ)⁻¹ :=
    logPrimeBand_mass_quarter hM _ (hu.trans (hpow _)) (he.trans (hpow _))
  have hdisj (i j : Fin N) (hij : i.val < j.val) : Disjoint (B i) (B j) := by
    apply Finset.disjoint_left.mpr
    intro p hi hj
    have hip := (logPrimeBand_mem hi).2.2
    have hjp := (logPrimeBand_mem hj).2.1
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hij)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    nlinarith
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) B := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h | h
    · exact hdisj i j h
    · exact (hdisj j i h).symm
  have hsub : (Finset.univ.biUnion B) ⊆ primeLogCellSet 1 0 u v := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hlo, hhi⟩ := logPrimeBand_mem hi
    apply mem_primeLogCellSet_iff.mpr
    refine ⟨hprime, by simp only [Nat.modEq_one], (hpow i.val).trans_lt hlo, ?_⟩
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt i.isLt)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    exact hhi.trans ((by nlinarith : 2 * ((2 : ℝ) ^ i.val * u) ≤ (2 : ℝ) ^ N * u).trans hN)
  calc
    (N : ℝ) / 4 = ∑ _i : Fin N, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ i : Fin N, ∑ p ∈ B i, (p : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hband i)
    _ = ∑ p ∈ Finset.univ.biUnion B, (p : ℝ)⁻¹ := (Finset.sum_biUnion hpair).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem whole_shell_linear_mass {C : ℝ} (hM : MertensEstimate C) :
    ∀ᶠ L : ℝ in atTop, L / 8000 ≤
      ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)), (p : ℝ)⁻¹ := by
  have ht := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [ht, eventually_ge_atTop (2000 : ℝ)] with L hlarge hL
  let N : ℕ := ⌊L / 1000⌋₊
  have hL0 : 0 ≤ L := by linarith
  have hNu : (N : ℝ) ≤ L / 1000 := Nat.floor_le (by positivity)
  have hNl : L / 1000 - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hp : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hN : (2 : ℝ) ^ N * Real.exp ((4 / 1000 : ℝ) * L) ≤
      Real.exp ((6 / 1000 : ℝ) * L) := by
    rw [hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N (α := ℝ))
    nlinarith
  have hmass := whole_shell_geometric_mass hM
    (Real.exp ((4 / 1000 : ℝ) * L)) (Real.exp ((6 / 1000 : ℝ) * L))
    (Real.one_le_exp (by positivity)) hlarge N hN
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellRetainedLinearMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear bulk mass after every allowed finite deletion -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem whole_shell_retained_linear_mass {C : ℝ} (hM : MertensEstimate C)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp (K * L) →
      L / 16000 ≤ ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D, (p : ℝ)⁻¹ := by
  filter_upwards [whole_shell_linear_mass hM,
    arithmetic_exponent_absorption 0 (4 / 1000) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (16000 : ℝ)] with L hmass hrate hL
  intro D hD
  let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
    (Real.exp ((6 / 1000 : ℝ) * L))
  have hL0 : 0 ≤ L := by linarith
  have hlo : ∀ p ∈ S, Real.exp (Real.exp ((4 / 1000 : ℝ) * L)) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hp, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp hp
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mp hlo).le
  have hdel : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ 1 := by
    apply (bulk_deleted_reciprocal_mass_le S D _ hlo).trans
    apply (mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply (Real.exp_le_exp.mpr (show K * L + -Real.exp ((4 / 1000 : ℝ) * L) ≤ 0 from ?_)).trans_eq
    · exact Real.exp_zero
    · simp only [zero_mul, Real.exp_zero, mul_one, one_mul, pow_one] at hrate
      nlinarith [mul_nonneg hK hL0]
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  change L / 16000 ≤ ∑ p ∈ S \ D, (p : ℝ)⁻¹
  change L / 8000 ≤ ∑ p ∈ S, (p : ℝ)⁻¹ at hmass
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailBroadPriorBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original broad bulk prior has balanced mass at least one half -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_broad_prior_balance
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ Y : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let Q := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      ∀ P : Finset ℕ, Q ⊆ P →
      (1 / 2 : ℝ) ≤ ∑ p : P,
        if (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3
        then primeSubsetPrior P Q p else 0 := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hlarge.and (eventual_tailCollisionCutoff N))
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  refine ⟨a, ha, ?_⟩
  filter_upwards [whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventual_tail_cell_window a C 0,
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop Y₀),
    (ht (4 / 1000) (by norm_num)).eventually
      (eventually_ge_atTop (128000 * tailCellLinearRate a C)),
    eventually_ge_atTop (1 : ℝ)] with L hmass hwindow hlargeY hratio hL
  intro Y hYlo hYhi hi hhi D hD Q P hQP
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  obtain ⟨hlarge, hcut⟩ := hY₀ Y (hlargeY.trans hYlo)
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let ambient := Nat.primesLE (tailCollisionCutoff Y)
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff Y) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff Y) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff Y) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff Y) hi).card : ℝ)) (negativeResidue p)
  have hprime (p) (hp : p ∈ ambient) := Nat.prime_of_mem_primesLE hp
  have hS (p) (hp : p ∈ ambient) : (S p).Nonempty := tailSupport_nonempty hA N p (hprime p hp).pos
  have hT (p) (hp : p ∈ ambient) : (T p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p) : (S p).card + (T p).card = p := tailSupport_card_add_complement A N p
  have hnon (p) (hp : p ∈ ambient) : 0 ≤ Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) :=
    mul_nonneg (Real.log_natCast_nonneg p) (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p).le)
  have hbudget : (∑ p ∈ ambient, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤
      tailDefectBudget a C Y := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff Y) hi a Y C ha
      hcut.1 hcut.2.1 hhi hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM.lower
  have hD0 : 0 ≤ tailDefectBudget a C Y := (Finset.sum_nonneg hnon).trans hbudget
  obtain ⟨_, hcellcut, _⟩ := hwindow Y (Real.exp ((1 / 100 : ℝ) * L)) hYlo hYhi le_rfl
    (Real.exp_le_exp.mpr (by linarith))
  have hQA : Q ⊆ ambient := by
    intro p hp
    obtain ⟨hpp, _, _, hupper⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    have hlog : Real.log (p : ℝ) ≤ Real.log (tailCollisionCutoff Y : ℝ) := by
      have hh : Real.exp ((6 / 1000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hQpos : (0 : ℝ) < tailCollisionCutoff Y := by
      exact_mod_cast (tailCollisionCutoff_bounds Y hcut.1 hcut.2.1).1
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast (Real.log_le_log_iff
      (by exact_mod_cast hpp.pos) hQpos).mp hlog, hpp⟩
  have hMQ : L / 16000 ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ := hmass D (by simpa only [one_mul] using hD)
  have hsmall : 4 * tailDefectBudget a C Y / Real.exp ((4 / 1000 : ℝ) * L) ≤
      (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 := by
    have hb := tailDefectBudget_linear a C L Y hL hYp hYhi
    have hK := tailCellLinearRate_nonneg a C
    have hprod := mul_le_mul_of_nonneg_right hratio (show 0 ≤ L by linarith)
    apply le_trans _ (show L / 32000 ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 by linarith)
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hbal := collision_harmonic_prior_balanced_mass P Q Q hQP (fun _ hp => hp) S T μ ν
    (tailDefectBudget a C Y) (Real.exp ((4 / 1000 : ℝ) * L)) (Real.exp_pos _)
    (fun p hp => hprime p (hQA hp)) (fun p hp => hS p (hQA hp)) (fun p hp => hT p (hQA hp))
    (fun p _ => hcard p)
    (fun p hp => (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1).2.2.1.le)
    ((Finset.sum_le_sum_of_subset_of_nonneg hQA (fun p hp _ => hnon p hp)).trans hbudget)
    ((by linarith : 0 < L / 16000).trans_le hMQ) hsmall
  have he (p : P) := tailDensityMask_balanced_iff A N p
  apply hbal.trans_eq
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (p : ℕ) ∈ Q
  · have hb := (he p (hprime p (hQA hp)).pos)
    simp only [hb, S]
  · have hz : primeSubsetPrior P Q p = 0 := by simp only [primeSubsetPrior, hp, ite_false, if_false]
    simp only [hz, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailSpectatorSupply
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator primes for the actual normalized tail transforms -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_tail_spectator_supply
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) (hc : 0 < c)
    (hsmall : (fun L => tailCharacterBandMass A N α β L) =o[atTop] (fun L : ℝ => L)) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      ∃ Q ⊆ P, (∑ p ∈ P, (p : ℝ)⁻¹) - c * L ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime,
            @MixedFourierBound p ⟨hp⟩
              (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  classical
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgrowth : Tendsto (fun L : ℝ => Real.exp (Real.exp (α * L))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα))
  filter_upwards [h.eventual_unbalanced_band_mass hsize hM hA hB N hN α β (c / 2)
    hα hβ (by positivity), eventual_bad_tail_character_mass A N α β δ (c / 2)
      hδ (by positivity) hsmall,
    hgrowth.eventually (eventually_ge_atTop (max 3 ((3 / ε) ^ 2)))]
    with L hbal hchar hlarge P hP
  let balanced := fun p => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
    residueDensity (tailDensityMask A N p) ≤ 2 / 3
  let Q := P.filter (fun p => balanced p ∧ tailCharacterBias A N p ≤ δ)
  have hmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + c * L := by
    have hpwise (p : ℕ) (_hp : p ∈ P) : (p : ℝ)⁻¹ ≤
        (if balanced p ∧ tailCharacterBias A N p ≤ δ then (p : ℝ)⁻¹ else 0) +
        (if ¬ balanced p then (p : ℝ)⁻¹ else 0) +
        (if δ < tailCharacterBias A N p then (p : ℝ)⁻¹ else 0) := by
      by_cases hb : balanced p <;> by_cases hd : tailCharacterBias A N p ≤ δ
      · simp only [hb, hd, and_self, ite_true, if_true, not_true_eq_false, ite_false, if_false, not_lt.mpr hd, add_zero]
        exact le_rfl
      · simp only [hb, hd, and_false, ite_false, if_false, not_true_eq_false, lt_of_not_ge hd, ite_true, if_true, zero_add]
        exact le_rfl
      · simp only [hb, hd, false_and, ite_false, if_false, not_false_eq_true, ite_true, if_true, not_lt.mpr hd, add_zero, zero_add]
        exact le_rfl
      · simp only [hb, hd, false_and, ite_false, if_false, not_false_eq_true, ite_true, if_true, lt_of_not_ge hd, zero_add]
        exact le_add_of_nonneg_right (by positivity)
    have hs := Finset.sum_le_sum hpwise
    simp only [Finset.sum_add_distrib] at hs
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter] at hs
    have hb := hbal P hP
    have hh := hchar P hP
    change (∑ p ∈ P.filter (fun p => ¬balanced p), (p : ℝ)⁻¹) ≤ _ at hb
    change (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) ≤ _ at hh
    change (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + _ + _ at hs
    linarith only [hs, hb, hh]
  refine ⟨Q, Finset.filter_subset _ _, by linarith only [hmass], ?_⟩
  intro p hp
  obtain ⟨hpP, hbp, hbias⟩ := Finset.mem_filter.mp hp
  have hband := (mem_closedLogLogPrimeBand_iff α β L p).mp (hP hpP)
  have hpbound := prime_of_loglog_lower p hband.1 _ hband.2.1
  have hp3 : 3 ≤ p := by exact_mod_cast (le_max_left _ _).trans (hlarge.trans hpbound)
  refine ⟨hp3, hbp.1, hbp.2, by simpa only [δ] using hbias, ?_⟩
  intro hpp
  let : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hsq : (3 / ε) ^ 2 ≤ (p : ℝ) := (le_max_right _ _).trans (hlarge.trans hpbound)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity : 0 ≤ 3 / ε)] at hsqrt
  have hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
    have hh := (div_le_iff₀ hε).mp hsqrt
    linarith only [hh]
  have htwobias : 2 * tailCharacterBias A N p ≤ ε := by
    dsimp only [δ] at hbias
    linarith only [hbias]
  intro χ a
  exact (tail_transform_mixed_bound A N p hp2 hbp.1 hbp.2 χ a).trans
    (max_le hprincipal htwobias)

/-- The spectator supply at any fixed admissible tail cutoff, with all
character smallness derived from the cited published inputs. -/
theorem EventuallyPrimeSumset.tail_spectator_supply
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε c : ℝ) (hα : 0 < α) (hαβ : α < β) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      ∃ Q ⊆ P, (∑ p ∈ P, (p : ℝ)⁻¹) - c * L ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime,
            @MixedFourierBound p ⟨hp⟩
              (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  obtain ⟨cψ, ψ, hcψ, hreal, hψ0, hψ1, hsupp⟩ := exists_positive_fourier_cutoff
  have hquad := closedQuadraticBandMass_isLittleO_of_halfopen A N
    (quadraticBandMass_isLittleO hBonami P0 H hSiegel sieve hsize hA hB h N hN C hM
      cψ 3 hcψ le_rfl ψ hreal hψ0 hψ1 hsupp)
  exact eventual_tail_spectator_supply hsize hM.lower h hA hB N hN α β ε c
    hα (hα.trans hαβ) hε hc
    (P0.all_character_decorrelation hsize hM hA hB h N hN hquad α β hα hαβ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailSpectatorPool
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A harmonic spectator pool for the original initial prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_spectator_pool
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ Q : Finset ℕ,
        Q ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, cutoff ≤ p ∧ 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime, @MixedFourierBound p ⟨hp⟩
            (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  have hscale := tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmass := hscale.eventually (whole_shell_retained_linear_mass hM 10 (by norm_num))
  have hsupply := h.tail_spectator_supply hBonami P0 H hSiegel sieve hsize hM hA hB N hN
    (4 / 10000) (6 / 10000) ε (1 / 320000) (by norm_num) (by norm_num) hε (by norm_num)
  have hgrowth := Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 4 / 10000 by norm_num)))
  filter_upwards [hmass, hsupply, hgrowth.eventually (eventually_ge_atTop (cutoff : ℝ))]
    with L hmass hsupply hlarge D hD
  simp only [id_eq, Function.comp_apply] at hmass hlarge
  let S := primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
    (Real.exp ((6 / 10000 : ℝ) * L))
  let P := S \ D
  have hmassP : L / 160000 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
    have hh := hmass D (by convert hD using 1; congr 1; ring)
    rw [show (1 / 10 : ℝ) * L / 16000 = L / 160000 by ring,
      show (4 / 1000 : ℝ) * ((1 / 10) * L) = (4 / 10000) * L by ring,
      show (6 / 1000 : ℝ) * ((1 / 10) * L) = (6 / 10000) * L by ring] at hh
    exact hh
  have hPband : P ⊆ closedLogLogPrimeBand (4 / 10000) (6 / 10000) L := by
    intro p hp
    obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    apply (mem_closedLogLogPrimeBand_iff _ _ _ _).mpr
    exact ⟨hpp, (Real.le_log_iff_exp_le (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hlo.le,
      (Real.log_le_iff_le_exp (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hhi⟩
  obtain ⟨Q, hQP, hmassQ, hgood⟩ := hsupply P hPband
  refine ⟨Q, hQP, by linarith only [hmassP, hmassQ], ?_⟩
  intro p hp
  obtain ⟨hpp, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQP hp)).1
  have hcutoff : (cutoff : ℝ) ≤ p := hlarge.trans
    ((Real.lt_log_iff_exp_lt (by exact_mod_cast hpp.pos)).mp hlo).le
  exact ⟨by exact_mod_cast hcutoff, hgood p hp⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailInitialBroadPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual harmonic priors and their original cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem harmonic_prior_prime_bound (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℝ) (ha : 0 < a) (hmass : a ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) (p : P) :
    (p : ℝ) * primeSubsetPrior P Q p ≤ a⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p p.property).ne_zero
  calc
    _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
    _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
    _ ≤ a⁻¹ := inv_anti₀ ha hmass

/-- The bulk center is chosen under its original harmonic prior and balanced
event. The spectator center uses the complete retained good-prime pool. Both
weights are kept as weights, before selecting any top or compensation cell. -/
theorem EventuallyPrimeSumset.initial_broad_prior_centers_oai
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k cutoff : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      let good := fun p : ℕ => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      ∃ Qd : Finset ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧ good p ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → Qb ⊆ P → Qd ⊆ P →
          (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
          (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
          (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
            (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
          ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊,
          ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊,
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qb) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cb x ∧
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qd) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cd x := by
  classical
  obtain ⟨_a, _ha, hbalance⟩ := h.tail_broad_prior_balance hsize hA hB N hN C hM
  filter_upwards [hbalance,
    h.tail_spectator_pool hBonami P0 H hSiegel sieve hsize hM hA hB N hN cutoff ε hε,
    whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbalance hpool hmass hL
  intro Y hYlo hYhi hi hhi D hD Qb m good
  obtain ⟨Qd, hQd, hMd, hgood⟩ := hpool D hD
  have hMb : L / 16000 ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹ :=
    hmass D (by simpa only [one_mul] using hD)
  have hsmall : L / 320000 ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹ := by linarith only [hMb, hL]
  have hpos : 0 < L / 320000 := by positivity
  refine ⟨Qd, hQd, hMd, ?_, ?_⟩
  · intro p hp
    exact ⟨(hgood p hp).1, ⟨(hgood p hp).2.2.1, (hgood p hp).2.2.2.1⟩,
      (hgood p hp).2.2.2.2.1⟩
  · intro P hP hQbP hQdP
    have hbm := primeSubsetPrior_mass P Qb hQbP (hpos.trans_le hsmall).ne'
    have hdm := primeSubsetPrior_mass P Qd hQdP (hpos.trans_le hMd).ne'
    refine ⟨hbm, hdm, fun p => ⟨harmonic_prior_prime_bound P Qb hP _ hpos hsmall p,
      harmonic_prior_prime_bound P Qd hP _ hpos hMd p⟩, ?_⟩
    have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hk) 4
      norm_num at hh
      exact hh
    have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by nlinarith only [hk4, hL]
    have hLm : L ≤ (m : ℝ) := by
      have hh := spectatorBulkCount_half k L hscale
      change (k : ℝ) ^ 4 * L / 2 ≤ (m : ℝ) at hh
      nlinarith only [hh, hk4, hL]
    have hm : 1 ≤ m := by exact_mod_cast hL.trans hLm
    have hn : m / 2 ≤ m := Nat.div_le_self _ _
    have hlogb (i : Fin (m / 2)) (p : P) (hp : primeSubsetPrior P Qb p ≠ 0) :
        Real.log (p : ℝ) ≤ Real.exp ((6 / 1000 : ℝ) * L) :=
      (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (primeSubsetPrior_support P Qb p hp)).1).2.2.2
    have hlogd (i : Fin (m / 2)) (p : P) (hp : primeSubsetPrior P Qd p ≠ 0) :
        Real.log (p : ℝ) ≤ Real.exp ((6 / 10000 : ℝ) * L) :=
      (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp
        (hQd (primeSubsetPrior_support P Qd p hp))).1).2.2.2
    have hb : (1 / 2 : ℝ) ≤ ∑ p : P, if good p then primeSubsetPrior P Qb p else 0 :=
      hbalance Y hYlo hYhi hi hhi D hD P hQbP
    have hd : (∑ p : P, if good p then primeSubsetPrior P Qd p else 0) = 1 := by
      calc
        _ = ∑ p : P, primeSubsetPrior P Qd p := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : primeSubsetPrior P Qd p = 0
          · simp only [hp, ite_self]
          · have hg := hgood p (primeSubsetPrior_support P Qd p hp)
            have hg' : good p := ⟨hg.2.2.1, hg.2.2.2.1⟩
            simp only [ite_eq_left hg']
        _ = 1 := hdm
    obtain ⟨cb, hcb, hbmass⟩ := exists_supported_prime_log_sum_center P hP (m / 2) m
      ((6 / 1000 : ℝ) * L) (fun _ => primeSubsetPrior P Qb) (fun _ p => good p)
      hm hn (by linarith only [hLm, hL]) hlogb (fun _ => by
        convert hb using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : good p <;> simp only [hp, ite_true, if_true, ite_false, if_false])
    obtain ⟨cd, hcd, hdmass⟩ := exists_supported_prime_log_sum_center P hP (m / 2) m
      ((6 / 10000 : ℝ) * L) (fun _ => primeSubsetPrior P Qd) (fun _ p => good p)
      hm hn (by linarith only [hLm, hL]) hlogd (fun _ => by
        convert ((show (1 / 2 : ℝ) ≤ 1 by norm_num).trans (le_of_eq hd.symm)) using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : good p <;> simp only [hp, ite_true, if_true, ite_false, if_false])
    exact ⟨cb, hcb, cd, hcd, hbmass, hdmass⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers_oai := @OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers_oai
