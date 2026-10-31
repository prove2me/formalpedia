-- Prove2me | solution 1 for OAI.Ostmann.fixed_pivot_full_original_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:17:40.840213+00:00
-- url     : https://prove2.me/submissions/f9735c23-af4d-4657-9498-3e292809434c

import Mathlib
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

theorem productPrior_cons {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (a : A) (x : Fin n → A) :
    productPrior μ (Fin.cons a x) = μ 0 a * productPrior (fun i => μ i.succ) x := by
  simp only [productPrior, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Integrate the first sample last, keeping the product prior on all remaining samples. -/
theorem sum_productPrior_cons {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, productPrior μ v * f v) =
      ∑ x : Fin n → A, productPrior (fun i => μ i.succ) x *
        ∑ a : A, μ 0 a * f (Fin.cons a x) := by
  have h := (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp
    (fun v => productPrior μ v * f v)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change productPrior μ (Fin.cons a x) * f (Fin.cons a x) = _
  rw [productPrior_cons]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPolynomialRoots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted polynomial root bounds for the arithmetic priors -/

namespace Ostmann

open scoped BigOperators

theorem weighted_univariate_roots_le {A : Type*} [Fintype A]
    (value : A → ℚ) (hinj : Function.Injective value) (P : Polynomial ℚ) (hP : P ≠ 0)
    (μ : A → ℝ) (α : ℝ) (hα : 0 ≤ α) (hμ : ∀ a, μ a ≤ α) :
    (∑ a : A, if P.eval (value a) = 0 then μ a else 0) ≤ (P.natDegree : ℝ) * α := by
  classical
  let S := Finset.univ.filter fun a => P.eval (value a) = 0
  have hc : S.card ≤ P.natDegree := by
    apply (Finset.card_le_card_of_injOn value (t := P.roots.toFinset) ?_ hinj.injOn).trans
      (P.roots.toFinset_card_le.trans P.card_roots')
    intro a ha
    change value a ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact (Finset.mem_filter.mp ha).2
  calc
    _ = ∑ a ∈ S, μ a := (Finset.sum_filter _ _).symm
    _ ≤ ∑ _a ∈ S, α := Finset.sum_le_sum fun a _ => hμ a
    _ = (S.card : ℝ) * α := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hα

/-- The arithmetic polynomial estimate for independent, possibly unequal finite priors. -/
theorem weighted_polynomial_roots_le {A : Type*} [Fintype A]
    (value : A → ℚ) (hinj : Function.Injective value) (α : ℝ) (hα : 0 ≤ α) :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℚ), P ≠ 0 →
      ∀ μ : Fin n → A → ℝ,
      (∀ i a, 0 ≤ μ i a) → (∀ i, ∑ a, μ i a = 1) → (∀ i a, μ i a ≤ α) →
      (∑ x : Fin n → A, productPrior μ x *
        (if MvPolynomial.eval (fun i => value (x i)) P = 0 then 1 else 0)) ≤
          (P.totalDegree : ℝ) * α := by
  classical
  intro n
  induction n with
  | zero =>
    intro P hP μ _ _ _
    have hc : P.coeff 0 ≠ 0 := by
      intro h
      apply hP
      rw [P.eq_C_of_isEmpty, h, map_zero]
    have he (x : Fin 0 → A) : MvPolynomial.eval (fun i => value (x i)) P ≠ 0 := by
      rw [P.eq_C_of_isEmpty, MvPolynomial.eval_C]
      exact hc
    simp only [he, ite_false, if_false, mul_zero, Finset.sum_const_zero]
    positivity
  | succ n ih =>
    intro P hP μ hμ hmass hmax
    let Q := MvPolynomial.finSuccEquiv ℚ n P
    let d := Q.natDegree
    let L := Q.leadingCoeff
    have hQ : Q ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hP
    have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have hdegree : L.totalDegree + d ≤ P.totalDegree := by
      exact MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P d (by
        change Q.coeff Q.natDegree ≠ 0
        exact hL)
    let μtail : Fin n → A → ℝ := fun i => μ i.succ
    let F (x : Fin n → A) :=
      if MvPolynomial.eval (fun i => value (x i)) L = 0 then (1 : ℝ) else 0
    have hinner (x : Fin n → A) :
        (∑ a : A, μ 0 a *
          (if MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = 0 then 1 else 0)) ≤
            F x + (d : ℝ) * α := by
      by_cases hx : MvPolynomial.eval (fun i => value (x i)) L = 0
      · have hsum : (∑ a : A, μ 0 a *
            (if MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = 0 then 1 else 0)) ≤ 1 := by
          apply le_trans ?_ (le_of_eq (hmass 0))
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact le_of_eq (mul_one _)
          · simpa only [mul_zero] using hμ 0 a
        exact hsum.trans (by
          simp only [F, hx, ite_true, if_true]
          exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hα))
      · let q : Polynomial ℚ := Q.map (MvPolynomial.eval (fun i => value (x i)))
        have hqd : q.natDegree = d :=
          Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hx
        have hq : q ≠ 0 := by
          intro hz
          apply hx
          change (MvPolynomial.eval (fun i => value (x i))) (Q.coeff d) = 0
          rw [← Polynomial.coeff_map, show Q.map (MvPolynomial.eval (fun i => value (x i))) = q from rfl,
            hz, Polynomial.coeff_zero]
        have he (a : A) : MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = q.eval (value a) := by
          have hc : (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) =
              Fin.cons (value a) (fun i => value (x i)) := by
            funext i
            refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
          rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
        simp_rw [he, mul_ite, mul_one, mul_zero]
        simpa only [F, hx, ite_false, if_false, zero_add, hqd] using
          weighted_univariate_roots_le value hinj q hq (μ 0) α hα (hmax 0)
    rw [sum_productPrior_cons]
    calc
      _ ≤ ∑ x : Fin n → A, productPrior μtail x * (F x + (d : ℝ) * α) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hinner x)
          (productPrior_nonneg μtail (fun i => hμ i.succ) x)
      _ = (∑ x : Fin n → A, productPrior μtail x * F x) + (d : ℝ) * α := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [productPrior_mass μtail (fun i => hmass i.succ), one_mul]
      _ ≤ (L.totalDegree : ℝ) * α + (d : ℝ) * α :=
        add_le_add (ih L hL μtail (fun i => hμ i.succ)
          (fun i => hmass i.succ) (fun i => hmax i.succ)) le_rfl
      _ ≤ _ := by
        rw [← add_mul, ← Nat.cast_add]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hα

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticCoincidences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accidental prime congruences in the arithmetic comparison

These finite estimates implement the two errors in §8: an exact polynomial
zero, and an independent sampled prime dividing a nonzero evaluation.
-/

namespace Ostmann

open scoped BigOperators

/-- A lower bound on the sizes of the sampled primes converts the logarithmic
prime-divisor budget into a bound on their number. -/
theorem prime_divisor_card_le (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ P, p.Prime) (B K : ℝ) (hB : 0 < B)
    (hsize : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hlog : Real.log (n : ℝ) ≤ K * B) :
    ((P.filter fun p => p ∣ n).card : ℝ) ≤ K := by
  classical
  have hsum := sum_log_prime_divisors_le (P.filter fun p => p ∣ n) hn
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hlower : ((P.filter fun p => p ∣ n).card : ℝ) * B ≤
      ∑ p ∈ P.filter (fun p => p ∣ n), Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ P.filter (fun p => p ∣ n), B := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp => hsize p (Finset.mem_filter.mp hp).1
  exact (mul_le_mul_iff_left₀ hB).mp (hlower.trans (hsum.trans hlog))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_IntegerPolynomialBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete integer evaluations in the arithmetic coincidence bounds -/

namespace Ostmann

open scoped BigOperators

theorem integerPolynomial_rational_eval {σ : Type*} (x : σ → ℤ)
    (F : MvPolynomial σ ℤ) :
    MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) F) =
      ((MvPolynomial.eval₂Hom (RingHom.id ℤ) x F : ℤ) : ℚ) := by
  rw [MvPolynomial.eval_map]
  symm
  simpa [Int.castRingHom] using
    (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F)

theorem integerPolynomial_rational_zero_iff {σ : Type*} (F : MvPolynomial σ ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) F = 0 ↔ F = 0 := by
  have hi : Function.Injective (MvPolynomial.map (Int.castRingHom ℚ) :
      MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  constructor
  · intro h
    apply hi
    simpa using h
  · intro h
    simp [h]

theorem integerPolynomial_rational_degree {σ : Type*} (F : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) F).totalDegree = F.totalDegree := by
  simp only [MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective F (show Function.Injective (Int.castRingHom ℚ) from
      Int.cast_injective)]

/-- A bound on an actual integer test gives the required independent-prime
cardinality bound without a separate polynomial-height hypothesis. -/
theorem int_prime_divisor_card_le (P : Finset ℕ) (z : ℤ) (hz : z ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime) (B H : ℝ) (hB : 0 < B)
    (hsize : ∀ p ∈ P, B ≤ Real.log (p : ℝ)) (hvalue : |(z : ℝ)| ≤ H) :
    ((P.filter fun p => p ∣ z.natAbs).card : ℝ) ≤ Real.log H / B := by
  have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hcast : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hlog : Real.log (z.natAbs : ℝ) ≤ Real.log H :=
    Real.log_le_log (by exact_mod_cast hzpos) (hcast ▸ hvalue)
  apply prime_divisor_card_le P hzpos hprime B (Real.log H / B) hB hsize
  simpa only [div_mul_cancel₀ _ hB.ne'] using hlog

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IndependentCoordinate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating an internal-prime representative from the other samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_insertNth {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (a : A) (x : Fin n → A) :
    productPrior μ (i.insertNth a x) = μ i a * productPrior (fun j => μ (i.succAbove j)) x := by
  unfold productPrior
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem sum_productPrior_insertNth {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, productPrior μ v * f v) =
      ∑ x : Fin n → A, productPrior (fun j => μ (i.succAbove j)) x *
        ∑ a : A, μ i a * f (i.insertNth a x) := by
  have h := (Fin.insertNthEquiv (fun _ : Fin (n + 1) => A) i).sum_comp
    (fun v => productPrior μ v * f v)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change productPrior μ (i.insertNth a x) * f (i.insertNth a x) = _
  rw [productPrior_insertNth]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_OmittedCoordinate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independence supplied by an absent compensation coordinate -/

namespace Ostmann

theorem polynomial_eval_insertNth_independent {A R : Type*} [CommRing R] {n : ℕ}
    (value : A → R) (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hi : i ∉ P.vars) (x : Fin n → A) (a b : A) :
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun j => value ((i.insertNth a x : Fin (n + 1) → A) j)) P =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun j => value ((i.insertNth b x : Fin (n + 1) → A) j)) P := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro j hj _
  have hji : j ≠ i := by
    intro heq
    exact hi (heq ▸ hj)
  have hjrange : j ∈ Set.range i.succAbove := by
    rw [Fin.range_succAbove]
    exact hji
  obtain ⟨q, rfl⟩ := hjrange
  simp only [Fin.insertNth_apply_succAbove]

theorem integerTestValue_insertNth_independent {A : Type*} {n : ℕ}
    (value : A → ℤ) (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hi : i ∉ P.vars) (x : Fin n → A) (a b : A) :
    integerTestValue value P (i.insertNth a x) = integerTestValue value P (i.insertNth b x) :=
  polynomial_eval_insertNth_independent value P i hi x a b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledPrimeCoincidence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coincidence bounds when the prime is one of the sampled coordinates

The omitted-variable condition proves the required independence inside one
joint product prior. No separate independent-prime hypothesis is assumed.
-/

namespace Ostmann

open scoped BigOperators Classical

private theorem sampled_prime_divisibility_le {A : Type*} [Fintype A]
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (ν : A → ℝ) (β V H : ℝ) (hβ : 0 ≤ β) (hV : 0 < V)
    (hν : ∀ a, ν a ≤ β) (hsize : ∀ a, ν a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (z : ℤ) (hz : z ≠ 0) (hvalue : |(z : ℝ)| ≤ H) :
    (∑ a, if prime a ∣ z.natAbs then ν a else 0) ≤ (Real.log H / V) * β := by
  let P : Finset ℕ := (Finset.univ.filter fun a => ν a ≠ 0).image prime
  let S : Finset A := Finset.univ.filter fun a => prime a ∣ z.natAbs ∧ ν a ≠ 0
  have hc : S.card ≤ (P.filter fun p => p ∣ z.natAbs).card := by
    apply Finset.card_le_card_of_injOn prime
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩, rfl⟩,
        (Finset.mem_filter.mp ha).2.1⟩
    · exact hinj.injOn
  have hc' := int_prime_divisor_card_le P z hz
    (fun p hp => by obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp; exact hprime a)
    V H hV
    (fun p hp => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hsize a (Finset.mem_filter.mp ha).2) hvalue
  calc
    _ = ∑ a ∈ S, ν a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hd : prime a ∣ z.natAbs <;> by_cases hn : ν a = 0 <;> simp [hd, hn]
    _ ≤ ∑ _a ∈ S, β := Finset.sum_le_sum fun a _ => hν a
    _ = (S.card : ℝ) * β := by simp
    _ ≤ ((P.filter fun p => p ∣ z.natAbs).card : ℝ) * β :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hβ
    _ ≤ _ := mul_le_mul_of_nonneg_right hc' hβ

theorem sampled_coordinate_prime_coincidence_le {A : Type*} [Fintype A] [Nonempty A]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : MvPolynomial (Fin (n + 1)) ℤ) (hF : F ≠ 0)
    (i : Fin (n + 1)) (hi : i ∉ F.vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ a, μ i a ≤ β)
    (hsize : ∀ a, μ i a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ x, |(integerTestValue value F x : ℝ)| ≤ H) :
    (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue value F x).natAbs then 1 else 0) ≤
      (F.totalDegree : ℝ) * α + (Real.log H / V) * β := by
  let a₀ : A := Classical.arbitrary A
  let z : (Fin n → A) → ℤ := fun x => integerTestValue value F (i.insertNth a₀ x)
  let W := productPrior (fun j => μ (i.succAbove j))
  have hz (x : Fin n → A) (a : A) : integerTestValue value F (i.insertNth a x) = z x :=
    integerTestValue_insertNth_independent value F i hi x a a₀
  have hinner (x : Fin n → A) :
      (∑ a, μ i a * if prime a ∣ (z x).natAbs then (1 : ℝ) else 0) ≤
        (if z x = 0 then 1 else 0) + (Real.log H / V) * β := by
    by_cases hx : z x = 0
    · simp only [hx, Int.natAbs_zero, dvd_zero, ite_true, if_true, mul_one, hmass]
      exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (Real.log_nonneg hH) hV.le) hβ)
    · simp only [hx, ite_false, if_false, zero_add]
      have he : (∑ a, μ i a * if prime a ∣ (z x).natAbs then (1 : ℝ) else 0) =
          ∑ a, if prime a ∣ (z x).natAbs then μ i a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      rw [he]
      exact sampled_prime_divisibility_le prime hpInj hprime (μ i) β V H hβ hV hpmax hsize
        (z x) hx (hvalue (i.insertNth a₀ x))
  have hzero : (∑ x, productPrior μ x * if integerTestValue value F x = 0 then (1 : ℝ) else 0) =
      ∑ x, W x * if z x = 0 then 1 else 0 := by
    rw [sum_productPrior_insertNth μ i]
    simp only [hz, ← Finset.sum_mul, hmass, one_mul, W]
  have hbound : (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue value F x).natAbs then 1 else 0) ≤
      (∑ x, W x * if z x = 0 then 1 else 0) + (Real.log H / V) * β := by
    rw [sum_productPrior_insertNth μ i]
    simp only [Fin.insertNth_apply_same, hz]
    calc
      _ ≤ ∑ x, W x * ((if z x = 0 then 1 else 0) + (Real.log H / V) * β) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hinner x)
          (productPrior_nonneg _ (fun j a => hμ (i.succAbove j) a) x)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [show (∑ x, W x) = 1 from productPrior_mass _ (fun j => hmass (i.succAbove j)), one_mul]
  rw [← hzero] at hbound
  have hroot := weighted_polynomial_roots_le (fun a => (value a : ℚ))
    (Int.cast_injective.comp hinj) α hα (MvPolynomial.map (Int.castRingHom ℚ) F)
    (fun hz => hF ((integerPolynomial_rational_zero_iff F).mp hz)) μ hμ hmass hmax
  simp only [integerPolynomial_rational_eval, Int.cast_eq_zero, integerPolynomial_rational_degree] at hroot
  change (∑ x, productPrior μ x * if integerTestValue value F x = 0 then (1 : ℝ) else 0) ≤
    (F.totalDegree : ℝ) * α at hroot
  exact hbound.trans (by linarith [hroot])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryPolynomialSpecialization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual cleared history polynomials with one prime left variable -/

namespace Ostmann

open scoped BigOperators Classical

theorem specializeHistoryVariable_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (x : ℝ) :
    (specializeHistoryVariable a i P).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P := by
  unfold specializeHistoryVariable
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom x).comp (Polynomial.C.comp (Int.castRingHom ℝ)) =
      Int.castRingHom ℝ := by ext z; simp
  rw [hc]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj, Function.update]

/-- Fixing all the other prime variables cannot increase the degree. The
bound comes from the original monomial support, so cancellation is harmless. -/
theorem specializeHistoryVariable_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) :
    (specializeHistoryVariable a i P).natDegree ≤ P.totalDegree := by
  let v : σ → Polynomial ℝ := fun j => if j = i then Polynomial.X else Polynomial.C (a j)
  have hv (j : σ) : (v j).natDegree ≤ 1 := by
    dsimp only [v]
    split_ifs <;> simp
  have hs : specializeHistoryVariable a i P =
      ∑ d ∈ P.support, specializeHistoryVariable a i (MvPolynomial.monomial d (P.coeff d)) := by
    rw [← map_sum]
    exact congrArg (specializeHistoryVariable a i) P.as_sum
  rw [hs]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hp : (d.prod fun j k => v j ^ k).natDegree ≤ d.sum (fun _ k => k) := by
    change (∏ j ∈ d.support, v j ^ d j).natDegree ≤ ∑ j ∈ d.support, d j
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    apply Finset.sum_le_sum
    intro j _
    exact (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d j) (hv j))).trans_eq (Nat.mul_one _)
  simp only [specializeHistoryVariable, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial, RingHom.comp_apply]
  change ((Polynomial.C ((P.coeff d : ℤ) : ℝ)) * d.prod (fun j k => v j ^ k)).natDegree ≤ _
  calc
    _ ≤ (Polynomial.C ((P.coeff d : ℤ) : ℝ)).natDegree + (d.prod fun j k => v j ^ k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d.sum (fun _ k => k) := by simpa only [Polynomial.natDegree_C, zero_add] using hp
    _ ≤ P.totalDegree := by simpa only [zero_add] using MvPolynomial.le_totalDegree hd

theorem normalizedHistoryPolynomial_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d x : ℝ) :
    (normalizedHistoryPolynomial P a i d).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d := by
  simp only [normalizedHistoryPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    specializeHistoryVariable_eval, div_eq_mul_inv]
  ring

theorem normalizedHistoryPolynomial_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d : ℝ) :
    (normalizedHistoryPolynomial P a i d).natDegree ≤ P.totalDegree := by
  exact (Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_C, zero_add] using specializeHistoryVariable_natDegree P a i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryResidueGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the residue gate for cleared integer history tests -/

namespace Ostmann

open scoped Classical

theorem smallDivisionTest_modEq (N N' d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (h : N ≡ N' [ZMOD d * s]) : smallDivisionTest N d s ↔ smallDivisionTest N' d s := by
  have hint : d ∣ N ↔ d ∣ N' := (h.of_dvd (dvd_mul_right d (s : ℤ))).dvd_iff
  have hquot (hN : d ∣ N) (hN' : d ∣ N') :
      (N / d : ℤ) ≡ N' / d [ZMOD s] := by
    apply Int.modEq_iff_dvd.mpr
    apply Int.dvd_of_mul_dvd_mul_left hd
    have he : d * (N' / d - N / d) = N' - N := by
      nlinarith only [Int.ediv_mul_cancel hN, Int.ediv_mul_cancel hN']
    rw [he]
    exact h.dvd
  constructor
  · rintro ⟨hN, hu⟩
    refine ⟨hint.mp hN, ?_⟩
    rwa [← (ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot hN (hint.mp hN))]
  · rintro ⟨hN', hu⟩
    refine ⟨hint.mpr hN', ?_⟩
    rwa [(ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot (hint.mpr hN') hN')]

theorem integerPolynomial_eval_modEq {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℤ) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    MvPolynomial.eval₂ (RingHom.id ℤ) a P ≡ MvPolynomial.eval₂ (RingHom.id ℤ) b P [ZMOD M] := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval₂_C, RingHom.id_apply]; exact .refl _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (h i)

theorem cleared_history_test_residue_invariant {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℕ) (d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (hdiv : d * s ∣ (M : ℤ)) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) a P) d s ↔
      smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) b P) d s :=
  smallDivisionTest_modEq _ _ d s hd ((integerPolynomial_eval_modEq P a b M h).of_dvd hdiv)

theorem clearedHistoryResidueGate_norm {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M] (z : ZMod M) :
    ‖clearedHistoryResidueGate P d s a i M z‖ ≤ 1 := by
  unfold clearedHistoryResidueGate
  split_ifs <;> norm_num

/-- The original conjunction of integer divisibility and frequency-unit
checks is exactly a bounded function of the surviving prime residue. -/
theorem clearedHistoryResidueGate_exact {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M]
    (hd : ∀ j, d j ≠ 0) (hdiv : ∀ j, d j * s j ∣ (M : ℤ)) (x : ℤ) :
    clearedHistoryResidueGate P d s a i M (x : ZMod M) =
      if ∀ j, smallDivisionTest
        (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (P j)) (d j) (s j)
        then 1 else 0 := by
  have hx : x ≡ ((x : ZMod M).val : ℤ) [ZMOD M] := by
    apply (ZMod.intCast_eq_intCast_iff x (((x : ZMod M).val : ℕ) : ℤ) M).mp
    rw [Int.cast_natCast]
    exact (ZMod.natCast_zmod_val (x : ZMod M)).symm
  have hcoord (k : σ) : Function.update a i x k ≡
      Function.update a i (((x : ZMod M).val : ℤ)) k [ZMOD M] := by
    by_cases hki : k = i
    · subst k; simpa [Function.update] using hx
    · simp [Function.update, hki]
  have ht : (∀ j, smallDivisionTest
      (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (P j)) (d j) (s j)) ↔
      (∀ j, smallDivisionTest
      (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i ((x : ZMod M).val : ℤ)) (P j)) (d j) (s j)) := by
    apply forall_congr'
    intro j
    exact cleared_history_test_residue_invariant (P j) _ _ M (d j) (s j) (hd j) (hdiv j) hcoord
  simp only [clearedHistoryResidueGate, ht]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZeroVariableHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing reconstructed-pivot coprimalities to actual prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem zeroHistoryVariable_absent {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) :
    i ∉ (zeroHistoryVariable i P).vars := by
  intro h
  obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_bind₁ _ P h
  by_cases hji : j = i <;> simp_all

theorem zeroHistoryVariable_eval {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) (x : σ → ℤ) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x (zeroHistoryVariable i P) =
      MvPolynomial.eval₂Hom (RingHom.id ℤ) (Function.update x i 0) P := by
  rw [zeroHistoryVariable, MvPolynomial.hom_bind₁, MvPolynomial.eval₂Hom_comp_C]
  congr 1
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, Function.update]

theorem zeroHistoryVariable_degree {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ) :
    (zeroHistoryVariable i P).totalDegree ≤ P.totalDegree := by
  let v : σ → MvPolynomial σ ℤ := fun j => if j = i then 0 else MvPolynomial.X j
  have hv (j : σ) : (v j).totalDegree ≤ 1 := by
    dsimp only [v]
    split_ifs <;> simp
  have hs : zeroHistoryVariable i P =
      ∑ d ∈ P.support, zeroHistoryVariable i (MvPolynomial.monomial d (P.coeff d)) := by
    rw [← map_sum]
    exact congrArg (zeroHistoryVariable i) P.as_sum
  rw [hs]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  have hp : (d.prod fun j k => v j ^ k).totalDegree ≤ d.sum (fun _ k => k) := by
    change (∏ j ∈ d.support, v j ^ d j).totalDegree ≤ ∑ j ∈ d.support, d j
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    exact ((MvPolynomial.totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left (d j) (hv j))).trans_eq (Nat.mul_one _)
  simp only [zeroHistoryVariable, MvPolynomial.bind₁_monomial]
  change (MvPolynomial.C (P.coeff d) * d.prod (fun j k => v j ^ k)).totalDegree ≤ _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using hp.trans (MvPolynomial.le_totalDegree hd))

/-- Divisibility by the sampled prime is unchanged on setting that variable
to zero in the cleared numerator. -/
theorem zeroHistoryVariable_dvd_iff {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ)
    (x : σ → ℤ) (p : ℕ) (hxi : x i = p) :
    p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x P).natAbs ↔
      p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x (zeroHistoryVariable i P)).natAbs := by
  rw [← Int.natCast_dvd, ← Int.natCast_dvd, zeroHistoryVariable_eval]
  apply Int.ModEq.dvd_iff
  apply integerPolynomial_eval_modEq
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, hxi]
    exact Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
  · simp [Function.update, hji]

theorem zeroHistoryVariable_identically_bad {σ : Type*} (i : σ) (P : MvPolynomial σ ℤ)
    (hP : zeroHistoryVariable i P = 0) (x : σ → ℤ) (p : ℕ) (hxi : x i = p) :
    p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x P).natAbs := by
  rw [zeroHistoryVariable_dvd_iff i P x p hxi, hP, map_zero, Int.natAbs_zero]
  exact dvd_zero p

theorem reconstructed_prime_coprimality_error {A : Type*} [Fintype A] [Nonempty A]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hP : zeroHistoryVariable i P ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ a, μ i a ≤ β)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ x, |(integerTestValue (fun a => (prime a : ℤ)) (zeroHistoryVariable i P) x : ℝ)| ≤ H) :
    (∑ x, productPrior μ x *
      if prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) P x).natAbs then 1 else 0) ≤
      (P.totalDegree : ℝ) * α + (Real.log H / V) * β := by
  have hinj : Function.Injective (fun a => (prime a : ℤ)) := by
    intro a b h
    exact hpInj (Int.natCast_inj.mp h)
  have he (x : Fin (n + 1) → A) :
      prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) P x).natAbs ↔
        prime (x i) ∣ (integerTestValue (fun a => (prime a : ℤ)) (zeroHistoryVariable i P) x).natAbs :=
    zeroHistoryVariable_dvd_iff i P (fun j => (prime (x j) : ℤ)) (prime (x i)) rfl
  simp_rw [he]
  apply (sampled_coordinate_prime_coincidence_le (fun a => (prime a : ℤ)) hinj prime hpInj hprime
    (zeroHistoryVariable i P) hP i (zeroHistoryVariable_absent i P)
    μ hμ hmass α β V H hα hβ hV hH hmax hpmax (fun a _ => hsize a) hvalue).trans
  have hd : ((zeroHistoryVariable i P).totalDegree : ℝ) ≤ P.totalDegree := by
    exact_mod_cast zeroHistoryVariable_degree i P
  exact add_le_add (mul_le_mul_of_nonneg_right hd hα) le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryCoprimalityRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual large-prime coprimalities of reconstructed histories -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_cleared_iff (p : ℕ) (hp : p.Prime) (N d y : ℤ)
    (hN : N = d * y) (hd : ¬p ∣ d.natAbs) :
    p ∣ N.natAbs ↔ p ∣ y.natAbs := by
  simp only [hN, Int.natAbs_mul, hp.dvd_mul, hd, false_or]

/-- The zero-polynomial branch has empty valid support, including when the
reconstructed integer is represented by a cleared numerator. -/
theorem zero_cleared_history_support {σ : Type*} (P : MvPolynomial σ ℤ)
    (i : σ) (hP : zeroHistoryVariable i P = 0) (x : σ → ℤ)
    (p : ℕ) (hp : p.Prime) (hxi : x i = p) (d y : ℤ)
    (hN : MvPolynomial.eval₂Hom (RingHom.id ℤ) x P = d * y)
    (hd : ¬p ∣ d.natAbs) : ¬p.Coprime y.natAbs := by
  rw [hp.coprime_iff_not_dvd, not_not]
  exact (prime_dvd_cleared_iff p hp _ d y hN hd).mp
    (zeroHistoryVariable_identically_bad i P hP x p hxi)

/-- A union bound for the complete finite list of numerator checks. These are
the original independent prime priors; no conditioning on history support is
introduced. -/
theorem history_coprimality_removal {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime)
    (hprime : ∀ a, (prime a).Prime)
    (N : I → MvPolynomial (Fin (n + 1)) ℤ) (coord : I → Fin (n + 1))
    (hN : ∀ j, zeroHistoryVariable (coord j) (N j) ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V : ℝ) (β H : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hH : ∀ j, 1 ≤ H j)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ j x, |(integerTestValue (fun a => (prime a : ℤ))
      (zeroHistoryVariable (coord j) (N j)) x : ℝ)| ≤ H j)
    (F : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) *
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (N j) x).natAbs then F x else 0)) -
      ∑ x, (productPrior μ x : ℂ) * F x‖ ≤
      B * ∑ j, (((N j).totalDegree : ℝ) * α + (Real.log (H j) / V) * β j) := by
  let bad (j : I) (x : Fin (n + 1) → A) : Prop :=
    prime (x (coord j)) ∣ (integerTestValue (fun a => (prime a : ℤ)) (N j) x).natAbs
  have hp (x : Fin (n + 1) → A) :
      ‖(if ∀ j, ¬bad j x then F x else 0) - F x‖ ≤
        B * ∑ j, if bad j x then (1 : ℝ) else 0 := by
    by_cases hx : ∀ j, ¬bad j x
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hx)), sub_self, norm_zero]
      exact mul_nonneg hB (Finset.sum_nonneg fun _ _ => by positivity)
    · obtain ⟨j, hj⟩ := not_forall.mp hx
      have hj' : bad j x := Classical.not_not.mp hj
      have hs : (1 : ℝ) ≤ ∑ j, if bad j x then 1 else 0 := by
        simpa only [hj', ite_true, if_true] using
          (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
            (show (0 : ℝ) ≤ if bad j x then 1 else 0 by positivity)) (Finset.mem_univ j))
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hx h)), zero_sub, norm_neg]
      exact (hF x).trans (by nlinarith)
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ x, ‖(productPrior μ x : ℂ) *
        ((if ∀ j, ¬bad j x then F x else 0) - F x)‖ := norm_sum_le _ _
    _ = ∑ x, productPrior μ x *
        ‖(if ∀ j, ¬bad j x then F x else 0) - F x‖ := by
      simp only [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (productPrior_nonneg μ hμ _)]
    _ ≤ ∑ x, productPrior μ x * (B * ∑ j, if bad j x then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (productPrior_nonneg μ hμ x)
    _ = B * ∑ j, ∑ x, productPrior μ x * if bad j x then (1 : ℝ) else 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      ext j
      congr 1
      ext x
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro j _
      exact reconstructed_prime_coprimality_error prime hpInj hprime (N j) (coord j) (hN j)
        μ hμ hmass α (β j) V (H j) hα (hβ j) hV (hH j) hmax (hpmax j) hsize (hvalue j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryPivot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

namespace ClearedHistoryValue

variable {σ : Type*}

theorem eval_variable (i : σ) (x : σ → ℚ) : (ofVariable i).eval x = x i := by
  simp only [eval, ofVariable, MvPolynomial.eval₂_X, Int.cast_one, div_one]

theorem eval_constant (a : ℤ) (x : σ → ℚ) : (constant a).eval x = a := by
  simp only [eval, constant, MvPolynomial.eval₂_C, Int.cast_one, div_one]
  rfl

theorem eval_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) (x : σ → ℚ) :
    (prod S f).eval x = ∏ i ∈ S, (f i).eval x := by
  simp only [eval, prod, MvPolynomial.eval₂_eq_eval_map, map_prod, Finset.prod_div_distrib]
  push_cast
  rfl

theorem eval_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℚ) :
    (pivot left right v w s hs).eval x = (v * right.eval x - w * left.eval x) / s := by
  have hL : (left.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr left.denominator_ne_zero
  have hR : (right.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr right.denominator_ne_zero
  have hS : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [eval, pivot, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

theorem degree_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) :
    (prod S f).numerator.totalDegree ≤ ∑ i ∈ S, (f i).numerator.totalDegree :=
  MvPolynomial.totalDegree_finsetProd _ _

theorem degree_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0) :
    (pivot left right v w s hs).numerator.totalDegree ≤
      max left.numerator.totalDegree right.numerator.totalDegree := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_right _ _)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact le_max_left _ _)

/-- Polynomial evaluation at an integer assignment is the numerator of the
actual rational value. The equality is useful on the integrality support. -/
theorem integer_value_cleared (F : ClearedHistoryValue σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator = F.denominator * y := by
  have hden : (F.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr F.denominator_ne_zero
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.numerator := by
    simpa [Int.castRingHom] using
      (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.numerator)
  apply Int.cast_injective (α := ℚ)
  rw [he, Int.cast_mul]
  have hh := (div_eq_iff hden).mp hy
  simpa only [mul_comm] using hh

theorem prime_coprime_integer_value (F : ClearedHistoryValue σ) (x : σ → ℤ)
    (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ F.denominator.natAbs) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    p.Coprime y.natAbs ↔ ¬p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator).natAbs := by
  rw [hp.coprime_iff_not_dvd, prime_dvd_cleared_iff p hp _ F.denominator y
    (F.integer_value_cleared x y hy) hd]

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree and value control survives clearing every history denominator -/

namespace Ostmann.ClearedHistoryValue

open scoped BigOperators Classical

variable {σ : Type*}

theorem bounded_variable (i : σ) (x : σ → ℝ) (H : ℝ) (hH : 1 ≤ H) (hx : |x i| ≤ H) :
    (ofVariable i).Bounded x H := by
  exact ⟨by simpa only [Bounded, ofVariable, MvPolynomial.eval₂_X] using hx,
    by simpa only [ofVariable, Int.cast_one, abs_one] using hH⟩

theorem bounded_constant (a : ℤ) (x : σ → ℝ) (H : ℝ) (hH : 1 ≤ H) (ha : |(a : ℝ)| ≤ H) :
    (constant a).Bounded x H := by
  exact ⟨by simpa only [constant, MvPolynomial.eval₂_C, Int.coe_castRingHom] using ha,
    by simpa only [constant, Int.cast_one, abs_one] using hH⟩

theorem bounded_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ)
    (x : σ → ℝ) (H : I → ℝ) (hf : ∀ i ∈ S, (f i).Bounded x (H i)) :
    (prod S f).Bounded x (∏ i ∈ S, H i) := by
  constructor
  · change |MvPolynomial.eval₂ (Int.castRingHom ℝ) x (∏ i ∈ S, (f i).numerator)| ≤ _
    change |(MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x) (∏ i ∈ S, (f i).numerator)| ≤ _
    rw [map_prod, Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => (hf i hi).1)
  · change |((∏ i ∈ S, (f i).denominator : ℤ) : ℝ)| ≤ _
    rw [Int.cast_prod, Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => (hf i hi).2)

/-- No coefficient-height estimate is assumed. The exact two products in the
substitution give a value bound that is valid at every real assignment. -/
theorem bounded_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℝ) (HL HR : ℝ) (hL : left.Bounded x HL) (hR : right.Bounded x HR) :
    (pivot left right v w s hs).Bounded x
      ((|(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)|) * HL * HR) := by
  have hHL : 0 ≤ HL := (abs_nonneg _).trans hL.2
  have hHR : 0 ≤ HR := (abs_nonneg _).trans hR.2
  have hprod : 0 ≤ HL * HR := mul_nonneg hHL hHR
  have hleft : |(v : ℝ) * (left.denominator : ℝ) *
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x right.numerator| ≤ |(v : ℝ)| * HL * HR := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)) hR.1
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hHL)
  have hright : |(w : ℝ) * (right.denominator : ℝ) *
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x left.numerator| ≤ |(w : ℝ)| * HR * HL := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR.2 (abs_nonneg _)) hL.1
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hHR)
  constructor
  · change |MvPolynomial.eval₂ (Int.castRingHom ℝ) x
      (MvPolynomial.C (v * left.denominator) * right.numerator -
        MvPolynomial.C (w * right.denominator) * left.numerator)| ≤ _
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      Int.coe_castRingHom, Int.cast_mul]
    apply (abs_sub _ _).trans
    nlinarith [mul_nonneg (abs_nonneg (s : ℝ)) hprod]
  · change |((s * left.denominator * right.denominator : ℤ) : ℝ)| ≤ _
    rw [Int.cast_mul, Int.cast_mul, abs_mul, abs_mul]
    have hd := mul_le_mul (mul_le_mul_of_nonneg_left hL.2 (abs_nonneg (s : ℝ))) hR.2
      (abs_nonneg (right.denominator : ℝ)) (mul_nonneg (abs_nonneg (s : ℝ)) hHL)
    nlinarith [mul_nonneg (abs_nonneg (v : ℝ)) hprod,
      mul_nonneg (abs_nonneg (w : ℝ)) hprod]

theorem zero_variable_value_bound (F : ClearedHistoryValue σ) (i : σ) (x : σ → ℤ) (H : ℝ)
    (hF : F.Bounded (fun j => ((Function.update x i 0) j : ℝ)) H) :
    |((MvPolynomial.eval₂Hom (RingHom.id ℤ) x
      (zeroHistoryVariable i F.numerator) : ℤ) : ℝ)| ≤ H := by
  rw [zeroHistoryVariable_eval]
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℤ) (Function.update x i 0)
    (Int.castRingHom ℝ) F.numerator
  have he' : ((MvPolynomial.eval₂Hom (RingHom.id ℤ) (Function.update x i 0) F.numerator : ℤ) : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun j => ((Function.update x i 0) j : ℝ)) F.numerator := by
    simpa [Int.castRingHom] using he
  rw [he']
  exact hF.1

end Ostmann.ClearedHistoryValue

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_WeightedPhaseExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

/-- Finite Abel summation bounds a weighted sum by the largest prefix sum
and the endpoint-plus-variation of the actual weights. -/
theorem weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ M) :
    ‖∑ j ∈ Finset.range N, w j * f j‖ ≤ discreteVariation w N * M := by
  have hab := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (N - 1) * ∑ j ∈ Finset.range N, f j‖ +
        ‖∑ j ∈ Finset.range (N - 1), (w (j + 1) - w j) * ∑ i ∈ Finset.range (j + 1), f i‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * M +
        ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖ * M := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.norm_mul]
        apply mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have hh := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [discreteVariation, ← Finset.sum_mul]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MonotoneWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of the smooth factors on monotone argument intervals -/

namespace Ostmann

open scoped BigOperators

theorem clipRealInterval_monotone (lo hi : ℝ) : Monotone (clipRealInterval lo hi) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Only bounds on the actual compact argument interval are needed. -/
theorem discreteVariation_comp_monotoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u (N - 1) - u 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u (j + 1) - u j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono j hj'))] using
          hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hw : u (N - 1) - u 0 ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).2
    have h0 := (hrange 0 (Nat.zero_le _)).1
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

theorem discreteVariation_comp_antitoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hanti : ∀ j < N - 1, u (j + 1) ≤ u j) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u 0 - u (N - 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u j - u (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti j hj'))] at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hw : u 0 - u (N - 1) ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).1
    have h0 := (hrange 0 (Nat.zero_le _)).2
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRootCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root cells used to split the long-variable weights

A cell records the side of each real root, retaining the roots themselves as
separate cells. Polynomial inequalities are constant on a cell; polynomial
arguments are monotone when the derivative roots are included among the cuts.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem rootCellCode_convex (S : Finset ℝ) {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) (hcode : rootCellCode S x = rootCellCode S z) :
    rootCellCode S y = rootCellCode S x := by
  funext r
  have he := congrFun hcode r
  change compare x r.val = compare z r.val at he
  change compare y r.val = compare x r.val
  rcases lt_trichotomy x r.val with hx | hx | hx
  · have hz : z < r.val := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hx))
    rw [compare_lt_iff_lt.mpr (hyz.trans_lt hz), compare_lt_iff_lt.mpr hx]
  · have hz : z = r.val := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hx))
    have hy : y = r.val := le_antisymm (hyz.trans_eq hz) (hx ▸ hxy)
    rw [compare_eq_iff_eq.mpr hy, compare_eq_iff_eq.mpr hx]
  · have hy : r.val < y := hx.trans_le hxy
    rw [compare_gt_iff_gt.mpr hy, compare_gt_iff_gt.mpr hx]

theorem rootCellCode_no_root_between (S : Finset ℝ) {x y : ℝ}
    (hxy : x < y) (hcode : rootCellCode S x = rootCellCode S y) :
    ∀ r ∈ S, r ∉ Set.Icc x y := by
  intro r hr hrange
  have he := congrFun hcode ⟨r, hr⟩
  change compare x r = compare y r at he
  rcases lt_or_eq_of_le hrange.1 with hxr | hxr
  · have hyr : y < r := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hxr))
    linarith [hrange.2]
  · have hyr : y = r := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hxr))
    linarith

/-- A continuous real function with no zeros on an interval has one sign. -/
theorem continuous_sign_on_interval (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b)) (hn : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo a b, f x ≤ 0) := by
  by_cases hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨x, hx, hfx⟩ := hpos
    intro y hy
    by_contra hfy
    have hfy' : 0 < f y := lt_of_not_ge hfy
    obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx hy hf
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) from ⟨hfx.le, hfy'.le⟩)
    exact hn z hz hfz

theorem polynomial_monotoneOn_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∈ S) {a b : ℝ}
    (hcode : rootCellCode S a = rootCellCode S b) :
    MonotoneOn P.eval (Set.Icc a b) ∨ AntitoneOn P.eval (Set.Icc a b) := by
  by_cases hd : P.derivative = 0
  · left
    have hp := Polynomial.eq_C_of_derivative_eq_zero hd
    intro x hx y hy hxy
    have hv (t : ℝ) : P.eval t = P.coeff 0 := by
      have hh := congrArg (fun Q : Polynomial ℝ => Q.eval t) hp
      simpa only [Polynomial.eval_C] using hh
    change P.eval x ≤ P.eval y
    rw [hv x, hv y]
  · have hn : ∀ x ∈ Set.Ioo a b, P.derivative.eval x ≠ 0 := by
      intro x hx hz
      have hm : x ∈ P.derivative.roots := (Polynomial.mem_roots hd).mpr hz
      exact rootCellCode_no_root_between S (hx.1.trans hx.2) hcode x (hroots x hm)
        ⟨hx.1.le, hx.2.le⟩
    rcases continuous_sign_on_interval P.derivative.eval a b
        P.derivative.continuous.continuousOn hn with hpos | hneg
    · left
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hpos x hx
    · right
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hneg x hx

/-- Even the crude count of all codes is exponential only in the total degree,
as required by the eventual exp(poly(m)) weight bound. Empty cells cost nothing. -/
theorem rootCellCode_card (S : Finset ℝ) :
    Fintype.card (S → Ordering) = 3 ^ S.card := by
  have ho : Fintype.card Ordering = 3 := by decide
  simp [ho]

theorem polynomialRootCuts_card {I : Type*} [Fintype I] (P : I → Polynomial ℝ) :
    (polynomialRootCuts P).card ≤ ∑ i, (P i).natDegree := by
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro i _
  exact (P i).roots.toFinset_card_le.trans (P i).card_roots'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ProductWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of the original smooth factors retain finite variation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_mul (f g : ℕ → ℂ) (B D : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hf : ∀ j, ‖f j‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ D) :
    discreteVariation (fun j => f j * g j) N ≤
      B * discreteVariation g N + D * discreteVariation f N := by
  have hend : ‖f (N - 1) * g (N - 1)‖ ≤ B * ‖g (N - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
  have hstep (j : ℕ) : ‖f (j + 1) * g (j + 1) - f j * g j‖ ≤
      B * ‖g (j + 1) - g j‖ + D * ‖f (j + 1) - f j‖ := by
    rw [show f (j + 1) * g (j + 1) - f j * g j =
      f (j + 1) * (g (j + 1) - g j) + (f (j + 1) - f j) * g j by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
    · simpa only [mul_comm D] using mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold discreteVariation
  nlinarith [mul_nonneg hD (norm_nonneg (f (N - 1)))]

theorem discreteVariation_prod (n : ℕ) (f : Fin n → ℕ → ℂ) (B V : Fin n → ℝ) (N : ℕ)
    (hB : ∀ i, 0 ≤ B i) (hV : ∀ i, 0 ≤ V i)
    (hf : ∀ i j, ‖f i j‖ ≤ B i) (hv : ∀ i, discreteVariation (f i) N ≤ V i) :
    discreteVariation (fun j => ∏ i, f i j) N ≤ ∏ i, (B i + V i) := by
  induction n with
  | zero => simp [discreteVariation]
  | succ n ih =>
    let g : ℕ → ℂ := fun j => ∏ i : Fin n, f i.succ j
    let C : ℝ := ∏ i : Fin n, B i.succ
    let E : ℝ := ∏ i : Fin n, (B i.succ + V i.succ)
    have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => hB i.succ
    have hg (j : ℕ) : ‖g j‖ ≤ C := by
      change ‖∏ i : Fin n, f i.succ j‖ ≤ C
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hf i.succ j)
    have hCE : C ≤ E := Finset.prod_le_prod (fun i _ => hB i.succ)
      (fun i _ => le_add_of_nonneg_right (hV i.succ))
    have hvg : discreteVariation g N ≤ E := ih (fun i => f i.succ) (fun i => B i.succ)
      (fun i => V i.succ) (fun i => hB i.succ) (fun i => hV i.succ)
      (fun i => hf i.succ) (fun i => hv i.succ)
    have hp : (fun j => ∏ i, f i j) = fun j => f 0 j * g j := by
      funext j
      exact Fin.prod_univ_succ _
    rw [hp, Fin.prod_univ_succ]
    apply (discreteVariation_mul (f 0) g (B 0) C N hC (hf 0) hg).trans
    calc
      _ ≤ B 0 * E + C * V 0 := add_le_add
        (mul_le_mul_of_nonneg_left hvg (hB 0)) (mul_le_mul_of_nonneg_left (hv 0) hC)
      _ ≤ B 0 * E + E * V 0 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hCE (hV 0))
      _ = _ := by change B 0 * E + E * V 0 = (B 0 + V 0) * E; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SubprobabilityTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy--Schwarz retains the internal distinctness restriction -/

namespace Ostmann

open scoped BigOperators

theorem subprobability_weighted_norm_sq_le {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1) (F : A → ℂ) :
    ‖∑ a, (μ a : ℂ) * F a‖ ^ 2 ≤ ∑ a, μ a * ‖F a‖ ^ 2 := by
  have hnorm : ‖∑ a, (μ a : ℂ) * F a‖ ≤ ∑ a, μ a * ‖F a‖ := by
    calc
      _ ≤ ∑ a, ‖(μ a : ℂ) * F a‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => Real.sqrt (μ a)) (fun a => Real.sqrt (μ a) * ‖F a‖)
  have hsq (a : A) : Real.sqrt (μ a) ^ 2 = μ a := Real.sq_sqrt (hμ a)
  have hprod (a : A) : Real.sqrt (μ a) * (Real.sqrt (μ a) * ‖F a‖) = μ a * ‖F a‖ := by
    rw [← mul_assoc, ← pow_two, hsq]
  simp only [mul_pow, hsq, hprod] at hCS
  have hpos : 0 ≤ ∑ a, μ a * ‖F a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hbound := hCS.trans (mul_le_of_le_one_left hpos hmass)
  have hn : 0 ≤ ∑ a, μ a * ‖F a‖ :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (norm_nonneg _))
  nlinarith [norm_nonneg (∑ a, (μ a : ℂ) * F a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrelationExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the two finite quadratic sums before the kernel average -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem finite_correlation_expansion {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (F : κ → ι → ℂ) (G : υ → ι → ℂ) :
    (∑ s ∈ S, (∑ w ∈ W, F w s) * conj (∑ v ∈ V, G v s)) =
      ∑ w ∈ W, ∑ v ∈ V, ∑ s ∈ S, F w s * conj (G v s) := by
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedCorrelationEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor sum after the large-kernel pair correlations -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_sum_energy_gram {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) =
      (∑ d ∈ D, ∑ e ∈ D, (c d * conj (c e)) *
        ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))).re := by
  have hpoint (s : ι) : μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2 =
      ((μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s))).re := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hpoint]
  rw [← Complex.re_sum]
  congr 1
  have hmul (s : ι) : (μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s)) =
      (∑ d ∈ D, (μ s : ℂ) * (c d * G d s)) * conj (∑ e ∈ D, c e * G e s) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hmul]
  rw [finite_correlation_expansion]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [map_mul]
  ring

theorem weighted_sum_energy_le_correlations {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) *
        ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ := by
  rw [weighted_sum_energy_gram, Complex.re_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm
    ((c d * conj (c e)) * ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy--Schwarz for the one-sided character interaction

The long-variable unary restriction is removed before extending its prior.
The diagonal short-variable pairs cost only their maximum atom.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem weighted_family_energy_le_atom {A B : Type*} [Fintype A] [Fintype B]
    (η : A → ℝ) (ν : B → ℝ) (V : B → ℂ) (F : B → A → ℂ)
    (α D ε : ℝ) (hα : 0 ≤ α) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hν : ∀ q, 0 ≤ ν q) (hmass : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hV : ∀ q, ‖V q‖ ≤ 1)
    (hcorr : ∀ q r, ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
      if q = r then D else ε) :
    (∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2) ≤ α * D + ε := by
  have hc (q : B) : ‖(ν q : ℂ) * V q‖ ≤ ν q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν q)]
    exact mul_le_of_le_one_right (hν q) (hV q)
  have hs := weighted_sum_energy_le_correlations Finset.univ Finset.univ η
    (fun q => (ν q : ℂ) * V q) F
  have hpair (q r : B) :
      (‖(ν q : ℂ) * V q‖ * ‖(ν r : ℂ) * V r‖) *
          ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
        D * (if q = r then ν q ^ 2 else 0) + ε * (ν q * ν r) := by
    calc
      _ ≤ (ν q * ν r) * (if q = r then D else ε) :=
        mul_le_mul (mul_le_mul (hc q) (hc r) (norm_nonneg _) (hν q)) (hcorr q r)
          (norm_nonneg _) (mul_nonneg (hν q) (hν r))
      _ ≤ _ := by
        split_ifs with h
        · subst r
          nlinarith [mul_nonneg hε (sq_nonneg (ν q))]
        · ring_nf
          exact le_refl _
  have hsum : (∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2) ≤
      D * (∑ q, ν q ^ 2) + ε * (∑ q, ν q) ^ 2 := by
    apply hs.trans
    calc
      _ ≤ (∑ q, ∑ r, (D * (if q = r then ν q ^ 2 else 0) + ε * (ν q * ν r))) :=
        Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun r _ => hpair q r))
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        have hd : (∑ q, ∑ r : B, D * (if q = r then ν q ^ 2 else 0)) = D * ∑ q, ν q ^ 2 := by
          simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
        have he : (∑ q, ∑ r, ε * (ν q * ν r)) = ε * (∑ q, ν q) ^ 2 := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          ring
        rw [hd, he]
  have hsquare : (∑ q, ν q ^ 2) ≤ α := by
    calc
      _ ≤ ∑ q, α * ν q := Finset.sum_le_sum (fun q _ => by
        nlinarith [mul_le_mul_of_nonneg_right (hatom q) (hν q)])
      _ = α * ∑ q, ν q := (Finset.mul_sum _ _ _).symm
      _ ≤ α := mul_le_of_le_one_right hα hmass
  have hmass0 : 0 ≤ ∑ q, ν q := Finset.sum_nonneg (fun q _ => hν q)
  have hmass2 : (∑ q, ν q) ^ 2 ≤ 1 := by nlinarith
  apply hsum.trans
  have hd := mul_le_mul_of_nonneg_left hsquare hD
  have he := mul_le_mul_of_nonneg_left hmass2 hε
  nlinarith

/-- Bounded unary factors on both variables are permitted. The extension
measure need not have mass one; its diagonal cost is recorded in D. -/
theorem one_sided_cauchy_bound {A B : Type*} [Fintype A] [Fintype B]
    (μ η : A → ℝ) (ν : B → ℝ) (U : A → ℂ) (V : B → ℂ) (F : B → A → ℂ)
    (C α D ε : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hμ : ∀ p, 0 ≤ μ p) (hmassμ : ∑ p, μ p ≤ 1)
    (hdom : ∀ p, μ p ≤ C * η p)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1)
    (hcorr : ∀ q r, ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
      if q = r then D else ε) :
    ‖∑ p, (μ p : ℂ) * (U p * ∑ q, (ν q : ℂ) * V q * F q p)‖ ^ 2 ≤
      C * (α * D + ε) := by
  apply (subprobability_weighted_norm_sq_le μ hμ hmassμ _).trans
  calc
    _ ≤ ∑ p, μ p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hU p)
    _ ≤ C * ∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hdom p) (sq_nonneg ‖∑ q, (ν q : ℂ) * V q * F q p‖)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_family_energy_le_atom η ν V F α D ε hα hD hε hν hmassν hatom hV hcorr) hC

theorem diagonal_correlation_envelope {A : Type*} [Fintype A]
    (η : A → ℝ) (F : A → ℂ) (H B : ℝ)
    (hη : ∀ p, 0 ≤ η p) (hmass : ∑ p, η p ≤ H) (hF : ∀ p, ‖F p‖ ≤ B) :
    ‖∑ p, (η p : ℂ) * (F p * conj (F p))‖ ≤ H * B ^ 2 := by
  calc
    _ ≤ ∑ p, ‖(η p : ℂ) * (F p * conj (F p))‖ := norm_sum_le _ _
    _ = ∑ p, η p * ‖F p‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hη p), pow_two]
    _ ≤ ∑ p, η p * B ^ 2 := Finset.sum_le_sum (fun p _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hF p) 2) (hη p))
    _ ≤ H * B ^ 2 := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hmass (sq_nonneg B)

/-- Only the off-diagonal character correlations require cancellation.
The diagonal estimate follows from the envelope and maximum short atom. -/
theorem one_sided_cauchy_of_offdiagonal {A B : Type*} [Fintype A] [Fintype B]
    (μ η : A → ℝ) (ν : B → ℝ) (U : A → ℂ) (V : B → ℂ) (F : B → A → ℂ)
    (C α H B₀ ε : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hμ : ∀ p, 0 ≤ μ p) (hmassμ : ∑ p, μ p ≤ 1)
    (hdom : ∀ p, μ p ≤ C * η p) (hη : ∀ p, 0 ≤ η p) (hmassη : ∑ p, η p ≤ H)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) (hF : ∀ q p, ‖F q p‖ ≤ B₀)
    (hoff : ∀ q r, q ≠ r →
      ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤ ε) :
    ‖∑ p, (μ p : ℂ) * (U p * ∑ q, (ν q : ℂ) * V q * F q p)‖ ^ 2 ≤
      C * (α * (H * B₀ ^ 2) + ε) := by
  apply one_sided_cauchy_bound μ η ν U V F C α (H * B₀ ^ 2) ε
    hC hα (mul_nonneg hH (sq_nonneg B₀)) hε hμ hmassμ hdom hν hmassν hatom hU hV
  intro q r
  by_cases hqr : q = r
  · subst r
    rw [ite_eq_left rfl]
    exact diagonal_correlation_envelope η (F q) H B₀ hη hmassη (hF q)
  · rw [ite_eq_right hqr]
    exact hoff q r hqr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionCharacterCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of distinct short characters on a fixed progression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem complex_periodic_blocks (f : ℕ → ℂ) (q : ℕ)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (k r : ℕ) : ∑ a ∈ Finset.range (k * q + r), f a = ∑ a ∈ Finset.range r, f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q + r = q + (k * q + r) by ring, Finset.sum_range_add, hz, zero_add]
    have hp' (a : ℕ) : f (q + a) = f a := by simpa only [Nat.add_comm] using hp a
    simpa only [hp'] using ih

theorem complex_periodic_zero_sum_bound (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (hb : ∀ a, ‖f a‖ ≤ 1) (N : ℕ) : ‖∑ a ∈ Finset.range N, f a‖ ≤ q := by
  have he : N / q * q + N % q = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  rw [← he, complex_periodic_blocks f q hp hz]
  calc
    _ ≤ ∑ a ∈ Finset.range (N % q), ‖f a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
    _ = (N % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le

theorem sum_range_residues {M : ℕ} [NeZero M] (F : ZMod M → ℂ) :
    (∑ a ∈ Finset.range M, F (a : ZMod M)) = ∑ a : ZMod M, F a := by
  have he := (ZMod.finEquiv M).toEquiv.sum_comp F
  have hval (a : Fin M) : (ZMod.finEquiv M).toEquiv a = (a.val : ZMod M) := by
    cases M with
    | zero => exact Fin.elim0 a
    | succ M =>
      apply Fin.ext
      exact (Nat.mod_eq_of_lt a.isLt).symm
  simp_rw [hval] at he
  exact (Fin.sum_univ_eq_sum_range (fun a => F (a : ZMod M)) M).symm.trans he

theorem characterPairValue_nat {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (a : ℕ) :
    characterPairValue hqr χ ψ (a : ZMod (q * r)) = χ (a : ZMod q) * conj (ψ (a : ZMod r)) := by
  simp only [characterPairValue, map_natCast, Prod.fst_natCast, Prod.snd_natCast]

theorem characterPairValue_sum_zero {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) : (∑ x : ZMod (q * r), characterPairValue hqr χ ψ x) = 0 := by
  have he := (ZMod.chineseRemainder hqr).toEquiv.sum_comp
    (fun x : ZMod q × ZMod r => χ x.1 * conj (ψ x.2))
  change (∑ x, characterPairValue hqr χ ψ x) = _ at he
  rw [he, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

theorem characterPairValue_norm_le_one {q r : ℕ} (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (x : ZMod (q * r)) :
    ‖characterPairValue hqr χ ψ x‖ ≤ 1 := by
  rw [characterPairValue, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (χ.norm_le_one _) (ψ.norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

/-- A step coprime to the two short moduli permutes the complete period.
This remains exact after fixing any residue class of the frequency modulus. -/
theorem character_progression_sum_bound {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (hM : M.Coprime (q * r)) :
    ‖∑ j ∈ Finset.range N, χ ((a + M * j : ℕ) : ZMod q) *
      conj (ψ ((a + M * j : ℕ) : ZMod r))‖ ≤ q * r := by
  let F := characterPairValue hqr χ ψ
  let f : ℕ → ℂ := fun j => F ((a + M * j : ℕ) : ZMod (q * r))
  have hp : Function.Periodic f (q * r) := by
    intro j
    simp only [f, Nat.cast_add, Nat.cast_mul]
    congr 1
    simp only [mul_add]
    have hz : ((q * r : ℕ) : ZMod (q * r)) = 0 := ZMod.natCast_self _
    simp only [Nat.cast_mul] at hz
    rw [hz, mul_zero, add_zero]
  have hz : (∑ j ∈ Finset.range (q * r), f j) = 0 := by
    have : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
    let e := (ZMod.unitOfCoprime M hM).mulLeft.trans (Equiv.addLeft (a : ZMod (q * r)))
    have he := e.sum_comp F
    have hev (z : ZMod (q * r)) : e z = (a : ZMod (q * r)) + (M : ZMod (q * r)) * z := by
      simp [e, Equiv.trans_apply, ZMod.coe_unitOfCoprime]
    simp_rw [hev] at he
    simp only [f, Nat.cast_add, Nat.cast_mul]
    have hs := sum_range_residues (M := q * r)
      (fun z => F ((a : ZMod (q * r)) + (M : ZMod (q * r)) * z))
    exact (hs.trans he).trans (characterPairValue_sum_zero hqr χ ψ hχ)
  have hb := complex_periodic_zero_sum_bound f (q * r)
    (Nat.mul_pos (NeZero.pos q) (NeZero.pos r)) hp hz
    (fun j => characterPairValue_norm_le_one hqr χ ψ _) N
  simpa only [f, F, characterPairValue_nat, Nat.cast_mul] using hb

theorem weighted_character_progression_bound {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (hM : M.Coprime (q * r)) (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j * (χ ((a + M * j : ℕ) : ZMod q) *
      conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤ discreteVariation w N * (q * r) := by
  apply weighted_sum_le_variation
  intro n _
  exact character_progression_sum_bound hqr χ ψ hχ a M n hM

/-- Sum the exact progression bounds over all interval/residue pieces.
The total variation budget includes the reciprocal-integer weight. -/
theorem character_interval_pieces_bound {I : Type*} [Fintype I]
    {q r : ℕ} [NeZero q] [NeZero r] (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hχ : χ ≠ 1)
    (a M N : I → ℕ) (hM : ∀ i, (M i).Coprime (q * r))
    (w : I → ℕ → ℂ) (V : ℝ) (hvar : ∑ i, discreteVariation (w i) (N i) ≤ V) :
    ‖∑ i, ∑ j ∈ Finset.range (N i), w i j *
      (χ ((a i + M i * j : ℕ) : ZMod q) * conj (ψ ((a i + M i * j : ℕ) : ZMod r)))‖ ≤
      V * (q * r) := by
  calc
    _ ≤ ∑ i, ‖∑ j ∈ Finset.range (N i), w i j *
      (χ ((a i + M i * j : ℕ) : ZMod q) * conj (ψ ((a i + M i * j : ℕ) : ZMod r)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, discreteVariation (w i) (N i) * (q * r) :=
      Finset.sum_le_sum (fun i _ => weighted_character_progression_bound hqr χ ψ hχ
        (a i) (M i) (N i) (hM i) (w i))
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hvar (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntegerProgressionPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue-progressions in a padded integer interval -/

namespace Ostmann

theorem integerProgressionPartition_value (Q K a : ℕ) (r : Fin Q) (j : Fin K) :
    a + ((integerProgressionPartition Q K).symm ⟨r, j⟩).val = (a + r.val) + Q * j.val := by
  change a + (r.val + Q * j.val) = _
  omega

/-- Reindexing the original integer sum introduces neither missing boundary
integers nor multiplicity. -/
theorem integerProgressionPartition_sum {M : Type*} [AddCommMonoid M]
    (Q K : ℕ) (f : Fin (K * Q) → M) :
    (∑ x, f x) = ∑ r : Fin Q, ∑ j : Fin K,
      f ((integerProgressionPartition Q K).symm ⟨r, j⟩) := by
  rw [← (integerProgressionPartition Q K).symm.sum_comp f, Fintype.sum_sigma]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteIntervalPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning convex finite fibers into exact integer interval pieces -/

namespace Ostmann

open scoped Classical

/-- A finite set of consecutive natural numbers is an interval whose length
is exactly its cardinality, including the empty case. -/
theorem finite_convex_set_interval (s : Finset ℕ)
    (hc : ∀ x ∈ s, ∀ y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s) :
    ∃ a : ℕ, s = Finset.Ico a (a + s.card) := by
  by_cases hs : s.Nonempty
  · have he : s = Finset.Icc (s.min' hs) (s.max' hs) := by
      ext z
      constructor
      · intro hz
        exact Finset.mem_Icc.mpr ⟨s.min'_le z hz, s.le_max' z hz⟩
      · intro hz
        obtain ⟨hx, hy⟩ := Finset.mem_Icc.mp hz
        exact hc _ (s.min'_mem hs) _ (s.max'_mem hs) z hx hy
    have hcard : s.card = s.max' hs + 1 - s.min' hs := by
      conv_lhs => rw [he]
      exact Nat.card_Icc _ _
    refine ⟨s.min' hs, ?_⟩
    ext z
    conv_lhs => rw [he]
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    have hmm := s.min'_le_max' hs
    omega
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    exact ⟨0, by simp [he]⟩

/-- The fibers of a code on an integer interval become consecutive subintervals.
This provides the exact bijection needed by the character-sum partition. -/
theorem exists_finite_interval_partition {I : Type*} (N : ℕ) (code : ℕ → I)
    (hc : ∀ x y z, x < N → y < N → x ≤ z → z ≤ y →
      code x = code y → code z = code x) :
    ∃ (a K : I → ℕ) (e : Fin N ≃ Σ i, Fin (K i)),
      (∀ i (j : Fin (K i)), (e.symm ⟨i, j⟩).val = a i + j.val) ∧
      (∀ i (j : Fin (K i)), code (a i + j.val) = i) := by
  let fiber (i : I) : Finset ℕ := (Finset.range N).filter (fun n => code n = i)
  have hi (i : I) : ∃ a : ℕ, fiber i = Finset.Ico a (a + (fiber i).card) := by
    apply finite_convex_set_interval
    intro x hx y hy z hxz hzy
    obtain ⟨hxN, hxi⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyN, hyi⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hzy (Finset.mem_range.mp hyN)), ?_⟩
    exact (hc x y z (Finset.mem_range.mp hxN) (Finset.mem_range.mp hyN)
      hxz hzy (hxi.trans hyi.symm)).trans hxi
  choose a ha using hi
  let K : I → ℕ := fun i => (fiber i).card
  have hm (i : I) (n : ℕ) : n < N ∧ code n = i ↔ a i ≤ n ∧ n < a i + K i := by
    simpa only [fiber, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] using
      Iff.of_eq (congrArg (fun s : Finset ℕ => n ∈ s) (ha i))
  have hstart (n : Fin N) : a (code n.val) ≤ n.val :=
    ((hm (code n.val) n.val).mp ⟨n.isLt, rfl⟩).1
  let e : Fin N ≃ Σ i, Fin (K i) := {
    toFun := fun n => ⟨code n.val, ⟨n.val - a (code n.val), by
      have h := ((hm (code n.val) n.val).mp ⟨n.isLt, rfl⟩).2
      have ha := hstart n
      omega⟩⟩
    invFun := fun z => ⟨a z.1 + z.2.val, ((hm z.1 _).mpr ⟨by omega, by omega⟩).1⟩
    left_inv := by
      intro n
      apply Fin.ext
      exact Nat.add_sub_of_le (hstart n)
    right_inv := by
      rintro ⟨i, j⟩
      have hci : code (a i + j.val) = i :=
        ((hm i _).mpr ⟨by omega, by omega⟩).2
      apply Sigma.ext hci
      apply (Fin.heq_ext_iff (congrArg K hci)).mpr
      simp only [hci, Nat.add_sub_cancel_left]
  }
  refine ⟨a, K, e, ?_, ?_⟩
  · intro i j
    rfl
  · intro i j
    exact ((hm i _).mpr ⟨by omega, by omega⟩).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCellVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual interval pieces and smooth polynomial weights -/

namespace Ostmann

open scoped BigOperators Classical

/-- Root comparisons give an exact interval decomposition of any increasing
integer sampling grid. Equality endpoints retain their own code. -/
theorem exists_rootCell_partition (S : Finset ℝ) (N : ℕ) (u : ℕ → ℝ)
    (hu : Monotone u) :
    ∃ (a K : (S → Ordering) → ℕ) (e : Fin N ≃ Σ i, Fin (K i)),
      (∀ i (j : Fin (K i)), (e.symm ⟨i, j⟩).val = a i + j.val) ∧
      (∀ i (j : Fin (K i)), rootCellCode S (u (a i + j.val)) = i) := by
  apply exists_finite_interval_partition N (fun j => rootCellCode S (u j))
  intro x y z _ _ hxz hzy he
  exact rootCellCode_convex S (hu hxz) (hu hzy) he

/-- On a root cell, polynomial inequality supports really are constant. -/
theorem polynomial_nonneg_iff_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.roots, r ∈ S) {x y : ℝ}
    (hcode : rootCellCode S x = rootCellCode S y) :
    0 ≤ P.eval x ↔ 0 ≤ P.eval y := by
  by_cases hp : P = 0
  · simp [hp]
  have hordered (a b : ℝ) (hab : a < b)
      (hc : rootCellCode S a = rootCellCode S b) : 0 ≤ P.eval a ↔ 0 ≤ P.eval b := by
    have hn (z : ℝ) (hz : z ∈ Set.Icc a b) : P.eval z ≠ 0 := by
      intro he
      have hm : z ∈ P.roots := (Polynomial.mem_roots hp).mpr he
      exact rootCellCode_no_root_between S hab hc z (hroots z hm) hz
    constructor
    · intro ha
      by_contra hb
      have hb' : P.eval b < 0 := lt_of_not_ge hb
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval b) (P.eval a) from ⟨hb'.le, ha⟩)
      exact hn z hz he
    · intro hb
      by_contra ha
      have ha' : P.eval a < 0 := lt_of_not_ge ha
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval a) (P.eval b) from ⟨ha'.le, hb⟩)
      exact hn z hz he
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hordered x y hxy hcode
  · rfl
  · exact (hordered y x hyx hcode.symm).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCellSupports
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp polynomial support conditions are functions of the root cell -/

namespace Ostmann

open scoped Classical

theorem polynomialSupportCode_of_rootCell {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (P i).roots → r ∈ S) {x y : ℝ}
    (hxy : rootCellCode S x = rootCellCode S y) :
    polynomialSupportCode P x = polynomialSupportCode P y := by
  funext i
  exact congrArg (fun p : Prop => decide p)
    (propext (polynomial_nonneg_iff_of_root_cell (P i) S (hroots i) hxy))

theorem polynomialRootCellFlag_norm {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (keep : (I → Bool) → Bool) (c : S → Ordering) :
    ‖polynomialRootCellFlag P S keep c‖ ≤ 1 := by
  unfold polynomialRootCellFlag
  split_ifs <;> norm_num

theorem polynomialRootCellFlag_value {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (P i).roots → r ∈ S)
    (keep : (I → Bool) → Bool) (x : ℝ) :
    polynomialRootCellFlag P S keep (rootCellCode S x) =
      if keep (polynomialSupportCode P x) = true then 1 else 0 := by
  have he : (∃ y : ℝ, rootCellCode S y = rootCellCode S x ∧
      keep (polynomialSupportCode P y) = true) ↔ keep (polynomialSupportCode P x) = true := by
    constructor
    · rintro ⟨y, hy, hk⟩
      rw [polynomialSupportCode_of_rootCell P S hroots hy] at hk
      exact hk
    · intro hk
      exact ⟨x, rfl, hk⟩
  simp only [polynomialRootCellFlag, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ReciprocalProgressionVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original reciprocal-integer weight in partial summation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_nonneg (f : ℕ → ℂ) (N : ℕ) : 0 ≤ discreteVariation f N := by
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem discreteVariation_ofReal_antitone (u : ℕ → ℝ) (N : ℕ)
    (hu : ∀ j, 0 ≤ u j) (hanti : Antitone u) :
    discreteVariation (fun j => (u j : ℂ)) N = u 0 := by
  have hs (j : ℕ) : ‖(u (j + 1) : ℂ) - (u j : ℂ)‖ = u j - u (j + 1) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hanti (by omega)))]
    ring
  unfold discreteVariation
  simp only [Complex.norm_real, Real.norm_of_nonneg (hu _), hs]
  rw [Finset.sum_range_sub']
  ring

theorem reciprocal_progression_antitone (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) :
    Antitone (fun j : ℕ => (b + d * j)⁻¹) := by
  intro i j hij
  have hi : 0 < b + d * i := lt_of_lt_of_le hb (le_add_of_nonneg_right (mul_nonneg hd (Nat.cast_nonneg _)))
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hj : b + d * i ≤ b + d * j :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hijR hd)
  exact inv_anti₀ hi hj

theorem reciprocal_progression_variation (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (N : ℕ) :
    discreteVariation (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹)) N = b⁻¹ := by
  simpa using discreteVariation_ofReal_antitone (fun j => (b + d * j)⁻¹) N
    (fun j => inv_nonneg.mpr (by positivity)) (reciprocal_progression_antitone b d hb hd)

theorem reciprocal_progression_norm (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (j : ℕ) :
    ‖Complex.ofReal ((b + d * (j : ℝ))⁻¹)‖ ≤ b⁻¹ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa using reciprocal_progression_antitone b d hb hd (Nat.zero_le j)

/-- Multiplying by 1/n costs only twice the endpoint bound divided by the
left endpoint, with no dependence on the progression length. -/
theorem reciprocal_progression_product_variation (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d)
    (f : ℕ → ℂ) (N : ℕ) (B V : ℝ) (hBV : B ≤ V)
    (hf : ∀ j, ‖f j‖ ≤ B) (hv : discreteVariation f N ≤ V) :
    discreteVariation (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹) * f j) N ≤ 2 * b⁻¹ * V := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0)
  have ht := discreteVariation_mul (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹)) f b⁻¹ B N hB
    (reciprocal_progression_norm b d hb hd) hf
  rw [reciprocal_progression_variation b d hb hd] at ht
  apply ht.trans
  nlinarith [mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hb.le),
    mul_le_mul_of_nonneg_right hBV (inv_nonneg.mpr hb.le)]

theorem discreteVariation_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun j => c * f j) N = ‖c‖ * discreteVariation f N := by
  simp only [discreteVariation, ← mul_sub, norm_mul, Finset.mul_sum, mul_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPolynomialWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the smooth factors appearing in a history

Profiles are clipped to their prescribed argument ranges. This leaves their
values unchanged on the retained range and requires no continuity of the sharp
range indicator; those indicators are separate functions of the root cell.
-/

namespace Ostmann

open scoped BigOperators

theorem ClippedPolynomialFactor.variation (f : ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ r, r ∈ f.polynomial.derivative.roots → r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1))) :
    discreteVariation (fun j => f.value (u j)) N ≤ f.bound + f.lip * (f.hi - f.lo) := by
  let v : ℕ → ℝ := fun j => clipRealInterval f.lo f.hi (f.polynomial.eval (u j))
  have hr (j : ℕ) (_hj : j ≤ N - 1) : v j ∈ Set.Icc f.lo f.hi :=
    clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi
  have hu' (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  change discreteVariation (fun j => f.profile (v j)) N ≤ _
  rcases polynomial_monotoneOn_of_root_cell f.polynomial S hroots hcode with hm | hm
  · apply discreteVariation_comp_monotoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))
  · apply discreteVariation_comp_antitoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))

theorem smoothPolynomialBudget_nonneg {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    0 ≤ smoothPolynomialBudget F := by
  apply Finset.prod_nonneg
  intro i _
  exact add_nonneg (mul_nonneg (by norm_num) (F i).bound_nonneg)
    (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))

theorem smoothPolynomialWeight_variation {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1))) :
    discreteVariation (fun j => smoothPolynomialWeight F (u j)) N ≤ smoothPolynomialBudget F := by
  have hV (i : Fin n) : 0 ≤ (F i).bound + (F i).lip * ((F i).hi - (F i).lo) :=
    add_nonneg (F i).bound_nonneg
      (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))
  have ht := discreteVariation_prod n (fun i j => (F i).value (u j))
    (fun i => (F i).bound) (fun i => (F i).bound + (F i).lip * ((F i).hi - (F i).lo)) N
    (fun i => (F i).bound_nonneg) hV (fun i j => (F i).norm_value (u j))
    (fun i => (F i).variation S (hroots i) u hu N hcode)
  change discreteVariation (fun j => ∏ i, (F i).value (u j)) N ≤ _
  apply ht.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- This is the weight used after the long-prime prior is extended to integers. -/
theorem smoothPolynomial_reciprocal_variation {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (N : ℕ)
    (hcode : rootCellCode S b = rootCellCode S (b + d * ((N - 1 : ℕ) : ℝ))) :
    discreteVariation (fun j => Complex.ofReal ((b + d * j)⁻¹) *
      smoothPolynomialWeight F (b + d * j)) N ≤ 2 * b⁻¹ * smoothPolynomialBudget F := by
  have hu : Monotone (fun j : ℕ => b + d * j) := by
    intro i j hij
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hijR hd)
  have hc : rootCellCode S (b + d * (0 : ℕ)) = rootCellCode S (b + d * (N - 1 : ℕ)) := by
    simpa only [Nat.cast_zero, mul_zero, add_zero] using hcode
  exact reciprocal_progression_product_variation b d hb hd _ N
    (smoothPolynomialBudget F) (smoothPolynomialBudget F) le_rfl
    (fun j => smoothPolynomialWeight_norm F _) (smoothPolynomialWeight_variation F S hroots _ hu N hc)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character cancellation for the actual smooth polynomial weight

The interval and variation hypotheses are constructed from the polynomial roots.
Only a bounded function of the root cell is retained for the regular supports.
Irregular unary prime restrictions are handled separately by Cauchy--Schwarz.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- One allowed residue progression. The factor 1/a is the long-variable
saving; summing over the residue classes gives the frequency-modulus loss. -/
theorem polynomial_weighted_character_progression {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (ha : 0 < a) (hM : M.Coprime (q * r))
    {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i x, x ∈ (F i).polynomial.derivative.roots → x ∈ S)
    (flag : (S → Ordering) → ℂ) (hflag : ∀ i, ‖flag i‖ ≤ 1) :
    ‖∑ j ∈ Finset.range N,
      flag (rootCellCode S ((a + M * j : ℕ) : ℝ)) *
      (Complex.ofReal (((a + M * j : ℕ) : ℝ)⁻¹) *
        smoothPolynomialWeight F ((a + M * j : ℕ) : ℝ)) *
      (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤
      (3 ^ S.card : ℕ) * (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r) := by
  let u : ℕ → ℝ := fun j => ((a + M * j : ℕ) : ℝ)
  have hu : Monotone u := by
    intro i j hij
    change ((a + M * i : ℕ) : ℝ) ≤ ((a + M * j : ℕ) : ℝ)
    exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left M hij) a
  obtain ⟨starts, K, e, he, hcode⟩ := exists_rootCell_partition S N u hu
  let b : (S → Ordering) → ℕ := fun i => a + M * starts i
  have hval (i : S → Ordering) (j : ℕ) : a + M * (starts i + j) = b i + M * j := by
    dsimp [b]
    ring
  have huval (i : S → Ordering) (j : ℕ) : u (starts i + j) = (b i : ℝ) + M * j := by
    change ((a + M * (starts i + j) : ℕ) : ℝ) = _
    rw [hval]
    push_cast
    rfl
  let w : (S → Ordering) → ℕ → ℂ := fun i j =>
    if K i = 0 then 0 else flag i *
      (Complex.ofReal (((b i : ℝ) + M * j)⁻¹) *
        smoothPolynomialWeight F ((b i : ℝ) + M * j))
  have hvar (i : S → Ordering) :
      discreteVariation (w i) (K i) ≤ 2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F := by
    by_cases hK : K i = 0
    · simp only [w, hK, ite_true, if_true, discreteVariation, norm_zero,
        zero_add]
      have hbudget := smoothPolynomialBudget_nonneg F
      positivity
    · have hKi : 0 < K i := Nat.pos_of_ne_zero hK
      have hc0 := hcode i ⟨0, hKi⟩
      have hc1 := hcode i ⟨K i - 1, by omega⟩
      have hc : rootCellCode S (b i : ℝ) =
          rootCellCode S ((b i : ℝ) + M * ((K i - 1 : ℕ) : ℝ)) := by
        have hc := hc0.trans hc1.symm
        simpa only [huval, Nat.cast_zero, mul_zero, add_zero] using hc
      have hba : (a : ℝ) ≤ b i := by
        change (a : ℝ) ≤ ((a + M * starts i : ℕ) : ℝ)
        exact_mod_cast Nat.le_add_right a (M * starts i)
      have hb : 0 < (b i : ℝ) := lt_of_lt_of_le (by exact_mod_cast ha) hba
      have hv := smoothPolynomial_reciprocal_variation F S hroots (b i) M hb
        (Nat.cast_nonneg M) (K i) hc
      have hvar0 := discreteVariation_nonneg
        (fun j => Complex.ofReal (((b i : ℝ) + M * j)⁻¹) *
          smoothPolynomialWeight F ((b i : ℝ) + M * j)) (K i)
      simp only [w, ite_eq_right hK]
      rw [discreteVariation_const_mul]
      calc
        _ ≤ 1 * (2 * (b i : ℝ)⁻¹ * smoothPolynomialBudget F) :=
          mul_le_mul (hflag i) hv hvar0 (by norm_num)
        _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (inv_anti₀ (by exact_mod_cast ha) hba) (by norm_num))
            (smoothPolynomialBudget_nonneg F)
  have hsum : (∑ j ∈ Finset.range N,
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))) =
      ∑ i : S → Ordering, ∑ j ∈ Finset.range (K i), w i j *
        (χ ((b i + M * j : ℕ) : ZMod q) * conj (ψ ((b i + M * j : ℕ) : ZMod r))) := by
    let f : ℕ → ℂ := fun j =>
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))
    change (∑ j ∈ Finset.range N, f j) = _
    rw [← Fin.sum_univ_eq_sum_range f N,
      ← e.symm.sum_comp (fun j : Fin N => f j.val), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hp (j : Fin (K i)) : f (e.symm ⟨i, j⟩).val = w i j.val *
        (χ ((b i + M * j.val : ℕ) : ZMod q) * conj (ψ ((b i + M * j.val : ℕ) : ZMod r))) := by
      have hK : K i ≠ 0 := by have hj := j.isLt; omega
      rw [he i j]
      dsimp only [f]
      rw [hcode i j, huval, hval]
      simp only [w, ite_eq_right hK]
    simp_rw [hp]
    exact Fin.sum_univ_eq_sum_range (fun j => w i j *
      (χ ((b i + M * j : ℕ) : ZMod q) * conj (ψ ((b i + M * j : ℕ) : ZMod r)))) (K i)
  change ‖∑ j ∈ Finset.range N,
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤ _
  rw [hsum]
  apply character_interval_pieces_bound hqr χ ψ hχ b (fun _ => M) K (fun _ => hM) w _
  calc
    _ ≤ ∑ _i : S → Ordering, 2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F :=
      Finset.sum_le_sum (fun i _ => hvar i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rootCellCode_card]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SupportedPolynomialCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted character bound with its actual polynomial support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem historyWeightRootCuts_factor {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (i : Fin n) (x : ℝ)
    (hx : x ∈ (F i).polynomial.derivative.roots) : x ∈ historyWeightRootCuts F H := by
  apply Finset.mem_biUnion.mpr
  exact ⟨Sum.inl i, Finset.mem_univ _, by simpa only [Sum.elim_inl, Multiset.mem_toFinset] using hx⟩

theorem historyWeightRootCuts_support {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (i : Fin t) (x : ℝ) (hx : x ∈ (H i).roots) :
    x ∈ historyWeightRootCuts F H := by
  apply Finset.mem_biUnion.mpr
  exact ⟨Sum.inr i, Finset.mem_univ _, by simpa only [Sum.elim_inr, Multiset.mem_toFinset] using hx⟩

theorem historyWeightRootCuts_card {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) :
    (historyWeightRootCuts F H).card ≤
      (∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree := by
  simpa only [historyWeightRootCuts, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using
    polynomialRootCuts_card (Sum.elim (fun i => (F i).polynomial.derivative) H)

theorem supported_polynomial_character_progression {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (ha : 0 < a) (hM : M.Coprime (q * r))
    {n t : ℕ} (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) :
    ‖∑ j ∈ Finset.range N,
      (if keep (polynomialSupportCode H ((a + M * j : ℕ) : ℝ)) = true then (1 : ℂ) else 0) *
      (Complex.ofReal (((a + M * j : ℕ) : ℝ)⁻¹) *
        smoothPolynomialWeight F ((a + M * j : ℕ) : ℝ)) *
      (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤
      (3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r) := by
  let S := historyWeightRootCuts F H
  have hb := polynomial_weighted_character_progression hqr χ ψ hχ a M N ha hM F S
    (historyWeightRootCuts_factor F H) (polynomialRootCellFlag H S keep)
    (polynomialRootCellFlag_norm H S keep)
  simp_rw [polynomialRootCellFlag_value H S (historyWeightRootCuts_support F H) keep] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by
    have hV := smoothPolynomialBudget_nonneg F
    positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) (historyWeightRootCuts_card F H)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pairedPolynomialFactors_weight {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) (x : ℝ) :
    smoothPolynomialWeight (pairedPolynomialFactors F G) x =
      smoothPolynomialWeight F x * conj (smoothPolynomialWeight G x) := by
  simp only [smoothPolynomialWeight, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate_value, map_prod]

theorem pairedPolynomialFactors_budget {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (pairedPolynomialFactors F G) =
      smoothPolynomialBudget F * smoothPolynomialBudget G := by
  simp only [smoothPolynomialBudget, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]

theorem pairedPolynomialAmplitude {n m t u : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (keep' : (Fin u → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude (pairedPolynomialFactors F G) (Fin.append H J)
      (pairedPolynomialKeep keep keep') x =
      polynomialAmplitude F H keep x * conj (polynomialAmplitude G J keep' x) := by
  have hleft : (fun i : Fin t => polynomialSupportCode (Fin.append H J) x (Fin.castAdd u i)) =
      polynomialSupportCode H x := by
    funext i
    simp only [polynomialSupportCode, Fin.append_left]
  have hright : (fun i : Fin u => polynomialSupportCode (Fin.append H J) x (Fin.natAdd t i)) =
      polynomialSupportCode J x := by
    funext i
    simp only [polynomialSupportCode, Fin.append_right]
  simp only [polynomialAmplitude, pairedPolynomialKeep, hleft, hright, Bool.and_eq_true,
    pairedPolynomialFactors_weight, map_mul]
  split_ifs <;> simp_all

theorem polynomialAmplitude_norm {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    ‖polynomialAmplitude F H keep x‖ ≤ smoothPolynomialBudget F := by
  unfold polynomialAmplitude
  split_ifs
  · simpa only [one_mul] using smoothPolynomialWeight_norm F x
  · simpa only [zero_mul, norm_zero] using smoothPolynomialBudget_nonneg F

theorem polynomialWeightComplexity_pair {n m t u : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ) :
    polynomialWeightComplexity (pairedPolynomialFactors F G) (Fin.append H J) =
      polynomialWeightComplexity F H + polynomialWeightComplexity G J := by
  simp only [polynomialWeightComplexity, pairedPolynomialFactors, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRangeGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual argument-range cutoffs as polynomial inequalities -/

namespace Ostmann

open scoped BigOperators Classical

theorem polynomialRangeKeep_iff {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    polynomialRangeKeep n (polynomialSupportCode (polynomialRangeBounds F) x) = true ↔
      ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi := by
  simp only [polynomialRangeKeep, decide_eq_true_eq, polynomialSupportCode,
    polynomialRangeBounds, Fin.append_left, Fin.append_right,
    Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg, Set.mem_Icc]

/-- The clipped extension agrees exactly with the original smooth factors
multiplied by their sharp argument-range indicator. -/
theorem polynomialAmplitude_range {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    polynomialAmplitude F (polynomialRangeBounds F) (polynomialRangeKeep n) x =
      (if ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi then (1 : ℂ) else 0) *
        ∏ i, (F i).profile ((F i).polynomial.eval x) := by
  unfold polynomialAmplitude
  by_cases h : ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi
  · rw [ite_eq_left ((polynomialRangeKeep_iff F x).mpr h), ite_eq_left h]
    simp only [one_mul, smoothPolynomialWeight]
    exact Finset.prod_congr rfl (fun i _ => (F i).value_of_mem x (h i))
  · rw [ite_eq_right (fun hh => h ((polynomialRangeKeep_iff F x).mp hh)), ite_eq_right h]
    simp only [zero_mul]

theorem polynomialRangeBounds_degree_sum {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    (∑ i, (polynomialRangeBounds F i).natDegree) ≤
      2 * ∑ i, (F i).polynomial.natDegree := by
  simp only [polynomialRangeBounds, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hl : (∑ i, ((F i).polynomial - Polynomial.C (F i).lo).natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)] using
      Polynomial.natDegree_sub_le (F i).polynomial (Polynomial.C (F i).lo)
  have hu : (∑ i, (Polynomial.C (F i).hi - (F i).polynomial).natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)] using
      Polynomial.natDegree_sub_le (Polynomial.C (F i).hi) (F i).polynomial
  omega

theorem polynomialRange_complexity {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    polynomialWeightComplexity F (polynomialRangeBounds F) ≤
      3 * ∑ i, (F i).polynomial.natDegree := by
  have hd : (∑ i, (F i).polynomial.derivative.natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    exact (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hr := polynomialRangeBounds_degree_sum F
  unfold polynomialWeightComplexity
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormula
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual product-and-pivot formulas of a fixed arithmetic history -/

namespace Ostmann

namespace HistoryFormula

variable {σ : Type*}

theorem degree_le_cost (F : HistoryFormula σ) : F.cleared.numerator.totalDegree ≤ F.cost := by
  induction F with
  | prime i => simp [cleared, cost, ClearedHistoryValue.ofVariable]
  | external z =>
    simp only [cleared, cost, ClearedHistoryValue.constant, MvPolynomial.totalDegree_C]
    omega
  | product f g ihf ihg =>
    apply (ClearedHistoryValue.degree_prod _ _).trans
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, cost] using
      Nat.add_le_add ihf ihg
  | solve f g v w s hs ihf ihg =>
    apply (ClearedHistoryValue.degree_pivot f.cleared g.cleared v w s hs).trans
    exact max_le (by dsimp only [cost]; omega) (by dsimp only [cost]; omega)

theorem denominator_eq_frequency_product (F : HistoryFormula σ) :
    F.cleared.denominator = F.frequencies.prod := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product f g ihf ihg =>
    simp only [cleared, ClearedHistoryValue.prod, Fintype.prod_bool, Bool.false_eq_true,
      ite_false, if_false, ite_true, if_true, ihf, ihg, frequencies, List.prod_append]
  | solve f g v w s hs ihf ihg =>
    simp only [cleared, ClearedHistoryValue.pivot, ihf, ihg, frequencies, List.prod_cons,
      List.prod_append]
    ring

theorem frequency_count_le_cost (F : HistoryFormula σ) : F.frequencies.length ≤ F.cost := by
  induction F with
  | prime i => simp [frequencies, cost]
  | external z => simp [frequencies, cost]
  | product f g ihf ihg => simp only [frequencies, cost, List.length_append]; omega
  | solve f g v w s hs ihf ihg =>
    simp only [frequencies, cost, List.length_cons, List.length_append]
    omega

/-- The same bound applies after any subset of independent variables is set
to zero; its proof uses only their absolute upper bounds. -/
theorem bounded (F : HistoryFormula σ) (x : σ → ℝ) (R : ℝ) (hR : 3 ≤ R)
    (hx : ∀ i, |x i| ≤ R) (hF : F.InputsBounded R) :
    F.cleared.Bounded x (R ^ F.cost) := by
  have hR0 : 0 ≤ R := by linarith
  induction F with
  | prime i =>
    simpa only [cleared, cost, pow_one] using
      ClearedHistoryValue.bounded_variable i x R (by linarith) (hx i)
  | external z =>
    simpa only [cleared, cost, pow_one] using
      ClearedHistoryValue.bounded_constant z x R (by linarith) hF
  | product f g ihf ihg =>
    have hf := ihf hF.1
    have hg := ihg hF.2
    have hh := ClearedHistoryValue.bounded_prod Finset.univ
      (fun b : Bool => if b then f.cleared else g.cleared) x
      (fun b : Bool => if b then R ^ f.cost else R ^ g.cost)
      (fun b _ => by cases b <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> assumption)
    simpa only [cleared, cost, Fintype.prod_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      ← pow_add, Nat.add_comm] using hh
  | solve f g v w s hs ihf ihg =>
    have hh := ClearedHistoryValue.bounded_pivot f.cleared g.cleared v w s hs x
      (R ^ f.cost) (R ^ g.cost) (ihf hF.1) (ihg hF.2.1)
    have hc : |(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)| ≤ R ^ 2 := by
      obtain ⟨_, _, hv, hw, hs⟩ := hF
      nlinarith
    have hb : (|(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)|) * R ^ f.cost * R ^ g.cost ≤
        R ^ (f.cost + g.cost + 2) := by
      calc
        _ ≤ R ^ 2 * R ^ f.cost * R ^ g.cost := by gcongr
        _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
    exact ⟨hh.1.trans hb, hh.2.trans hb⟩

theorem zero_variable_bound (F : HistoryFormula σ) (i : σ) (x : σ → ℤ)
    (R : ℝ) (hR : 3 ≤ R) (hx : ∀ j, |(x j : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    |((MvPolynomial.eval₂Hom (RingHom.id ℤ) x
      (zeroHistoryVariable i F.cleared.numerator) : ℤ) : ℝ)| ≤ R ^ F.cost := by
  classical
  apply ClearedHistoryValue.zero_variable_value_bound F.cleared i x
  apply F.bounded _ R hR _ hF
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self, Int.cast_zero, abs_zero] using (show 0 ≤ R by linarith)
  · simpa only [Function.update_of_ne hj] using hx j

end HistoryFormula

theorem integer_list_product_dvd_power (l : List ℤ) (M : ℤ) (h : ∀ d ∈ l, d ∣ M) :
    l.prod ∣ M ^ l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd := h d (by simp)
    have hl := ih (fun e he => h e (by simp [he]))
    simpa only [List.prod_cons, List.length_cons, pow_succ, mul_comm] using mul_dvd_mul hd hl

theorem HistoryFormula.denominator_test_period {σ : Type*} (F : HistoryFormula σ)
    (M s : ℤ) (h : ∀ d ∈ F.frequencies, d ∣ M) (hs : s ∣ M) :
    F.cleared.denominator * s ∣ M ^ (F.frequencies.length + 1) := by
  rw [F.denominator_eq_frequency_product, pow_succ]
  exact mul_dvd_mul (integer_list_product_dvd_power _ M h) hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution constructs the actual rational expressions of a reversed history -/

namespace Ostmann.HistoryFormula

variable {σ τ : Type*}

@[simp] theorem value_prime (i : σ) (x : σ → ℚ) : (prime i).value x = x i :=
  ClearedHistoryValue.eval_variable i x

@[simp] theorem value_external (z : ℤ) (x : σ → ℚ) : (external z).value x = z :=
  ClearedHistoryValue.eval_constant z x

@[simp] theorem value_product (l r : HistoryFormula σ) (x : σ → ℚ) :
    (product l r).value x = l.value x * r.value x := by
  simp only [value, cleared, ClearedHistoryValue.eval_prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true]

@[simp] theorem value_solve (l r : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0) (x : σ → ℚ) :
    (solve l r v w s hs).value x = (v * r.value x - w * l.value x) / s :=
  ClearedHistoryValue.eval_pivot l.cleared r.cleared v w s hs x

theorem value_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (x : τ → ℚ) :
    (F.bind f).value x = F.value (fun i => (f i).value x) := by
  induction F with
  | prime i => simp only [bind, value_prime]
  | external z => simp only [bind, value_external]
  | product l r hl hr => simp only [bind, value_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, value_solve, hl, hr]

/-- A fixed number of substitutions multiplies the expression-size bound;
for fixed transfer depth this remains a polynomial in the word length. -/
theorem cost_bind_le (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (C : ℕ) (hC : 1 ≤ C) (hf : ∀ i, (f i).cost ≤ C) :
    (F.bind f).cost ≤ C * F.cost := by
  induction F with
  | prime i => simpa only [bind, cost, Nat.mul_one] using hf i
  | external z => simpa only [bind, cost, Nat.mul_one] using hC
  | product l r hl hr =>
    simpa only [bind, cost, Nat.mul_add] using Nat.add_le_add hl hr
  | solve l r v w s hs hl hr =>
    simp only [bind, cost, Nat.mul_add]
    have hc2 : 2 ≤ C * 2 := by omega
    omega

theorem inputsBounded_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (R : ℝ)
    (hF : F.InputsBounded R) (hf : ∀ i, (f i).InputsBounded R) :
    (F.bind f).InputsBounded R := by
  induction F with
  | prime i => exact hf i
  | external z => exact hF
  | product l r hl hr => exact ⟨hl hF.1, hr hF.2⟩
  | solve l r v w s hs hl hr => exact ⟨hl hF.1, hr hF.2.1, hF.2.2⟩

theorem value_listProduct (fs : List (HistoryFormula σ)) (x : σ → ℚ) :
    (listProduct fs).value x = (fs.map (fun F => F.value x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, value_product, List.map_cons, List.prod_cons, ih]

theorem cost_listProduct (fs : List (HistoryFormula σ)) :
    (listProduct fs).cost = (fs.map cost).sum + 1 := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [listProduct, cost, List.map_cons, List.sum_cons, ih]; omega

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerHistoryReconstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cleared formulas evaluate to the actual integer pivot reconstructions -/

namespace Ostmann

open scoped Classical

namespace HistoryPivotStep

variable {σ : Type*}

theorem formula_value (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x : ℚ) / step.s := by
  have hp (l : List σ) : (l.map (fun i => (x i : ℚ))).prod = ((l.map x).prod : ℚ) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simp only [formula, HistoryFormula.value_solve, HistoryFormula.value_listProduct,
    List.map_map, Function.comp_def, HistoryFormula.value_prime, hp, numerator,
    Int.cast_sub, Int.cast_mul]

theorem formula_value_integer (step : HistoryPivotStep σ) (x : σ → ℤ) (hx : step.Valid x) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x / step.s : ℤ) := by
  rw [formula_value, Int.cast_div hx (Int.cast_ne_zero.mpr step.s_ne_zero)]

theorem formula_cost (step : HistoryPivotStep σ) :
    step.formula.cost = step.left.length + step.right.length + 4 := by
  have hc (l : List σ) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  simp only [formula, HistoryFormula.cost, HistoryFormula.cost_listProduct, List.map_map,
    Function.comp_def, hc]
  omega

end HistoryPivotStep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructionIntegrality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original integer-divisibility gate is a cleared polynomial test -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.integralAt_iff {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.IntegralAt x ↔ F.cleared.denominator ∣
      MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, F.cleared.integer_value_cleared x y hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (div_eq_iff (Int.cast_ne_zero.mpr F.cleared.denominator_ne_zero)).mpr
    have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
      simpa [Int.castRingHom] using
        (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator)
    rw [← he, hy, Int.cast_mul, mul_comm]

theorem HistoryPivotStep.valid_iff_integral {σ : Type*} (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.Valid x ↔ step.formula.IntegralAt x := by
  constructor
  · intro hx
    exact ⟨step.numerator x / step.s, step.formula_value_integer x hx⟩
  · rintro ⟨y, hy⟩
    rw [step.formula_value] at hy
    have he : (step.numerator x : ℚ) = (y : ℚ) * step.s :=
      (div_eq_iff (Int.cast_ne_zero.mpr step.s_ne_zero)).mp hy
    have hi : step.numerator x = step.s * y := by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_mul, he, mul_comm]
    exact ⟨y, hi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructionFrequencyPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common small-frequency period for the constructed reconstruction tests -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

variable {σ τ : Type*}

theorem frequencies_bind_dvd (F : HistoryFormula σ) (env : σ → HistoryFormula τ) (M : ℤ)
    (hF : ∀ d ∈ F.frequencies, d ∣ M)
    (henv : ∀ i d, d ∈ (env i).frequencies → d ∣ M) :
    ∀ d ∈ (F.bind env).frequencies, d ∣ M := by
  induction F with
  | prime i => exact henv i
  | external z => simp only [bind, frequencies, List.not_mem_nil, false_implies, implies_true]
  | product l r hl hr =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hl (fun a ha => hF a (List.mem_append_left _ ha)) d hd
    · exact hr (fun a ha => hF a (List.mem_append_right _ ha)) d hd
  | solve l r v w s hs hl hr =>
    intro d hd
    rcases List.mem_cons.mp hd with hds | hd
    · subst d; exact hF s (by simp [frequencies])
    · rcases List.mem_append.mp hd with hd | hd
      · exact hl (fun a ha => hF a (by simp only [frequencies, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl ha))) d hd
      · exact hr (fun a ha => hF a (by simp only [frequencies, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr ha))) d hd

theorem frequencies_listProduct_dvd (fs : List (HistoryFormula σ)) (M : ℤ)
    (h : ∀ F ∈ fs, ∀ d ∈ F.frequencies, d ∣ M) :
    ∀ d ∈ (listProduct fs).frequencies, d ∣ M := by
  induction fs with
  | nil => simp only [listProduct, frequencies, List.not_mem_nil, false_implies, implies_true]
  | cons F fs ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h F (by simp) d hd
    · exact ih (fun G hG => h G (by simp [hG])) d hd

end HistoryFormula

theorem HistoryPivotStep.formula_frequencies_dvd {σ : Type*}
    (step : HistoryPivotStep σ) (M : ℤ) (hs : step.s ∣ M) :
    ∀ d ∈ step.formula.frequencies, d ∣ M := by
  intro d hd
  have hprime (l : List σ) : ∀ a ∈ (HistoryFormula.listProduct (l.map .prime)).frequencies, a ∣ M := by
    apply HistoryFormula.frequencies_listProduct_dvd
    intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    simp only [HistoryFormula.frequencies, List.not_mem_nil, false_implies, implies_true]
  rcases List.mem_cons.mp hd with he | hd
  · subst d; exact hs
  · rcases List.mem_append.mp hd with hd | hd
    · exact hprime step.left d hd
    · exact hprime step.right d hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonHistoryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero common modulus constructed from the actual small frequencies -/

namespace Ostmann

theorem historyFrequencyBase_pos (frequencies : List ℤ)
    (h : ∀ s ∈ frequencies, s ≠ 0) : 0 < historyFrequencyBase frequencies := by
  induction frequencies with
  | nil => simp [historyFrequencyBase]
  | cons s rest ih =>
    simp only [historyFrequencyBase, List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (h s (by simp)))
      (ih (fun t ht => h t (by simp [ht])))

theorem historyFrequencyPeriod_pos (frequencies : List ℤ) (degree : ℕ)
    (h : ∀ s ∈ frequencies, s ≠ 0) : 0 < historyFrequencyPeriod frequencies degree :=
  pow_pos (historyFrequencyBase_pos frequencies h) degree

theorem frequency_dvd_historyFrequencyBase (frequencies : List ℤ) (s : ℤ)
    (hs : s ∈ frequencies) : s ∣ (historyFrequencyBase frequencies : ℤ) := by
  apply Int.dvd_natCast.mpr
  exact List.dvd_prod (List.mem_map.mpr ⟨s, hs, rfl⟩)

theorem prime_coprime_historyFrequencyPeriod (frequencies : List ℤ) (degree p : ℕ)
    (hp : p.Prime) (hsmall : ∀ s ∈ frequencies, 0 < s.natAbs ∧ s.natAbs < p) :
    p.Coprime (historyFrequencyPeriod frequencies degree) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_list_prod_right_iff.mpr
  intro n hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (hsmall s hs).1 (hsmall s hs).2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pushforward to log-cell and residue coordinates

The finite partition of each actual prime sample induces independent cell
priors. This is an equality, before any progression approximation is used.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem cellPrior_nonneg {A B : Type*} [Fintype A]
    (μ : A → ℝ) (cell : A → B) (hμ : ∀ a, 0 ≤ μ a) (b : B) :
    0 ≤ cellPrior μ cell b := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hμ a
  · exact le_rfl

theorem cellPrior_mass {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (cell : A → B) : (∑ b, cellPrior μ cell b) = ∑ a, μ a := by
  unfold cellPrior
  rw [Finset.sum_comm]
  simp

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PeriodicPolynomialCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the actual small-frequency residue restrictions -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- A bounded function of the residue modulo the frequency modulus is constant
on each progression. It therefore retains the same cancellation bound. -/
theorem periodic_polynomial_integer_character_sum {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a Q K : ℕ) (ha : 0 < a) (hQ : Q.Coprime (q * r))
    {n t : ℕ} (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (gate : ZMod Q → ℂ) (hgate : ∀ z, ‖gate z‖ ≤ 1) :
    ‖∑ j : Fin (K * Q), gate ((a + j.val : ℕ) : ZMod Q) *
      supportedPolynomialWeight F H keep ((a + j.val : ℕ) : ℝ) *
      (χ ((a + j.val : ℕ) : ZMod q) * conj (ψ ((a + j.val : ℕ) : ZMod r)))‖ ≤
      (Q : ℝ) * ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
  let g : ℕ → ℂ := fun v => supportedPolynomialWeight F H keep (v : ℝ) *
    (χ (v : ZMod q) * conj (ψ (v : ZMod r)))
  simp only [mul_assoc]
  change ‖∑ j : Fin (K * Q), gate ((a + j.val : ℕ) : ZMod Q) * g (a + j.val)‖ ≤ _
  rw [integerProgressionPartition_sum Q K (fun j => gate ((a + j.val : ℕ) : ZMod Q) * g (a + j.val))]
  simp_rw [integerProgressionPartition_value Q K a]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s : Fin Q, ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
      apply Finset.sum_le_sum
      intro s _
      have hmod (j : Fin K) : ((a + s.val + Q * j.val : ℕ) : ZMod Q) = (a + s.val : ℕ) := by
        simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
      simp_rw [hmod]
      rw [← Finset.mul_sum, norm_mul]
      apply (mul_le_mul_of_nonneg_right (hgate _) (norm_nonneg _)).trans
      rw [one_mul]
      have hb := supported_polynomial_character_progression hqr χ ψ hχ (a + s.val) Q K
        (by omega) hQ F H keep
      rw [Fin.sum_univ_eq_sum_range (fun j => g (a + s.val + Q * j)) K]
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (smoothPolynomialBudget_nonneg F)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply inv_anti₀ (by exact_mod_cast ha)
      exact_mod_cast Nat.le_add_right a s.val
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PeriodicPolynomialOneSidedBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided cancellation with the retained small-frequency residue tests -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem periodic_polynomial_one_sided_bound (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (gate : Q → ZMod M → ℂ) (hgate : ∀ q z, ‖gate q z‖ ≤ 1)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (μ : Fin (K * M) → ℝ) (ν : Q → ℝ) (U : Fin (K * M) → ℂ) (V : Q → ℂ)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hμ : ∀ j, 0 ≤ μ j) (hmassμ : ∑ j, μ j ≤ 1)
    (hdom : ∀ j, μ j ≤ C * ((a + j.val : ℕ) : ℝ)⁻¹)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ j, (μ j : ℂ) * (U j * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
        (gate q ((a + j.val : ℕ) : ZMod M) *
        polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ))))‖ ^ 2 ≤
      C * (α * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  let η : Fin (K * M) → ℝ := fun j => ((a + j.val : ℕ) : ℝ)⁻¹
  let G : Q → Fin (K * M) → ℂ := fun q j =>
    χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
      (gate q ((a + j.val : ℕ) : ZMod M) *
        polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ))
  have hη (j : Fin (K * M)) : 0 ≤ η j := by dsimp [η]; positivity
  have hηatom (j : Fin (K * M)) : η j ≤ (a : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast ha)
    exact_mod_cast Nat.le_add_right a j.val
  have hηmass : ∑ j, η j ≤ ((K * M : ℕ) : ℝ) / a := by
    calc
      _ ≤ ∑ _j : Fin (K * M), (a : ℝ)⁻¹ := Finset.sum_le_sum (fun j _ => hηatom j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
  have hG (q : Q) (j : Fin (K * M)) : ‖G q j‖ ≤ B := by
    change ‖χ q _ * (gate q _ * polynomialAmplitude (F q) (H q) (keep q) _)‖ ≤ B
    rw [norm_mul, norm_mul]
    have hb := mul_le_mul (hgate q ((a + j.val : ℕ) : ZMod M))
      ((polynomialAmplitude_norm (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ)).trans (hbudget q))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (mul_le_mul ((χ q).norm_le_one _) hb
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).trans
      (by simp only [one_mul, le_refl])
  apply one_sided_cauchy_of_offdiagonal μ η ν U V G C α (((K * M : ℕ) : ℝ) / a) B
    ((M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
    hC hα (by positivity) (by positivity) hμ hmassμ hdom hη hηmass hν hmassν hatom hU hV hG
  intro q r hqr
  have : NeZero (q : ℕ) := ⟨(hprime q q.property).ne_zero⟩
  have : NeZero (r : ℕ) := ⟨(hprime r r.property).ne_zero⟩
  have hcop : (q : ℕ).Coprime (r : ℕ) :=
    (Nat.coprime_primes (hprime q q.property) (hprime r r.property)).mpr
      (fun he => hqr (Subtype.ext he))
  let FP := pairedPolynomialFactors (F q) (F r)
  let HP := Fin.append (H q) (H r)
  let kP := pairedPolynomialKeep (keep q) (keep r)
  have he (j : Fin (K * M)) : (η j : ℂ) * (G q j * conj (G r j)) =
      (gate q ((a + j.val : ℕ) : ZMod M) * conj (gate r ((a + j.val : ℕ) : ZMod M))) *
        supportedPolynomialWeight FP HP kP ((a + j.val : ℕ) : ℝ) *
        (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
          conj (χ r ((a + j.val : ℕ) : ZMod (r : ℕ)))) := by
    have hp := pairedPolynomialAmplitude (F q) (F r) (H q) (H r) (keep q) (keep r)
      ((a + j.val : ℕ) : ℝ)
    change polynomialAmplitude FP HP kP _ = _ at hp
    have hs : supportedPolynomialWeight FP HP kP ((a + j.val : ℕ) : ℝ) =
        (η j : ℂ) * polynomialAmplitude FP HP kP ((a + j.val : ℕ) : ℝ) := by
      unfold supportedPolynomialWeight polynomialAmplitude η
      ring
    rw [hs, hp]
    simp only [G, map_mul]
    ring
  have hg (z : ZMod M) : ‖gate q z * conj (gate r z)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (hgate q z) (hgate r z) (norm_nonneg _) (by norm_num)).trans
      (by norm_num)
  have hb := periodic_polynomial_integer_character_sum hcop (χ q) (χ r) (hnonprincipal q)
    a M K ha ((hM q).mul_right (hM r)) FP HP kP (fun z => gate q z * conj (gate r z)) hg
  simp_rw [he]
  apply hb.trans
  have hc : polynomialWeightComplexity FP HP ≤ 2 * R := by
    change polynomialWeightComplexity (pairedPolynomialFactors (F q) (F r))
      (Fin.append (H q) (H r)) ≤ _
    rw [polynomialWeightComplexity_pair]
    have hq := hcomplexity q
    have hr := hcomplexity r
    omega
  have hpow : ((3 ^ polynomialWeightComplexity FP HP : ℕ) : ℝ) ≤ (3 ^ (2 * R) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hc
  have hbud : smoothPolynomialBudget FP ≤ B ^ 2 := by
    change smoothPolynomialBudget (pairedPolynomialFactors (F q) (F r)) ≤ _
    rw [pairedPolynomialFactors_budget, pow_two]
    exact mul_le_mul (hbudget q) (hbudget r) (smoothPolynomialBudget_nonneg _) hB
  have hqrB : (q : ℝ) * (r : ℝ) ≤ (Bq : ℝ) ^ 2 := by
    have hq : (q : ℝ) ≤ Bq := by exact_mod_cast hBq q
    have hr : (r : ℝ) ≤ Bq := by exact_mod_cast hBq r
    simpa only [pow_two] using mul_le_mul hq hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hFP0 := smoothPolynomialBudget_nonneg FP
  change (M : ℝ) * (((3 ^ polynomialWeightComplexity FP HP : ℕ) : ℝ) *
      (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget FP) * ((q : ℝ) * (r : ℝ))) ≤ _
  calc
    _ ≤ (M : ℝ) * (((3 ^ (2 * R) : ℕ) : ℝ) * (2 * (a : ℝ)⁻¹ * B ^ 2) * (Bq : ℝ) ^ 2) := by
      gcongr
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinitePairCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint cells for the two different giant sampling spaces -/

namespace Ostmann

open scoped BigOperators Classical

theorem sum_cellPrior_mul {A C : Type*} [Fintype A] [Fintype C]
    (μ : A → ℝ) (cell : A → C) (F : C → ℂ) :
    (∑ a, (μ a : ℂ) * F (cell a)) = ∑ c, (cellPrior μ cell c : ℂ) * F c := by
  simp only [cellPrior, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEmbeddingPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the original finite prior without changing its mean -/

namespace Ostmann

open scoped BigOperators Classical

theorem embeddingExtend_apply {A B C : Type*} [Zero C] (e : A ↪ B) (f : A → C) (a : A) :
    embeddingExtend e f (e a) = f a := by
  have h : ∃ x, e x = e a := ⟨a, rfl⟩
  unfold embeddingExtend
  rw [dite_eq_left h]
  have he : h.choose = a := e.injective h.choose_spec
  rw [he]

theorem embeddingExtend_norm_le {A B : Type*} (e : A ↪ B) (f : A → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a, ‖f a‖ ≤ C) (b : B) :
    ‖embeddingExtend e f b‖ ≤ C := by
  unfold embeddingExtend
  split_ifs with h
  · exact hf h.choose
  · simpa only [norm_zero] using hC

theorem cellPrior_embedding {A B : Type*} [Fintype A] (e : A ↪ B) (ρ : A → ℝ) (a : A) :
    cellPrior ρ e (e a) = ρ a := by
  unfold cellPrior
  have he (x : A) : e x = e a ↔ x = a := e.injective.eq_iff
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem cellPrior_embedding_le {A B : Type*} [Fintype A] (e : A ↪ B) (ρ : A → ℝ)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hρ : ∀ a, ρ a ≤ w (e a)) (b : B) :
    cellPrior ρ e b ≤ w b := by
  by_cases h : ∃ a, e a = b
  · obtain ⟨a, rfl⟩ := h
    rw [cellPrior_embedding]
    exact hρ a
  · have he : cellPrior ρ e b = 0 := by
      unfold cellPrior
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => h ⟨a, ha⟩)
    rw [he]
    exact hw b

theorem intervalSampleEmbedding_value {A : Type*} (value : A → ℕ) (hinj : Function.Injective value)
    (a N : ℕ) (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + N) (x : A) :
    a + (intervalSampleEmbedding value hinj a N hlow hhigh x).val = value x := by
  exact Nat.add_sub_of_le (hlow x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPriorPeriodicBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original sampling law with the small-frequency residue restrictions -/

namespace Ostmann

open scoped BigOperators Classical

/-- An arbitrary original sample in the long interval is extended by zero.
Its unary factor and mean are retained exactly. -/
theorem original_prior_periodic_polynomial_one_sided_bound {A : Type*} [Fintype A]
    (value : A → ℕ) (hinj : Function.Injective value)
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (gate : Q → ZMod M → ℂ) (hgate : ∀ q z, ‖gate q z‖ ≤ 1)
    (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + K * M)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (ρ : A → ℝ) (ν : Q → ℝ) (U : A → ℂ) (V : Q → ℂ)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hρ : ∀ x, 0 ≤ ρ x) (hmassρ : ∑ x, ρ x ≤ 1)
    (hdom : ∀ x, ρ x ≤ C * (value x : ℝ)⁻¹)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ x, (ρ x : ℂ) * (U x * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q (value x : ZMod (q : ℕ)) *
        (gate q (value x : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (value x : ℝ))))‖ ^ 2 ≤
      C * (α * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  let e := intervalSampleEmbedding value hinj a (K * M) hlow hhigh
  let μ := cellPrior ρ e
  let U' := embeddingExtend e U
  have he (x : A) : a + (e x).val = value x :=
    intervalSampleEmbedding_value value hinj a (K * M) hlow hhigh x
  have hμ : ∀ j, 0 ≤ μ j := cellPrior_nonneg ρ e hρ
  have hμmass : ∑ j, μ j ≤ 1 := by
    change ∑ j, cellPrior ρ e j ≤ 1
    rw [cellPrior_mass]
    exact hmassρ
  have hμdom : ∀ j, μ j ≤ C * ((a + j.val : ℕ) : ℝ)⁻¹ := by
    apply cellPrior_embedding_le e ρ _ (fun j => by positivity)
    intro x
    rw [he]
    exact hdom x
  have hU' : ∀ j, ‖U' j‖ ≤ 1 := embeddingExtend_norm_le e U 1 (by norm_num) hU
  have hb := periodic_polynomial_one_sided_bound Q hprime χ hnonprincipal a M K ha hM gate hgate F H keep B R Bq
    hB hbudget hcomplexity hBq μ ν U' V C α hC hα hμ hμmass hμdom hν hmassν hatom hU' hV
  let f : Fin (K * M) → ℂ := fun j => U' j * ∑ q : Q, (ν q : ℂ) * V q *
    (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
      (gate q ((a + j.val : ℕ) : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ)))
  have hs := sum_cellPrior_mul ρ e f
  have hf (x : A) : f (e x) = U x * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q (value x : ZMod (q : ℕ)) * (gate q (value x : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (value x : ℝ))) := by
    dsimp only [f, U']
    rw [embeddingExtend_apply, he]
  simp only [hf] at hs
  rw [hs]
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicPeriodicBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original harmonic prime priors with all frequency residue tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_periodic_polynomial_one_sided_bound (P Q : Finset ℕ)
    (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (gate : Q → ZMod M → ℂ) (hgate : ∀ q z, ‖gate q z‖ ≤ 1)
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : P → ℂ) (V : Q → ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          (gate q ((p : ℕ) : ZMod M) * polynomialAmplitude (F q) (H q) (keep q) (p : ℝ))))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  apply original_prior_periodic_polynomial_one_sided_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    Q hprime χ hnonprincipal a M K ha hM gate hgate
    (fun p => hlow p p.property) (fun p => hhigh p p.property) F H keep B R Bq hB
    hbudget hcomplexity hBq (primeSubsetPrior P P) (primeSubsetPrior Q Q) U V
    ((∑ p ∈ P, (p : ℝ)⁻¹)⁻¹) ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹)
    (by positivity) (by positivity) (primeSubsetPrior_nonneg P P)
  · exact (primeSubsetPrior_mass P P (Finset.Subset.refl _) hPmass.ne').le
  · exact primeSubsetPrior_atom P P
  · exact primeSubsetPrior_nonneg Q Q
  · exact (primeSubsetPrior_mass Q Q (Finset.Subset.refl _) hQmass.ne').le
  · intro q
    apply (primeSubsetPrior_atom Q Q q).trans
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hb (hbQ q q.property)) (by positivity)
  · exact hU
  · exact hV

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GuardedHistoryCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided cancellation retaining all polynomial history tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem guardedHistoryAmplitude_residue {σ I : Type*} [Fintype I] {n t : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (M : ℕ) [NeZero M]
    (hd : ∀ j, d j ≠ 0) (hdiv : ∀ j, d j * s j ∣ (M : ℤ)) (x : ℤ) :
    guardedHistoryAmplitude N d s a i F H keep x =
      clearedHistoryResidueGate N d s a i M (x : ZMod M) * polynomialAmplitude F H keep (x : ℝ) := by
  rw [clearedHistoryResidueGate_exact N d s a i M hd hdiv x]
  rfl

theorem harmonic_guarded_history_bound {σ I : Type*} [Fintype I] {n t : ℕ}
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) [NeZero M] (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : P → ℂ) (V : Q → ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ)))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have he (q : Q) (p : P) : guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord
      (F q) (H q) (keep q) (p : ℕ) =
      clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M ((p : ℕ) : ZMod M) *
        polynomialAmplitude (F q) (H q) (keep q) (p : ℝ) := by
    simpa only [Int.cast_natCast] using guardedHistoryAmplitude_residue
      (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) M (hd q) (hdiv q) (p : ℕ)
  simp_rw [he]
  exact harmonic_periodic_polynomial_one_sided_bound P Q hprime χ hnonprincipal a M K ha hM
    (fun q => clearedHistoryResidueGate (N q) (d q) (s q) (fixed q) coord M)
    (fun q => clearedHistoryResidueGate_norm (N q) (d q) (s q) (fixed q) coord M)
    hlow hhigh b hb hbQ hPmass hQmass F H keep B R Bq hB hbudget hcomplexity hBq U V hU hV

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullHistoryGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier ranges and all additional history inequalities in one exact guard -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullHistoryAmplitude_factor {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude F (fullHistoryPolynomials F H) (fullHistoryKeep keep) x =
      (if keep (polynomialSupportCode H x) = true then (1 : ℂ) else 0) *
        polynomialAmplitude F (polynomialRangeBounds F) (polynomialRangeKeep n) x := by
  have hl : (fun i : Fin (n + n) => polynomialSupportCode (fullHistoryPolynomials F H) x
      (Fin.castAdd t i)) = polynomialSupportCode (polynomialRangeBounds F) x := by
    funext i
    simp only [fullHistoryPolynomials, polynomialSupportCode, Fin.append_left]
  have hr : (fun i : Fin t => polynomialSupportCode (fullHistoryPolynomials F H) x
      (Fin.natAdd (n + n) i)) = polynomialSupportCode H x := by
    funext i
    simp only [fullHistoryPolynomials, polynomialSupportCode, Fin.append_right]
  simp only [polynomialAmplitude, fullHistoryKeep, pairedPolynomialKeep, hl, hr, Bool.and_eq_true]
  split_ifs <;> simp_all

/-- The extension agrees with every original range/bin restriction, including
boundary points, before the one-sided cancellation estimate is invoked. -/
theorem fullHistoryAmplitude_exact {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude F (fullHistoryPolynomials F H) (fullHistoryKeep keep) x =
      (if keep (polynomialSupportCode H x) = true ∧
        ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi then (1 : ℂ) else 0) *
        ∏ i, (F i).profile ((F i).polynomial.eval x) := by
  rw [fullHistoryAmplitude_factor, polynomialAmplitude_range]
  split_ifs <;> simp_all

theorem fullHistoryPolynomials_complexity {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) :
    polynomialWeightComplexity F (fullHistoryPolynomials F H) ≤
      3 * (∑ i, (F i).polynomial.natDegree) + ∑ j, (H j).natDegree := by
  have hbase := polynomialRange_complexity F
  simp only [polynomialWeightComplexity, fullHistoryPolynomials, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right] at *
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedHistoryGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact range and residue guards for the reconstructed original pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem formulaPolynomial_degree {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) : (formulaPolynomial F a coord).natDegree ≤ F.cost :=
  (normalizedHistoryPolynomial_natDegree _ _ _ _).trans F.degree_le_cost

theorem formulaRangePolynomials_iff {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) (x : ℝ) :
    polynomialRangeKeep n (polynomialSupportCode (formulaRangePolynomials F a coord lo hi) x) = true ↔
      ∀ i, (formulaPolynomial (F i) a coord).eval x ∈ Set.Icc (lo i) (hi i) := by
  simp only [polynomialRangeKeep, decide_eq_true_eq, polynomialSupportCode,
    formulaRangePolynomials, Fin.append_left, Fin.append_right,
    Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg, Set.mem_Icc]

theorem formulaRangePolynomials_degree {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) :
    (∑ i, (formulaRangePolynomials F a coord lo hi i).natDegree) ≤ 2 * ∑ i, (F i).cost := by
  simp only [formulaRangePolynomials, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hl : (∑ i, (formulaPolynomial (F i) a coord - Polynomial.C (lo i)).natDegree) ≤
      ∑ i, (F i).cost := by
    apply Finset.sum_le_sum
    intro i _
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact formulaPolynomial_degree _ _ _
  have hu : (∑ i, (Polynomial.C (hi i) - formulaPolynomial (F i) a coord).natDegree) ≤
      ∑ i, (F i).cost := by
    apply Finset.sum_le_sum
    intro i _
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
    exact formulaPolynomial_degree _ _ _
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormulaFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier factors of the constructed history formulas, with derived budgets -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem formulaFourierBudget_nonneg {n : ℕ} (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hhi : ∀ j, lo j ≤ hi j) : 0 ≤ formulaFourierBudget ψ v lo hi := by
  have hψ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
    (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  exact Finset.prod_nonneg fun j _ => add_nonneg (mul_nonneg (by norm_num) hψ)
    (mul_nonneg (add_nonneg hψ (mul_nonneg (schwartz_profile_lip_nonneg ψ) (abs_nonneg _)))
      (sub_nonneg.mpr (hhi j)))

theorem formulaFourierFactors_degree {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (j : Fin n) :
    ((formulaFourierFactors F a coord X ψ v lo hi hlo hhi) j).polynomial.natDegree ≤
      (F j).cost :=
  (normalizedHistoryPolynomial_natDegree _ _ _ _).trans (F j).degree_le_cost

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GlobalHistoryCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The global history coefficient and its exact one-variable polynomial form -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem formulaPolynomial_eval_update {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    (formulaPolynomial F (fun j => (a j : ℝ)) coord).eval (z : ℝ) =
      F.realValue (Function.update a coord z) := by
  rw [formulaPolynomial, normalizedHistoryPolynomial_eval]
  unfold HistoryFormula.realValue
  congr 2
  funext j
  by_cases hj : j = coord
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

theorem formulaFourier_polynomial_eval {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℤ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (j : Fin n) (z : ℤ) :
    ((formulaFourierFactors F (fun i => (a i : ℝ)) coord X ψ v lo hi hlo hhi) j).polynomial.eval (z : ℝ) =
      (F j).realValue (Function.update a coord z) / X j := by
  change (normalizedHistoryPolynomial _ _ _ ((F j).cleared.denominator * X j)).eval (z : ℝ) = _
  rw [normalizedHistoryPolynomial_eval, ← div_div]
  have he := formulaPolynomial_eval_update (F j) a coord z
  rw [formulaPolynomial, normalizedHistoryPolynomial_eval] at he
  rw [he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GuardedHistoryPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of both reconstructed history supports -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem guardedHistoryAmplitude_pair {σ : Type*} {r s n m t u : ℕ}
    (N : Fin r → MvPolynomial σ ℤ) (d : Fin r → ℤ) (v : Fin r → ℕ)
    (N' : Fin s → MvPolynomial σ ℤ) (d' : Fin s → ℤ) (v' : Fin s → ℕ)
    (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (keep' : (Fin u → Bool) → Bool) (x : ℤ) :
    guardedHistoryAmplitude (Fin.append N N') (Fin.append d d') (Fin.append v v')
      a coord (pairedPolynomialFactors F G) (Fin.append H J) (pairedPolynomialKeep keep keep') x =
    guardedHistoryAmplitude N d v a coord F H keep x *
      conj (guardedHistoryAmplitude N' d' v' a coord G J keep' x) := by
  unfold guardedHistoryAmplitude
  rw [pairedPolynomialAmplitude]
  simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, map_mul]
  split_ifs <;> simp_all

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotRowPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded pivot row after grouping by v/H -/

namespace Ostmann

open scoped BigOperators

theorem character_zpow_norm_le_one {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (ε : ℤ) : ‖χ x ^ ε‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp only [norm_zpow, χ.unit_norm_eq_one, one_zpow, le_refl]
  · rw [χ.map_nonunit hx]
    by_cases he : ε = 0
    · simp [he]
    · simp [zero_zpow, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_OneSidedGraphFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating a one-sided graph edge from the bounded unary factors -/

namespace Ostmann

open scoped BigOperators

theorem one_sided_graph_factorization {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (q p : ℕ)
    (hself : E (.inl true) (.inl true) q q = 1 ∧ E (.inl false) (.inl false) p p = 1)
    (hreverse : E (.inl false) (.inl true) p q = 1) :
    finiteEdgeWeight E ν (twoVertexLabels fixed q p) =
      longGraphFactor E ν fixed p * shortGraphFactor E ν fixed q * E (.inl true) (.inl false) q p := by
  simp only [finiteEdgeWeight, Fintype.prod_sum_type, Fintype.prod_bool, twoVertexLabels,
    hself.1, hself.2, hreverse, one_mul, mul_one]
  simp only [longGraphFactor, shortGraphFactor, fixedGraphFactor]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem norm_mul_le_one' (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

private theorem norm_prod_le_one' {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) : ‖∏ i, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hf i)

theorem fixedGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) :
    ‖fixedGraphFactor E ν fixed‖ ≤ 1 := by
  apply norm_prod_le_one'
  intro i
  exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))

theorem longGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) (p : ℕ) :
    ‖longGraphFactor E ν fixed p‖ ≤ 1 := by
  apply norm_mul_le_one'
  · exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))
  · exact norm_prod_le_one' _ (fun i => hE _ _ _ _)

theorem shortGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) (q : ℕ) :
    ‖shortGraphFactor E ν fixed q‖ ≤ 1 := by
  apply norm_mul_le_one'
  · apply norm_mul_le_one'
    · exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))
    · exact norm_prod_le_one' _ (fun i => hE _ _ _ _)
  · exact fixedGraphFactor_norm E ν fixed hE hν

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DirichletGraphFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine character attached to a surviving directed edge -/

namespace Ostmann

open scoped BigOperators

/-- Nonzero powers commute with evaluation also at nonunits. This permits
the same bounded extension convention after large coprimalities are removed. -/
theorem dirichlet_zpow_apply_nonzero {p : ℕ} (χ : DirichletCharacter ℂ p)
    (e : ℤ) (he : e ≠ 0) (x : ZMod p) : (χ ^ e) x = χ x ^ e := by
  cases e with
  | ofNat n =>
    have hn : n ≠ 0 := by intro hn; subst n; exact he rfl
    change (χ ^ (n : ℤ)) x = χ x ^ (n : ℤ)
    simp only [zpow_natCast]
    exact χ.pow_apply' hn x
  | negSucc n =>
    simp only [zpow_negSucc, MulChar.inv_apply_eq_inv',
      χ.pow_apply' (Nat.succ_ne_zero n)]

theorem dirichletGraphEdge_norm {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (b : I → I → ℤ)
    (i j : I) (x y : ℕ) : ‖dirichletGraphEdge χ b i j x y‖ ≤ 1 :=
  character_zpow_norm_le_one (χ i x) _ _

/-- A zero reverse edge leaves exactly one short-modulus character of the
long prime. All other factors depend on at most one of the two variables. -/
theorem dirichlet_one_sided_graph_factorization {J : Type*} [Fintype J]
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hν : ∀ i x, ‖ν i x‖ ≤ 1)
    (hself : b (.inl true) (.inl true) = 0 ∧ b (.inl false) (.inl false) = 0)
    (hreverse : b (.inl false) (.inl true) = 0)
    (hforward : b (.inl true) (.inl false) ≠ 0) :
    ∃ U V : ℕ → ℂ, (∀ p, ‖U p‖ ≤ 1) ∧ (∀ q, ‖V q‖ ≤ 1) ∧
      ∀ q p, finiteEdgeWeight (dirichletGraphEdge χ b) ν (twoVertexLabels fixed q p) =
        U p * V q * (χ (.inl true) q ^ b (.inl true) (.inl false)) (p : ZMod q) := by
  refine ⟨longGraphFactor (dirichletGraphEdge χ b) ν fixed,
    shortGraphFactor (dirichletGraphEdge χ b) ν fixed,
    longGraphFactor_norm _ ν fixed (dirichletGraphEdge_norm χ b) hν,
    shortGraphFactor_norm _ ν fixed (dirichletGraphEdge_norm χ b) hν, ?_⟩
  intro q p
  rw [one_sided_graph_factorization _ ν fixed q p
    (by simp only [dirichletGraphEdge, hself.1, hself.2, zpow_zero, and_self])
    (by simp only [dirichletGraphEdge, hreverse, zpow_zero])]
  rw [dirichlet_zpow_apply_nonzero _ _ hforward]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructedWordQueries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products queried at the actual intermediate reconstruction stages -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.inputsBounded_listProduct {σ : Type*} (fs : List (HistoryFormula σ))
    (R : ℝ) (hR : 1 ≤ R) (h : ∀ F ∈ fs, F.InputsBounded R) :
    (HistoryFormula.listProduct fs).InputsBounded R := by
  induction fs with
  | nil => simpa only [listProduct, InputsBounded, Int.cast_one, abs_one] using hR
  | cons F fs ih => exact ⟨h F (by simp), ih (fun G hG => h G (by simp [hG]))⟩

theorem HistoryPivotStep.formula_inputsBounded {σ : Type*} (step : HistoryPivotStep σ)
    (R : ℝ) (hR : 1 ≤ R) (hv : |(step.v : ℝ)| ≤ R)
    (hw : |(step.w : ℝ)| ≤ R) (hs : |(step.s : ℝ)| ≤ R) : step.formula.InputsBounded R := by
  have hp (l : List σ) : (HistoryFormula.listProduct (l.map .prime)).InputsBounded R := by
    apply HistoryFormula.inputsBounded_listProduct _ R hR
    intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    trivial
  exact ⟨hp _, hp _, hv, hw, hs⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FormulaCoprimality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coprimality error with constructed history degree and value budgets -/

namespace Ostmann

open scoped BigOperators Classical

theorem formula_coprimality_removal {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (Fin (n + 1))) (coord : I → Fin (n + 1))
    (hzero : ∀ j, zeroHistoryVariable (coord j) (F j).cleared.numerator ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hW : ∀ x, ‖W x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) *
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
          then W x else 0)) - ∑ x, (productPrior μ x : ℂ) * W x‖ ≤
      B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  have hvalue (j : I) (x : Fin (n + 1) → A) :
      |(integerTestValue (fun a => (prime a : ℤ))
        (zeroHistoryVariable (coord j) (F j).cleared.numerator) x : ℝ)| ≤ R ^ (F j).cost := by
    apply (F j).zero_variable_bound (coord j) (fun i => (prime (x i) : ℤ)) R hR _ (hinputs j)
    intro i
    simpa only [Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ prime (x i) from Nat.cast_nonneg _)] using hupper (x i)
  have hh := history_coprimality_removal prime hpInj hprime
    (fun j => (F j).cleared.numerator) coord hzero μ hμ hmass α V β
    (fun j => R ^ (F j).cost) hα hβ hV
    (fun j => one_le_pow₀ (by linarith : (1 : ℝ) ≤ R)) hmax hpmax hlower hvalue W B hB hW
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Finset.sum_le_sum
  intro j _
  have hd : ((F j).cleared.numerator.totalDegree : ℝ) ≤ (F j).cost := by
    exact_mod_cast (F j).degree_le_cost
  rw [Real.log_pow]
  have hdeg := mul_le_mul_of_nonneg_right hd hα
  calc
    _ ≤ ((F j).cost : ℝ) * α + ((F j).cost : ℝ) * Real.log R / V * β j :=
      add_le_add hdeg le_rfl
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BranchingHistoryReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

namespace BranchingWordHistory

variable {σ : Type*}

theorem wordFormula_value (word : List σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) :
    (HistoryFormula.listProduct (word.map env)).value a = ((word.map x).prod : ℚ) := by
  rw [HistoryFormula.value_listProduct, List.map_map]
  simp only [Function.comp_def]
  have hmap : word.map (fun i => (env i).value a) = word.map (fun i => (x i : ℚ)) := by
    apply List.map_congr_left
    intro i _
    exact he i
  rw [hmap]
  clear hmap
  induction word with
  | nil => simp
  | cons i word ih => simpa only [List.map_cons, List.prod_cons, Int.cast_mul] using congrArg (fun z => (x i : ℚ) * z) ih

theorem updatedFormulas_value (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) (hx : step.Valid x) :
    ∀ i, (updatedFormulas step env i).value a = (step.applyInteger x i : ℚ) := by
  have hstep : (step.formula.bind env).value a = (step.numerator x / step.s : ℤ) := by
    rw [HistoryFormula.value_bind]
    have he' : (fun i => (env i).value a) = fun i => (x i : ℚ) := funext he
    rw [he']
    exact step.formula_value_integer x hx
  intro i
  by_cases hi : i = step.target
  · subst i
    simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_self] using hstep
  · simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_of_ne hi] using he i

end BranchingWordHistory
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BranchingHistoryIntegrality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every branching reconstruction gate is its constructed polynomial divisibility test -/

namespace Ostmann.BranchingWordHistory

open scoped Classical

variable {σ : Type*}

theorem updatedFormula_integral_iff (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ)
    (a x : σ → ℤ) (he : ∀ i, (env i).value (fun j => (a j : ℚ)) = x i) :
    (step.formula.bind env).IntegralAt a ↔ step.Valid x := by
  have hv : (step.formula.bind env).value (fun j => (a j : ℚ)) =
      step.formula.value (fun j => (x j : ℚ)) := by
    rw [HistoryFormula.value_bind]
    congr 1
    funext i
    exact he i
  rw [step.valid_iff_integral]
  simp only [HistoryFormula.IntegralAt, hv]

/-- The full branching support has precisely one constructed integrality
test for each internal node. Child branches are evaluated independently. -/
theorem pivotFormulas_integral_iff (history : BranchingWordHistory σ)
    (env : σ → HistoryFormula σ) (a x : σ → ℤ)
    (he : ∀ i, (env i).value (fun j => (a j : ℚ)) = x i) :
    (∀ F ∈ history.pivotFormulas env, F.IntegralAt a) ↔ history.Valid x := by
  induction history generalizing env x with
  | leaf word => simp [pivotFormulas, Valid]
  | node step left right hl hr =>
    have hh := updatedFormula_integral_iff step env a x he
    simp only [pivotFormulas, List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq, Valid]
    rw [hh]
    constructor
    · rintro ⟨hs, hleft, hright⟩
      have hu := updatedFormulas_value step env (fun j => (a j : ℚ)) x he hs
      exact ⟨hs, (hl _ _ hu).mp hleft, (hr _ _ hu).mp hright⟩
    · rintro ⟨hs, hleft, hright⟩
      have hu := updatedFormulas_value step env (fun j => (a j : ℚ)) x he hs
      exact ⟨hs, (hl _ _ hu).mpr hleft, (hr _ _ hu).mpr hright⟩

end Ostmann.BranchingWordHistory

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

theorem wordTransferStep_numerator {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (x : σ → ℕ) :
    (wordTransferStep d s v w hs).numerator (fun i => (x i : ℤ)) =
      v * ((d.right.map x).prod : ℤ) - w * ((d.left.map x).prod : ℤ) := by
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  simp only [HistoryPivotStep.numerator, wordTransferStep, hcast]

theorem wordTransferStep_valid {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).Valid (fun i => (x i : ℤ)) := by
  have hnum := wordTransferStep_numerator d s v w hp.root_ne_zero x
  change s ∣ (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ))
  rw [hnum]
  exact ⟨(P : ℤ), hp.relation⟩

theorem wordTransferStep_apply {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).applyInteger (fun i => (x i : ℤ)) =
      fun i => (Function.update x d.target P i : ℤ) := by
  have hnum : (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) = s * P := by
    rw [wordTransferStep_numerator]
    exact hp.relation
  funext i
  by_cases hi : i = d.target
  · subst i
    simp only [HistoryPivotStep.applyInteger,
      show (wordTransferStep d s v w hp.root_ne_zero).target = d.target from rfl, Function.update_self]
    change (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) / s = (P : ℤ)
    rw [hnum]
    exact Int.mul_ediv_cancel_left (P : ℤ) hp.root_ne_zero
  · simp only [HistoryPivotStep.applyInteger, wordTransferStep, Function.update_of_ne hi]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

theorem WordTransferTemplate.branching_valid {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (template.branching t hn).Valid (fun i => (x i : ℤ)) := by
  induction template generalizing x with
  | leaf word => trivial
  | @node n d l r hl hr =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    have hs := wordTransferStep_valid d l r x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P hp
    have he := wordTransferStep_apply d l r x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P hp
    change _ ∧ _ ∧ _
    refine ⟨hs, ?_, ?_⟩
    · rw [he]
      exact hl _ _ hn.2.1 hvL
    · rw [he]
      exact hr _ _ hn.2.2 hvR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFormulaBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived polynomial sizes for the concrete fixed-depth word transfer -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*}

/-- Every output formula is obtained by at most n substitutions, each of
size at most B. This supplies the polynomial loss used by the analytic bound. -/
theorem branching_formula_cost {n : ℕ} (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t)
    (B C : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C) (hwords : template.WordsBounded B)
    (env : σ → HistoryFormula σ) (henv : ∀ i, (env i).cost ≤ C) :
    (∀ z ∈ (template.branching t hn).formulaLeaves env, z.2.cost ≤ C * B ^ (n + 1)) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas env, F.cost ≤ C * B ^ (n + 1)) := by
  induction template generalizing C env with
  | leaf word =>
    constructor
    · intro z hz
      simp only [branching, BranchingWordHistory.formulaLeaves, List.mem_singleton] at hz
      subst z
      simp only [HistoryFormula.cost_listProduct, List.map_map, Function.comp_def, Nat.zero_add, pow_one]
      have hsum : (word.map (fun i => (env i).cost)).sum ≤ word.length * C := by
        clear hwords
        induction word with
        | nil => simp
        | cons i word ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          exact (Nat.add_le_add (henv i) ih).trans_eq (by ring)
      have hlen : word.length + 1 ≤ B := hwords
      have hb := Nat.mul_le_mul_left C hlen
      nlinarith
    · intro F hF
      simp only [branching, BranchingWordHistory.pivotFormulas, List.not_mem_nil] at hF
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    have hstep : (step.formula.bind env).cost ≤ C * B := by
      apply (HistoryFormula.cost_bind_le step.formula env C hC henv).trans
      rw [HistoryPivotStep.formula_cost]
      exact Nat.mul_le_mul_left C hwords.1
    have hCB : 1 ≤ C * B := by simpa using Nat.mul_le_mul hC hB
    have hu : ∀ i, (BranchingWordHistory.updatedFormulas step env i).cost ≤ C * B := by
      intro i
      by_cases hi : i = step.target
      · subst i
        simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hstep
      · simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne hi] using
          (henv i).trans (by simpa using Nat.mul_le_mul_left C hB)
    obtain ⟨hll, hlp⟩ := hl t.2.1 hn.2.1 (C * B) hCB hwords.2.1
      (BranchingWordHistory.updatedFormulas step env) hu
    obtain ⟨hrl, hrp⟩ := hr t.2.2 hn.2.2 (C * B) hCB hwords.2.2
      (BranchingWordHistory.updatedFormulas step env) hu
    have heq : C * B * B ^ (n + 1) = C * B ^ (n + 1 + 1) := by rw [pow_succ]; ring
    have hroot : C * B ≤ C * B ^ (n + 1 + 1) := by
      apply Nat.mul_le_mul_left C
      calc
        B = B ^ 1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right hB (by omega)
    constructor
    · intro z hz
      change z ∈ (l.branching t.2.1 hn.2.1).formulaLeaves (BranchingWordHistory.updatedFormulas step env) ++
        ((r.branching t.2.2 hn.2.2).formulaLeaves (BranchingWordHistory.updatedFormulas step env)).map
          BranchingWordHistory.flipSigned at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (hll z hz).trans_eq heq
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact (hrl w hw).trans_eq heq
    · intro F hF
      change F ∈ step.formula.bind env ::
        ((l.branching t.2.1 hn.2.1).pivotFormulas (BranchingWordHistory.updatedFormulas step env) ++
          (r.branching t.2.2 hn.2.2).pivotFormulas (BranchingWordHistory.updatedFormulas step env)) at hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hstep.trans hroot
      · rcases List.mem_append.mp hF with hF | hF
        · exact (hlp F hF).trans_eq heq
        · exact (hrp F hF).trans_eq heq

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier factors and polynomial budgets of a concrete word history -/

namespace Ostmann

open scoped SchwartzMap FourierTransform ComplexConjugate Classical

/-- Rational reconstruction and the real polynomial specialization agree,
including away from the integral support. -/
theorem HistoryFormula.realValue_ratCast {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.realValue x = (F.value (fun i => (x i : ℚ)) : ℝ) := by
  have hr : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℝ) F.cleared.numerator
  have hq : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator
  simp only [realValue, value, ClearedHistoryValue.eval, ← hr, ← hq,
    Rat.cast_div, Rat.cast_intCast]

/-- The frequency-carrying leaves inherit the derived substitution budget. -/
theorem WordTransferTemplate.weightedLeaves_cost {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ z ∈ template.weightedLeaves t hn .prime, z.formula.cost ≤ B ^ (n + 1) := by
  intro z hz
  have hmem : z.toSignedFormula ∈ (template.branching t hn).formulaLeaves .prime := by
    rw [← template.weightedLeaves_projection t hn .prime]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa only [Nat.one_mul, WeightedWordLeaf.toSignedFormula] using
    (template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime
      (fun _ => le_rfl)).1 z.toSignedFormula hmem

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferPeriods
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common residue period derived from the actual branching frequencies -/

namespace Ostmann

open scoped Classical

theorem WordTransferTemplate.branching_frequencies_dvd {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (M : ℤ)
    (hfreq : ∀ s ∈ internalFrequencyList n t, s ∣ M)
    (env : σ → HistoryFormula σ)
    (henv : ∀ i s, s ∈ (env i).frequencies → s ∣ M) :
    (∀ z ∈ (template.branching t hn).formulaLeaves env, ∀ s ∈ z.2.frequencies, s ∣ M) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas env, ∀ s ∈ F.frequencies, s ∣ M) := by
  induction template generalizing env with
  | leaf word =>
    constructor
    · intro z hz
      simp only [branching, BranchingWordHistory.formulaLeaves, List.mem_singleton] at hz
      subst z
      apply HistoryFormula.frequencies_listProduct_dvd
      intro F hF
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
      exact henv i
    · intro F hF
      simp only [branching, BranchingWordHistory.pivotFormulas, List.not_mem_nil] at hF
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    have hs : step.s ∣ M := hfreq _ (List.mem_cons_self ..)
    have hhead := HistoryFormula.frequencies_bind_dvd step.formula env M
      (step.formula_frequencies_dvd M hs) henv
    have hu : ∀ i s, s ∈ (BranchingWordHistory.updatedFormulas step env i).frequencies → s ∣ M := by
      intro i s hi
      by_cases he : i = step.target
      · subst i
        exact hhead s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hi)
      · exact henv i s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne he] using hi)
    obtain ⟨hll, hlp⟩ := hl t.2.1 hn.2.1
      (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
    obtain ⟨hrl, hrp⟩ := hr t.2.2 hn.2.2
      (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
    constructor
    · intro z hz
      change z ∈ (l.branching t.2.1 hn.2.1).formulaLeaves (BranchingWordHistory.updatedFormulas step env) ++
        ((r.branching t.2.2 hn.2.2).formulaLeaves (BranchingWordHistory.updatedFormulas step env)).map
          BranchingWordHistory.flipSigned at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hll z hz
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact hrl w hw
    · intro F hF
      change F ∈ step.formula.bind env ::
        ((l.branching t.2.1 hn.2.1).pivotFormulas (BranchingWordHistory.updatedFormulas step env) ++
          (r.branching t.2.2 hn.2.2).pivotFormulas (BranchingWordHistory.updatedFormulas step env)) at hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hhead
      · rcases List.mem_append.mp hF with hF | hF
        · exact hlp F hF
        · exact hrp F hF

/-- This is the actual small-frequency modulus, not a new periodicity assumption. -/
theorem WordTransferTemplate.branching_denominator_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) (s : ℤ)
    (hs : s ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ)) :
    (∀ z ∈ (template.branching t hn).formulaLeaves .prime,
      z.2.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas .prime,
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) := by
  have hfreq := template.branching_frequencies_dvd t hn
    (historyFrequencyBase (internalFrequencyList n t) : ℤ)
    (fun s hs => frequency_dvd_historyFrequencyBase _ s hs) .prime
    (by intro i s hs; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hs)
  have hcost := template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime (fun _ => le_rfl)
  have hperiod (F : HistoryFormula σ) (hf : ∀ d ∈ F.frequencies,
      d ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ))
      (hc : F.cost ≤ B ^ (n + 1)) :
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
    simp only [historyFrequencyPeriod, Nat.cast_pow]
    exact (F.denominator_test_period _ s hf hs).trans
      (pow_dvd_pow _ (Nat.add_le_add_right (F.frequency_count_le_cost.trans hc) 1))
  constructor
  · intro z hz
    exact hperiod z.2 (hfreq.1 z hz) (by simpa only [Nat.one_mul] using hcost.1 z hz)
  · intro F hF
    exact hperiod F (hfreq.2 F hF) (by simpa only [Nat.one_mul] using hcost.2 F hF)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial support of one original arithmetic transfer node -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.smallDivisionTest_of_value {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.value (fun i => (x i : ℚ)) = y) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔ IsUnit (y : ZMod m) := by
  have he := F.cleared.integer_value_cleared x y hy
  simp only [smallDivisionTest, he, dvd_mul_right, true_and,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

theorem HistoryFormula.smallDivisionTest_iff {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔
      ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y ∧ IsUnit (y : ZMod m) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (F.integralAt_iff x).mpr h.1
    exact ⟨y, hy, (F.smallDivisionTest_of_value x y hy m).mp h⟩
  · rintro ⟨y, hy, hu⟩
    exact (F.smallDivisionTest_of_value x y hy m).mpr hu

/-- All original node conditions are represented: both coprimality tests,
integrality, positive bounded pivot, child-frequency bounds and strict gap. -/
theorem wordTransferGuard_iff {σ : Type*} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (s v w : ℤ) (hs : s ≠ 0)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (wordTransferGuard d s v w hs env).ValidAt a ↔
      ∃ P, ValidTransferNode (wordTransferSystem σ)
        ((WordTransferTemplate.node d l r).state x) s v w P := by
  let step := wordTransferStep d s v w hs
  let f := step.formula.bind env
  let g := HistoryFormula.listProduct (d.right.map env)
  let R := (d.right.map x).prod
  let L := (d.left.map x).prod
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  have hright : g.value (fun j => (a j : ℚ)) = (R : ℤ) := by
    have hh := BranchingWordHistory.wordFormula_value d.right env (fun j => (a j : ℚ))
      (fun i => (x i : ℤ)) (by intro i; simpa only [Int.cast_natCast] using henv i)
    have hc : (d.right.map (fun i => (x i : ℤ))).prod = (R : ℤ) := hcast d.right
    exact hh.trans (congrArg (fun z : ℤ => (z : ℚ)) hc)
  have hrightR : g.realValue a = (R : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hright, Rat.cast_intCast, Int.cast_natCast]
  have hf : f.value (fun j => (a j : ℚ)) = ((v * (R : ℤ) - w * (L : ℤ) : ℤ) : ℚ) / s := by
    rw [HistoryFormula.value_bind]
    have he : (fun i => (env i).value (fun j => (a j : ℚ))) = fun i => ((x i : ℤ) : ℚ) := by
      funext i; simpa only [Int.cast_natCast] using henv i
    rw [he, HistoryPivotStep.formula_value, wordTransferStep_numerator]
    rfl
  have hroot : IsUnit ((R : ℤ) : ZMod s.natAbs) ↔ IsCoprime s (R : ℤ) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  change (smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a f.cleared.numerator) f.cleared.denominator w.natAbs ∧
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.cleared.numerator) g.cleared.denominator s.natAbs ∧
    1 ≤ f.realValue a ∧ f.realValue a ≤ d.pivotBound ∧
    (2 * d.pivotBound * d.childBound : ℕ) < g.realValue a ∧
    v.natAbs ≤ d.childBound ∧ w.natAbs ≤ d.childBound) ↔ _
  rw [f.smallDivisionTest_iff, g.smallDivisionTest_of_value a (R : ℤ) hright,
    hrightR, hroot]
  constructor
  · rintro ⟨⟨Y, hY, hunit⟩, hcop, hlo, hhi, hgap, hv, hw⟩
    have hreal : f.realValue a = (Y : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hY, Rat.cast_intCast]
    rw [hreal] at hlo hhi
    have hY0 : 0 ≤ Y := by exact_mod_cast (show (0 : ℝ) ≤ Y by linarith)
    let P := Y.toNat
    have hPY : (P : ℤ) = Y := Int.toNat_of_nonneg hY0
    have hrel : v * (R : ℤ) - w * (L : ℤ) = s * P := by
      have he := (div_eq_iff (Int.cast_ne_zero.mpr hs)).mp (hf.symm.trans hY)
      have hi : v * (R : ℤ) - w * (L : ℤ) = Y * s := by exact_mod_cast he
      rw [hi, hPY, mul_comm]
    refine ⟨P, ⟨hs, hcop, hrel, ?_, ?_, hv, hw, ?_, ?_⟩⟩
    · have : (1 : ℤ) ≤ P := by rw [hPY]; exact_mod_cast hlo
      omega
    · have : (P : ℤ) ≤ d.pivotBound := by rw [hPY]; exact_mod_cast hhi
      exact_mod_cast this
    · exact_mod_cast hgap
    · have hu : IsUnit (P : ZMod w.natAbs) := by
        simpa only [← hPY, Int.cast_natCast] using hunit
      exact (ZMod.isUnit_iff_coprime P w.natAbs).mp hu
  · rintro ⟨P, hp⟩
    have hvalue : f.value (fun j => (a j : ℚ)) = (P : ℤ) := by
      have he : v * (R : ℤ) - w * (L : ℤ) = s * P := hp.relation
      rw [hf, he]
      push_cast
      exact mul_div_cancel_left₀ (P : ℚ) (Int.cast_ne_zero.mpr hs)
    have hreal : f.realValue a = (P : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hvalue, Rat.cast_intCast, Int.cast_natCast]
    refine ⟨⟨(P : ℤ), hvalue, ?_⟩, hp.root_unit, ?_, ?_, ?_, hp.left_bound, hp.right_bound⟩
    · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime P w.natAbs).mpr hp.pivot_unit
    · rw [hreal]; exact_mod_cast hp.pivot_pos
    · rw [hreal]; exact_mod_cast hp.pivot_bound
    · exact_mod_cast hp.range_gap

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All branching support tests are the original recursive arithmetic support -/

namespace Ostmann

open scoped Classical

theorem wordTransferUpdatedFormulas_nat {σ : Type*} {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ)
    (s v w : ℤ) (hs : s ≠ 0) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P)
    (env : σ → HistoryFormula σ) (a : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    ∀ i, (BranchingWordHistory.updatedFormulas (wordTransferStep d s v w hs) env i).value
      (fun j => (a j : ℚ)) = (Function.update x d.target P i : ℚ) := by
  have hu := BranchingWordHistory.updatedFormulas_value (wordTransferStep d s v w hs)
    env (fun j => (a j : ℚ)) (fun i => (x i : ℤ))
    (by intro i; simpa only [Int.cast_natCast] using henv i)
    (wordTransferStep_valid d l r x s v w P hp)
  rw [wordTransferStep_apply d l r x s v w P hp] at hu
  intro i
  simpa only [Int.cast_natCast] using hu i

/-- The list contains precisely the original support conditions at every
node, including the independent substitutions on the two child branches. -/
theorem WordTransferTemplate.guards_iff {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ)
    (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (∀ g ∈ template.guards t hn env, g.ValidAt a) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  induction template generalizing env x with
  | leaf word => simp [guards, ValidTransferHistory]
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    change (∀ g ∈ wordTransferGuard d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1 env ::
      (l.guards t.2.1 hn.2.1 (BranchingWordHistory.updatedFormulas step env) ++
        r.guards t.2.2 hn.2.2 (BranchingWordHistory.updatedFormulas step env)), g.ValidAt a) ↔ _
    simp only [List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq]
    rw [wordTransferGuard_iff d l r _ _ _ hn.1 env a x henv]
    constructor
    · rintro ⟨⟨P, hp⟩, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨P, hp, (hl _ _ _ _ hu).mp hL, (hr _ _ _ _ hu).mp hR⟩
    · rintro ⟨P, hp, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨⟨P, hp⟩, (hl _ _ _ _ hu).mpr hL, (hr _ _ _ _ hu).mpr hR⟩

theorem WordTransferTemplate.guards_pivots {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.guards t hn env).map WordTransferGuard.pivot =
      (template.branching t hn).pivotFormulas env := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [guards, branching, BranchingWordHistory.pivotFormulas,
      List.map_cons, List.map_append, hl, hr]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact one-variable polynomial form of each branching node guard -/

namespace Ostmann

open scoped Classical

theorem WordTransferGuard.gap_iff {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ)
    (h : g.residueAt x) :
    ((2 * g.pivotBound * g.childBound : ℕ) : ℝ) < g.rightProduct.realValue x ↔
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realValue x := by
  obtain ⟨y, hy, _⟩ := (g.rightProduct.smallDivisionTest_iff x g.root.natAbs).mp h.2
  have he : g.rightProduct.realValue x = (y : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hy, Rat.cast_intCast]
  rw [he]
  constructor
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by omega
    exact_mod_cast hj
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by omega
    exact_mod_cast hj

/-- Strict product gaps are closed polynomial inequalities because the
residue tests already enforce the exact integral word values. -/
theorem WordTransferGuard.validAt_polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    g.ValidAt (Function.update a coord z) ↔
      g.residueAt (Function.update a coord z) ∧ g.frequencyBounds ∧
        ∀ j, 0 ≤ (g.polynomials a coord j).eval (z : ℝ) := by
  have hrange : (∀ j, 0 ≤ (g.polynomials a coord j).eval (z : ℝ)) ↔
      1 ≤ g.pivot.realValue (Function.update a coord z) ∧
      g.pivot.realValue (Function.update a coord z) ≤ g.pivotBound ∧
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤
        g.rightProduct.realValue (Function.update a coord z) := by
    simp only [polynomials, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Fin.forall_fin_zero, Polynomial.eval_sub, Polynomial.eval_C,
      formulaPolynomial_eval_update, sub_nonneg, and_true]
  rw [hrange]
  constructor
  · rintro ⟨hp, hr, hlo, hhi, hgap, hv, hw⟩
    exact ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, (g.gap_iff _ ⟨hp, hr⟩).mp hgap⟩
  · rintro ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, hgap⟩
    exact ⟨hp, hr, hlo, hhi, (g.gap_iff _ ⟨hp, hr⟩).mpr hgap, hv, hw⟩

/-- Each node contributes three inequalities of derived polynomial degree. -/
theorem WordTransferGuard.polynomials_degree {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) :
    ∀ j, (g.polynomials a coord j).natDegree ≤ max g.pivot.cost g.rightProduct.cost := by
  intro j
  fin_cases j
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, zero_max]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_right _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formula costs and frequency denominators of all actual node guards -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.bind_listProduct {σ τ : Type*} (fs : List (HistoryFormula σ))
    (env : σ → HistoryFormula τ) :
    (HistoryFormula.listProduct fs).bind env = HistoryFormula.listProduct (fs.map (fun F => F.bind env)) := by
  induction fs with
  | nil => rfl
  | cons F fs ih => simp only [listProduct, bind, List.map_cons, ih]

theorem wordTransferGuard_pivot {σ : Type*} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (env : σ → HistoryFormula σ) :
    (wordTransferGuard d s v w hs env).pivot =
      .solve (HistoryFormula.listProduct (d.left.map env))
        (HistoryFormula.listProduct (d.right.map env)) v w s hs := by
  simp only [wordTransferGuard, HistoryPivotStep.formula, wordTransferStep, HistoryFormula.bind,
    HistoryFormula.bind_listProduct, List.map_map, Function.comp_def]

theorem WordTransferTemplate.guards_right_le_pivot {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ template.guards t hn env,
      g.rightProduct.cost ≤ g.pivot.cost ∧
      ∀ s ∈ g.rightProduct.frequencies, s ∈ g.pivot.frequencies := by
  induction template generalizing env with
  | leaf word => simp [guards]
  | @node n d l r hl hr =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [wordTransferGuard_pivot]
      constructor
      · change (HistoryFormula.listProduct (d.right.map env)).cost ≤
          (HistoryFormula.listProduct (d.left.map env)).cost +
            (HistoryFormula.listProduct (d.right.map env)).cost + 2
        omega
      · intro s hs
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hs)
    · rcases List.mem_append.mp hg with hg | hg
      · exact hl _ _ _ _ hg
      · exact hr _ _ _ _ hg

theorem WordTransferTemplate.guards_cost {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ g ∈ template.guards t hn .prime,
      max g.pivot.cost g.rightProduct.cost ≤ B ^ (n + 1) := by
  intro g hg
  have hp : g.pivot ∈ (template.branching t hn).pivotFormulas .prime := by
    rw [← template.guards_pivots]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have hc : g.pivot.cost ≤ B ^ (n + 1) := by
    simpa only [Nat.one_mul] using
      (template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime (fun _ => le_rfl)).2 _ hp
  exact max_le hc ((template.guards_right_le_pivot t hn .prime g hg).1.trans hc)

theorem WordTransferTemplate.guards_denominator_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) (s : ℤ)
    (hs : s ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ)) :
    ∀ g ∈ template.guards t hn .prime,
      g.pivot.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) ∧
      g.rightProduct.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
  intro g hg
  have hp : g.pivot ∈ (template.branching t hn).pivotFormulas .prime := by
    rw [← template.guards_pivots]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  constructor
  · exact (template.branching_denominator_period t hn B hB hwords s hs).2 _ hp
  · have hfreq := (template.branching_frequencies_dvd t hn
      (historyFrequencyBase (internalFrequencyList n t) : ℤ)
      (fun a ha => frequency_dvd_historyFrequencyBase _ a ha) .prime
      (by intro i a ha; simp only [HistoryFormula.frequencies, List.not_mem_nil] at ha)).2 _ hp
    have hright := (template.guards_right_le_pivot t hn .prime g hg).2
    have hc := (le_max_right g.pivot.cost g.rightProduct.cost).trans
      (template.guards_cost t hn B hB hwords g hg)
    simp only [historyFrequencyPeriod, Nat.cast_pow]
    exact (g.rightProduct.denominator_test_period _ s
      (fun a ha => hfreq a (hright a ha)) hs).trans
        (pow_dvd_pow _ (Nat.add_le_add_right (g.rightProduct.frequency_count_le_cost.trans hc) 1))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One residue gate and one polynomial partition for a complete guard family -/

namespace Ostmann

open scoped BigOperators Classical

theorem wordGuard_residue_iff {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) (x : σ → ℤ) :
    (∀ j, smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) x (wordGuardNumerators G j))
      (wordGuardDenominators G j) (wordGuardModuli G j)) ↔ ∀ i, (G i).residueAt x := by
  simp only [wordGuardNumerators, wordGuardDenominators, wordGuardModuli,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right, WordTransferGuard.residueAt,
    MvPolynomial.coe_eval₂Hom, forall_and]

theorem wordGuard_keep_iff {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) (z : ℝ) :
    wordGuardKeep G (polynomialSupportCode (wordGuardPolynomials G a coord) z) = true ↔
      (∀ i, (G i).frequencyBounds) ∧ ∀ i j, 0 ≤ ((G i).polynomials a coord j).eval z := by
  simp only [wordGuardKeep, Bool.and_eq_true, decide_eq_true_eq, polynomialSupportCode,
    wordGuardPolynomials, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨hf, h0, h1, h2⟩
    refine ⟨hf, fun i j => ?_⟩
    fin_cases j
    · exact h0 i
    · exact h1 i
    · exact h2 i
  · rintro ⟨hf, hp⟩
    exact ⟨hf, (fun i => hp i 0), (fun i => hp i 1), (fun i => hp i 2)⟩

/-- The full branching support is exactly the residue-and-polynomial gate
accepted by the one-sided estimate. -/
theorem wordGuard_family_support {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    (∀ i, (G i).ValidAt (Function.update a coord z)) ↔
      (∀ j, smallDivisionTest
        (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a coord z) (wordGuardNumerators G j))
        (wordGuardDenominators G j) (wordGuardModuli G j)) ∧
      wordGuardKeep G (polynomialSupportCode (wordGuardPolynomials G a coord) (z : ℝ)) = true := by
  rw [wordGuard_residue_iff, wordGuard_keep_iff]
  simp only [WordTransferGuard.validAt_polynomials, forall_and]

theorem wordGuard_family_degree {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) :
    (∑ j, (wordGuardPolynomials G a coord j).natDegree) ≤
      3 * ∑ i, max (G i).pivot.cost (G i).rightProduct.cost := by
  simp only [wordGuardPolynomials, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have h0 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 0)
  have h1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 1)
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 2)
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

theorem frequencyRoot_mem_allFrequencyList (n : ℕ) (t : FrequencyTree ℤ n) :
    frequencyRoot n t ∈ allFrequencyList n t := by
  cases n <;> simp [allFrequencyList, frequencyRoot]

theorem internalFrequencyList_subset_all (n : ℕ) (t : FrequencyTree ℤ n) :
    ∀ s ∈ internalFrequencyList n t, s ∈ allFrequencyList n t := by
  induction n with
  | zero => simp [internalFrequencyList]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_cons_self ..
    · rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ s hs))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ s hs))

theorem WordTransferTemplate.guards_frequencies_mem {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ template.guards t hn env,
      g.root ∈ allFrequencyList n t ∧ g.right ∈ allFrequencyList n t := by
  induction template generalizing env with
  | leaf word => simp [guards]
  | @node n d l r hl hr =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _
        (List.mem_append_right _ (frequencyRoot_mem_allFrequencyList n t.2.2))⟩
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨hs, hw⟩ := hl _ _ _ g hg
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hs),
          List.mem_cons_of_mem _ (List.mem_append_left _ hw)⟩
      · obtain ⟨hs, hw⟩ := hr _ _ _ g hg
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hs),
          List.mem_cons_of_mem _ (List.mem_append_right _ hw)⟩

theorem wordTransferFullPeriod_pos (n : ℕ) (t : FrequencyTree ℤ n) (B : ℕ)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) : 0 < wordTransferFullPeriod n t B := by
  exact Nat.mul_pos (historyFrequencyPeriod_pos _ _
    (fun s hs => hz s (internalFrequencyList_subset_all n t s hs)))
    (historyFrequencyBase_pos _ hz)

/-- Both units at every original node are periodic in this explicitly
constructed modulus, including units modulo leaf frequencies. -/
theorem WordTransferTemplate.guards_full_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ g ∈ template.guards t hn .prime,
      g.pivot.cleared.denominator * g.right.natAbs ∣ (wordTransferFullPeriod n t B : ℤ) ∧
      g.rightProduct.cleared.denominator * g.root.natAbs ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hd := template.guards_denominator_period t hn B hB hwords 1 (one_dvd _) g hg
  simp only [mul_one] at hd
  have hf := template.guards_frequencies_mem t hn .prime g hg
  have hmod (s : ℤ) (hs : s ∈ allFrequencyList n t) :
      (s.natAbs : ℤ) ∣ (historyFrequencyBase (allFrequencyList n t) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Int.dvd_natCast.mp (frequency_dvd_historyFrequencyBase _ s hs))
  constructor
  · simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd.1 (hmod _ hf.2)
  · simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd.2 (hmod _ hf.1)

theorem prime_coprime_wordTransferFullPeriod (n : ℕ) (t : FrequencyTree ℤ n) (B p : ℕ)
    (hp : p.Prime) (hsmall : ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p) :
    p.Coprime (wordTransferFullPeriod n t B) := by
  have hi := prime_coprime_historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) p hp
    (fun s hs => hsmall s (internalFrequencyList_subset_all n t s hs))
  have ha := prime_coprime_historyFrequencyPeriod (allFrequencyList n t) 1 p hp hsmall
  simp only [historyFrequencyPeriod, pow_one] at ha
  exact hi.mul_right ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferArrays
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed arrays of the actual branching guards and Fourier leaves -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*} {n : ℕ}

theorem guardAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n - 1)) :
    template.guardAt t hn i ∈ template.guards t hn .prime := List.getElem_mem _

theorem leafAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) :
    template.leafAt t hn i ∈ template.weightedLeaves t hn .prime := List.getElem_mem _

theorem guardAt_valid_iff (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (x : σ → ℕ) :
    (∀ i, (template.guardAt t hn i).ValidAt (fun j => (x j : ℤ))) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  rw [← template.guards_iff t hn .prime (fun j => (x j : ℤ)) x
    (by intro i; simp only [HistoryFormula.value_prime, Int.cast_natCast])]
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hib : i < 2 ^ n - 1 := by rwa [template.guards_length] at hi
    exact h ⟨i, hib⟩
  · intro h i
    exact h _ (template.guardAt_mem t hn i)

theorem guardAt_cost (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B)
    (i : Fin (2 ^ n - 1)) :
    max (template.guardAt t hn i).pivot.cost (template.guardAt t hn i).rightProduct.cost ≤ B ^ (n + 1) :=
  template.guards_cost t hn B hB hwords _ (template.guardAt_mem t hn i)

theorem leafAt_cost (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B)
    (i : Fin (2 ^ n)) : (template.leafAt t hn i).formula.cost ≤ B ^ (n + 1) :=
  template.weightedLeaves_cost t hn B hB hwords _ (template.leafAt_mem t hn i)

theorem guardAt_denominators_ne_zero (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) :
    ∀ i, wordGuardDenominators (template.guardAt t hn) i ≠ 0 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [wordGuardDenominators, Fin.append_left] using
      (template.guardAt t hn j).pivot.cleared.denominator_ne_zero
  · simpa only [wordGuardDenominators, Fin.append_right] using
      (template.guardAt t hn j).rightProduct.cleared.denominator_ne_zero

theorem guardAt_full_period (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ i, wordGuardDenominators (template.guardAt t hn) i *
      (wordGuardModuli (template.guardAt t hn) i : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [wordGuardDenominators, wordGuardModuli, Fin.append_left] using
      (template.guards_full_period t hn B hB hwords _ (template.guardAt_mem t hn j)).1
  · simpa only [wordGuardDenominators, wordGuardModuli, Fin.append_right] using
      (template.guards_full_period t hn B hB hwords _ (template.guardAt_mem t hn j)).2

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed coefficient for a branching word history -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

namespace WordFourierParameters

variable {σ : Type*} {n : ℕ}

/-- No representation hypothesis is needed: these are the exact polynomial
and residue gates constructed from the original branching data. -/
theorem coefficient_local (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.coefficient template t hn (Function.update a coord z) =
      guardedHistoryAmplitude (wordGuardNumerators (template.guardAt t hn))
        (wordGuardDenominators (template.guardAt t hn)) (wordGuardModuli (template.guardAt t hn))
        a coord (p.factors template t hn a coord) (p.polynomials template t hn a coord)
        (keep template t hn) z := by
  have hs := wordGuard_family_support (template.guardAt t hn) a coord z
  simp only [coefficient, factors, polynomials, keep, guardedHistoryAmplitude,
    fullHistoryAmplitude_exact, formulaFourier_polynomial_eval]
  have he : (∏ j, ((formulaFourierFactors (fun i => (template.leafAt t hn i).formula)
      (fun i => (a i : ℝ)) coord p.scale p.profile (p.frequency template t hn) p.lower p.upper
      p.lower_one p.lower_upper) j).profile
        ((template.leafAt t hn j).formula.realValue (Function.update a coord z) / p.scale j)) =
      ∏ j, normalizedFourierProfile p.profile (p.frequency template t hn j)
        ((template.leafAt t hn j).formula.realValue (Function.update a coord z) / p.scale j) := rfl
  rw [he]
  simp only [formulaFourierFactors, historyFourierFactor, fourierPolynomialFactor]
  split_ifs <;> simp_all

theorem factors_budget (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    smoothPolynomialBudget (p.factors template t hn a coord) = p.budget template t hn := rfl

theorem budget_nonneg (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    0 ≤ p.budget template t hn :=
  formulaFourierBudget_nonneg _ _ _ _ p.lower_upper

/-- The complete partition complexity is polynomial in the word size for
fixed depth, including every original support inequality. -/
theorem complexity_bound (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    polynomialWeightComplexity (p.factors template t hn a coord) (p.polynomials template t hn a coord) ≤
      (3 * 2 ^ n + 3 * (2 ^ n - 1)) * B ^ (n + 1) := by
  have hl : (∑ i, ((p.factors template t hn a coord) i).polynomial.natDegree) ≤
      2 ^ n * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _i : Fin (2 ^ n), B ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (formulaFourierFactors_degree _ _ _ _ _ _ _ _ _ _ i).trans
          (template.leafAt_cost t hn B hB hwords i)
      _ = _ := by simp
  have hg : (∑ i, max (template.guardAt t hn i).pivot.cost
      (template.guardAt t hn i).rightProduct.cost) ≤ (2 ^ n - 1) * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _i : Fin (2 ^ n - 1), B ^ (n + 1) :=
        Finset.sum_le_sum fun i _ => template.guardAt_cost t hn B hB hwords i
      _ = _ := by simp
  have hguard := wordGuard_family_degree (template.guardAt t hn) a coord
  apply (fullHistoryPolynomials_complexity (p.factors template t hn a coord)
    (wordGuardPolynomials (template.guardAt t hn) a coord)).trans
  nlinarith

end WordFourierParameters
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedGraphQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph quotient under an actual matching of the prime variables -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem finiteEdgeWeight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (E : J → J → ℕ → ℕ → ℂ) (ν : J → ℕ → ℂ) (p : J → ℕ) :
    finiteEdgeWeight (fun i j => E (e i) (e j)) (fun i => ν (e i)) (fun i => p (e i)) =
      finiteEdgeWeight E ν p := by
  unfold finiteEdgeWeight
  calc
    _ = ∏ i, ν (e i) (p (e i)) * ∏ j, E (e i) j (p (e i)) (p j) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [e.prod_comp (fun j => E (e i) j (p (e i)) (p j))]
    _ = _ := e.prod_comp (fun i => ν i (p i) * ∏ j, E i j (p i) (p j))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TwoVertexReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isolating two selected actual vertices without changing a graph product -/

namespace Ostmann

open scoped Classical

/-- Reindexing is exact even when the unary factors contain role membership
or counterpart-prior restrictions. -/
theorem finiteEdgeWeight_two_vertices {V : Type*} [Fintype V] (a b : V) (hab : a ≠ b)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (ν : V → ℕ → ℂ) (p : Bool ⊕ OtherVertices a b → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge (fun i => χ (twoVertexEquiv a b hab i))
        (fun i j => graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j)))
      (fun i => ν (twoVertexEquiv a b hab i)) p =
    finiteEdgeWeight (dirichletGraphEdge χ graph) ν (fun v => p ((twoVertexEquiv a b hab).symm v)) := by
  classical
  have h := finiteEdgeWeight_equiv (twoVertexEquiv a b hab)
    (dirichletGraphEdge χ graph) ν (fun v => p ((twoVertexEquiv a b hab).symm v))
  have hp : (fun i => p ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab i))) = p := by
    funext i
    rw [Equiv.symm_apply_apply]
  change finiteEdgeWeight
    (fun i j => dirichletGraphEdge χ graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j))
    (fun i => ν (twoVertexEquiv a b hab i))
    (fun i => p ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab i))) = _ at h
  rw [hp] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TwoCoordinatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the selected pair inside the unchanged original product prior -/

namespace Ostmann

open scoped BigOperators Classical

theorem twoCoordinateAssignment_update_long {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p p' : A) :
    Function.update (twoCoordinateAssignment a b hab outside q p) b p' =
      twoCoordinateAssignment a b hab outside q p' := by
  funext v
  obtain ⟨w, rfl⟩ := (twoVertexEquiv a b hab).surjective v
  cases w with
  | inl t =>
    cases t
    · simp only [twoVertexEquiv_long, Function.update_self, twoCoordinateAssignment_long]
    · simp only [twoVertexEquiv_short, Function.update_of_ne hab, twoCoordinateAssignment_short]
  | inr v =>
    simp only [twoVertexEquiv_other, Function.update_of_ne v.property.2, twoCoordinateAssignment_other]

theorem productPrior_twoCoordinates {V A : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ)
    (outside : OtherVertices a b → A) (q p : A) :
    (∏ v, μ v (twoCoordinateAssignment a b hab outside q p v)) =
      (∏ v : OtherVertices a b, μ v (outside v)) * (μ a q * μ b p) := by
  rw [← (twoVertexEquiv a b hab).prod_comp (fun v => μ v (twoCoordinateAssignment a b hab outside q p v))]
  rw [Fintype.prod_sum_type, Fintype.prod_bool]
  simp only [twoVertexEquiv_short, twoVertexEquiv_long, twoVertexEquiv_other,
    twoCoordinateAssignment_short, twoCoordinateAssignment_long, twoCoordinateAssignment_other]
  ring

theorem sum_productPrior_twoCoordinates {V A : Type*} [Fintype V] [Fintype A]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ) (F : (V → A) → ℂ) :
    (∑ x, ((∏ v, μ v (x v) : ℝ) : ℂ) * F x) =
      ∑ outside : OtherVertices a b → A,
        ((∏ v : OtherVertices a b, μ v (outside v) : ℝ) : ℂ) *
          ∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
            F (twoCoordinateAssignment a b hab outside q p) := by
  rw [← (twoCoordinateEquiv (A := A) a b hab).sum_comp
    (fun x => ((∏ v, μ v (x v) : ℝ) : ℂ) * F x)]
  simp only [Fintype.sum_prod_type, twoCoordinateEquiv]
  apply Finset.sum_congr rfl
  intro outside _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  change ((∏ v, μ v (twoCoordinateAssignment a b hab outside q p v) : ℝ) : ℂ) *
    F (twoCoordinateAssignment a b hab outside q p) = _
  rw [productPrior_twoCoordinates, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- The section bound is averaged under every remaining original coordinate
prior. All range, distinctness and history restrictions stay inside `F`. -/
theorem original_prior_twoCoordinate_bound {V A : Type*} [Fintype V] [Fintype A]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ)
    (hμ : ∀ v x, 0 ≤ μ v x) (hmass : ∀ v, ∑ x, μ v x ≤ 1)
    (F : (V → A) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices a b → A,
      ‖∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
        F (twoCoordinateAssignment a b hab outside q p)‖ ≤ δ) :
    ‖∑ x, ((∏ v, μ v (x v) : ℝ) : ℂ) * F x‖ ≤ δ := by
  have hprod (outside : OtherVertices a b → A) : 0 ≤ ∏ v : OtherVertices a b, μ v (outside v) :=
    Finset.prod_nonneg fun v _ => hμ v _
  have hm : (∑ outside : OtherVertices a b → A, ∏ v : OtherVertices a b, μ v (outside v)) ≤ 1 := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_le_one (fun v _ => Finset.sum_nonneg fun x _ => hμ v x)
      (fun v _ => hmass v)
  rw [sum_productPrior_twoCoordinates a b hab μ F]
  calc
    _ ≤ ∑ outside : OtherVertices a b → A,
        ‖((∏ v : OtherVertices a b, μ v (outside v) : ℝ) : ℂ) *
          ∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
            F (twoCoordinateAssignment a b hab outside q p)‖ := norm_sum_le _ _
    _ ≤ ∑ outside : OtherVertices a b → A, (∏ v : OtherVertices a b, μ v (outside v)) * δ := by
      apply Finset.sum_le_sum
      intro outside _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hprod outside)]
      exact mul_le_mul_of_nonneg_left (hsection outside) (hprod outside)
    _ = (∑ outside : OtherVertices a b → A, ∏ v : OtherVertices a b, μ v (outside v)) * δ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hm hδ
    _ = δ := one_mul _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalHarmonicPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-prime estimate inside the original role-dependent harmonic law -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_restrict_sum (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * F q := by
  rw [primeSubsetPrior_mean P Q hQP F, primeSubsetPrior_mean Q Q (by rfl) F]

theorem twoCoordinateAssignment_map {V A B : Type*} (a b : V) (hab : a ≠ b)
    (f : A → B) (outside : OtherVertices a b → A) (q p : A) :
    (fun v => f (twoCoordinateAssignment a b hab outside q p v)) =
      twoCoordinateAssignment a b hab (fun v => f (outside v)) (f q) (f p) := by
  funext v
  unfold twoCoordinateAssignment
  cases (twoVertexEquiv a b hab).symm v with
  | inl t => cases t <;> rfl
  | inr v => rfl

/-- A uniform long/short-prime estimate is inserted in the complete original
expectation. The remaining coordinates retain their individual role priors. -/
theorem original_harmonic_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (P : Finset ℕ) (Q : V → Finset ℕ)
    (hQP : ∀ v, Q v ⊆ P) (hQmass : ∀ v, (∑ q ∈ Q v, (q : ℝ)⁻¹) ≠ 0)
    (F : (V → ℕ) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices a b → P,
      ‖∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment a b hab (fun v => (outside v : ℕ)) (q : ℕ) (p : ℕ))‖ ≤ δ) :
    ‖∑ x : V → P, ((∏ v, primeSubsetPrior P (Q v) (x v) : ℝ) : ℂ) *
      F (fun v => (x v : ℕ))‖ ≤ δ := by
  apply original_prior_twoCoordinate_bound a b hab (fun v => primeSubsetPrior P (Q v))
    (fun v p => primeSubsetPrior_nonneg P (Q v) p)
    (fun v => (primeSubsetPrior_mass P (Q v) (hQP v) (hQmass v)).le)
    (fun x => F (fun v => (x v : ℕ))) δ hδ
  intro outside
  simp_rw [twoCoordinateAssignment_map]
  let outside' : OtherVertices a b → ℕ := fun v => (outside v : ℕ)
  have hp (q : ℕ) :
      (∑ p : P, (primeSubsetPrior P (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' q (p : ℕ))) =
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' q (p : ℕ)) :=
    primeSubsetPrior_restrict_sum P (Q b) (hQP b)
      (fun p : ℕ => F (twoCoordinateAssignment a b hab outside' q p))
  change ‖∑ q : P, (primeSubsetPrior P (Q a) q : ℂ) *
    ∑ p : P, (primeSubsetPrior P (Q b) p : ℂ) *
      F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ))‖ ≤ δ
  simp_rw [hp]
  rw [primeSubsetPrior_restrict_sum P (Q a) (hQP a)
    (fun q : ℕ => ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
      F (twoCoordinateAssignment a b hab outside' q (p : ℕ)))]
  have he : (∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ))) =
      ∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment a b hab outside' (q : ℕ) (p : ℕ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  exact hsection outside

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicBlockRecombination
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the dyadic pieces of an original harmonic prime prior -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_raw_of_mean_bound (S : Finset ℕ) (F : ℕ → ℂ) (C : ℝ)
    (hm : 0 < ∑ p ∈ S, (p : ℝ)⁻¹)
    (h : ‖∑ p : S, (primeSubsetPrior S S p : ℂ) * F p‖ ^ 2 ≤
      (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ * C) :
    ‖∑ p ∈ S, ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤ (∑ p ∈ S, (p : ℝ)⁻¹) * C := by
  rw [primeSubsetPrior_mean S S (Finset.Subset.refl _) F, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg hm.le, mul_pow] at h
  have ht := mul_le_mul_of_nonneg_left h (sq_nonneg (∑ p ∈ S, (p : ℝ)⁻¹))
  have h₁ : (∑ p ∈ S, (p : ℝ)⁻¹) ^ 2 * (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm.ne', one_pow]
  have h₂ : (∑ p ∈ S, (p : ℝ)⁻¹) ^ 2 * (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹ =
      ∑ p ∈ S, (p : ℝ)⁻¹ := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hm.ne', mul_one]
  simpa only [← mul_assoc, h₁, h₂, one_mul] using ht

/-- The cost is the number of dyadic pieces, while the normalizer is the
original total harmonic mass. No lower bound for an individual piece is used. -/
theorem harmonic_partition_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) (key : ℕ → I) (F : ℕ → ℂ) (C : ℝ)
    (hm : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hlocal : ∀ i, ‖∑ p ∈ P.filter (fun p => key p = i), ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤
      (∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) * C) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) * F p‖ ^ 2 ≤
      (Fintype.card I : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ * C := by
  let z (i : I) : ℂ := ∑ p ∈ P.filter (fun p => key p = i), ((p : ℝ)⁻¹ : ℂ) * F p
  have hz : (∑ i, z i) = ∑ p ∈ P, ((p : ℝ)⁻¹ : ℂ) * F p :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hmasses : (∑ i : I, ∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) =
      ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hsq : ‖∑ i, z i‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
    have hn := norm_sum_le (Finset.univ : Finset I) z
    have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
      (fun _ => (1 : ℝ)) (fun i => ‖z i‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  have hraw : ‖∑ p ∈ P, ((p : ℝ)⁻¹ : ℂ) * F p‖ ^ 2 ≤
      (Fintype.card I : ℝ) * ((∑ p ∈ P, (p : ℝ)⁻¹) * C) := by
    rw [← hz]
    apply hsq.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ i : I, (∑ p ∈ P.filter (fun p => key p = i), (p : ℝ)⁻¹) * C :=
        Finset.sum_le_sum fun i _ => hlocal i
      _ = _ := by rw [← Finset.sum_mul, hmasses]
  rw [primeSubsetPrior_mean P P (Finset.Subset.refl _) F, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg hm.le, mul_pow]
  have hh := mul_le_mul_of_nonneg_left hraw (sq_nonneg (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicSupportedHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported one-sided estimate over the entire long-prime range -/

namespace Ostmann

open scoped BigOperators Classical

theorem boundedDyadicIndex_eq (E p : ℕ) (hp : p ≤ E) :
    (boundedDyadicIndex E p : ℕ) = Nat.log 2 p :=
  min_eq_left (Nat.log_mono_right hp)

theorem dyadic_progression_padding (a M : ℕ) (ha : 0 < a) (hM : 0 < M) (hMa : M ≤ a) :
    a < (a / M + 1) * M ∧ (((a / M + 1) * M : ℕ) : ℝ) / a ≤ 2 := by
  have hdiv := Nat.mod_add_div a M
  have hmod := Nat.mod_lt a hM
  have hmul := Nat.div_mul_le_self a M
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a)).mpr
    have hn : (a / M + 1) * M ≤ 2 * a := by nlinarith
    exact_mod_cast hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicGuardedHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full long-prime range with all arithmetic polynomial guards -/

namespace Ostmann

open scoped BigOperators Classical

/-- Every sharp support condition is retained. The loss for all long-prime
dyadic pieces is only their count, and the original normalizing mass remains. -/
theorem dyadic_guarded_history_bound {σ I : Type*} [Fintype I] {n t : ℕ}
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (A E M : ℕ) [NeZero M] (hA : 0 < A) (hMA : M ≤ A)
    (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : ℕ → ℂ) (V : Q → ℂ) (hU : ∀ p ∈ P, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ)))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  classical
  let G (p : ℕ) : ℂ := U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
    (χ q (p : ZMod (q : ℕ)) *
      guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) p)
  have hc := harmonic_partition_bound P (boundedDyadicIndex E) G
      (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
      hPmass
  simp only [Fintype.card_fin] at hc
  apply hc
  intro j
  let S : Finset ℕ := @Finset.filter ℕ (fun p => boundedDyadicIndex E p = j)
    (fun _ => Classical.propDecidable _) P
  have hmem (p : ℕ) : p ∈ S ↔ p ∈ P ∧ boundedDyadicIndex E p = j := by
    simp only [S, Finset.mem_filter]
  change ‖∑ p ∈ S, ((p : ℝ)⁻¹ : ℂ) * G p‖ ^ 2 ≤
    (∑ p ∈ S, (p : ℝ)⁻¹) *
      (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
  by_cases hS : S.Nonempty
  · have hpos (p : ℕ) (hp : p ∈ S) : 0 < p := by
      have := hlow p ((hmem p).mp hp).1
      omega
    have hm : 0 < ∑ p ∈ S, (p : ℝ)⁻¹ := by
      apply Finset.sum_pos (fun p hp => inv_pos.mpr (by exact_mod_cast hpos p hp)) hS
    let a : ℕ := 2 ^ (j : ℕ)
    have ha : 0 < a := pow_pos (by norm_num) _
    have hr (p : ℕ) (hp : p ∈ S) : a ≤ p ∧ p < 2 * a := by
      have hmp := (hmem p).mp hp
      have he : Nat.log 2 p = (j : ℕ) := by
        rw [← boundedDyadicIndex_eq E p (hhigh p hmp.1), hmp.2]
      constructor
      · simpa only [he] using Nat.pow_log_le_self 2 (Nat.ne_of_gt (hpos p hp))
      · simpa only [he, pow_succ, mul_comm] using
          Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
    have hAa : A ≤ a := by
      obtain ⟨p, hp⟩ := hS
      have := (hr p hp).2
      have := hlow p ((hmem p).mp hp).1
      omega
    have hpad := dyadic_progression_padding a M ha (NeZero.pos M) (hMA.trans hAa)
    have hlocal := harmonic_guarded_history_bound S Q hprime χ hnonprincipal
      a M (a / M + 1) ha hM (fun p hp => (hr p hp).1)
      (fun p hp => by have := (hr p hp).2; omega)
      b hb hbQ hm hQmass N d s fixed coord hd hdiv F H keep B R Bq hB hbudget hcomplexity hBq
      (fun p => U p) V (fun p => hU p ((hmem p).mp p.property).1) hV
    apply harmonic_raw_of_mean_bound S G _ hm
    apply hlocal.trans
    have hi : (a : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast hA) (by exact_mod_cast hAa)
    gcongr
    exact hpad.2
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicGuardedGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-range one-sided cancellation for the supported quotient graph -/

namespace Ostmann

open scoped BigOperators Classical

theorem dyadic_guarded_graph_bound {J σ I : Type*} [Fintype J] [Fintype I] {n t : ℕ}
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E M : ℕ) [NeZero M] (hA : 0 < A) (hMA : M ≤ A)
    (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have hQne : Q.Nonempty := by
    by_contra h
    have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hQmass
    exact (lt_irrefl (0 : ℝ)) hQmass
  obtain ⟨q₀, hq₀⟩ := hQne
  have hforward : graph (.inl true) (.inl false) ≠ 0 := by
    intro h
    have hh := hnonprincipal q₀ hq₀
    simp only [h, zpow_zero, ne_eq, not_true_eq_false] at hh
  obtain ⟨U, V, hU, hV, hfactor⟩ := dirichlet_one_sided_graph_factorization
    χ graph unary outside hunary hself hreverse hforward
  have hbound := dyadic_guarded_history_bound P Q hprime
    (fun q => χ (.inl true) q ^ graph (.inl true) (.inl false))
    (fun q => hnonprincipal q q.property) A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
    N d s fixed coord hd hdiv F H keep B R Bq hB hbudget hcomplexity hBq U (fun q => V q)
    (fun p _ => hU p) (fun q => hV q)
  have he : (∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))) =
      ∑ p : P, (primeSubsetPrior P P p : ℂ) *
        (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
          ((χ (.inl true) q ^ graph (.inl true) (.inl false)) ((p : ℕ) : ZMod (q : ℕ)) *
            guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))) := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hfactor]
    ring
  rw [he]
  exact hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedWordPairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed prime-word coefficient under the original product law -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem expandedPrimeValues_update {V : Type*} [DecidableEq V]
    (n : ℕ) (x : V → ℤ) (v : V) (z : ℤ) :
    expandedPrimeValues n (Function.update x v z) =
      Function.update (expandedPrimeValues n x) (.inl v) z := by
  funext i
  cases i with
  | inl w =>
    by_cases hw : w = v <;> simp [expandedPrimeValues, hw]
  | inr w => simp [expandedPrimeValues]

theorem expandedPrimeValues_twoCoordinate {V : Type*} (a b : V) (hab : a ≠ b)
    (n : ℕ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    expandedPrimeValues n
      (fun i => ((twoCoordinateAssignment a b hab outside q p i : ℕ) : ℤ)) =
      wordCoordinateUpdate (expandedPrimeValues n
        (twoCoordinateAssignment a b hab (fun i => (outside i : ℤ)) q 0)) (.inl b) p := by
  rw [twoCoordinateAssignment_map,
    ← twoCoordinateAssignment_update_long a b hab (fun i => (outside i : ℤ)) q 0 p]
  rw [expandedPrimeValues_update]
  funext i
  by_cases hi : i = Sum.inl b <;> simp only [wordCoordinateUpdate, Function.update_apply, hi, ite_true, if_true, ite_false, if_false]

theorem finiteEdgeWeight_twoCoordinate_reindex {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    finiteEdgeWeight (dirichletGraphEdge χ graph) unary
        (twoCoordinateAssignment a b hab outside q p) =
      finiteEdgeWeight
        (dirichletGraphEdge (fun i => χ (twoVertexEquiv a b hab i))
          (fun i j => graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j)))
        (fun i => unary (twoVertexEquiv a b hab i)) (twoVertexLabels outside q p) := by
  rw [finiteEdgeWeight_two_vertices]
  congr 1
  funext i
  unfold twoCoordinateAssignment
  cases (twoVertexEquiv a b hab).symm i with
  | inl v => cases v <;> rfl
  | inr v => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedHistoryFormula
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # History formulas on the original independent prime variables

Internal pivot addresses are initialized to one. Substitution removes them
from the polynomial variable type before the prime-divisibility estimate. -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

theorem originalPrimes_value {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (x : V → ℤ) :
    F.originalPrimes.value (fun i => (x i : ℚ)) =
      F.value (fun i => (expandedPrimeValues n x i : ℚ)) := by
  rw [originalPrimes, value_bind]
  congr 1
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, value_prime,
    value_external, expandedPrimeValues, Int.cast_one]

theorem originalPrimes_cost {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.cost = F.cost := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ (· + ·) ihf ihg
  | solve f g v w s hs ihf ihg =>
    change f.originalPrimes.cost + g.originalPrimes.cost + 2 = f.cost + g.cost + 2
    rw [ihf, ihg]

theorem originalPrimes_frequencies {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.frequencies = F.frequencies := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ List.append ihf ihg
  | solve f g v w s hs ihf ihg => exact congrArg (s :: ·) (congrArg₂ List.append ihf ihg)

theorem originalPrimes_denominator {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, originalPrimes_frequencies,
    denominator_eq_frequency_product]

theorem originalPrimes_inputs {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (R : ℝ) (hR : 1 ≤ R)
    (hF : F.InputsBounded R) : F.originalPrimes.InputsBounded R := by
  apply inputsBounded_bind F _ R hF
  intro i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, InputsBounded, Int.cast_one, abs_one]
  exact hR

end HistoryFormula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructedCoprimalityBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large-prime support after reconstruction

An identically divisible reconstructed numerator has empty valid support.
Otherwise the original independent prime priors give the polynomial error.
No conditioning of those priors is used in either case. -/

namespace Ostmann

open scoped BigOperators Classical

theorem reconstructed_coprimality_bound
    {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (Fin (n + 1))) (coord : I → Fin (n + 1))
    (y : I → (Fin (n + 1) → A) → ℤ)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (Fin (n + 1) → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hvalid : ∀ x, W x ≠ 0 → ∀ j,
      (F j).value (fun i => (prime (x i) : ℚ)) = y j x ∧
      ¬prime (x (coord j)) ∣ (F j).cleared.denominator.natAbs)
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)‖ ≤
      δ + B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  by_cases hz : ∀ j, zeroHistoryVariable (coord j) (F j).cleared.numerator ≠ 0
  · have hgate (x : Fin (n + 1) → A) :
        (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0) =
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
          then W x else 0) := by
      by_cases hw : W x = 0
      · simp only [hw, ite_self]
      · have hi (j : I) := (F j).cleared.prime_coprime_integer_value
          (fun i => (prime (x i) : ℤ)) (prime (x (coord j))) (hprime _)
          (hvalid x hw j).2 (y j x) (by
            simpa only [HistoryFormula.value, Int.cast_natCast] using (hvalid x hw j).1)
        have hg : (∀ j, (prime (x (coord j))).Coprime (y j x).natAbs) ↔
            (∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs) :=
          forall_congr' hi
        simp only [hg]
    simp_rw [hgate]
    let S := ∑ x, (productPrior μ x : ℂ) * W x
    have he := formula_coprimality_removal prime hpInj hprime F coord hz μ hμ hmass
      α V R β hα hβ hV hR hmax hpmax hlower hupper hinputs W B hB hW
    calc
      _ = ‖((∑ x, (productPrior μ x : ℂ) *
            (if ∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
              then W x else 0)) - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖(∑ x, (productPrior μ x : ℂ) *
            (if ∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
              then W x else 0)) - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) + δ :=
        add_le_add he hcancel
      _ = _ := add_comm _ _
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hj0 : zeroHistoryVariable (coord j) (F j).cleared.numerator = 0 :=
      Classical.not_not.mp hj
    have hzero (x : Fin (n + 1) → A) :
        (if ∀ k, (prime (x (coord k))).Coprime (y k x).natAbs then W x else 0) = 0 := by
      split_ifs with hg
      · by_contra hw
        have hn := zero_cleared_history_support (F j).cleared.numerator (coord j) hj0
          (fun i => (prime (x i) : ℤ)) (prime (x (coord j))) (hprime _) rfl
          (F j).cleared.denominator (y j x)
          ((F j).cleared.integer_value_cleared _ _ (by
            simpa only [HistoryFormula.value, Int.cast_natCast] using (hvalid x hw j).1))
          (hvalid x hw j).2
        exact hn (hg j)
      · rfl
    simp_rw [hzero, mul_zero]
    rw [Finset.sum_const_zero, norm_zero]
    have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    exact add_nonneg hδ (mul_nonneg hB (Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg hα
        (mul_nonneg (div_nonneg hlog hV.le) (hβ j)))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity of all replayed intermediate range tests -/

namespace Ostmann

open scoped Classical

theorem WordRange.toHistory_cost {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (B C : ℕ) (hC : 1 ≤ C)
    (hr : r.word.length + 1 ≤ B) (henv : ∀ i, (env i).cost ≤ C) :
    (r.toHistory env).formula.cost ≤ C * B := by
  change (HistoryFormula.listProduct (r.word.map env)).cost ≤ C * B
  rw [HistoryFormula.cost_listProduct, List.map_map]
  have hs : (r.word.map (fun i => (env i).cost)).sum ≤ r.word.length * C := by
    induction r.word with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [henv i]
  have hb := Nat.mul_le_mul_left C hr
  simp only [Function.comp_def]
  nlinarith

theorem WordRangeDecoration.formulas_cost {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (B C : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hwords : template.WordsBounded B) (hD : D.WordsBounded B)
    (henv : ∀ i, (env i).cost ≤ C) :
    ∀ r ∈ D.formulas template t ht env, r.formula.cost ≤ C * B ^ (n + 1) := by
  induction template generalizing C env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      simpa only [Nat.zero_add, pow_one] using q.toHistory_cost env B C hC (hD q hq) henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      have hstep : (step.formula.bind env).cost ≤ C * B := by
        apply (HistoryFormula.cost_bind_le step.formula env C hC henv).trans
        rw [HistoryPivotStep.formula_cost]
        exact Nat.mul_le_mul_left C hwords.1
      have hCB : 1 ≤ C * B := by simpa using Nat.mul_le_mul hC hB
      have hu : ∀ i, (BranchingWordHistory.updatedFormulas step env i).cost ≤ C * B := by
        intro i
        by_cases hi : i = step.target
        · subst i
          simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hstep
        · simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne hi] using
            (henv i).trans (by simpa using Nat.mul_le_mul_left C hB)
      have hL := ihL L t.2.1 ht.2.1 _ (C * B) hCB hwords.2.1 hD.2.1 hu
      have hR := ihR R t.2.2 ht.2.2 _ (C * B) hCB hwords.2.2 hD.2.2 hu
      have he : C * B * B ^ (n + 1) = C * B ^ (n + 1 + 1) := by rw [pow_succ]; ring
      have hb : C * B ≤ C * B ^ (n + 1 + 1) := by
        apply Nat.mul_le_mul_left C
        simpa only [pow_one] using
          (show B ^ 1 ≤ B ^ (n + 1 + 1) from Nat.pow_le_pow_right hB (by omega))
      intro q hq
      change q ∈ ranges.map (fun q => q.toHistory env) ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨q0, hq0, heq⟩ := List.mem_map.mp hq
        rw [← heq]
        exact (q0.toHistory_cost env B C hC (hD.1 q0 hq0) henv).trans hb
      · rcases List.mem_append.mp hq with hq | hq
        · exact (hL q hq).trans_eq he
        · exact (hR q hq).trans_eq he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangePolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite polynomial guard for all intermediate range tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem WordRangeDecoration.rangeAt_mem {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    D.rangeAt template t ht i ∈ D.formulas template t ht .prime := List.getElem_mem _

theorem WordRangeDecoration.rangeAt_all {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    (∀ i, (D.rangeAt template t ht i).Holds x) ↔
      ∀ r ∈ D.formulas template t ht .prime, r.Holds x := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < D.count := by rwa [D.formulas_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (D.rangeAt_mem template t ht i)

theorem WordRangeDecoration.polynomials_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    polynomialRangeKeep D.count
        (polynomialSupportCode (D.polynomials template t ht a coord) (z : ℝ)) = true ↔
      ∀ r ∈ D.formulas template t ht .prime, r.Holds (Function.update a coord z) := by
  rw [polynomials, formulaRangePolynomials_iff]
  simp only [formulaPolynomial_eval_update]
  exact D.rangeAt_all template t ht _

theorem WordRangeDecoration.polynomials_degree {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    (∑ i, (D.polynomials template t ht a coord i).natDegree) ≤ 2 * D.count * B ^ (n + 1) := by
  apply (formulaRangePolynomials_degree _ _ _ _ _).trans
  have hs : (∑ i, (D.rangeAt template t ht i).formula.cost) ≤ D.count * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _ : Fin D.count, B ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Nat.one_mul] using D.formulas_cost template t ht .prime B 1 hB le_rfl hwords hD
          (fun _ => le_rfl) _ (D.rangeAt_mem template t ht i)
      _ = _ := by simp
  nlinarith

/-- Adding a finite polynomial support family does not change the smooth
factor or any arithmetic residue condition. -/
theorem guardedHistoryAmplitude_extra {σ I : Type*} [Fintype I] {n t u : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (extra : (Fin u → Bool) → Bool) (z : ℤ) :
    guardedHistoryAmplitude N d s a coord F (Fin.append H J) (pairedPolynomialKeep keep extra) z =
      (if extra (polynomialSupportCode J (z : ℝ)) = true then 1 else 0) *
        guardedHistoryAmplitude N d s a coord F H keep z := by
  have hleft : (fun i => polynomialSupportCode (Fin.append H J) (z : ℝ) (Fin.castAdd u i)) =
      polynomialSupportCode H (z : ℝ) := by
    funext i
    simp only [polynomialSupportCode, Fin.append_left]
  have hright : (fun i => polynomialSupportCode (Fin.append H J) (z : ℝ) (Fin.natAdd t i)) =
      polynomialSupportCode J (z : ℝ) := by
    funext i
    simp only [polynomialSupportCode, Fin.append_right]
  simp only [guardedHistoryAmplitude, polynomialAmplitude, pairedPolynomialKeep,
    hleft, hright, Bool.and_eq_true]
  split_ifs <;> simp_all

namespace WordFourierParameters

theorem rangedCoefficient_local {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.rangedCoefficient D template t ht (Function.update a coord z) =
      guardedHistoryAmplitude (wordGuardNumerators (template.guardAt t ht))
        (wordGuardDenominators (template.guardAt t ht)) (wordGuardModuli (template.guardAt t ht))
        a coord (p.factors template t ht a coord) (p.rangedPolynomials D template t ht a coord)
        (rangedKeep D template t ht) z := by
  rw [rangedPolynomials, rangedKeep, guardedHistoryAmplitude_extra, ← coefficient_local]
  unfold rangedCoefficient
  simp only [D.polynomials_iff template t ht a coord z]

theorem ranged_complexity_bound {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    polynomialWeightComplexity (p.factors template t ht a coord)
      (p.rangedPolynomials D template t ht a coord) ≤
      (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * D.count) * B ^ (n + 1) := by
  have hbase := p.complexity_bound template t ht a coord B hB hwords
  have hextra := D.polynomials_degree template t ht a coord B hB hwords hD
  simp only [polynomialWeightComplexity, rangedPolynomials, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right] at *
  nlinarith

end WordFourierParameters

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inherited frequency-unit tests along the actual word reconstruction -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.unitGuards_formulas {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.unitGuards template t ht env).map HistoryUnitGuard.formula =
      (D.formulas template t ht env).map HistoryRange.formula := by
  induction template generalizing env with
  | leaf word =>
    cases D
    simp only [unitGuards, formulas, List.map_map, Function.comp_def, WordRange.toUnitGuard]
  | node d l r ihL ihR =>
    cases D
    simp only [unitGuards, formulas, List.map_append, ihL, ihR, List.map_map,
      Function.comp_def, WordRange.toUnitGuard]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common period for the inherited frequency-unit conditions -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.formulas_frequencies_dvd {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (M : ℤ)
    (hfreq : ∀ s ∈ internalFrequencyList n t, s ∣ M)
    (env : σ → HistoryFormula σ) (henv : ∀ i s, s ∈ (env i).frequencies → s ∣ M) :
    ∀ r ∈ D.formulas template t ht env, ∀ s ∈ r.formula.frequencies, s ∣ M := by
  induction template generalizing env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro r hr
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
      apply HistoryFormula.frequencies_listProduct_dvd
      intro F hF
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
      exact henv i
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      have hs : step.s ∣ M := hfreq _ (List.mem_cons_self ..)
      have hhead := HistoryFormula.frequencies_bind_dvd step.formula env M
        (step.formula_frequencies_dvd M hs) henv
      have hu : ∀ i s, s ∈ (BranchingWordHistory.updatedFormulas step env i).frequencies → s ∣ M := by
        intro i s hi
        by_cases he : i = step.target
        · subst i
          exact hhead s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hi)
        · exact henv i s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne he] using hi)
      have hL := ihL L t.2.1 ht.2.1
        (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
      have hR := ihR R t.2.2 ht.2.2
        (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
      intro q hq
      change q ∈ ranges.map (fun q => q.toHistory env) ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
        apply HistoryFormula.frequencies_listProduct_dvd
        intro F hF
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
        exact henv i
      · rcases List.mem_append.mp hq with hq | hq
        · exact hL q hq
        · exact hR q hq

theorem WordRangeDecoration.formulas_denominator_period {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    ∀ r ∈ D.formulas template t ht .prime, r.formula.cleared.denominator ∣
      (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
  have hfreq := D.formulas_frequencies_dvd template t ht
    (historyFrequencyBase (internalFrequencyList n t) : ℤ)
    (fun s hs => frequency_dvd_historyFrequencyBase _ s hs) .prime
    (by intro i s hs; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hs)
  intro r hr
  have hc : r.formula.cost ≤ B ^ (n + 1) := by
    simpa only [Nat.one_mul] using D.formulas_cost template t ht .prime B 1 hB le_rfl
      hwords hD (fun _ => le_rfl) r hr
  have hd := r.formula.denominator_test_period
    (historyFrequencyBase (internalFrequencyList n t) : ℤ) 1 (hfreq r hr) (one_dvd _)
  simp only [mul_one] at hd
  simp only [historyFrequencyPeriod, Nat.cast_pow]
  exact hd.trans (pow_dvd_pow _ (Nat.add_le_add_right (r.formula.frequency_count_le_cost.trans hc) 1))

theorem WordRangeDecoration.unitGuards_modulus {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.unitGuards template t ht env, ∃ s ∈ allFrequencyList n t, g.modulus = s.natAbs := by
  induction template generalizing env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro g hg
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
      exact ⟨t, List.mem_singleton_self _, rfl⟩
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      intro g hg
      change g ∈ ranges.map (fun q => q.toUnitGuard env t.1) ++ _ at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
        exact ⟨t.1, List.mem_cons_self .., rfl⟩
      · rcases List.mem_append.mp hg with hg | hg
        · obtain ⟨s, hs, he⟩ := ihL L _ _ _ g hg
          exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_left _ hs), he⟩
        · obtain ⟨s, hs, he⟩ := ihR R _ _ _ g hg
          exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_right _ hs), he⟩

/-- The extra inherited unit gates use the same explicit modulus as the
node integrality gates; no new periodicity input is assumed. -/
theorem WordRangeDecoration.unitGuards_period {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    ∀ g ∈ D.unitGuards template t ht .prime,
      g.formula.cleared.denominator * (g.modulus : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hF : g.formula ∈ (D.formulas template t ht .prime).map HistoryRange.formula := by
    rw [← D.unitGuards_formulas]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hF
  have hd := D.formulas_denominator_period template t ht B hB hwords hD r hr
  rw [he] at hd
  obtain ⟨s, hs, he⟩ := D.unitGuards_modulus template t ht .prime g hg
  have hm : (g.modulus : ℤ) ∣ (historyFrequencyBase (allFrequencyList n t) : ℤ) := by
    rw [he]
    exact Int.natCast_dvd_natCast.mpr (Int.dvd_natCast.mp (frequency_dvd_historyFrequencyBase _ s hs))
  simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue support for all inherited word units -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.unitAt_mem {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin U.count) :
    U.unitAt template t ht i ∈ U.unitGuards template t ht .prime := List.getElem_mem _

theorem WordRangeDecoration.unitAt_all {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    (∀ i, (U.unitAt template t ht i).Holds x) ↔
      ∀ g ∈ U.unitGuards template t ht .prime, g.Holds x := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hi' : i < U.count := by rwa [U.unitGuards_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (U.unitAt_mem template t ht i)

theorem WordRangeDecoration.unitAt_period {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hU : U.WordsBounded B) :
    ∀ i, wordUnitDenominators (U.unitAt template t ht) i *
      (wordUnitModuli (U.unitAt template t ht) i : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro i
  exact U.unitGuards_period template t ht B hB hwords hU _ (U.unitAt_mem template t ht i)

theorem guardedHistoryAmplitude_extra_units {σ : Type*} {r s n t : ℕ}
    (N : Fin r → MvPolynomial σ ℤ) (d : Fin r → ℤ) (v : Fin r → ℕ)
    (G : Fin s → HistoryUnitGuard σ) (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (z : ℤ) :
    guardedHistoryAmplitude (Fin.append N (wordUnitNumerators G))
      (Fin.append d (wordUnitDenominators G)) (Fin.append v (wordUnitModuli G)) a coord F H keep z =
      (if ∀ i, (G i).Holds (Function.update a coord z) then 1 else 0) *
        guardedHistoryAmplitude N d v a coord F H keep z := by
  simp only [guardedHistoryAmplitude, Fin.forall_fin_add, Fin.append_left, Fin.append_right,
    wordUnitNumerators, wordUnitDenominators, wordUnitModuli, HistoryUnitGuard.Holds]
  split_ifs <;> simp_all
  all_goals
    left
    apply ite_eq_right
    intro hgood
    aesop

namespace WordFourierParameters

/-- All inherited unit tests are literal divisibility tests on the constructed
numerators, with the same polynomial inequalities and smooth factors. -/
theorem unitRangedCoefficient_local {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.unitRangedCoefficient U D template t ht (Function.update a coord z) =
      guardedHistoryAmplitude
        (Fin.append (wordGuardNumerators (template.guardAt t ht)) (wordUnitNumerators (U.unitAt template t ht)))
        (Fin.append (wordGuardDenominators (template.guardAt t ht)) (wordUnitDenominators (U.unitAt template t ht)))
        (Fin.append (wordGuardModuli (template.guardAt t ht)) (wordUnitModuli (U.unitAt template t ht)))
        a coord (p.factors template t ht a coord) (p.rangedPolynomials D template t ht a coord)
        (rangedKeep D template t ht) z := by
  rw [guardedHistoryAmplitude_extra_units, ← rangedCoefficient_local]
  unfold unitRangedCoefficient
  simp only [U.unitAt_all]

theorem coefficient_eq_zero_of_not_valid {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hv : ¬ ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    p.coefficient template t ht (fun i => (x i : ℤ)) = 0 := by
  unfold coefficient
  split_ifs with h
  · exact False.elim (hv ((template.guardAt_valid_iff t ht x).mp h.1))
  · exact zero_mul _

end WordFourierParameters

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_UnitRangedWordPairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided cancellation with every original word and product range -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

private theorem append_nonzero {r s : ℕ} (d : Fin r → ℤ) (e : Fin s → ℤ)
    (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0) : ∀ i, Fin.append d e i ≠ 0 := by
  intro i
  exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hd j)
    (fun j => by simpa only [Fin.append_right] using he j) i

private theorem append_test_dvd {r s : ℕ} (d : Fin r → ℤ) (e : Fin s → ℤ)
    (v : Fin r → ℕ) (w : Fin s → ℕ) (M : ℤ)
    (hd : ∀ i, d i * (v i : ℤ) ∣ M) (he : ∀ i, e i * (w i : ℤ) ∣ M) :
    ∀ i, Fin.append d e i * ((Fin.append v w i : ℕ) : ℤ) ∣ M := by
  intro i
  exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hd j)
    (fun j => by simpa only [Fin.append_right] using he j) i

theorem unitRangedWordTransfer_pair_dyadic_bound {J σ : Type*} [Fintype J] {n : ℕ}
    (template template' : WordTransferTemplate σ n)
    (U U' D D' : WordRangeDecoration σ n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (fixed : Q → σ → ℤ) (coord : σ) (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
    let R := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
    let C := f.budget template t hn * f'.budget template' t' hn'
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          (f.unitRangedCoefficient U D template t hn (Function.update (fixed q) coord (p : ℕ)) *
            conj (f'.unitRangedCoefficient U' D' template' t' hn' (Function.update (fixed q) coord (p : ℕ)))))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * C ^ 2) +
          (M : ℝ) * ((3 ^ (2 * (R + R)) : ℕ) * (2 * (A : ℝ)⁻¹ * C ^ 2)) * (Bq : ℝ) ^ 2) := by
  let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
  let R := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
  let G := template.guardAt t hn
  let G' := template'.guardAt t' hn'
  have hMpos : 0 < M := Nat.mul_pos (wordTransferFullPeriod_pos n t B hz)
    (wordTransferFullPeriod_pos n t' B hz')
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM (q : Q) : M.Coprime (q : ℕ) := by
    exact ((prime_coprime_wordTransferFullPeriod n t B q (hprime q q.property)
      (fun s hs => ⟨Int.natAbs_pos.mpr (hz s hs), hsmall q q.property s hs⟩)).mul_right
      (prime_coprime_wordTransferFullPeriod n t' B q (hprime q q.property)
        (fun s hs => ⟨Int.natAbs_pos.mpr (hz' s hs), hsmall' q q.property s hs⟩))).symm
  let UG := U.unitAt template t hn
  let UG' := U'.unitAt template' t' hn'
  let d1 := Fin.append (wordGuardDenominators G) (wordUnitDenominators UG)
  let d2 := Fin.append (wordGuardDenominators G') (wordUnitDenominators UG')
  let s1 := Fin.append (wordGuardModuli G) (wordUnitModuli UG)
  let s2 := Fin.append (wordGuardModuli G') (wordUnitModuli UG')
  have hd1 : ∀ i, d1 i ≠ 0 := append_nonzero _ _
    (template.guardAt_denominators_ne_zero t hn) (fun i => (UG i).formula.cleared.denominator_ne_zero)
  have hd2 : ∀ i, d2 i ≠ 0 := append_nonzero _ _
    (template'.guardAt_denominators_ne_zero t' hn') (fun i => (UG' i).formula.cleared.denominator_ne_zero)
  have hden := append_nonzero d1 d2 hd1 hd2
  have hdiv1 : ∀ i, d1 i * (s1 i : ℤ) ∣ (M : ℤ) := by
    apply append_test_dvd
    · intro i
      exact (template.guardAt_full_period t hn B hB hwords i).trans
        (by exact_mod_cast dvd_mul_right (wordTransferFullPeriod n t B) (wordTransferFullPeriod n t' B))
    · intro i
      exact (U.unitAt_period template t hn B hB hwords hU i).trans
        (by exact_mod_cast dvd_mul_right (wordTransferFullPeriod n t B) (wordTransferFullPeriod n t' B))
  have hdiv2 : ∀ i, d2 i * (s2 i : ℤ) ∣ (M : ℤ) := by
    apply append_test_dvd
    · intro i
      exact (template'.guardAt_full_period t' hn' B hB hwords' i).trans
        (by exact_mod_cast dvd_mul_left (wordTransferFullPeriod n t' B) (wordTransferFullPeriod n t B))
    · intro i
      exact (U'.unitAt_period template' t' hn' B hB hwords' hU' i).trans
        (by exact_mod_cast dvd_mul_left (wordTransferFullPeriod n t' B) (wordTransferFullPeriod n t B))
  have hdiv := append_test_dvd d1 d2 s1 s2 (M : ℤ) hdiv1 hdiv2
  simp_rw [f.unitRangedCoefficient_local U D template t hn, f'.unitRangedCoefficient_local U' D' template' t' hn']
  simp_rw [← guardedHistoryAmplitude_pair]
  apply dyadic_guarded_graph_bound χ graph unary outside hunary hself hreverse P Q hprime
    hnonprincipal A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
  · exact fun _ => hden
  · exact fun _ => hdiv
  · exact mul_nonneg (f.budget_nonneg template t hn) (f'.budget_nonneg template' t' hn')
  · intro q
    rw [pairedPolynomialFactors_budget, f.factors_budget, f'.factors_budget]
  · intro q
    rw [polynomialWeightComplexity_pair]
    have hleft := f.ranged_complexity_bound D template t hn (fixed q) coord B hB hwords hD
    have hright := f'.ranged_complexity_bound D' template' t' hn' (fixed q) coord B hB hwords' hD'
    apply Nat.add_le_add
    · apply hleft.trans
      apply Nat.mul_le_mul_right
      omega
    · apply hright.trans
      apply Nat.mul_le_mul_right
      omega

  · exact hBq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_UnitRangedOriginalPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior cancellation retaining inherited frequency-units -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem selected_unit_ranged_expanded_word_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) {n : ℕ}
    (template template' : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable V n) n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q, lower ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) (outside : OtherVertices a b → ℕ) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (let x := twoCoordinateAssignment a b hab outside (q : ℕ) (p : ℕ)
         finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
           (f.unitRangedCoefficient U D template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
             conj (f'.unitRangedCoefficient U' D' template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ))))))‖ ^ 2 ≤
      rangedWordTransferPairBound template template' D D' t t' hn hn' B f f' A E P Q lower Bq := by
  let e := twoVertexEquiv a b hab
  let fixed (q : Q) := expandedPrimeValues n
    (twoCoordinateAssignment a b hab (fun i => (outside i : ℤ)) (q : ℕ) 0)
  have hh := unitRangedWordTransfer_pair_dyadic_bound template template' U U' D D' t t' hn hn' B hB hwords hwords'
    hD hD' hU hU' hz hz' f f' (fun i => χ (e i)) (fun i j => graph (e i) (e j))
    (fun i => unary (e i)) outside (fun i x => hunary (e i) x) hself hreverse
    P Q hprime hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ
    hPmass hQmass fixed (.inl b) Bq hBq
  simp_rw [finiteEdgeWeight_twoCoordinate_reindex a b hab,
    expandedPrimeValues_twoCoordinate a b hab n]
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

namespace HistoryFormula

theorem rename_value {V W : Type*} (f : V → W) (F : HistoryFormula V) (x : W → ℚ) :
    (F.rename f).value x = F.value (x ∘ f) := by
  rw [rename, value_bind]
  simp only [value_prime, Function.comp_def]

theorem rename_cost {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).cost = F.cost := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product l r hl hr => exact congrArg₂ (· + ·) hl hr
  | solve l r v w s hs hl hr =>
    change (l.rename f).cost + (r.rename f).cost + 2 = l.cost + r.cost + 2
    rw [hl, hr]

theorem rename_frequencies {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).frequencies = F.frequencies := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product l r hl hr => exact congrArg₂ List.append hl hr
  | solve l r v w s hs hl hr => exact congrArg (s :: ·) (congrArg₂ List.append hl hr)

theorem rename_denominator {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, rename_frequencies, denominator_eq_frequency_product]

theorem rename_inputs {V W : Type*} (f : V → W) (F : HistoryFormula V)
    (R : ℝ) (hF : F.InputsBounded R) : (F.rename f).InputsBounded R :=
  inputsBounded_bind F _ R hF (fun _ => trivial)

end HistoryFormula

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterpart harmonic normalization on the actual finite slot type -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_enumeration_sum {A M : Type*} [AddCommMonoid M]
    (F G : Fintype A) (f : A → M) :
    Finset.sum (@Finset.univ A F) f = Finset.sum (@Finset.univ A G) f := by
  cases Subsingleton.elim F G
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteReconstructedCoprimality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators Classical

theorem finite_reconstructed_coprimality_bound
    {A I K : Type*} [Fintype A] [Nonempty A] [Fintype I] [Fintype K] [Nonempty K]
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (K)) (coord : I → K)
    (y : I → (K → A) → ℤ)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (K → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hvalid : ∀ x, W x ≠ 0 → ∀ j,
      (F j).value (fun i => (prime (x i) : ℚ)) = y j x ∧
      ¬prime (x (coord j)) ∣ (F j).cleared.denominator.natAbs)
    (hcancel : ‖∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) *
      (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)‖ ≤
      δ + B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := K))
  let e : Fin (m + 1) ≃ K := (finCongr hm.symm).trans (Fintype.equivFin K).symm
  have hv (x : Fin (m + 1) → A) (hx : W (x ∘ e.symm) ≠ 0) (j : I) :
      ((F j).rename e.symm).value (fun i => (prime (x i) : ℚ)) = y j (x ∘ e.symm) ∧
      ¬prime (x (e.symm (coord j))) ∣ ((F j).rename e.symm).cleared.denominator.natAbs := by
    have h := hvalid (x ∘ e.symm) hx j
    simpa only [HistoryFormula.rename_value, HistoryFormula.rename_denominator,
      Function.comp_def] using h
  have hb : ‖∑ x : Fin (m + 1) → A, (productPrior (fun i => μ (e i)) x : ℂ) *
      W (x ∘ e.symm)‖ ≤ δ := by
    simp only [productPrior]
    apply Eq.trans_le (congrArg norm ?_) hcancel
    convert finite_prior_reindex e μ W using 1
    all_goals try with_reducible_and_instances rfl
    with_reducible exact finite_enumeration_sum _ _ _
  have hh := reconstructed_coprimality_bound prime hpInj hprime
    (fun j => (F j).rename e.symm) (fun j => e.symm (coord j))
    (fun j x => y j (x ∘ e.symm)) (fun i => μ (e i))
    (fun i a => hμ (e i) a) (fun i => hmass (e i))
    α V R β hα hβ hV hR (fun i a => hmax (e i) a)
    (by intro j a; simpa only [Equiv.apply_symm_apply] using hpmax j a)
    hlower hupper (fun j => (F j).rename_inputs e.symm R (hinputs j))
    (fun x => W (x ∘ e.symm)) B δ hB hδ (fun x => hW (x ∘ e.symm)) hv hb
  simp only [HistoryFormula.rename_cost, productPrior] at hh
  have he := finite_prior_reindex e μ (fun x =>
    if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)
  simp only [Function.comp_apply] at he
  apply Eq.trans_le (congrArg norm ?_) hh
  symm
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  with_reducible exact finite_enumeration_sum _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopPrimeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual-prime collisions and coprimality to a fixed external integer -/

namespace Ostmann

open scoped BigOperators Classical

theorem TopPrimeCondition.formula_value {V : Type*} (g : TopPrimeCondition V) (x : V → ℕ) :
    g.formula.value (fun i => (x i : ℚ)) = g.target x := by
  cases g <;> simp only [formula, target, HistoryFormula.value_prime,
    HistoryFormula.value_external, Int.cast_natCast]

theorem TopPrimeCondition.formula_cost {V : Type*} (g : TopPrimeCondition V) :
    g.formula.cost = 1 := by cases g <;> rfl

theorem TopPrimeCondition.formula_denominator {V : Type*} (g : TopPrimeCondition V) :
    g.formula.cleared.denominator = 1 := by cases g <;> rfl

theorem TopPrimeCondition.formula_inputs {V : Type*} (g : TopPrimeCondition V)
    (R : ℝ) (hg : g.Bounded R) : g.formula.InputsBounded R := by
  cases g <;> exact hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators Classical

theorem finite_top_prime_support_bound {A J K : Type*} [Fintype A] [Nonempty A] [Fintype J] [Fintype K] [Nonempty K]
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (checks : J → TopPrimeCondition (K))
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hbound : ∀ j, (checks j).Bounded R)
    (W : (K → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then W x else 0)‖ ≤
      δ + B * (Fintype.card J : ℝ) * (α + Real.log R / V * α) := by
  have hv (x : K → A) (_ : W x ≠ 0) (j : J) :
      (checks j).formula.value (fun i => (prime (x i) : ℚ)) =
          (checks j).target (fun i => prime (x i)) ∧
        ¬prime (x (checks j).coordinate) ∣ (checks j).formula.cleared.denominator.natAbs := by
    refine ⟨(checks j).formula_value _, ?_⟩
    rw [TopPrimeCondition.formula_denominator, Int.natAbs_one]
    exact (hprime _).not_dvd_one
  have hh := finite_reconstructed_coprimality_bound prime hpInj hprime
    (fun j => (checks j).formula) (fun j => (checks j).coordinate)
    (fun j x => (checks j).target (fun i => prime (x i))) μ hμ hmass α V R
    (fun _ => α) hα (fun _ => hα) hV hR hmax (fun j a => hmax (checks j).coordinate a)
    hlower hupper (fun j => (checks j).formula_inputs R (hbound j)) W B δ hB hδ hW hv hcancel
  have he (x : K → A) :
      (if ∀ j, (prime (x (checks j).coordinate)).Coprime
        ((checks j).target (fun i => prime (x i))).natAbs then W x else 0) =
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then W x else 0) := by
    congr 1
  simpa only [finiteProductPrior, he, TopPrimeCondition.formula_cost, Nat.cast_one, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replaying the large-prime coprimalities at every reconstructed pivot -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.integerValue_of_value {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (y : ℤ) (hy : F.value (fun i => (a i : ℚ)) = y) :
    F.integerValue a = y := by
  unfold integerValue
  rw [F.cleared.integer_value_cleared a y hy,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

/-- Each check is attached to one of the actual pivot formulas, so it inherits
the already proved degree and small-denominator bounds. -/
theorem WordPrimeDecoration.check_formula_mem {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.checks template t ht env,
      g.formula ∈ (template.branching t ht).pivotFormulas env := by
  induction template generalizing env with
  | leaf word => cases D; simp only [checks, List.not_mem_nil, false_implies, implies_true]
  | @node n d l r ihL ihR =>
    cases D with
    | node coordinates L R =>
      intro g hg
      change g ∈ coordinates.map _ ++ _ at hg
      change g.formula ∈ _ :: (_ ++ _)
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hg
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp hg with hg | hg
        · exact List.mem_append_left _ (ihL L _ _ _ g hg)
        · exact List.mem_append_right _ (ihR R _ _ _ g hg)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived size, integrality and denominator bounds for the prime checks -/

namespace Ostmann

open scoped Classical

theorem WordPrimeDecoration.check_cost {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ g ∈ D.checks template t ht .prime, g.formula.cost ≤ B ^ (n + 1) := by
  intro g hg
  simpa only [Nat.one_mul] using
    (template.branching_formula_cost t ht B 1 hB le_rfl hwords .prime (fun _ => le_rfl)).2
      g.formula (D.check_formula_mem template t ht .prime g hg)

theorem WordPrimeDecoration.check_denominator {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ g ∈ D.checks template t ht .prime,
      g.formula.cleared.denominator ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hd := (template.branching_denominator_period t ht B hB hwords 1 (one_dvd _)).2
    g.formula (D.check_formula_mem template t ht .prime g hg)
  simp only [mul_one] at hd
  exact hd.trans (by
    rw [wordTransferFullPeriod, Nat.cast_mul]
    exact dvd_mul_right _ _)

theorem WordPrimeDecoration.check_integer_value {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (x : σ → ℕ) (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    ∀ g ∈ D.checks template t ht .prime,
      g.formula.value (fun i => (x i : ℚ)) = g.formula.integerValue (fun i => (x i : ℤ)) := by
  intro g hg
  have hi := (BranchingWordHistory.pivotFormulas_integral_iff (template.branching t ht)
    .prime (fun i => (x i : ℤ)) (fun i => (x i : ℤ))
    (by intro i; simp only [HistoryFormula.value_prime])).mpr
      (template.branching_valid x t ht hv)
  obtain ⟨z, hz⟩ := hi g.formula (D.check_formula_mem template t ht .prime g hg)
  rw [g.formula.integerValue_of_value _ z hz]
  simpa only [Int.cast_natCast] using hz

theorem WordTransferTemplate.pivot_inputsBounded {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (env : σ → HistoryFormula σ) (henv : ∀ i, (env i).InputsBounded R) :
    ∀ F ∈ (template.branching t ht).pivotFormulas env, F.InputsBounded R := by
  induction template generalizing env with
  | leaf word => simp only [branching, BranchingWordHistory.pivotFormulas,
      List.not_mem_nil, false_implies, implies_true]
  | @node n d l r ihL ihR =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
    have hs : step.formula.InputsBounded R := step.formula_inputsBounded R hR
      (hf _ (List.mem_cons_of_mem _ (List.mem_append_left _ (frequencyRoot_mem_allFrequencyList n t.2.1))))
      (hf _ (List.mem_cons_of_mem _ (List.mem_append_right _ (frequencyRoot_mem_allFrequencyList n t.2.2))))
      (hf _ (List.mem_cons_self ..))
    have hp := step.formula.inputsBounded_bind env R hs henv
    have hu : ∀ i, (BranchingWordHistory.updatedFormulas step env i).InputsBounded R := by
      intro i
      by_cases hi : i = step.target
      · subst i
        simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hp
      · simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne hi] using henv i
    have hl := ihL t.2.1 ht.2.1
      (fun s hs => hf s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
    have hr := ihR t.2.2 ht.2.2
      (fun s hs => hf s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
    intro F hF
    change F ∈ step.formula.bind env :: (_ ++ _) at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hp
    · rcases List.mem_append.mp hF with hF | hF
      · exact hl F hF
      · exact hr F hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedScheduleCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original grouped-atom amplitudes in the independent prime variables -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem expandedPrimeNatValues_cast {V : Type*} (n : ℕ) (x : V → ℕ) :
    (fun i => (expandedPrimeNatValues n x i : ℤ)) =
      expandedPrimeValues n (fun i => (x i : ℤ)) := by
  funext i
  cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordCoefficientNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform norms and valid support of the constructed coefficients -/

namespace Ostmann.WordFourierParameters

open scoped BigOperators Classical SchwartzMap

theorem coefficient_norm {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    ‖p.coefficient template t ht x‖ ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 p.profile :=
    (norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)
  unfold coefficient
  split_ifs with h
  · simp only [one_mul, norm_prod]
    calc
      _ ≤ ∏ _j : Fin (2 ^ n), SchwartzMap.seminorm ℝ 0 0 p.profile := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j _
        exact normalizedFourierProfile_norm p.profile _ _ _
          (p.profile.norm_le_seminorm ℝ)
          ((p.lower_one j).trans (h.2 j).1)
      _ = _ := by simp
  · simpa only [zero_mul, norm_zero] using pow_nonneg hS (2 ^ n)

theorem unitRangedCoefficient_norm {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    ‖p.unitRangedCoefficient U D template t ht x‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 p.profile :=
    (norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)
  unfold unitRangedCoefficient rangedCoefficient
  split_ifs <;> simp only [one_mul, zero_mul, norm_zero]
  · exact p.coefficient_norm template t ht x
  all_goals exact pow_nonneg hS (2 ^ n)

theorem unitRangedCoefficient_valid {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hx : p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) ≠ 0) :
    ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  by_contra hv
  apply hx
  simp only [unitRangedCoefficient, rangedCoefficient,
    p.coefficient_eq_zero_of_not_valid template t ht x hv, mul_zero]

end Ostmann.WordFourierParameters

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeCheckBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior cancellation retains every reconstructed prime check -/

namespace Ostmann

open scoped BigOperators Classical

theorem WordPrimeDecoration.checkAt_mem {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    D.checkAt template t ht i ∈ D.checks template t ht .prime := List.getElem_mem _

theorem WordPrimeDecoration.checkAt_all {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (a : σ → ℤ) (prime : V → ℕ) :
    (∀ i, (D.checkAt template t ht i).Holds a prime) ↔
      ∀ g ∈ D.checks template t ht .prime, g.Holds a prime := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hi' : i < D.count := by rwa [D.checks_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (D.checkAt_mem template t ht i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient retaining the large-prime coprimality support -/

namespace Ostmann.WordFourierParameters

open scoped Classical

theorem primeUnitRangedCoefficient_norm {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    ‖p.primeUnitRangedCoefficient C U D template t ht x‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  unfold primeUnitRangedCoefficient
  split_ifs
  · exact p.unitRangedCoefficient_norm U D template t ht _
  · simpa only [norm_zero] using pow_nonneg
      ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) (2 ^ n)

end Ostmann.WordFourierParameters

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every reconstructed prime check excludes the fixed pivot coordinate -/

namespace Ostmann

open scoped Classical

theorem WordPrimeDecoration.checks_coordinates {V σ : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (p : V → Prop) (hD : D.Coordinates p)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.checks template t ht env, p g.coordinate := by
  induction template generalizing env with
  | leaf word => cases D; simp [checks]
  | @node n d l r ihl ihr =>
    cases D with
    | node xs L R =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
        exact hD.1 v hv
      · rcases List.mem_append.mp hg with hg | hg
        · exact ihl L hD.2.1 t.2.1 ht.2.1 _ g hg
        · exact ihr R hD.2.2 t.2.2 ht.2.2 _ g hg

theorem WordPrimeDecoration.checkAt_unfixed {V σ : Type*} {n : ℕ}
    (D : WordPrimeDecoration (Option V) n) (hD : D.Coordinates (· ≠ none))
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    ∃ v, (D.checkAt template t ht i).coordinate = some v := by
  have h := D.checks_coordinates (· ≠ none) hD template t ht .prime
    _ (D.checkAt_mem template t ht i)
  cases he : (D.checkAt template t ht i).coordinate with
  | none => exact False.elim (h he)
  | some v => exact ⟨v, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotFormulas
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the fixed pivot from the independent polynomial variables -/

namespace Ostmann.HistoryFormula

open scoped Classical

theorem fixNone_value {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) (x : V → ℤ) :
    (F.fixNone M).value (fun i => (x i : ℚ)) =
      F.value (fun i => match i with | none => (M : ℚ) | some v => (x v : ℚ)) := by
  rw [fixNone, value_bind]
  congr 1
  funext i
  cases i <;> simp only [value_external, value_prime]

theorem fixNone_cost {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).cost = F.cost := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ (· + ·) ihf ihg
  | solve f g v w s hs ihf ihg =>
    change (f.fixNone M).cost + (g.fixNone M).cost + 2 = f.cost + g.cost + 2
    rw [ihf, ihg]

theorem fixNone_frequencies {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).frequencies = F.frequencies := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ List.append ihf ihg
  | solve f g v w s hs ihf ihg => exact congrArg (s :: ·) (congrArg₂ List.append ihf ihg)

theorem fixNone_denominator {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, fixNone_frequencies, denominator_eq_frequency_product]

theorem fixNone_inputs {V : Type*} (M : ℤ) (F : HistoryFormula (Option V))
    (R : ℝ) (hM : |(M : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    (F.fixNone M).InputsBounded R := by
  apply inputsBounded_bind F _ R hF
  intro i
  cases i
  · exact hM
  · trivial

theorem fixedOriginalPrimes_value {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) (x : V → ℤ) :
    (F.fixedOriginalPrimes M).value (fun i => (x i : ℚ)) =
      F.value (fun i => (expandedPrimeValues n (fun i => match i with
        | none => M | some v => x v) i : ℚ)) := by
  rw [fixedOriginalPrimes, fixNone_value]
  have he : (fun i : Option V => match i with | none => (M : ℚ) | some v => (x v : ℚ)) =
      (fun i : Option V => (((match i with | none => M | some v => x v) : ℤ) : ℚ)) := by
    funext i
    cases i <;> rfl
  rw [he]
  exact F.originalPrimes_value (fun i => match i with | none => M | some v => x v)

theorem fixedOriginalPrimes_cost {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) :
    (F.fixedOriginalPrimes M).cost = F.cost := by
  rw [fixedOriginalPrimes, fixNone_cost, originalPrimes_cost]

theorem fixedOriginalPrimes_denominator {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) :
    (F.fixedOriginalPrimes M).cleared.denominator = F.cleared.denominator := by
  rw [fixedOriginalPrimes, fixNone_denominator, originalPrimes_denominator]

theorem fixedOriginalPrimes_inputs {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n))
    (R : ℝ) (hR : 1 ≤ R) (hM : |(M : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    (F.fixedOriginalPrimes M).InputsBounded R :=
  F.originalPrimes.fixNone_inputs M R hM (F.originalPrimes_inputs R hR hF)

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotPrimeChecks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructed prime checks with a fixed external integer coordinate -/

namespace Ostmann

open scoped BigOperators Classical

theorem word_prime_checks_fixed_pivot_bound
    {A : Type*} [Fintype A] [Nonempty A] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (D : WordPrimeDecoration (Option (K)) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (coord : Fin D.count → K)
    (hcoord : ∀ i, (D.checkAt template t ht i).coordinate = some (coord i))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (M : ℕ)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (W : (K → A) → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ C)
    (hvalid : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if ∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ)))
            (fixedPivotPrimeValues M (fun i => prime (x i))) then W x else 0)‖ ≤
      δ + C * (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let G := D.checkAt template t ht
  let F := fun i => (G i).formula.fixedOriginalPrimes (M : ℤ)
  let q := fun x : K → A => fixedPivotPrimeValues M (fun i => prime (x i))
  let a := fun x => expandedPrimeValues n (fun i => (q x i : ℤ))
  let y := fun i x => (G i).formula.integerValue (a x)
  have hmem i := D.checkAt_mem template t ht i
  have hinputs i : (F i).InputsBounded R := by
    apply (G i).formula.fixedOriginalPrimes_inputs (M : ℤ) R (by linarith)
      (by simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M)] using hM)
    exact template.pivot_inputsBounded t ht R (by linarith) hfreq .prime (fun _ => trivial)
      _ (D.check_formula_mem template t ht .prime _ (hmem i))
  have hv (x : K → A) (hw : W x ≠ 0) (i : Fin D.count) :
      (F i).value (fun k => (prime (x k) : ℚ)) = y i x ∧
        ¬prime (x (coord i)) ∣ (F i).cleared.denominator.natAbs := by
    constructor
    · have hi := D.check_integer_value template t ht
        (expandedPrimeNatValues n (q x)) (hvalid x hw) _ (hmem i)
      rw [expandedPrimeNatValues_cast] at hi
      have hq : (fun k => (expandedPrimeNatValues n (q x) k : ℚ)) =
          (fun k => (a x k : ℚ)) := by
        funext k
        cases k <;> rfl
      rw [hq] at hi
      have he := (G i).formula.fixedOriginalPrimes_value (M : ℤ) (fun k => (prime (x k) : ℤ))
      apply he.trans
      have hcast : (fun k => (q x k : ℤ)) =
          (fun k => match k with | none => (M : ℤ) | some j => (prime (x j) : ℤ)) := by
        funext k
        cases k <;> rfl
      change (G i).formula.value (fun k => (a x k : ℚ)) = (y i x : ℚ) at hi
      dsimp only [a] at hi
      rw [hcast] at hi
      exact hi
    · have hd := D.check_denominator template t ht B hB hwords _ (hmem i)
      have hdN : (G i).formula.cleared.denominator.natAbs ∣ wordTransferFullPeriod n t B := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
      have hp := prime_coprime_wordTransferFullPeriod n t B (prime (x (coord i)))
        (hprime _) (hsmall _)
      change ¬prime (x (coord i)) ∣ ((G i).formula.fixedOriginalPrimes (M : ℤ)).cleared.denominator.natAbs
      rw [HistoryFormula.fixedOriginalPrimes_denominator]
      exact (hprime _).coprime_iff_not_dvd.mp (hp.of_dvd_right hdN)
  have hh := finite_reconstructed_coprimality_bound prime hpInj hprime F coord y μ hμ hmass
    α V R (fun _ => β) hα (fun _ => hβ) hV hR hmax
    (fun i a => hpmax (coord i) a) hlower hupper hinputs W C δ hC hδ hW hv hcancel
  have he (x : K → A) :
      (∀ i, (prime (x (coord i))).Coprime (y i x).natAbs) ↔
        ∀ g ∈ D.checks template t ht .prime, g.Holds (a x) (q x) := by
    rw [← D.checkAt_all template t ht (a x) (q x)]
    apply forall_congr'
    intro i
    change (prime (x (coord i))).Coprime (y i x).natAbs ↔
      (q x ((G i).coordinate)).Coprime (y i x).natAbs
    rw [hcoord]
    rfl
  simp_rw [he] at hh
  apply hh.trans
  apply add_le_add le_rfl
  have hnonneg : 0 ≤ α + Real.log R / V * β :=
    add_nonneg hα (mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hV.le) hβ)
  have hs : (∑ i : Fin D.count, ((F i).cost : ℝ) * (α + Real.log R / V * β)) ≤
      (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
    calc
      _ ≤ ∑ _i : Fin D.count, (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ hnonneg
        exact_mod_cast (show (F i).cost ≤ B ^ (n + 1) by
          rw [HistoryFormula.fixedOriginalPrimes_cost]
          exact D.check_cost template t ht B hB hwords _ (hmem i))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact (mul_le_mul_of_nonneg_left hs hC).trans_eq (by ring)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotPairSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both histories retain their large-prime support under the original law -/

namespace Ostmann

open scoped BigOperators Classical

theorem word_prime_pair_checks_fixed_pivot_bound
    {A : Type*} [Fintype A] [Nonempty A] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (D D' : WordPrimeDecoration (Option (K)) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hD : D.Coordinates (· ≠ none)) (hD' : D'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (hsmall' : ∀ a, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < prime a)
    (W : (K → A) → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ C)
    (hvalid : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t)
    (hvalid' : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template'.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t')
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if (∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
        (∀ g ∈ D'.checks template' t' ht' .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i))))
        then W x else 0)‖ ≤
      δ + C * ((D.count + D'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  choose coord hcoord using D.checkAt_unfixed hD template t ht
  choose coord' hcoord' using D'.checkAt_unfixed hD' template' t' ht'
  let good := fun x : K → A => ∀ g ∈ D.checks template t ht .prime,
    g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i)))
  let W₁ := fun x => if good x then W x else 0
  let E := C * (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β)
  have hE : 0 ≤ E := by
    apply mul_nonneg
    · positivity
    · exact add_nonneg hα (mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hV.le) hβ)
  have hfirst : ‖∑ x, (finiteProductPrior μ x : ℂ) * W₁ x‖ ≤ δ + E :=
    word_prime_checks_fixed_pivot_bound prime hpInj hprime D template t ht coord hcoord B hB hwords M μ hμ hmass
      α β V R hα hβ hV hR hM hmax hpmax hlower hupper hfreq hsmall W C δ hC hδ hW hvalid hcancel
  have hW₁ (x) : ‖W₁ x‖ ≤ C := by
    dsimp only [W₁]
    split_ifs
    · exact hW x
    · simpa only [norm_zero] using hC
  have hWne (x) (hx : W₁ x ≠ 0) : W x ≠ 0 := by
    intro hw
    apply hx
    simp only [W₁, hw, ite_self]
  have hsecond := word_prime_checks_fixed_pivot_bound prime hpInj hprime D' template' t' ht' coord' hcoord' B hB hwords' M
    μ hμ hmass α β V R hα hβ hV hR hM hmax hpmax hlower hupper hfreq' hsmall'
    W₁ C (δ + E) hC (add_nonneg hδ hE) hW₁ (fun x hx => hvalid' x (hWne x hx)) hfirst
  have he (x : K → A) :
      (if ∀ g ∈ D'.checks template' t' ht' .prime,
        g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i)))
        then W₁ x else 0) =
      (if (∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
        (∀ g ∈ D'.checks template' t' ht' .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) (fixedPivotPrimeValues M (fun i => prime (x i))))
        then W x else 0) := by
    dsimp only [W₁, good]
    split_ifs <;> simp_all
  simp_rw [he] at hsecond
  apply hsecond.trans_eq
  dsimp only [E]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotCoefficientPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large-prime support in the actual two-history coefficient estimate -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_prime_coefficient_pair_bound
    {A : Type*} [Fintype A] [Nonempty A] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (p p' : WordFourierParameters n)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (hsmall' : ∀ a, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < prime a)
    (G : (Option (K) → ℕ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.unitRangedCoefficient U D template t ht
          (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) *
        conj (p'.unitRangedCoefficient U' D' template' t' ht'
          (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))))))‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
        conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))))‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)) *
        ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let a := fun x : K → A => expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))
  let f := fun x => p.unitRangedCoefficient U D template t ht (a x)
  let f' := fun x => p'.unitRangedCoefficient U' D' template' t' ht' (a x)
  let W := fun x => G (fixedPivotPrimeValues M (fun i => prime (x i))) * (f x * conj (f' x))
  let N := (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)
  have hp0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) _
  have hp'0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p'.profile 0)).trans (p'.profile.norm_le_seminorm ℝ 0)) _
  have hN : 0 ≤ N := mul_nonneg hp0 hp'0
  have hW (x) : ‖W x‖ ≤ N := by
    dsimp only [W]
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hff : ‖f x‖ * ‖f' x‖ ≤ N := mul_le_mul
      (p.unitRangedCoefficient_norm U D template t ht (a x))
      (p'.unitRangedCoefficient_norm U' D' template' t' ht' (a x)) (norm_nonneg _) hp0
    exact (mul_le_mul (hG _) hff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (by norm_num)).trans_eq (one_mul N)
  have hv (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t := by
    apply p.unitRangedCoefficient_valid U D template t ht
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f, a, hf, zero_mul, mul_zero]
  have hv' (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template'.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t' := by
    apply p'.unitRangedCoefficient_valid U' D' template' t' ht'
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f', a, hf, map_zero, mul_zero]
  have hh := word_prime_pair_checks_fixed_pivot_bound prime hpInj hprime C C' template template' t t' ht ht' hC hC'
    B hB hwords hwords' μ hμ hmass α β V R hα hβ hV hR M hM hmax hpmax hlower hupper
    hfreq hfreq' hsmall hsmall' W N δ hN hδ hW hv hv' hcancel
  have he (x : K → A) :
      (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
        (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i))))
        then W x else 0) =
      G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
          conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))) := by
    unfold WordFourierParameters.primeUnitRangedCoefficient
    simp only [W, f, f', a]
    split_ifs <;> simp_all
  change ‖∑ x, (finiteProductPrior μ x : ℂ) *
    (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
      (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i))))
      then W x else 0)‖ ≤ _ at hh
  simp only [he] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTwoCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed integer outside the two selected original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

theorem fixedPivotPrimeValues_twoCoordinates {V : Type*} (a b : V) (hab : a ≠ b)
    (M : ℕ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    fixedPivotPrimeValues M (twoCoordinateAssignment a b hab outside q p) =
      twoCoordinateAssignment (some a) (some b) (fun h => hab (Option.some.inj h))
        (fixedPivotOutside a b M outside) q p := by
  funext i
  cases i with
  | none =>
    have hn : (none : Option V) ≠ some a ∧ (none : Option V) ≠ some b := by simp
    simpa only [fixedPivotPrimeValues, fixedPivotOutside] using
      (twoCoordinateAssignment_other (some a) (some b) _
        (fixedPivotOutside a b M outside) q p ⟨none, hn⟩).symm
  | some v =>
    by_cases ha : v = a
    · subst v
      simp only [fixedPivotPrimeValues, twoCoordinateAssignment_short]
    by_cases hb : v = b
    · subst v
      simp only [fixedPivotPrimeValues, twoCoordinateAssignment_long]
    have hs : some v ≠ some a ∧ some v ≠ some b :=
      ⟨fun h => ha (Option.some.inj h), fun h => hb (Option.some.inj h)⟩
    have h1 := twoCoordinateAssignment_other a b hab outside q p ⟨v, ha, hb⟩
    have h2 := twoCoordinateAssignment_other (some a) (some b) (fun h => hab (Option.some.inj h))
      (fixedPivotOutside a b M outside) q p ⟨some v, hs⟩
    simpa only [fixedPivotPrimeValues, fixedPivotOutside] using h1.trans h2.symm

theorem fixed_pivot_original_harmonic_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (M : ℕ) (P : Finset ℕ) (Q : V → Finset ℕ)
    (hQP : ∀ v, Q v ⊆ P) (hQmass : ∀ v, (∑ q ∈ Q v, (q : ℝ)⁻¹) ≠ 0)
    (F : (Option V → ℕ) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices (some a) (some b) → ℕ,
      ‖∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment (some a) (some b)
            (fun h => hab (Option.some.inj h)) outside (q : ℕ) (p : ℕ))‖ ≤ δ) :
    ‖∑ x : V → P, ((∏ v, primeSubsetPrior P (Q v) (x v) : ℝ) : ℂ) *
      F (fixedPivotPrimeValues M (fun v => (x v : ℕ)))‖ ≤ δ := by
  apply original_harmonic_pair_bound a b hab P Q hQP hQmass
    (fun x => F (fixedPivotPrimeValues M x)) δ hδ
  intro outside
  simp_rw [fixedPivotPrimeValues_twoCoordinates]
  exact hsection (fixedPivotOutside a b M (fun i => (outside i : ℕ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotUnitPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Every remaining coordinate keeps its own original harmonic prior.
Only the displayed numerical estimate remains to be specialized. -/
theorem fixed_pivot_unit_ranged_original_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) {n : ℕ}
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option V) n) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option V) n) n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : Option V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : Option V → Option V → ℤ)
    (unary : Option V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (Q : V → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hprime : ∀ q ∈ Q a, q.Prime)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (M : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' hn hn' B f f' A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : V → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.unitRangedCoefficient U D template t hn (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => (x j : ℕ)) i : ℤ))) *
          conj (f'.unitRangedCoefficient U' D' template' t' hn' (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => (x j : ℕ)) i : ℤ))))))‖ ≤ δ := by
  apply fixed_pivot_original_harmonic_pair_bound a b hab M P Q hQP (fun i => (hQmass i).ne')
    (fun x => finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
      (f.unitRangedCoefficient U D template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
        conj (f'.unitRangedCoefficient U' D' template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ)))))) δ hδ
  intro outside
  have hs := selected_unit_ranged_expanded_word_pair_bound (some a) (some b) (fun h => hab (Option.some.inj h)) template template' U U' D D' t t' hn hn' B hB
    hwords hwords' hD hD' hU hU' hz hz' f f' χ graph unary hunary hself hreverse (Q b) (Q a) hprime
    hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ
    (hQmass b) (hQmass a) Bq hBq outside
  exact (sq_le_sq₀ (norm_nonneg _) hδ).mp (hs.trans hnum)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeOriginalPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete two-history Y-coprimality estimate under harmonic priors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem finiteEdgeWeight_norm {I : Type*} [Fintype I]
    (E : I → I → ℕ → ℕ → ℂ) (ν : I → ℕ → ℂ) (x : I → ℕ)
    (hE : ∀ i j p q, ‖E i j p q‖ ≤ 1) (hν : ∀ i p, ‖ν i p‖ ≤ 1) :
    ‖finiteEdgeWeight E ν x‖ ≤ 1 := by
  unfold finiteEdgeWeight
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_mul, norm_prod]
  have hp : (∏ j, ‖E i j (x i) (x j)‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hE i j _ _)
  exact (mul_le_mul (hν i _) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (by norm_num)).trans_eq (one_mul 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotPrimeOriginal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_prime_original_pair_bound {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Option (K) → Option (K) → ℤ)
    (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))))‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * α) := by
  let : Nonempty P := hP.to_subtype
  obtain ⟨p₀, hp₀⟩ := hP
  have hz : ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
    intro s hs
    exact Int.natAbs_pos.mp (hsmall p₀ hp₀ s hs).1
  have hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0 := by
    intro s hs
    exact Int.natAbs_pos.mp (hsmall' p₀ hp₀ s hs).1
  have hbase := fixed_pivot_unit_ranged_original_pair_bound a b hab template template'
    U U' D D' t t' ht ht' B hB hwords hwords' hD hD' hU hU' hz hz' f f' χ graph unary hunary
    hself hreverse P Q hQP hQmass (fun q hq => hprime q (hQP a hq)) hnonprincipal
    A E hA hMA (fun q hq s hs => (hsmall q (hQP a hq) s hs).2)
    (fun q hq s hs => (hsmall' q (hQP a hq) s hs).2)
    hlow hhigh lower hlower hlowerQ Bq hBq M δ hδ hnum
  exact fixed_pivot_prime_coefficient_pair_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    (fun p => hprime p p.property) C C' U U' D D' template template' t t' ht ht' hC hC'
    B hB hwords hwords' f f' (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQmass i).ne')
    α α V R hα hα hV hR M hM hmax hmax
    (fun p => hlowerP p p.property) (fun p => hupperP p p.property) hfreq hfreq'
    (fun p => hsmall p p.property) (fun p => hsmall' p p.property)
    (finiteEdgeWeight (dirichletGraphEdge χ graph) unary)
    (fun x => finiteEdgeWeight_norm _ _ x (dirichletGraphEdge_norm χ graph) hunary)
    δ hδ (by
      simp only [finiteProductPrior]
      convert hbase using 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top collisions and external integers in the supported history pair -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_top_prime_coefficient_pair_bound
    {A J : Type*} [Fintype A] [Nonempty A] [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (checks : J → TopPrimeCondition (K))
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (p p' : WordFourierParameters n)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hbound : ∀ j, (checks j).Bounded R)
    (M : ℕ) (G : (Option (K) → ℕ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
        conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))))‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then
        G (fixedPivotPrimeValues M (fun i => prime (x i))) *
          (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
          conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i)))))
        else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)) *
        (Fintype.card J : ℝ) * (α + Real.log R / V * α) := by
  let B := (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)
  have hp0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) _
  have hp'0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p'.profile 0)).trans (p'.profile.norm_le_seminorm ℝ 0)) _
  apply finite_top_prime_support_bound prime hpInj hprime checks μ hμ hmass α V R
    hα hV hR hmax hlower hupper hbound _ B δ (mul_nonneg hp0 hp'0) hδ _ hcancel
  intro x
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hprod := mul_le_mul
    (p.primeUnitRangedCoefficient_norm C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))))
    (p'.primeUnitRangedCoefficient_norm C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))
    (norm_nonneg _) hp0
  exact (mul_le_mul (hG _) hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num)).trans_eq (one_mul B)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotFullPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior cancellation retaining all top prime tests -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_full_original_pair_bound_oai {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Option (K) → Option (K) → ℤ)
    (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (checks : J → TopPrimeCondition (K))
    (hchecks : ∀ j, (checks j).Bounded R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
        finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
        (α + Real.log R / V * α) := by
  let : Nonempty P := hP.to_subtype
  let N := (SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)
  let cost := ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ)
  let atom := α + Real.log R / V * α
  have hatom : 0 ≤ atom := by
    dsimp [atom]
    have hr : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (pow_nonneg (apply_nonneg _ _) _) (pow_nonneg (apply_nonneg _ _) _)
  have hbase := fixed_pivot_prime_original_pair_bound a b hab template template'
    C C' U U' D D' t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU' f f'
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP hfreq hfreq' δ hδ hnum
  have hh := fixed_pivot_top_prime_coefficient_pair_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    (fun p => hprime p p.property) checks C C' U U' D D' template template' t t' ht ht'
    f f' (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQmass i).ne')
    α V R hα hV hR hmax (fun p => hlowerP p p.property)
    (fun p => hupperP p p.property) hchecks M
    (finiteEdgeWeight (dirichletGraphEdge χ graph) unary)
    (fun x => finiteEdgeWeight_norm _ _ x (dirichletGraphEdge_norm χ graph) hunary)
    (δ + N * cost * atom) (add_nonneg hδ (mul_nonneg (mul_nonneg hN (by positivity)) hatom))
    (by
      simp only [finiteProductPrior]
      convert hbase using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [N, cost, atom]
      ring)
  change _ ≤ δ + N * (cost + Fintype.card J) * atom
  simp only [finiteProductPrior] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [N, cost, atom]
  ring

end Ostmann

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Ostmann.fixed_pivot_full_original_pair_bound_oai.{u_1, u_2} := @OAI.Ostmann.fixed_pivot_full_original_pair_bound_oai.{u_1, u_2}
