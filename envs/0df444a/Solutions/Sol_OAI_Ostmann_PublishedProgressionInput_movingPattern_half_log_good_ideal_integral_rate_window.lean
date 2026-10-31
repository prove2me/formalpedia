-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:21:17.912983+00:00
-- url     : https://prove2.me/submissions/7cc985ae-ab3f-4890-9f1a-e1cf310cec00

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_half_log_selected_prime_rate_window

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact line counts in the ideal giant residues -/

namespace Ostmann

open scoped BigOperators

theorem card_unitLine {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (a b : G) :
    Fintype.card {xy : G × G // a * xy.1 = b * xy.2} = Fintype.card G :=
  Fintype.card_congr (unitLineEquiv a b)

theorem card_externalLine {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    Fintype.card {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} =
      Fintype.card (ZMod p)ˣ :=
  Fintype.card_congr (externalLineEquiv a b)

theorem unitLine_probability {p : ℕ} [Fact p.Prime] (a b : (ZMod p)ˣ) :
    (Fintype.card {xy : (ZMod p)ˣ × (ZMod p)ˣ // a * xy.1 = b * xy.2} : ℝ) /
      (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℝ) =
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ := by
  rw [card_unitLine, Fintype.card_prod, Nat.cast_mul]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem externalLine_probability {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    (Fintype.card {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} : ℝ) /
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ) = (p : ℝ)⁻¹ := by
  rw [card_externalLine, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem line_zero_first_coefficient {K : Type*} [Field K]
    (b x y : K) (hb : b ≠ 0) (hy : y ≠ 0) : ¬ (0 : K) * x + b * y = 0 := by
  simpa only [zero_mul, zero_add] using mul_ne_zero hb hy

/-- Vanishing two-by-two minors reduce all occurrence tests to one nonzero row. -/
theorem dependent_lines_iff {K I : Type*} [Field K]
    (a b : I → K) (i : I) (ha : a i ≠ 0)
    (hdet : ∀ j, a i * b j - b i * a j = 0) (x y : K) :
    (∀ j, a j * x + b j * y = 0) ↔ a i * x + b i * y = 0 := by
  constructor
  · exact fun h => h i
  · intro h j
    have he : a i * (a j * x + b j * y) = 0 := by
      linear_combination a j * h + y * hdet j
    exact (mul_eq_zero.mp he).resolve_left ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lifts of a nonzero line modulo a prime square

The reduction map has exactly `p` lifts over every residue. A line with a
unit coefficient has exactly `p` zero lifts among the `p²` pairs over a
fixed solution modulo `p`. This is the relative `1/p` loss in §8.
-/

namespace Ostmann

open scoped BigOperators

/-- Every fiber of a surjective homomorphism between finite additive groups
has the same size. -/
theorem card_additiveFiber {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H]
    (φ : G →+ H) (hφ : Function.Surjective φ) (a : H) :
    Fintype.card G = Fintype.card H * Fintype.card {y : G // φ y = a} := by
  have hsame (b : H) : Fintype.card {y : G // φ y = b} =
      Fintype.card {y : G // φ y = a} := by
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    exact Fintype.card_congr ((additiveFiberEquiv φ y).trans (additiveFiberEquiv φ x).symm)
  calc
    _ = Fintype.card (Σ b : H, {y : G // φ y = b}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv φ)).symm
    _ = ∑ b : H, Fintype.card {y : G // φ y = b} := Fintype.card_sigma
    _ = _ := by simp only [hsame, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem card_squareReduction_fiber {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    Fintype.card {x : ZMod (p ^ 2) // squareReduction p x = a} = p := by
  have h := card_additiveFiber (squareReduction p).toAddMonoidHom
    (ZMod.castHom_surjective (dvd_pow_self p (by decide : 2 ≠ 0))) a
  simp only [ZMod.card] at h
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (h.symm.trans (pow_two p))

/-- In both giant environments the second residue is a unit. A nonzero
row vanishing there must have a unit first coefficient. -/
theorem square_line_first_isUnit {p : ℕ} [Fact p.Prime]
    (a b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0)
    (hrow : squareReduction p a ≠ 0 ∨ squareReduction p b ≠ 0)
    (hbase : squareReduction p a * x₀ + squareReduction p b * y₀ = 0) :
    IsUnit a := by
  apply (isUnit_square_iff a).mpr
  intro ha
  have hb := hrow.resolve_left (not_not.mpr ha)
  exact line_zero_first_coefficient (squareReduction p b) x₀ y₀ hb hy (ha ▸ hbase)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedFlagComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted error when finitely many arithmetic flags are replaced -/

namespace Ostmann

open scoped BigOperators

/-- A bounded function of finitely many flags changes only on their union of
exceptional events. This estimate retains the original independent weights. -/
theorem weighted_flag_comparison_le {X I : Type*} [Fintype X] [Fintype I]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f g : X → I → Bool) (bad : I → X → Prop) [∀ i x, Decidable (bad i x)]
    (heq : ∀ x, (∀ i, ¬bad i x) → f x = g x)
    (Ψ : X → (I → Bool) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x v, ‖Ψ x v‖ ≤ B) :
    ‖∑ x, (w x : ℂ) * (Ψ x (f x) - Ψ x (g x))‖ ≤
      2 * B * ∑ i, ∑ x, w x * if bad i x then 1 else 0 := by
  classical
  have hpoint (x : X) : ‖Ψ x (f x) - Ψ x (g x)‖ ≤
      2 * B * ∑ i, if bad i x then (1 : ℝ) else 0 := by
    by_cases hx : ∃ i, bad i x
    · obtain ⟨i, hi⟩ := hx
      have hsum : (1 : ℝ) ≤ ∑ j, if bad j x then 1 else 0 := by
        simpa only [hi, ite_true, if_true] using
          (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
            (show (0 : ℝ) ≤ if bad j x then 1 else 0 by split <;> norm_num))
            (Finset.mem_univ i))
      have hn : ‖Ψ x (f x) - Ψ x (g x)‖ ≤ 2 * B :=
        (norm_sub_le _ _).trans (by linarith [hΨ x (f x), hΨ x (g x)])
      exact hn.trans (by nlinarith)
    · have hf : f x = g x := heq x (by simpa only [not_exists] using hx)
      rw [hf, sub_self, norm_zero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  calc
    _ ≤ ∑ x, ‖(w x : ℂ) * (Ψ x (f x) - Ψ x (g x))‖ := norm_sum_le _ _
    _ = ∑ x, w x * ‖Ψ x (f x) - Ψ x (g x)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ ≤ ∑ x, w x * (2 * B * ∑ i, if bad i x then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = _ := by
      simp only [Finset.mul_sum]
      simp_rw [show ∀ x i, w x * (2 * B * (if bad i x then (1 : ℝ) else 0)) =
        2 * B * (w x * (if bad i x then 1 else 0)) by intros; ring]
      rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReversalRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient rows of the giant reversals

At a reversal one current giant is retained and the other becomes
`(v * Hminus - w * Hplus) / u`, with all three coefficients units modulo
the internal prime. The two current giants remain independent linear
forms in the top giants, so every subsequent numerator is a nonzero row.
-/

namespace Ostmann

namespace GiantRows

variable {R : Type*} [CommRing R]

theorem det_reverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) :
    (T.reverse left v w u).det =
      (if left then (u⁻¹ : Rˣ) * (v : R) else -(u⁻¹ : Rˣ) * (w : R)) * T.det := by
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, det] <;> ring

theorem isUnit_det_reverse (T : GiantRows R) (hT : IsUnit T.det)
    (left : Bool) (v w u : Rˣ) : IsUnit (T.reverse left v w u).det := by
  rw [det_reverse]
  apply IsUnit.mul _ hT
  cases left
  · exact (u⁻¹).isUnit.neg.mul w.isUnit
  · exact (u⁻¹).isUnit.mul v.isUnit

/-- Every numerator in an invertible current pair is a nonzero row. -/
theorem numerator_nonzero {K : Type*} [Field K] (T : GiantRows K)
    (hT : T.det ≠ 0) (v w : Kˣ) :
    (v : K) * T.c - (w : K) * T.a ≠ 0 ∨
      (v : K) * T.d - (w : K) * T.b ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨ha, hb⟩ := h
  have he : (v : K) * T.det = 0 := by
    dsimp [det]
    linear_combination T.a * hb - T.b * ha
  exact mul_ne_zero (Units.ne_zero v) hT he

end GiantRows

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialGiantRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clearing denominators along the giant histories

The five integer polynomials below represent both coefficient rows with a
common denominator. Each reversal uses only multiplication and subtraction;
their degree grows by at most the degree of the new slot data.
-/

namespace Ostmann

noncomputable section

namespace PolynomialGiantRows

variable {σ : Type*}

private theorem retained_quotient {K : Type*} [Field K] (a d u : K) (hu : u ≠ 0) :
    (u * a) / (d * u) = a / d := by
  field_simp

private theorem reversed_quotient {K : Type*} [Field K] (a c d v w u : K)
    (hd : d ≠ 0) (hu : u ≠ 0) :
    (v * c - w * a) / (d * u) = u⁻¹ * (v * (c / d) - w * (a / d)) := by
  field_simp

/-- The polynomial recurrence evaluates to the actual rational reversal. -/
theorem normalized_reverse {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hd : φ T.denominator ≠ 0) (hv : φ v ≠ 0) (hw : φ w ≠ 0) (hu : φ u ≠ 0) :
    (T.reverse left v w u).normalized φ =
      (T.normalized φ).reverse left (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
        (Units.mk0 (φ u) hu) := by
  cases left <;> apply GiantRows.ext <;>
    simp only [reverse, normalized, GiantRows.reverse, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, map_mul, map_sub, Units.val_mk0, Units.val_inv_eq_inv_val]
  all_goals first
    | exact retained_quotient _ _ _ hu
    | exact reversed_quotient _ _ _ _ _ _ hd hu

theorem degreeLE_identity : (identity : PolynomialGiantRows σ).DegreeLE 0 := by
  simp [DegreeLE, identity, GiantRows.identity]

theorem degreeLE_reverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) (d e : ℕ) (hT : T.DegreeLE d)
    (hv : v.totalDegree ≤ e) (hw : w.totalDegree ≤ e) (hu : u.totalDegree ≤ e) :
    (T.reverse left v w u).DegreeLE (d + e) := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  have hmul (f g : MvPolynomial σ ℤ) (hf : f.totalDegree ≤ e) (hg : g.totalDegree ≤ d) :
      (f * g).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_mul f g).trans (by omega)
  have hsub (f g : MvPolynomial σ ℤ) (hf : f.totalDegree ≤ d + e)
      (hg : g.totalDegree ≤ d + e) : (f - g).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_sub f g).trans (max_le hf hg)
  have hden' : (T.denominator * u).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hden hu)
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, DegreeLE]
  · exact ⟨hsub _ _ (hmul _ _ hv hc) (hmul _ _ hw ha),
      hsub _ _ (hmul _ _ hv hd) (hmul _ _ hw hb), hmul _ _ hu hc, hmul _ _ hu hd, hden'⟩
  · exact ⟨hmul _ _ hu ha, hmul _ _ hu hb,
      hsub _ _ (hmul _ _ hv hc) (hmul _ _ hw ha),
      hsub _ _ (hmul _ _ hv hd) (hmul _ _ hw hb), hden'⟩

end PolynomialGiantRows

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialGiantTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cleared coefficient and minor tests for the giant lines -/

namespace Ostmann

noncomputable section

namespace PolynomialGiantLine

variable {σ : Type*}

theorem normalized_zero_iff {K : Type*} [Field K] (L : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K) (hden : φ L.denominator ≠ 0) :
    ((L.normalized φ).1 = 0 ↔ φ L.a = 0) ∧
      ((L.normalized φ).2 = 0 ↔ φ L.b = 0) := by
  simp only [normalized, div_eq_zero_iff, hden, or_false, and_self]

theorem normalized_minor {K : Type*} [Field K] (L M : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K)
    (hL : φ L.denominator ≠ 0) (hM : φ M.denominator ≠ 0) :
    (L.normalized φ).1 * (M.normalized φ).2 -
      (L.normalized φ).2 * (M.normalized φ).1 =
      φ (L.minor M) / (φ L.denominator * φ M.denominator) := by
  simp only [normalized, minor, map_sub, map_mul]
  field_simp

theorem normalized_minor_zero_iff {K : Type*} [Field K] (L M : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K)
    (hL : φ L.denominator ≠ 0) (hM : φ M.denominator ≠ 0) :
    ((L.normalized φ).1 * (M.normalized φ).2 -
      (L.normalized φ).2 * (M.normalized φ).1 = 0) ↔ φ (L.minor M) = 0 := by
  rw [normalized_minor L M φ hL hM]
  simp only [div_eq_zero_iff, mul_ne_zero hL hM, or_false]

end PolynomialGiantLine

/-- Normalizing the cleared numerator gives its actual two coefficients. -/
theorem PolynomialGiantRows.normalized_numeratorLine {σ K : Type*} [Field K]
    (T : PolynomialGiantRows σ) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K) (hd : φ T.denominator ≠ 0) :
    (T.numeratorLine v w).normalized φ =
      (φ v * (T.normalized φ).c - φ w * (T.normalized φ).a,
        φ v * (T.normalized φ).d - φ w * (T.normalized φ).b) := by
  apply Prod.ext <;>
    simp only [PolynomialGiantLine.normalized, PolynomialGiantRows.numeratorLine,
      PolynomialGiantRows.normalized, map_sub, map_mul] <;> field_simp

/-- Reduction of an integer polynomial evaluation commutes with casting to a
prime residue ring. Thus these tests are genuine integer divisibility tests. -/
theorem integerPolynomial_cast_eval {σ : Type*} (x : σ → ℤ) (F : MvPolynomial σ ℤ) (p : ℕ) :
    ((MvPolynomial.eval₂Hom (RingHom.id ℤ) x F : ℤ) : ZMod p) =
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) F := by
  simpa [Int.castRingHom] using
    (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom (ZMod p)) F)

/-- A cleared polynomial vanishes in the prime field exactly when the prime
divides its actual integer evaluation. -/
theorem integerPolynomial_mod_zero_iff {σ : Type*} (x : σ → ℤ)
    (F : MvPolynomial σ ℤ) (p : ℕ) :
    MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) F = 0 ↔
      (p : ℤ) ∣ MvPolynomial.eval₂Hom (RingHom.id ℤ) x F := by
  rw [← integerPolynomial_cast_eval, ZMod.intCast_zmod_eq_zero_iff_dvd]

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialValueBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size of the cleared arithmetic tests at actual prime values

A uniform bound on the slot values gives an explicit bound on every cleared
coefficient and denominator. This avoids any assumed bound on the height of
newly constructed polynomials.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

theorem valueLE_identity (φ : MvPolynomial σ ℤ →+* ℝ) :
    (identity : PolynomialGiantRows σ).ValueLE φ 1 := by
  simp [ValueLE, identity, GiantRows.identity]

theorem valueLE_reverse (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* ℝ)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (H L : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) (hu : |φ u| ≤ L) :
    (T.reverse left v w u).ValueLE φ (2 * L * H) := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  have hm (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ L) (hg : |φ g| ≤ H) :
      |φ (f * g)| ≤ L * H := by
    rw [map_mul, abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) hL
  have hs (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ L * H) (hg : |φ g| ≤ L * H) :
      |φ (f - g)| ≤ 2 * L * H := by
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith)
  have htwice : L * H ≤ 2 * L * H := by nlinarith
  have hden' : |φ (T.denominator * u)| ≤ 2 * L * H := by
    rw [mul_comm T.denominator u]
    exact (hm u T.denominator hu hden).trans htwice
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, ValueLE]
  · exact ⟨hs _ _ (hm v T.rows.c hv hc) (hm w T.rows.a hw ha),
      hs _ _ (hm v T.rows.d hv hd) (hm w T.rows.b hw hb),
      (hm _ _ hu hc).trans htwice, (hm _ _ hu hd).trans htwice, hden'⟩
  · exact ⟨(hm _ _ hu ha).trans htwice, (hm _ _ hu hb).trans htwice,
      hs _ _ (hm v T.rows.c hv hc) (hm w T.rows.a hw ha),
      hs _ _ (hm v T.rows.d hv hd) (hm w T.rows.b hw hb), hden'⟩

/-- A minor of two bounded coefficient rows has the stated elementary size. -/
theorem minor_value_le (φ : MvPolynomial σ ℤ →+* ℝ) (a b c d : MvPolynomial σ ℤ)
    (H : ℝ) (hH : 0 ≤ H) (ha : |φ a| ≤ H) (hb : |φ b| ≤ H)
    (hc : |φ c| ≤ H) (hd : |φ d| ≤ H) : |φ (a * d - b * c)| ≤ 2 * H ^ 2 := by
  have h₁ : |φ a * φ d| ≤ H * H := by
    rw [abs_mul]
    exact mul_le_mul ha hd (abs_nonneg _) hH
  have h₂ : |φ b * φ c| ≤ H * H := by
    rw [abs_mul]
    exact mul_le_mul hb hc (abs_nonneg _) hH
  simp only [map_sub, map_mul]
  exact (abs_sub _ _).trans (by nlinarith)

end PolynomialGiantRows

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_InternalLineProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rank and feasibility tests for repeated internal-prime occurrences

Section 8, equation `arith-line-probabilities`: the simultaneous linear tests
have probability zero in rank two, and exactly `1/(p-1)` or `1/p` in the
respective feasible rank-one cases. A distinguished nonzero occurrence is
sufficient; no independence of the repeated tests is assumed.
-/

namespace Ostmann

open scoped BigOperators
open scoped Classical

theorem lineSystem_iff {K I : Type*} [Field K] (a b : I → K) (i : I)
    (hrow : a i ≠ 0 ∨ b i ≠ 0) (x y : K) (hy : y ≠ 0) :
    (∀ j, a j * x + b j * y = 0) ↔
      externalLineFeasible a b i ∧ a i * x + b i * y = 0 := by
  constructor
  · intro h
    have ha : a i ≠ 0 := by
      intro ha
      exact line_zero_first_coefficient (b i) x y
        (hrow.resolve_left (not_not.mpr ha)) hy (ha ▸ h i)
    refine ⟨⟨ha, fun j => ?_⟩, h i⟩
    have he : (a i * b j - b i * a j) * y = 0 := by
      linear_combination a i * h j - a j * h i
    exact (mul_eq_zero.mp he).resolve_right hy
  · rintro ⟨⟨ha, hrank⟩, h⟩
    exact (dependent_lines_iff a b i ha hrank x y).mpr h

theorem unit_lineSystem_iff {K I : Type*} [Field K] (a b : I → K) (i : I)
    (hrow : a i ≠ 0 ∨ b i ≠ 0) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (∀ j, a j * x + b j * y = 0) ↔
      unitLineFeasible a b i ∧ a i * x + b i * y = 0 := by
  rw [lineSystem_iff a b i hrow x y hy]
  constructor
  · rintro ⟨⟨ha, hrank⟩, h⟩
    have hb : b i ≠ 0 := by
      intro hb
      have he : a i * x = 0 := by simpa only [hb, zero_mul, add_zero] using h
      exact mul_ne_zero ha hx he
    exact ⟨⟨ha, hb, hrank⟩, h⟩
  · exact fun ⟨⟨ha, _, hrank⟩, h⟩ => ⟨⟨ha, hrank⟩, h⟩

theorem external_lineSystem_probability {I : Type*} {p : ℕ} [Fact p.Prime]
    (a b : I → ZMod p) (i : I) (hrow : a i ≠ 0 ∨ b i ≠ 0) :
    (Fintype.card {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ) =
      if externalLineFeasible a b i then (p : ℝ)⁻¹ else 0 := by
  classical
  by_cases hg : externalLineFeasible a b i
  · rw [ite_eq_left hg]
    let u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.1).unit
    have hu : (u : ZMod p) = a i := IsUnit.unit_spec _
    have he (z : ZMod p × (ZMod p)ˣ) :
        (∀ j, a j * z.1 + b j * z.2 = 0) ↔ (u : ZMod p) * z.1 = (-b i) * z.2 := by
      rw [lineSystem_iff a b i hrow z.1 z.2 (Units.ne_zero z.2), and_iff_right hg, hu]
      constructor <;> intro h <;> linear_combination h
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    exact externalLine_probability u (-b i)
  · rw [ite_eq_right hg]
    have : IsEmpty {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} :=
      ⟨fun z => hg ((lineSystem_iff a b i hrow z.1.1 z.1.2
        (Units.ne_zero z.1.2)).mp z.2).1⟩
    simp

theorem unit_lineSystem_probability {I : Type*} {p : ℕ} [Fact p.Prime]
    (a b : I → ZMod p) (i : I) (hrow : a i ≠ 0 ∨ b i ≠ 0) :
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) =
      if unitLineFeasible a b i then (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ else 0 := by
  classical
  by_cases hg : unitLineFeasible a b i
  · rw [ite_eq_left hg]
    let u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.1).unit
    let v : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.2.1).unit
    have hu : (u : ZMod p) = a i := IsUnit.unit_spec _
    have hv : (v : ZMod p) = b i := IsUnit.unit_spec _
    have he (z : (ZMod p)ˣ × (ZMod p)ˣ) :
        (∀ j, a j * z.1 + b j * z.2 = 0) ↔ u * z.1 = (-v) * z.2 := by
      rw [unit_lineSystem_iff a b i hrow z.1 z.2 (Units.ne_zero z.1) (Units.ne_zero z.2),
        and_iff_right hg]
      rw [← Units.val_inj]
      simp only [Units.val_mul, Units.val_neg, hu, hv]
      constructor <;> intro h <;> linear_combination h
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    exact unitLine_probability u (-v)
  · rw [ite_eq_right hg]
    have : IsEmpty {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} :=
      ⟨fun z => hg ((unit_lineSystem_iff a b i hrow z.1.1 z.1.2
        (Units.ne_zero z.1.1) (Units.ne_zero z.1.2)).mp z.2).1⟩
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialLineFlags
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact cleared polynomial flags for an internal line system -/

namespace Ostmann

noncomputable section

open scoped Classical

theorem external_polynomialLine_flags_iff {σ J K : Type*} [Field K]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* K)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    lineFeasibleFlags true (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) ↔
      externalLineFeasible (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) i := by
  simp only [lineFeasibleFlags, lineTestPolynomials, arithmeticTestFlag_eq_false_iff,
    arithmeticTestFlag_eq_true_iff, true_or, true_and, externalLineFeasible, lineRankOne]
  apply and_congr
  · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).1).symm
  · exact forall_congr' fun j =>
      ((L i).normalized_minor_zero_iff (L j) φ (hd i) (hd j)).symm

theorem unit_polynomialLine_flags_iff {σ J K : Type*} [Field K]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* K)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    lineFeasibleFlags false (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) ↔
      unitLineFeasible (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) i := by
  simp only [lineFeasibleFlags, lineTestPolynomials, arithmeticTestFlag_eq_false_iff,
    arithmeticTestFlag_eq_true_iff, Bool.false_eq_true, false_or,
    unitLineFeasible, lineRankOne]
  apply and_congr
  · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).1).symm
  · apply and_congr
    · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).2).symm
    · exact forall_congr' fun j =>
        ((L i).normalized_minor_zero_iff (L j) φ (hd i) (hd j)).symm

/-- The divisibility flags of the actual integer evaluations agree exactly
with zero tests in the prime residue field. -/
theorem line_divisibility_flags_eq {J A : Type*} {n : ℕ} (value : A → ℤ)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (x : Fin n → A) (p : ℕ) :
    (fun s => arithmeticTestFlag (p ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) =
      (fun s => arithmeticTestFlag
        (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p))
          (fun j => (value (x j) : ZMod p)) (lineTestPolynomials L i s) = 0)) := by
  funext s
  apply congrArg arithmeticTestFlag
  apply propext
  exact (Int.natCast_dvd).symm.trans
    (integerPolynomial_mod_zero_iff (fun j => value (x j)) _ p).symm

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLineIntegration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual line integrals as bounded functions of the cleared polynomial tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem internalLineScalar_nonneg (external : Bool) (p : ℕ) :
    0 ≤ internalLineScalar external p := by
  unfold internalLineScalar
  positivity

theorem internalLineFlagWeight_nonneg {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) : 0 ≤ internalLineFlagWeight external p flags := by
  unfold internalLineFlagWeight
  split_ifs
  · exact internalLineScalar_nonneg external p
  · rfl

theorem internalLineProbability_nonneg {J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (a b : J → ZMod p) : 0 ≤ internalLineProbability external a b := by
  unfold internalLineProbability
  split_ifs <;> positivity

theorem external_lineSystem_integral_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    (Fintype.card {z : ZMod p × (ZMod p)ˣ //
      ∀ j, ((L j).normalized φ).1 * z.1 + ((L j).normalized φ).2 * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ) =
      internalLineFlagWeight true p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  rw [external_lineSystem_probability _ _ i hrow]
  unfold internalLineFlagWeight
  rw [external_polynomialLine_flags_iff L i φ hd]
  rfl

theorem unit_lineSystem_integral_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ //
      ∀ j, ((L j).normalized φ).1 * z.1 + ((L j).normalized φ).2 * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) =
      internalLineFlagWeight false p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  rw [unit_lineSystem_probability _ _ i hrow]
  unfold internalLineFlagWeight
  rw [unit_polynomialLine_flags_iff L i φ hd]
  have hc : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
  simp only [internalLineScalar, Bool.false_eq_true, ite_false, if_false, hc]

theorem internalLineProbability_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (L : J → PolynomialGiantLine σ) (i : J)
    (φ : MvPolynomial σ ℤ →+* ZMod p) (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    internalLineProbability external (fun j => ((L j).normalized φ).1)
      (fun j => ((L j).normalized φ).2) =
      internalLineFlagWeight external p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  cases external
  · exact unit_lineSystem_integral_eq_flags L i φ hd hrow
  · exact external_lineSystem_integral_eq_flags L i φ hd hrow

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

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

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialVariableSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variables absent from the arithmetic coefficient tests

Clearing ancestor denominators introduces only variables from the existing
slots. In particular a compensation type omitted from those slots stays absent
from every coefficient polynomial and every minor formed from them.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

private theorem vars_mul_subset [DecidableEq σ] {f g : MvPolynomial σ ℤ} {S : Finset σ}
    (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) : (f * g).vars ⊆ S :=
  (MvPolynomial.vars_mul f g).trans (Finset.union_subset hf hg)

private theorem vars_sub_subset [DecidableEq σ] {f g : MvPolynomial σ ℤ} {S : Finset σ}
    (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) : (f - g).vars ⊆ S :=
  (MvPolynomial.vars_sub_subset (p := f) (q := g)).trans (Finset.union_subset hf hg)

theorem usesOnly_identity (S : Finset σ) : (identity : PolynomialGiantRows σ).UsesOnly S := by
  simp [UsesOnly, identity, GiantRows.identity]

theorem usesOnly_reverse [DecidableEq σ] (T : PolynomialGiantRows σ) (S : Finset σ) (hT : T.UsesOnly S)
    (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) (hu : u.vars ⊆ S) :
    (T.reverse left v w u).UsesOnly S := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, UsesOnly]
  · exact ⟨vars_sub_subset (vars_mul_subset hv hc) (vars_mul_subset hw ha),
      vars_sub_subset (vars_mul_subset hv hd) (vars_mul_subset hw hb),
      vars_mul_subset hu hc, vars_mul_subset hu hd, vars_mul_subset hden hu⟩
  · exact ⟨vars_mul_subset hu ha, vars_mul_subset hu hb,
      vars_sub_subset (vars_mul_subset hv hc) (vars_mul_subset hw ha),
      vars_sub_subset (vars_mul_subset hv hd) (vars_mul_subset hw hb),
      vars_mul_subset hden hu⟩

/-- A two-by-two minor has no variables beyond those of its four entries. -/
theorem minor_usesOnly [DecidableEq σ] {a b c d : MvPolynomial σ ℤ} {S : Finset σ}
    (ha : a.vars ⊆ S) (hb : b.vars ⊆ S) (hc : c.vars ⊆ S) (hd : d.vars ⊆ S) :
    (a * d - b * c).vars ⊆ S :=
  vars_sub_subset (vars_mul_subset ha hd) (vars_mul_subset hb hc)

/-- Forming a rank test doubles the available coefficient degree bound. -/
theorem minor_degree_le {a b c d : MvPolynomial σ ℤ} (D : ℕ)
    (ha : a.totalDegree ≤ D) (hb : b.totalDegree ≤ D)
    (hc : c.totalDegree ≤ D) (hd : d.totalDegree ≤ D) :
    (a * d - b * c).totalDegree ≤ 2 * D := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

end PolynomialGiantRows

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialLineBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree, value and variable bounds for the actual line tests -/

namespace Ostmann

namespace PolynomialGiantRows

theorem numeratorLine_degree_le {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) (D d : ℕ) (hT : T.DegreeLE D)
    (hv : v.totalDegree ≤ d) (hw : w.totalDegree ≤ d) :
    (T.numeratorLine v w).a.totalDegree ≤ D + d ∧
      (T.numeratorLine v w).b.totalDegree ≤ D + d := by
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  constructor <;> apply (MvPolynomial.totalDegree_sub _ _).trans <;> apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

theorem numeratorLine_value_le {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) (φ : MvPolynomial σ ℤ →+* ℝ)
    (H U : ℝ) (hU : 0 ≤ U) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ U) (hw : |φ w| ≤ U) :
    |φ (T.numeratorLine v w).a| ≤ 2 * U * H ∧
      |φ (T.numeratorLine v w).b| ≤ 2 * U * H := by
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  have hm (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ U) (hg : |φ g| ≤ H) :
      |φ (f * g)| ≤ U * H := by
    rw [map_mul, abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) hU
  constructor
  · change |φ (v * T.rows.c - w * T.rows.a)| ≤ _
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith [hm v T.rows.c hv hc, hm w T.rows.a hw ha])
  · change |φ (v * T.rows.d - w * T.rows.b)| ≤ _
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith [hm v T.rows.d hv hd, hm w T.rows.b hw hb])

theorem numeratorLine_vars_subset {σ : Type*} [DecidableEq σ]
    (T : PolynomialGiantRows σ) (v w : MvPolynomial σ ℤ) (S : Finset σ)
    (hT : T.UsesOnly S) (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) :
    (T.numeratorLine v w).a.vars ⊆ S ∧ (T.numeratorLine v w).b.vars ⊆ S := by
  have hm (f g : MvPolynomial σ ℤ) (hf : f.vars ⊆ S) (hg : g.vars ⊆ S) :
      (f * g).vars ⊆ S := (MvPolynomial.vars_mul f g).trans (Finset.union_subset hf hg)
  obtain ⟨ha, hb, hc, hd, _⟩ := hT
  constructor
  · exact (MvPolynomial.vars_sub_subset (p := v * T.rows.c) (q := w * T.rows.a)).trans
      (Finset.union_subset (hm v T.rows.c hv hc) (hm w T.rows.a hw ha))
  · exact (MvPolynomial.vars_sub_subset (p := v * T.rows.d) (q := w * T.rows.b)).trans
      (Finset.union_subset (hm v T.rows.d hv hd) (hm w T.rows.b hw hb))

end PolynomialGiantRows

theorem lineTestPolynomials_degree_le {σ J : Type*} (L : J → PolynomialGiantLine σ)
    (i : J) (D : ℕ) (hL : ∀ j, (L j).a.totalDegree ≤ D ∧ (L j).b.totalDegree ≤ D)
    (s : Bool ⊕ J) : (lineTestPolynomials L i s).totalDegree ≤ 2 * D := by
  rcases s with b | j
  · cases b
    · exact (hL i).1.trans (by omega)
    · exact (hL i).2.trans (by omega)
  · exact PolynomialGiantRows.minor_degree_le D (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem lineTestPolynomials_value_le {σ J : Type*} (L : J → PolynomialGiantLine σ)
    (i : J) (φ : MvPolynomial σ ℤ →+* ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hL : ∀ j, |φ (L j).a| ≤ H ∧ |φ (L j).b| ≤ H)
    (s : Bool ⊕ J) : |φ (lineTestPolynomials L i s)| ≤ 2 * H ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hh : H ≤ 2 * H ^ 2 := by nlinarith
  rcases s with b | j
  · cases b
    · exact (hL i).1.trans hh
    · exact (hL i).2.trans hh
  · exact PolynomialGiantRows.minor_value_le φ _ _ _ _ H hH0
      (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem lineTestPolynomials_vars_subset {σ J : Type*} [DecidableEq σ]
    (L : J → PolynomialGiantLine σ) (i : J) (S : Finset σ)
    (hL : ∀ j, (L j).a.vars ⊆ S ∧ (L j).b.vars ⊆ S) (s : Bool ⊕ J) :
    (lineTestPolynomials L i s).vars ⊆ S := by
  rcases s with b | j
  · cases b
    · exact (hL i).1
    · exact (hL i).2
  · exact PolynomialGiantRows.minor_usesOnly (hL i).1 (hL i).2 (hL j).1 (hL j).2

theorem integerTestValue_real_cast {A : Type*} {n : ℕ} (value : A → ℤ)
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → A) :
    (integerTestValue value F x : ℝ) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun j => (value (x j) : ℝ)) F := by
  simpa [integerTestValue, Int.castRingHom] using
    MvPolynomial.map_eval₂Hom (RingHom.id ℤ) (fun j => value (x j)) (Int.castRingHom ℝ) F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IndependentCoordinate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_JointSampledComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint signed replacement with actual internal-prime coordinates

Different tests can use different sampled primes and can depend on the other
prime coordinates. Each test only excludes its own prime coordinate.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem joint_sampled_polynomial_comparison_le {A I : Type*}
    [Fintype A] [Nonempty A] [Fintype I] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → MvPolynomial (Fin (n + 1)) ℤ) (coordinate : I → Fin (n + 1))
    (habsent : ∀ i, coordinate i ∉ (F i).vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ i a, μ (coordinate i) a ≤ β)
    (hsize : ∀ i a, μ (coordinate i) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ i x, |(integerTestValue value (F i) x : ℝ)| ≤ H)
    (Ψ : (Fin (n + 1) → A) → (I → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x flags, ‖Ψ x flags‖ ≤ B) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (Ψ x (fun i => arithmeticTestFlag
        (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs)) -
       Ψ x (fun i => arithmeticTestFlag (F i = 0)))‖ ≤
      2 * B * ∑ i, (((F i).totalDegree : ℝ) * α + (Real.log H / V) * β) := by
  let bad := fun i x => F i ≠ 0 ∧ prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs
  have hprob (i : I) : (∑ x, productPrior μ x * if bad i x then (1 : ℝ) else 0) ≤
      ((F i).totalDegree : ℝ) * α + (Real.log H / V) * β := by
    by_cases hi : F i = 0
    · simp only [bad, hi, ne_eq, not_true_eq_false, false_and, ite_false, if_false, mul_zero,
        Finset.sum_const_zero]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hα)
        (mul_nonneg (div_nonneg (Real.log_nonneg hH) hV.le) hβ)
    · simp only [bad, hi, ne_eq, not_false_eq_true, true_and]
      exact sampled_coordinate_prime_coincidence_le value hinj prime hpInj hprime (F i) hi
        (coordinate i) (habsent i) μ hμ hmass α β V H hα hβ hV hH hmax (hpmax i) (hsize i) (hvalue i)
  have heq (x : Fin (n + 1) → A) (hx : ∀ i, ¬bad i x) :
      (fun i => arithmeticTestFlag
        (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs)) =
      (fun i => arithmeticTestFlag (F i = 0)) := by
    funext i
    by_cases hi : F i = 0
    · simp [hi, integerTestValue]
    · have hnd : ¬prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs :=
        fun h => hx i ⟨hi, h⟩
      simp [hi, hnd]
  have h := @weighted_flag_comparison_le (Fin (n + 1) → A) I inferInstance inferInstance
    (productPrior μ) (productPrior_nonneg μ hμ)
    (fun x i => arithmeticTestFlag
      (prime (x (coordinate i)) ∣ (integerTestValue value (F i) x).natAbs))
    (fun _ i => arithmeticTestFlag (F i = 0)) bad (fun _ _ => inferInstance)
    heq Ψ B hB hΨ
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hprob i) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered coefficient rows for the moving-giant reversal

In the manuscript's order both children put the inserted giant first. The
left child is therefore the exchanged version of the retained-first reversal.
This exchange preserves the nonvanishing determinant used in the line bounds.
-/

namespace Ostmann
namespace GiantRows

variable {R : Type*} [CommRing R]

theorem det_swap (T : GiantRows R) : T.swap.det = -T.det := by
  simp only [swap, det]
  ring

theorem isUnit_det_movingReverse (T : GiantRows R) (hT : IsUnit T.det)
    (left : Bool) (v w u : Rˣ) : IsUnit (T.movingReverse left v w u).det := by
  cases left
  · exact isUnit_det_reverse T hT false v w u
  · change IsUnit (T.reverse true v w u).swap.det
    rw [det_swap]
    exact (isUnit_det_reverse T hT true v w u).neg

end GiantRows

namespace PolynomialGiantRows

variable {σ : Type*}

theorem normalized_movingReverse {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hd : φ T.denominator ≠ 0) (hv : φ v ≠ 0) (hw : φ w ≠ 0) (hu : φ u ≠ 0) :
    (T.movingReverse left v w u).normalized φ =
      (T.normalized φ).movingReverse left (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
        (Units.mk0 (φ u) hu) := by
  cases left <;> simp only [movingReverse, GiantRows.movingReverse, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true, normalized_swap, normalized_reverse T φ _ v w u hd hv hw hu]

theorem degreeLE_movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) (d e : ℕ) (hT : T.DegreeLE d)
    (hv : v.totalDegree ≤ e) (hw : w.totalDegree ≤ e) (hu : u.totalDegree ≤ e) :
    (T.movingReverse left v w u).DegreeLE (d + e) := by
  have h := degreeLE_reverse T left v w u d e hT hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

end PolynomialGiantRows
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cleared line bounds for the source-ordered moving giant histories -/

namespace Ostmann
namespace PolynomialGiantRows

variable {σ : Type*}

theorem denominator_movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) :
    (T.movingReverse left v w u).denominator = T.denominator * u := by
  cases left <;> rfl

theorem usesOnly_movingReverse [DecidableEq σ] (T : PolynomialGiantRows σ)
    (S : Finset σ) (hT : T.UsesOnly S) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) (hu : u.vars ⊆ S) :
    (T.movingReverse left v w u).UsesOnly S := by
  have h := usesOnly_reverse T S hT left v w u hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

theorem valueLE_movingReverse (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* ℝ) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) (hu : |φ u| ≤ L) :
    (T.movingReverse left v w u).ValueLE φ (2 * L * H) := by
  have h := valueLE_reverse T φ left v w u H L hH hL hT hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

end PolynomialGiantRows

theorem movingPolynomialAncestors_denominator {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (movingPolynomialAncestors steps).denominator ≠ 0 := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity]
  | cons s steps ih =>
    rw [movingPolynomialAncestors, PolynomialGiantRows.denominator_movingReverse, map_mul]
    exact mul_ne_zero (ih fun t ht => h t (by simp [ht])) (h s (by simp))

theorem movingPolynomialAncestors_det {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0) :
    IsUnit ((movingPolynomialAncestors steps).normalized φ).det := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity,
      PolynomialGiantRows.normalized, GiantRows.identity, GiantRows.det]
  | cons s steps ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    have hd := movingPolynomialAncestors_denominator steps φ
      (fun t ht => (h t (by simp [ht])).2.2)
    rw [movingPolynomialAncestors, PolynomialGiantRows.normalized_movingReverse _ φ
      s.left s.v s.w s.u hd hs.1 hs.2.1 hs.2.2]
    exact GiantRows.isUnit_det_movingReverse _ ht _ _ _ _

theorem movingPolynomialAncestors_degree {σ : Type*}
    (steps : List (PolynomialReversal σ)) (d : ℕ)
    (h : ∀ s ∈ steps, s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d) :
    (movingPolynomialAncestors steps).DegreeLE (steps.length * d) := by
  induction steps with
  | nil => simpa only [movingPolynomialAncestors, List.length_nil, Nat.zero_mul] using
      (PolynomialGiantRows.degreeLE_identity (σ := σ))
  | cons s steps ih =>
    have hs := h s (by simp)
    simpa only [movingPolynomialAncestors, List.length_cons, Nat.add_mul, one_mul] using
      PolynomialGiantRows.degreeLE_movingReverse (movingPolynomialAncestors steps)
        s.left s.v s.w s.u (steps.length * d) d (ih fun t ht => h t (by simp [ht]))
        hs.1 hs.2.1 hs.2.2

theorem movingPolynomialAncestors_usesOnly {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (S : Finset σ)
    (h : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S) :
    (movingPolynomialAncestors steps).UsesOnly S := by
  induction steps with
  | nil => exact PolynomialGiantRows.usesOnly_identity S
  | cons s steps ih =>
    have hs := h s (by simp)
    exact PolynomialGiantRows.usesOnly_movingReverse _ S
      (ih fun t ht => h t (by simp [ht])) s.left s.v s.w s.u hs.1 hs.2.1 hs.2.2

theorem movingPolynomialAncestors_value {σ : Type*}
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ s ∈ steps, |φ s.v| ≤ L ∧ |φ s.w| ≤ L ∧ |φ s.u| ≤ L) :
    (movingPolynomialAncestors steps).ValueLE φ ((2 * L) ^ steps.length) := by
  induction steps with
  | nil => exact PolynomialGiantRows.valueLE_identity φ
  | cons s steps ih =>
    have hs := h s (by simp)
    have he : 2 * L * (2 * L) ^ steps.length = (2 * L) ^ (s :: steps).length := by
      rw [List.length_cons, pow_succ]
      ring
    rw [← he]
    exact PolynomialGiantRows.valueLE_movingReverse _ φ s.left s.v s.w s.u _ L
      (pow_nonneg (by positivity) _) hL (ih fun t ht => h t (by simp [ht]))
      hs.1 hs.2.1 hs.2.2

/-- Nonvanishing needed before the current compensation prime is sampled. -/
theorem movingHistoryLine_nonzero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0)
    (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    φ (movingHistoryLine steps v w).a ≠ 0 ∨ φ (movingHistoryLine steps v w).b ≠ 0 := by
  have hd := movingPolynomialAncestors_denominator steps φ (fun s hs => (h s hs).2.2)
  have hdet := (movingPolynomialAncestors_det steps φ h).ne_zero
  have hn := GiantRows.numerator_nonzero ((movingPolynomialAncestors steps).normalized φ)
    hdet (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
  have hn' : ((movingHistoryLine steps v w).normalized φ).1 ≠ 0 ∨
      ((movingHistoryLine steps v w).normalized φ).2 ≠ 0 := by
    rw [movingHistoryLine, PolynomialGiantRows.normalized_numeratorLine _ v w φ hd]
    simpa only [Units.val_mk0] using hn
  have hz := (movingHistoryLine steps v w).normalized_zero_iff φ hd
  exact hn'.imp (fun h h₀ => h (hz.1.mpr h₀)) (fun h h₀ => h (hz.2.mpr h₀))

/-- Concrete degree bound for the coefficient tests in the ancestor ordering. -/
theorem movingHistoryLine_degree {σ : Type*}
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (d : ℕ) (hs : ∀ s ∈ steps,
      s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d)
    (hv : v.totalDegree ≤ d) (hw : w.totalDegree ≤ d) :
    (movingHistoryLine steps v w).a.totalDegree ≤ (steps.length + 1) * d ∧
      (movingHistoryLine steps v w).b.totalDegree ≤ (steps.length + 1) * d := by
  simpa only [movingHistoryLine, Nat.add_mul, one_mul] using
    PolynomialGiantRows.numeratorLine_degree_le (movingPolynomialAncestors steps) v w
      (steps.length * d) d (movingPolynomialAncestors_degree steps d hs) hv hw

theorem movingHistoryLine_value {σ : Type*}
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ s ∈ steps, |φ s.v| ≤ L ∧ |φ s.w| ≤ L ∧ |φ s.u| ≤ L)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) :
    |φ (movingHistoryLine steps v w).a| ≤ (2 * L) ^ (steps.length + 1) ∧
      |φ (movingHistoryLine steps v w).b| ≤ (2 * L) ^ (steps.length + 1) := by
  have h := PolynomialGiantRows.numeratorLine_value_le (movingPolynomialAncestors steps)
    v w φ ((2 * L) ^ steps.length) L hL (movingPolynomialAncestors_value steps φ L hL hs) hv hw
  have he : 2 * L * (2 * L) ^ steps.length = (2 * L) ^ (steps.length + 1) := by
    rw [pow_succ]
    ring
  simpa only [movingHistoryLine, he] using h

theorem movingHistoryLine_vars_subset {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ) (S : Finset σ)
    (hs : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) :
    (movingHistoryLine steps v w).a.vars ⊆ S ∧ (movingHistoryLine steps v w).b.vars ⊆ S :=
  PolynomialGiantRows.numeratorLine_vars_subset _ v w S
    (movingPolynomialAncestors_usesOnly steps S hs) hv hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual slot products in the moving-giant line polynomials

Lists retain multiplicities: an ancestral compensation prime may occur in
several descendant regular products. No squarefree polynomial is substituted.
-/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSlotProduct_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotProduct slots) = (slots.map x).prod := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih => simpa [movingSlotProduct] using congrArg (x i * ·) ih

theorem movingSlotCoefficient_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (s : ℤ) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotCoefficient s slots) =
      f s * (slots.map x).prod := by
  simp only [movingSlotCoefficient, map_mul, MvPolynomial.eval₂Hom_C,
    movingSlotProduct_eval]

theorem movingSlotProduct_degree {σ : Type*} (slots : List σ) :
    (movingSlotProduct slots).totalDegree ≤ slots.length := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih =>
    change (MvPolynomial.X i * movingSlotProduct slots).totalDegree ≤ slots.length + 1
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_X]
      omega)

theorem movingSlotCoefficient_degree {σ : Type*} (s : ℤ) (slots : List σ) :
    (movingSlotCoefficient s slots).totalDegree ≤ slots.length := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using movingSlotProduct_degree slots)

theorem movingSlotProduct_vars {σ : Type*} [DecidableEq σ] (slots : List σ) :
    (movingSlotProduct slots).vars ⊆ slots.toFinset := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih =>
    intro j hj
    have h := MvPolynomial.vars_mul (MvPolynomial.X i) (movingSlotProduct slots) hj
    rcases Finset.mem_union.mp h with h | h
    · have hji : j = i := by
        simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using h
      simp [hji]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih h)))

theorem movingSlotCoefficient_vars {σ : Type*} [DecidableEq σ] (s : ℤ) (slots : List σ) :
    (movingSlotCoefficient s slots).vars ⊆ slots.toFinset := by
  intro i hi
  have h := MvPolynomial.vars_mul (MvPolynomial.C s) (movingSlotProduct slots) hi
  rcases Finset.mem_union.mp h with h | h
  · rw [MvPolynomial.vars_C] at h
    exact (Finset.notMem_empty _ h).elim
  · exact movingSlotProduct_vars slots h

theorem movingSlotProduct_abs_le {σ : Type*} (x : σ → ℝ) (slots : List σ)
    (T : ℝ) (hT : 0 ≤ T) (hx : ∀ i ∈ slots, |x i| ≤ T) :
    |(slots.map x).prod| ≤ T ^ slots.length := by
  induction slots with
  | nil => simp
  | cons i slots ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul, List.length_cons, pow_succ]
    calc
      |x i| * |(slots.map x).prod| ≤ T * T ^ slots.length :=
        mul_le_mul (hx i (by simp)) (ih fun j hj => hx j (by simp [hj]))
          (abs_nonneg _) hT
      _ = _ := mul_comm _ _

theorem movingSlotCoefficient_abs_le {σ : Type*} (x : σ → ℝ) (s : ℤ)
    (slots : List σ) (F T : ℝ) (hF : |(s : ℝ)| ≤ F) (hT : 0 ≤ T)
    (hx : ∀ i ∈ slots, |x i| ≤ T) :
    |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (movingSlotCoefficient s slots)| ≤
      F * T ^ slots.length := by
  rw [movingSlotCoefficient_eval, abs_mul]
  exact mul_le_mul hF (movingSlotProduct_abs_le x slots T hT hx)
    (abs_nonneg _) (le_trans (abs_nonneg _) hF)

theorem movingSlotCoefficient_ne_zero {σ K : Type*} [Field K]
    (x : σ → K) (s : ℤ) (slots : List σ)
    (hs : (s : K) ≠ 0) (hx : ∀ i ∈ slots, x i ≠ 0) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) x (movingSlotCoefficient s slots) ≠ 0 := by
  rw [movingSlotCoefficient_eval]
  apply mul_ne_zero hs
  induction slots with
  | nil => simp
  | cons i slots ih =>
    exact mul_ne_zero (hx i (by simp)) (ih fun j hj => hx j (by simp [hj]))

namespace MovingSlotReversal

theorem polynomial_degree {σ : Type*} (s : MovingSlotReversal σ) (d : ℕ)
    (h : s.lengthLE d) :
    s.polynomial.v.totalDegree ≤ d ∧ s.polynomial.w.totalDegree ≤ d ∧
      s.polynomial.u.totalDegree ≤ d :=
  ⟨(movingSlotCoefficient_degree _ _).trans h.1,
   (movingSlotCoefficient_degree _ _).trans h.2.1,
   (movingSlotCoefficient_degree _ _).trans h.2.2⟩

theorem polynomial_height {σ : Type*} (s : MovingSlotReversal σ) (x : σ → ℝ)
    (F T : ℝ) (d : ℕ) (hF : s.frequencyLE F) (hT : 1 ≤ T)
    (hd : s.lengthLE d) (hx : ∀ i, |x i| ≤ T) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x
    |φ s.polynomial.v| ≤ F * T ^ d ∧ |φ s.polynomial.w| ≤ F * T ^ d ∧
      |φ s.polynomial.u| ≤ F * T ^ d := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hF.1
  have hb (a : ℤ) (slots : List σ) (ha : |(a : ℝ)| ≤ F) (hlen : slots.length ≤ d) :
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (movingSlotCoefficient a slots)| ≤ F * T ^ d :=
    (movingSlotCoefficient_abs_le x a slots F T ha (by linarith) (fun i _ => hx i)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT hlen) hF0)
  exact ⟨hb _ _ hF.1 hd.1, hb _ _ hF.2.1 hd.2.1, hb _ _ hF.2.2 hd.2.2⟩

end MovingSlotReversal
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous arithmetic replacement for concrete moving-giant slots -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSlotLine_degree {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (k d : ℕ)
    (hlen : path.length ≤ k) (hd : ∀ s ∈ path, s.lengthLE d) (hc : current.lengthLE d) :
    (movingSlotLine path current).a.totalDegree ≤ (k + 1) * d ∧
      (movingSlotLine path current).b.totalDegree ≤ (k + 1) * d := by
  have h := movingHistoryLine_degree (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w d
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs; exact t.polynomial_degree d (hd t ht))
    (current.polynomial_degree d hc).1 (current.polynomial_degree d hc).2.1
  have hb : ((path.map MovingSlotReversal.polynomial).length + 1) * d ≤ (k + 1) * d := by
    simpa only [List.length_map] using Nat.mul_le_mul_right d (Nat.add_le_add_right hlen 1)
  exact ⟨h.1.trans hb, h.2.trans hb⟩

theorem movingSlotLine_height {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (x : σ → ℝ) (k d : ℕ) (F T : ℝ)
    (hF : 1 ≤ F) (hT : 1 ≤ T) (hlen : path.length ≤ k)
    (hd : ∀ s ∈ path, s.lengthLE d ∧ s.frequencyLE F)
    (hc : current.lengthLE d ∧ current.frequencyLE F) (hx : ∀ i, |x i| ≤ T) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x
    |φ (movingSlotLine path current).a| ≤ (2 * (F * T ^ d)) ^ (k + 1) ∧
      |φ (movingSlotLine path current).b| ≤ (2 * (F * T ^ d)) ^ (k + 1) := by
  have hK : 1 ≤ F * T ^ d := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hT)
  have hh := movingHistoryLine_value (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w _ (F * T ^ d) (by linarith)
    (by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact t.polynomial_height x F T d (hd t ht).2 hT (hd t ht).1 hx)
    (current.polynomial_height x F T d hc.2 hT hc.1 hx).1
    (current.polynomial_height x F T d hc.2 hT hc.1 hx).2.1
  have hb : (2 * (F * T ^ d)) ^ ((path.map MovingSlotReversal.polynomial).length + 1) ≤
      (2 * (F * T ^ d)) ^ (k + 1) := by
    apply pow_le_pow_right₀ (by linarith)
    simpa only [List.length_map] using Nat.add_le_add_right hlen 1
  exact ⟨hh.1.trans hb, hh.2.trans hb⟩

theorem movingSlotLine_vars {σ : Type*} [DecidableEq σ]
    (path : List (MovingSlotReversal σ)) (current : MovingSlotReversal σ) (S : Finset σ)
    (hp : ∀ s ∈ path, (∀ i ∈ s.leftSlots, i ∈ S) ∧ (∀ i ∈ s.rightSlots, i ∈ S) ∧
      (∀ i ∈ s.compensationSlots, i ∈ S))
    (hc : (∀ i ∈ current.leftSlots, i ∈ S) ∧ (∀ i ∈ current.rightSlots, i ∈ S)) :
    (movingSlotLine path current).a.vars ⊆ S ∧ (movingSlotLine path current).b.vars ⊆ S := by
  have hsub (a : ℤ) (slots : List σ) (h : ∀ i ∈ slots, i ∈ S) :
      (movingSlotCoefficient a slots).vars ⊆ S :=
    (movingSlotCoefficient_vars a slots).trans (fun i hi => h i (List.mem_toFinset.mp hi))
  apply movingHistoryLine_vars_subset
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact ⟨hsub _ _ (hp t ht).2.1, hsub _ _ (hp t ht).1, hsub _ _ (hp t ht).2.2⟩
  · exact hsub _ _ hc.2
  · exact hsub _ _ hc.1

/-- All occurrence tests for all representative internal primes are replaced
at once, under the original independent slot priors. The multiplier remains
complex-valued. Independence follows from absence of the tested coordinate in
the actual slot lists, including every ancestor compensation list. -/
theorem moving_slot_joint_symbolic_comparison {A J O : Type*}
    [Fintype A] [Nonempty A] [Fintype J] [Fintype O] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin (n + 1))))
    (current : J → O → MovingSlotReversal (Fin (n + 1)))
    (base : J → O) (coordinate : J → Fin (n + 1))
    (k d : ℕ) (F T : ℝ) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hlen : ∀ j o, (path j o).length ≤ k)
    (hd : ∀ j o, (∀ s ∈ path j o, s.lengthLE d ∧ s.frequencyLE F) ∧
      (current j o).lengthLE d ∧ (current j o).frequencyLE F)
    (habsent : ∀ j o,
      (∀ s ∈ path j o, coordinate j ∉ s.leftSlots ∧ coordinate j ∉ s.rightSlots ∧
        coordinate j ∉ s.compensationSlots) ∧
      coordinate j ∉ (current j o).leftSlots ∧ coordinate j ∉ (current j o).rightSlots)
    (hvalues : ∀ a, |(value a : ℝ)| ≤ T)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coordinate j) a ≤ β)
    (hsize : ∀ j a, μ (coordinate j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (Ψ : (Fin (n + 1) → A) → (J × (Bool ⊕ O) → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x flags, ‖Ψ x flags‖ ≤ B) :
    let tests := fun t : J × (Bool ⊕ O) =>
      lineTestPolynomials (fun o => movingSlotLine (path t.1 o) (current t.1 o)) (base t.1) t.2
    ‖∑ x, (productPrior μ x : ℂ) *
      (Ψ x (fun t => arithmeticTestFlag
        (prime (x (coordinate t.1)) ∣ (integerTestValue value (tests t) x).natAbs)) -
       Ψ x (fun t => arithmeticTestFlag (tests t = 0)))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card O)) *
        ((2 * ((k + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * T ^ d)) ^ (k + 1)) ^ 2) / V) * β) := by
  let lines := fun j o => movingSlotLine (path j o) (current j o)
  let tests := fun t : J × (Bool ⊕ O) => lineTestPolynomials (lines t.1) (base t.1) t.2
  let H := (2 * (F * T ^ d)) ^ (k + 1)
  have hH : 1 ≤ H := one_le_pow₀ (by
    have := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hT (n := d))
    linarith)
  have hdeg (t : J × (Bool ⊕ O)) : (tests t).totalDegree ≤ 2 * ((k + 1) * d) :=
    lineTestPolynomials_degree_le (lines t.1) (base t.1) _
      (fun o => movingSlotLine_degree _ _ k d (hlen _ _) (fun s hs => (hd _ _).1 s hs |>.1)
        (hd _ _).2.1) t.2
  have hheight (t : J × (Bool ⊕ O)) (x : Fin (n + 1) → A) :
      |(integerTestValue value (tests t) x : ℝ)| ≤ 2 * H ^ 2 := by
    rw [integerTestValue_real_cast]
    apply lineTestPolynomials_value_le (lines t.1) (base t.1) _ H hH
    intro o
    exact movingSlotLine_height _ _ _ k d F T hF hT (hlen _ _) (hd _ _).1 (hd _ _).2
      (fun i => hvalues (x i))
  have hab (t : J × (Bool ⊕ O)) : coordinate t.1 ∉ (tests t).vars := by
    let S : Finset (Fin (n + 1)) := Finset.univ.erase (coordinate t.1)
    have hl (o : O) : (lines t.1 o).a.vars ⊆ S ∧ (lines t.1 o).b.vars ⊆ S := by
      apply movingSlotLine_vars
      · intro s hs
        refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> apply Finset.mem_erase.mpr <;>
          refine ⟨?_, Finset.mem_univ _⟩
        · exact fun h => (habsent t.1 o).1 s hs |>.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).1 s hs |>.2.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).1 s hs |>.2.2 (h ▸ hi)
      · constructor <;> intro i hi <;> apply Finset.mem_erase.mpr <;>
          refine ⟨?_, Finset.mem_univ _⟩
        · exact fun h => (habsent t.1 o).2.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).2.2 (h ▸ hi)
    exact fun h => Finset.notMem_erase _ _
      (lineTestPolynomials_vars_subset (lines t.1) (base t.1) S hl t.2 h)
  have hh := joint_sampled_polynomial_comparison_le value hinj prime hpInj hprime tests
    (fun t => coordinate t.1) hab μ hμ hmass α β V (2 * H ^ 2) hα hβ hV
    (by nlinarith [sq_nonneg H]) hmax (fun t => hpmax t.1) (fun t => hsize t.1) hheight Ψ B hB hΨ
  apply hh.trans
  have hterm (t : J × (Bool ⊕ O)) :
      ((tests t).totalDegree : ℝ) * α + (Real.log (2 * H ^ 2) / V) * β ≤
        ((2 * ((k + 1) * d) : ℕ) : ℝ) * α + (Real.log (2 * H ^ 2) / V) * β := by
    have hd' : ((tests t).totalDegree : ℝ) ≤ ((2 * ((k + 1) * d) : ℕ) : ℝ) := by
      exact_mod_cast hdeg t
    exact add_le_add (mul_le_mul_of_nonneg_right hd' hα) le_rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hterm t)
  apply (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hB)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, H]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotOccurrences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual occurrence paths and absence of their compensation type -/

namespace Ostmann
open scoped Classical

/-- The current compensation type is strictly below every variable in the
current numerator and all its ancestor denominators. This holds for every
occurrence simultaneously, including repeated occurrences of one sample. -/
theorem MovingSlotData.occurrence_bounds {σ : Type*} (tier : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, 0 < o.level ∧ o.level + o.path.length ≤ n ∧ o.AvoidsBelow tier := by
  induction T with
  | leaf s regular => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      refine ⟨by change 0 < n + 1; omega, by change n + 1 + 0 ≤ n + 1; omega, ?_⟩
      exact ⟨by simp, hT.1, hT.2.1⟩
    · have hl := ihL hT.2.2.2.1
      have hr := ihR hT.2.2.2.2
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hl o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hr o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega

theorem MovingSlotOccurrence.absent_of_level {σ : Type*} (tier : σ → ℕ)
    (o : MovingSlotOccurrence σ) (ho : o.AvoidsBelow tier) (i : σ) (hi : tier i < o.level) :
    (∀ s ∈ o.path, i ∉ s.leftSlots ∧ i ∉ s.rightSlots ∧ i ∉ s.compensationSlots) ∧
      i ∉ o.current.leftSlots ∧ i ∉ o.current.rightSlots := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ⟨fun h => (not_le.mpr hi) ((ho.1 s hs).1 i h),
      fun h => (not_le.mpr hi) ((ho.1 s hs).2.1 i h),
      fun h => (not_le.mpr hi) ((ho.1 s hs).2.2 i h)⟩
  · exact fun h => (not_le.mpr hi) (ho.2.1 i h)
  · exact fun h => (not_le.mpr hi) (ho.2.2 i h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit coefficients for the actual sampled occurrence paths -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Frequencies.root {σ : Type*} {P : ℤ → Prop} {n : ℕ}
    {T : MovingSlotData σ n} (h : T.Frequencies P) : P T.frequency := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem MovingSlotData.occurrence_frequencies {σ : Type*} (P : ℤ → Prop) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Frequencies P) :
    ∀ o ∈ T.occurrences, o.current.Frequencies P ∧ ∀ s ∈ o.path, s.Frequencies P := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    have hb (b : Bool) : (step s CL CR u left right b).Frequencies P :=
      ⟨hT.2.1.root, hT.2.2.root, hT.1⟩
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨hb false, by simp⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihL hT.2.1 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb true
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihR hT.2.2 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb false

/-- The current compensation primes can repeat within their equality pattern.
Only their disjointness from the earlier coefficient types is used here. -/
theorem MovingSlotData.occurrence_units {σ : Type*} {q : ℕ} [Fact q.Prime]
    (tier : σ → ℕ) (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hfreq : T.Frequencies (fun s => (s : ZMod q) ≠ 0))
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences)
    (hcop : ∀ i, o.level ≤ tier i → (value i).Coprime q) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction q value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction q value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value o.current.polynomial.w ≠ 0 := by
  have hl := (T.occurrence_bounds tier hlevels o ho).2.2
  have hf := T.occurrence_frequencies _ hfreq o ho
  have hc (s : ℤ) (slots : List σ) (hs : (s : ZMod q) ≠ 0)
      (hslots : ∀ i ∈ slots, o.level ≤ tier i) :
      MovingSlotReversal.naturalReduction q value (movingSlotCoefficient s slots) ≠ 0 := by
    simpa only [MovingSlotReversal.naturalReduction] using
      movingSlotCoefficient_ne_zero (fun i => (value i : ZMod q)) s slots hs
        (fun i hi => ((ZMod.isUnit_iff_coprime _ _).mpr (hcop i (hslots i hi))).ne_zero)
  refine ⟨?_, hc _ _ hf.1.1 hl.2.2, hc _ _ hf.1.2.1 hl.2.1⟩
  intro s hs
  exact ⟨hc _ _ (hf.2 s hs).1 (hl.1 s hs).2.1,
    hc _ _ (hf.2 s hs).2.1 (hl.1 s hs).1,
    hc _ _ (hf.2 s hs).2.2 (hl.1 s hs).2.2⟩

/-- Disjoint prime types discharge all denominator and nonzero-row conditions
at every occurrence of the selected representative. -/
theorem MovingSlotData.occurrence_units_of_prime_types {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences) (rep : σ)
    (hrep : tier rep < o.level)
    (hfreq : T.Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.w ≠ 0 := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  apply T.occurrence_units tier value hlevels hfreq o ho
  intro i hi
  exact (Nat.coprime_primes (hprime i) (hprime rep)).mpr
    (hdisjoint i rep (by omega))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem MovingSlotReversal.continuous_realPivot {σ : Type*}
    (value : σ → ℕ) (s : MovingSlotReversal σ) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realPivot value (L x) (R x)) := by
  unfold realPivot
  exact ((continuous_const.mul hR).sub (continuous_const.mul hL)).div_const _

theorem MovingSlotData.continuous_realLeafModuli {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) (i : TreeLeafIndex n) :
    Continuous (fun x => T.realLeafModuli value (L x) (R x) i) := by
  induction T generalizing L R with
  | leaf => exact (hL.mul hR).mul_const _
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    cases i with
    | inl i => exact ihL _ L hp hL i
    | inr i => exact ihR _ R hp hR i

theorem continuous_movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealFourierWeight value T ψ X lo hi hlo hhi (L x) (R x)) := by
  apply continuous_finsetProd
  intro i _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_realLeafModuli value L R hL hR i).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_movingRealNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealNodeCutoff value φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul (ihL _ L hc hL)).mul (ihR _ R hc hR)

theorem continuous_movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {A : Type*} [TopologicalSpace A] (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L x) (R x)) :=
  (continuous_movingRealFourierWeight value T ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_movingRealNodeCutoff value φ G B D hB hD hφ hlip hout T L R hL hR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

theorem HistoryFormula.continuous_realEval {σ : Type*} (F : HistoryFormula σ) :
    Continuous F.realEval := by
  unfold realEval
  simp only [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval _).div_const _

theorem WordTransferGuard.isClosed_archimedeanAt {σ : Type*} (g : WordTransferGuard σ) :
    IsClosed {x | g.archimedeanAt x} :=
  (isClosed_le continuous_const g.pivot.continuous_realEval).inter
    ((isClosed_le g.pivot.continuous_realEval continuous_const).inter
      (isClosed_le continuous_const g.rightProduct.continuous_realEval))

theorem isClosed_movingArchimedeanGate (nodes : List MovingFormulaNode) :
    IsClosed {x | movingArchimedeanGate nodes x} := by
  induction nodes with
  | nil => simpa only [movingArchimedeanGate, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, Set.ofPred_true] using isClosed_univ
  | cons f nodes ih =>
    simpa only [movingArchimedeanGate, List.forall_mem_cons, Set.ofPred_and] using
      f.guard.isClosed_archimedeanAt.inter ih

theorem continuous_topGiantReal : Continuous (fun x : ℝ × ℝ => topGiantReal x.1 x.2) := by
  apply continuous_pi
  intro b
  cases b
  · exact continuous_fst
  · exact continuous_snd

theorem measurable_movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ) :
    Measurable (fun x : ℝ × ℝ => movingRealGateWeight value T nodes X lo hi (topGiantReal x.1 x.2)) := by
  have ha : Measurable (fun x : ℝ × ℝ => movingArchimedeanFlag nodes (topGiantReal x.1 x.2)) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact ((isClosed_movingArchimedeanGate nodes).preimage continuous_topGiantReal).measurableSet
  have hw : Measurable (fun x : ℝ × ℝ => movingRealWindowFlag value T X lo hi x.1 x.2) := by
    apply Measurable.ite _ measurable_const measurable_const
    have hc : IsClosed {x : ℝ × ℝ | ∀ i, T.realLeafModuli value x.1 x.2 i / X ∈ Set.Icc lo hi} := by
      simpa only [Set.ofPred_forall, Set.preimage] using isClosed_iInter (fun i : TreeLeafIndex n =>
        isClosed_Icc.preimage ((T.continuous_realLeafModuli value Prod.fst Prod.snd
          continuous_fst continuous_snd i).div_const X))
    exact hc.measurableSet
  exact ha.mul hw

theorem measurable_movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun x : ℝ × ℝ => movingRealKernel value T nodes ψ X lo hi hlo hhi φ G x.1 x.2) :=
  (measurable_movingRealGateWeight value T nodes X lo hi).mul
    (continuous_movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Prod.fst Prod.snd continuous_fst continuous_snd).measurable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantDensitySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving the finite residue average inside the common real integral -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem double_integral_finset_sum {A : Type*} (S : Finset A)
    (μ ν : Measure ℝ) (F : A → ℝ → ℝ → ℂ)
    (hinner : ∀ a ∈ S, ∀ x, Integrable (F a x) ν)
    (houter : ∀ a ∈ S, Integrable (fun x => ∫ y, F a x y ∂ν) μ) :
    (∫ x, ∫ y, ∑ a ∈ S, F a x y ∂ν ∂μ) =
      ∑ a ∈ S, ∫ x, ∫ y, F a x y ∂ν ∂μ := by
  have hin (x : ℝ) : (∫ y, ∑ a ∈ S, F a x y ∂ν) =
      ∑ a ∈ S, ∫ y, F a x y ∂ν :=
    integral_finsetSum S (fun a ha => hinner a ha x)
  simp_rw [hin]
  exact integral_finsetSum S houter

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicPairIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem norm_harmonic_pair_integral_le (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (F : ℝ → ℝ → ℂ)
    (hF : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖F x y‖ ≤ C) :
    ‖∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
    have hx0 := hu0.trans hx.1
    have hy0 := hr0.trans hy.1
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0, abs_of_pos hy0]
    exact (div_le_div_of_nonneg_right (hF x hx y hy) (mul_nonneg hx0.le hy0.le)).trans
      (div_le_div_of_nonneg_left hC (mul_pos hu0 hr0)
        (mul_le_mul hx.1.le hy.1.le hr0.le hx0.le))
  have hin (x : ℝ) (hx : x ∈ Set.Ioc u v) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top (hpoint x hx)
  simp only [Real.volume_real_Ioc_of_le hrs] at hin
  have hout := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hin
  rw [Real.volume_real_Ioc_of_le huv] at hout
  calc
    _ ≤ (C / (u * r) * (s - r)) * (v - u) := hout
    _ ≤ C / (u * r) * 1 * 1 := by gcongr <;> linarith
    _ = _ := by ring

/-- A finite signed average is integrated before its norm is bounded. This
retains cancellation in the arithmetic coefficient on each giant cell. -/
theorem finite_harmonic_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (w : A → ℂ) (F : A → ℝ → ℝ → ℂ)
    (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  let box := Set.Ioc u v ×ˢ Set.Ioc r s
  let H := fun a (z : ℝ × ℝ) => box.indicator
    (fun z => w a * F a z.1 z.2 / ((z.1 : ℂ) * (z.2 : ℂ))) z
  have hH (a : A) : Measurable (H a) := by
    apply Measurable.indicator _ (measurableSet_Ioc.prod measurableSet_Ioc)
    exact (measurable_const.mul (hmeas a)).div
      ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hnorm (a : A) (z : ℝ × ℝ) : ‖H a z‖ ≤ ‖w a‖ * K a / (u * r) := by
    by_cases hz : z ∈ box
    · obtain ⟨hx, hy⟩ := hz
      have hx0 : 0 < z.1 := (lt_of_lt_of_le zero_lt_one hu).trans hx.1
      have hy0 : 0 < z.2 := (lt_of_lt_of_le zero_lt_one hr).trans hy.1
      simp only [H, Set.indicator_of_mem (show z ∈ box from ⟨hx, hy⟩), norm_div,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hy0]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound a z.1 hx z.2 hy) (norm_nonneg _))
        (mul_nonneg hx0.le hy0.le)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (hK a)) (by positivity)
          (mul_le_mul hx.1.le hy.1.le (by linarith) hx0.le))
    · rw [show H a z = 0 from Set.indicator_of_notMem hz _]
      simp only [norm_zero]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (hK a)) (by linarith [mul_pos (lt_of_lt_of_le zero_lt_one hu) (lt_of_lt_of_le zero_lt_one hr)])
  let μ := volume.restrict (Set.Ioc u v)
  let ν := volume.restrict (Set.Ioc r s)
  have hp (a : A) : Integrable (H a) (μ.prod ν) :=
    ⟨(hH a).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (hnorm a))⟩
  have hi (a : A) (x : ℝ) : Integrable (fun y => H a (x, y)) ν :=
    ⟨((hH a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hnorm a (x, y)))⟩
  have hswap := double_integral_finset_sum (Finset.univ : Finset A) μ ν
    (fun a x y => H a (x, y)) (fun a _ => hi a) (fun a _ => (hp a).integral_prod_left)
  have heq (a : A) : (∫ x, ∫ y, H a (x, y) ∂ν ∂μ) =
      w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        F a x y / ((x : ℂ) * (y : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩)]
    ring
  have hinside : (∫ x, ∫ y, ∑ a, H a (x, y) ∂ν ∂μ) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        (∑ a, w a * F a x y) / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩),
      Finset.sum_div]
  simp only [heq] at hswap
  rw [← hswap, hinside]
  exact norm_harmonic_pair_integral_le u v r s C hu hr huv hrs hv hs hC _ hmean

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prior domination for a repeated compensation-prime sample -/

namespace Ostmann

open scoped BigOperators

/-- Keep one occurrence's prior and charge the other occurrences their pointwise bounds. -/
theorem repeated_prior_weight_le {I : Type*} [DecidableEq I]
    (S : Finset I) (i : I) (hi : i ∈ S) (μ : I → ℝ) (b E : ℝ)
    (hb : 2 ≤ b) (hμ : ∀ j ∈ S, 0 ≤ μ j)
    (hbound : ∀ j ∈ S.erase i, b * μ j ≤ E) :
    (∏ j ∈ S, b * μ j) / (b - 1) ≤ 2 * μ i * E ^ (S.card - 1) := by
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hprod : (∏ j ∈ S.erase i, b * μ j) ≤ E ^ (S.card - 1) := by
    have h := Finset.prod_le_prod
      (fun j hj => mul_nonneg hb0 (hμ j (Finset.mem_of_mem_erase hj))) hbound
    simpa only [Finset.prod_const, Finset.card_erase_of_mem hi] using h
  have hquot : b / (b - 1) ≤ 2 := by
    apply (div_le_iff₀ hb1).mpr
    linarith
  calc
    _ = (b / (b - 1)) * μ i * ∏ j ∈ S.erase i, b * μ j := by
      rw [← Finset.prod_erase_mul S (fun j => b * μ j) hi]
      ring
    _ ≤ 2 * μ i * ∏ j ∈ S.erase i, b * μ j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hquot (hμ i hi))
        (Finset.prod_nonneg fun j hj => mul_nonneg hb0 (hμ j (Finset.mem_of_mem_erase hj)))
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hμ i hi))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous product fibers for an arbitrary partition of the leaves -/

namespace Ostmann

open scoped BigOperators

theorem sum_card_partition {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq C] (component : L → C) :
    (∑ c : C, Fintype.card {i : L // component i = c}) = Fintype.card L := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv component)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatedPatternPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous prior domination for a fixed internal-prime equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

private theorem product_pattern_fibers {I C : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (f : I → ℝ) :
    (∏ c, ∏ i : {i : I // pattern i = c}, f i.val) = ∏ i, f i := by
  exact Fintype.prod_fiberwise pattern f

private theorem product_pattern_powers {I C : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c}) (E : ℝ) :
    (∏ c, E ^ (Fintype.card {i : I // pattern i = c} - 1)) =
      E ^ (Fintype.card I - Fintype.card C) := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    congr 2
    simpa only [Fintype.card_eq_nat_card] using sum_card_partition pattern
  · intro c _
    exact Fintype.card_pos_iff.mpr ⟨rep c⟩

theorem repeated_pattern_prior_domination {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (value : A → ℝ) (E : ℝ)
    (hvalue : ∀ a, 2 ≤ value a)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, value a * μ i a ≤ E)
    (x : C → A) :
    ((∏ i, value (x (pattern i)) * μ i (x (pattern i))) *
        ∏ c, (value (x c) - 1)⁻¹) ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
  have hl (c : C) :
      (∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) /
          (value (x c) - 1) ≤
        2 * μ (rep c).val (x c) * E ^ (Fintype.card {i : I // pattern i = c} - 1) := by
    simpa only [Finset.mem_univ, Finset.card_univ] using
      repeated_prior_weight_le (Finset.univ : Finset {i : I // pattern i = c}) (rep c)
        (Finset.mem_univ _) (fun i => μ i.val (x c)) (value (x c)) E (hvalue _)
        (fun i _ => hμ i.val _) (fun i _ => hbound i.val _)
  have hp := Finset.prod_le_prod (s := (Finset.univ : Finset C))
    (fun c _ => div_nonneg
      (Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [hvalue (x c)]) (hμ i.val _)))
      (by linarith [hvalue (x c)])) (fun c _ => hl c)
  have hflat : (∏ c, ∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) =
      ∏ i, value (x (pattern i)) * μ i (x (pattern i)) := by
    calc
      _ = ∏ c, ∏ i : {i : I // pattern i = c},
          value (x (pattern i.val)) * μ i.val (x (pattern i.val)) := by
        apply Finset.prod_congr rfl
        intro c _
        apply Finset.prod_congr rfl
        intro i _
        rw [i.property]
      _ = _ := product_pattern_fibers pattern (fun i => value (x (pattern i)) * μ i (x (pattern i)))
  have hc := product_pattern_powers pattern rep E
  have hleft :
      (∏ c, (∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) /
        (value (x c) - 1)) =
      (∏ i, value (x (pattern i)) * μ i (x (pattern i))) *
        ∏ c, (value (x c) - 1)⁻¹ := by
    simp only [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, hflat]
  have hright :
      (∏ c, 2 * μ (rep c).val (x c) * E ^ (Fintype.card {i : I // pattern i = c} - 1)) =
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
    simp only [Finset.prod_mul_distrib, hc, Finset.prod_const, Finset.card_univ]
    ring
  rw [hleft, hright] at hp
  exact hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FinitePriorDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing a dominated finite sampling law into a complex multiplier -/

namespace Ostmann

/-- The scalar is the retained product of one-over-prime line probabilities.
It is positive, so a zero dominating prior forces the original summand to vanish. -/
theorem finitePriorDensity_cancel {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (c : X → ℝ) (B : ℝ) (hc : ∀ x, 0 < c x)
    (hbound : ∀ x, ‖F x‖ * c x ≤ B * μ x) (x : X) :
    (μ x : ℂ) * finitePriorDensity μ F x = F x := by
  by_cases hμ : μ x = 0
  · have hF : F x = 0 := by
      apply norm_eq_zero.mp
      have h := hbound x
      rw [hμ, mul_zero] at h
      have hp := hc x
      exact le_antisymm (by nlinarith [norm_nonneg (F x)]) (norm_nonneg _)
    simp only [finitePriorDensity, hμ, hF, Complex.ofReal_zero, zero_div, mul_zero]
  · unfold finitePriorDensity
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hμ)

theorem finitePriorDensity_bound {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (c : X → ℝ) (B : ℝ) (hμ : ∀ x, 0 ≤ μ x) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ * c x ≤ B * μ x) (x : X) :
    ‖finitePriorDensity μ F x‖ * c x ≤ B := by
  by_cases hz : μ x = 0
  · simp only [finitePriorDensity, hz, Complex.ofReal_zero, div_zero, norm_zero, zero_mul]
    exact hB
  · have hp : 0 < μ x := lt_of_le_of_ne (hμ x) (Ne.symm hz)
    simp only [finitePriorDensity, norm_div, Complex.norm_real, Real.norm_of_nonneg (hμ x)]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hp).mpr (hbound x)

theorem finitePriorDensity_ne_zero {X : Type*} (μ : X → ℝ) (F : X → ℂ)
    (x : X) (h : finitePriorDensity μ F x ≠ 0) : F x ≠ 0 := by
  intro hF
  apply h
  simp only [finitePriorDensity, hF, zero_div]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_InternalPatternWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the line-probability scale in an internal-prime pattern -/

namespace Ostmann
open scoped BigOperators

/-- Collapsing equal samples keeps the prior at one fixed representative and
charges only the repeated occurrences. The estimate also covers the larger
`1/(p-1)` line probability and hence the actual mixed `1/p` law. -/
theorem internalPatternWeight_bound {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (prime : A → ℕ) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, (prime a : ℝ) * μ i a ≤ E)
    (x : C → A) :
    internalPatternWeight pattern μ prime x * (∏ c, (prime (x c) : ℝ)⁻¹) ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
  have hp : ∀ a, (2 : ℝ) ≤ prime a := fun a => by exact_mod_cast (hprime a).two_le
  have hi (c : C) : (prime (x c) : ℝ)⁻¹ ≤ ((prime (x c) : ℝ) - 1)⁻¹ := by
    apply inv_anti₀ (by linarith [hp (x c)])
    linarith
  have hw : 0 ≤ internalPatternWeight pattern μ prime x :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hμ i _))
  exact (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun c _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun c _ => hi c)) hw).trans
      (repeated_pattern_prior_domination pattern rep μ (fun a => (prime a : ℝ)) E hp hμ hbound x)

theorem internalPatternWeight_complex_bound {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (prime : A → ℕ) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, (prime a : ℝ) * μ i a ≤ E)
    (G : (C → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ x, ‖G x‖ ≤ B)
    (x : C → A) :
    ‖(internalPatternWeight pattern μ prime x : ℂ) * G x‖ *
        (∏ c, (prime (x c) : ℝ)⁻¹) ≤
      (B * ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C))) *
        ∏ c, μ (rep c).val (x c) := by
  have hw : 0 ≤ internalPatternWeight pattern μ prime x :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hμ i _))
  have hc : 0 ≤ ∏ c, (prime (x c) : ℝ)⁻¹ :=
    Finset.prod_nonneg (fun c _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ internalPatternWeight pattern μ prime x * B * (∏ c, (prime (x c) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG x) hw) hc
    _ = B * (internalPatternWeight pattern μ prime x * (∏ c, (prime (x c) : ℝ)⁻¹)) := by ring
    _ ≤ B * (((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c)) :=
      mul_le_mul_of_nonneg_left (internalPatternWeight_bound pattern rep μ prime E hprime hμ hbound x) hB
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareLiftExclusions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dropping the prime-square exclusions in a two-history expansion -/

namespace Ostmann

open scoped BigOperators

theorem card_zeroLift {p : ℕ} [Fact p.Prime]
    (a : (ZMod (p ^ 2))ˣ) (b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : squareReduction p a * x₀ + squareReduction p b * y₀ = 0) :
    Fintype.card {v : SquareLiftPairs p x₀ y₀ //
      (a : ZMod (p ^ 2)) * v.1.1 + b * v.2.1 = 0} = p := by
  rw [Fintype.card_congr (zeroLiftEquiv a b x₀ y₀),
    Fintype.card_congr (liftedLineEquiv (squareReduction p) a b x₀ y₀ hbase),
    card_squareReduction_fiber]

theorem card_squareLiftBad_le {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0) :
    (squareLiftBad a b x₀ y₀).card ≤ Fintype.card I * p := by
  classical
  have heq : squareLiftBad a b x₀ y₀ = Finset.univ.biUnion
      (fun i => Finset.univ.filter fun v : SquareLiftPairs p x₀ y₀ =>
        (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0) := by
    ext v
    simp [squareLiftBad]
  rw [heq]
  refine (Finset.card_biUnion_le).trans_eq ?_
  have hc (i : I) : (Finset.univ.filter fun v : SquareLiftPairs p x₀ y₀ =>
      (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0).card = p := by
    simpa only [Fintype.card_subtype] using card_zeroLift (a i) (b i) x₀ y₀ (hbase i)
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A bounded integrand loses at most `B * (# occurrences) / p` when all
prime-square exclusions are imposed. No independence of the exclusions is used. -/
theorem square_lift_removed_mass_le {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0)
    (F : SquareLiftPairs p x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    ‖∑ v ∈ squareLiftBad a b x₀ y₀, F v‖ / (p : ℝ) ^ 2 ≤
      B * (Fintype.card I : ℝ) / p := by
  classical
  have hcard : ((squareLiftBad a b x₀ y₀).card : ℝ) ≤ (Fintype.card I : ℝ) * p :=
    by exact_mod_cast card_squareLiftBad_le a b x₀ y₀ hbase
  have hsum : ‖∑ v ∈ squareLiftBad a b x₀ y₀, F v‖ ≤ B * (Fintype.card I : ℝ) * p := by
    calc
      _ ≤ ∑ v ∈ squareLiftBad a b x₀ y₀, ‖F v‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ squareLiftBad a b x₀ y₀, B := Finset.sum_le_sum fun v _ => hF v
      _ = B * ((squareLiftBad a b x₀ y₀).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := by nlinarith
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ ≤ (B * (Fintype.card I : ℝ) * p) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by field_simp

/-- The form used in both giant environments: the second giant has a nonzero
residue, and every occurrence has a nonzero row. This supplies the unit
coefficient needed for the lift count rather than assuming it separately. -/
theorem square_lift_nonzero_rows_removed_mass_le {I : Type*} [Fintype I]
    {p : ℕ} [Fact p.Prime] (a b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hy : y₀ ≠ 0)
    (hrow : ∀ i, squareReduction p (a i) ≠ 0 ∨ squareReduction p (b i) ≠ 0)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0)
    (F : SquareLiftPairs p x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    ‖∑ v ∈ Finset.univ.filter (fun v : SquareLiftPairs p x₀ y₀ =>
      ∃ i, a i * v.1.1 + b i * v.2.1 = 0), F v‖ / (p : ℝ) ^ 2 ≤
      B * (Fintype.card I : ℝ) / p := by
  classical
  let u : I → (ZMod (p ^ 2))ˣ := fun i =>
    (square_line_first_isUnit (a i) (b i) x₀ y₀ hy (hrow i) (hbase i)).unit
  have hu (i : I) : (u i : ZMod (p ^ 2)) = a i := IsUnit.unit_spec _
  have hb : ∀ i, squareReduction p (u i) * x₀ + squareReduction p (b i) * y₀ = 0 := by
    intro i
    rw [hu]
    exact hbase i
  simpa only [squareLiftBad, hu] using
    square_lift_removed_mass_le u b x₀ y₀ hb F B hB hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_JointSquareLiftExclusions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dropping all prime-square exclusions in the uniform CRT fibers -/

namespace Ostmann
open scoped BigOperators Classical

theorem squareLiftPairs_card (p : ℕ) [Fact p.Prime] (x₀ y₀ : ZMod p) :
    Fintype.card (SquareLiftPairs p x₀ y₀) = p ^ 2 := by
  rw [Fintype.card_prod, card_squareReduction_fiber, card_squareReduction_fiber, pow_two]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLineIntegration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the actual moving-giant line systems on their full support -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSlotLineProbability_eq_flags {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → List (MovingSlotReversal (Fin n)))
    (current : J → MovingSlotReversal (Fin n)) (base : J) (external : Bool)
    (x : Fin n → A) (a : A)
    (hpath : ∀ j s, s ∈ path j →
      let φ := integerLineReduction value x (prime a)
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : let φ := integerLineReduction value x (prime a)
      φ (current base).polynomial.v ≠ 0 ∧ φ (current base).polynomial.w ≠ 0) :
    movingSlotLineProbability value prime hprime path current external x a =
      internalLineFlagWeight external (prime a) (fun s => arithmeticTestFlag
        (prime a ∣ (integerTestValue value
          (lineTestPolynomials (fun j => movingSlotLine (path j) (current j)) base s) x).natAbs)) := by
  let : Fact (prime a).Prime := ⟨hprime a⟩
  let φ := integerLineReduction value x (prime a)
  have hsteps (j : J) : ∀ s ∈ (path j).map MovingSlotReversal.polynomial,
      φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hpath j t ht
  have hd (j : J) : φ (movingSlotLine (path j) (current j)).denominator ≠ 0 :=
    movingPolynomialAncestors_denominator _ φ (fun s hs => (hsteps j s hs).2.2)
  have hr := movingHistoryLine_nonzero _ _ _ φ (hsteps base) hcurrent.1 hcurrent.2
  have hz := (movingSlotLine (path base) (current base)).normalized_zero_iff φ (hd base)
  have hr' : ((movingSlotLine (path base) (current base)).normalized φ).1 ≠ 0 ∨
      ((movingSlotLine (path base) (current base)).normalized φ).2 ≠ 0 :=
    hr.imp (fun h h₀ => h (hz.1.mp h₀)) (fun h h₀ => h (hz.2.mp h₀))
  unfold movingSlotLineProbability
  rw [internalLineProbability_eq_flags external _ base φ hd hr']
  change internalLineFlagWeight external (prime a) (fun s => arithmeticTestFlag
    (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (prime a)))
      (fun i => (value (x i) : ZMod (prime a)))
      (lineTestPolynomials (fun j => movingSlotLine (path j) (current j)) base s) = 0)) = _
  rw [line_divisibility_flags_eq]

theorem internalLineFlagWeight_le_scalar {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) :
    internalLineFlagWeight external p flags ≤ internalLineScalar external p := by
  unfold internalLineFlagWeight
  split_ifs
  · rfl
  · exact internalLineScalar_nonneg external p

/-- The remaining weight may be large. Its bound is imposed only after the
one-over-prime line scalars have been included, exactly as in (8.20). -/
theorem line_product_multiplier_bound {A J O : Type*} [Fintype J]
    (prime : A → ℕ) (external : J → Bool) (representative : J → A)
    (weight : ℂ) (B : ℝ)
    (h : ‖weight‖ * ∏ j, internalLineScalar (external j) (prime (representative j)) ≤ B)
    (flags : J × (Bool ⊕ O) → Bool) :
    ‖weight * ∏ j, (internalLineFlagWeight (external j) (prime (representative j))
      (fun s => flags (j, s)) : ℂ)‖ ≤ B := by
  rw [norm_mul, norm_prod]
  have he (j : J) : ‖(internalLineFlagWeight (external j) (prime (representative j))
      (fun s => flags (j, s)) : ℂ)‖ =
      internalLineFlagWeight (external j) (prime (representative j)) (fun s => flags (j, s)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (internalLineFlagWeight_nonneg _ _ _)]
  simp_rw [he]
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg weight)
  exact Finset.prod_le_prod (fun _ _ => internalLineFlagWeight_nonneg _ _ _)
    (fun _ _ => internalLineFlagWeight_le_scalar _ _ _)

/-- On the original full support the actual line counts can be inserted into
the same signed expression. No line identity is requested on rejected samples. -/
theorem moving_line_product_on_support {A J O : Type*} [Fintype J] {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin n)))
    (current : J → O → MovingSlotReversal (Fin n)) (base : J → O)
    (external : J → Bool) (representative : J → A) (x : Fin n → A) (weight : ℂ)
    (hpath : weight ≠ 0 → ∀ j o s, s ∈ path j o →
      let φ := integerLineReduction value x (prime (representative j))
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : weight ≠ 0 → ∀ j,
      let φ := integerLineReduction value x (prime (representative j))
      φ (current j (base j)).polynomial.v ≠ 0 ∧ φ (current j (base j)).polynomial.w ≠ 0) :
    weight * ∏ j, (movingSlotLineProbability value prime hprime (path j) (current j)
        (external j) x (representative j) : ℂ) =
      weight * ∏ j, (internalLineFlagWeight (external j) (prime (representative j))
        (fun s => arithmeticTestFlag (prime (representative j) ∣
          (integerTestValue value (lineTestPolynomials
            (fun o => movingSlotLine (path j o) (current j o)) (base j) s) x).natAbs)) : ℂ) := by
  by_cases hw : weight = 0
  · simp only [hw, zero_mul]
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg (fun r : ℝ => (r : ℂ))
      (movingSlotLineProbability_eq_flags value prime hprime (path j) (current j) (base j)
        (external j) x (representative j) (hpath hw j) (hcurrent hw j))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLineProductComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed joint arithmetic comparison with the actual line integrals -/

namespace Ostmann
open scoped BigOperators Classical

/-- This replaces the actual simultaneous line probabilities, under the
original product law, by their symbolic rank and feasibility flags. The
support may contain any further arithmetic and smooth restrictions. -/
theorem moving_slot_line_product_comparison {A J O : Type*}
    [Fintype A] [Nonempty A] [Fintype J] [Fintype O] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin (n + 1))))
    (current : J → O → MovingSlotReversal (Fin (n + 1)))
    (base : J → O) (coordinate : J → Fin (n + 1)) (external : J → Bool)
    (k d : ℕ) (F T : ℝ) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hlen : ∀ j o, (path j o).length ≤ k)
    (hd : ∀ j o, (∀ s ∈ path j o, s.lengthLE d ∧ s.frequencyLE F) ∧
      (current j o).lengthLE d ∧ (current j o).frequencyLE F)
    (habsent : ∀ j o,
      (∀ s ∈ path j o, coordinate j ∉ s.leftSlots ∧ coordinate j ∉ s.rightSlots ∧
        coordinate j ∉ s.compensationSlots) ∧
      coordinate j ∉ (current j o).leftSlots ∧ coordinate j ∉ (current j o).rightSlots)
    (hvalues : ∀ a, |(value a : ℝ)| ≤ T)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coordinate j) a ≤ β)
    (hsize : ∀ j a, μ (coordinate j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (weight : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ x, ‖weight x‖ *
      ∏ j, internalLineScalar (external j) (prime (x (coordinate j))) ≤ B)
    (hpath : ∀ x, weight x ≠ 0 → ∀ j o s, s ∈ path j o →
      let φ := integerLineReduction value x (prime (x (coordinate j)))
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : ∀ x, weight x ≠ 0 → ∀ j,
      let φ := integerLineReduction value x (prime (x (coordinate j)))
      φ (current j (base j)).polynomial.v ≠ 0 ∧ φ (current j (base j)).polynomial.w ≠ 0) :
    ‖∑ x, (productPrior μ x : ℂ) * weight x *
      ((∏ j, (movingSlotLineProbability value prime hprime (path j) (current j)
          (external j) x (x (coordinate j)) : ℂ)) -
       ∏ j, (internalLineFlagWeight (external j) (prime (x (coordinate j)))
          (fun s => arithmeticTestFlag (lineTestPolynomials
            (fun o => movingSlotLine (path j o) (current j o)) (base j) s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card O)) *
        ((2 * ((k + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * T ^ d)) ^ (k + 1)) ^ 2) / V) * β) := by
  let Ψ := fun (x : Fin (n + 1) → A) (flags : J × (Bool ⊕ O) → Bool) =>
    weight x * ∏ j, (internalLineFlagWeight (external j) (prime (x (coordinate j)))
      (fun s => flags (j, s)) : ℂ)
  have hΨ (x : Fin (n + 1) → A) (flags : J × (Bool ⊕ O) → Bool) : ‖Ψ x flags‖ ≤ B :=
    line_product_multiplier_bound prime external (fun j => x (coordinate j)) (weight x) B
      (hweight x) flags
  have h := moving_slot_joint_symbolic_comparison value hinj prime hpInj hprime
    path current base coordinate k d F T hF hT hlen hd habsent hvalues μ hμ hmass
    α β V hα hβ hV hmax hpmax hsize Ψ B hB hΨ
  have he (x : Fin (n + 1) → A) := moving_line_product_on_support value prime hprime
    path current base external (fun j => x (coordinate j)) x (weight x) (hpath x) (hcurrent x)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [Ψ]
  rw [mul_sub, mul_assoc, he, ← mul_sub]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full square support as the actual occurrence line tests -/

namespace Ostmann
open scoped Classical

/-- A current compensation slot belongs to the type immediately below the
occurrence, including when a prime represents multiple occurrences. -/
theorem MovingSlotData.occurrence_compensation_level {σ : Type*} (tier : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, tier i < o.level := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR U left right ihL ihR =>
    intro o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have he := hT.2.2.1 i hi
      change tier i < n + 1
      omega
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihL hT.2.2.2.1 o' hmem i hi
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihR hT.2.2.2.2 o' hmem i hi

theorem MovingSlotData.occurrences_length {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.occurrences.length = 2 ^ n - 1 := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR U left right ihL ihR =>
    simp only [occurrences, List.length_cons, List.length_append, List.length_map, ihL, ihR,
      pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by decide) n
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSizes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete degree budgets for the sampled moving-giant paths -/

namespace Ostmann

theorem moving_flatten_length_le {σ : Type*} (n : ℕ) (x : TreeLeafTuple (List σ) n)
    (A : ℕ) (hx : MovingLeafLengthLE n x A) :
    (flattenMovingSlots n x).length ≤ 2 ^ n * A := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, flattenMovingSlots, pow_zero, one_mul] using hx
  | succ n ih =>
    simp only [flattenMovingSlots, List.length_append]
    have h := Nat.add_le_add (ih x.1 hx.1) (ih x.2 hx.2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_succ]
    ring

theorem moving_append_length_le {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) (A B : ℕ)
    (hx : MovingLeafLengthLE n x A) (hy : MovingLeafLengthLE n y B) :
    MovingLeafLengthLE n (appendMovingSlotLeaves n x y) (A + B) := by
  induction n with
  | zero =>
    change ((show List σ from x) ++ (show List σ from y)).length ≤ A + B
    rw [List.length_append]
    exact Nat.add_le_add hx hy
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length {σ : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n) :
    MovingLeafLengthLE n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => simp [MovingLeafLengthLE, movingCompensationSlots]
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem MovingSlotData.SizeLE.mono {σ : Type*} {n D E : ℕ} {T : MovingSlotData σ n}
    (h : T.SizeLE D) (hDE : D ≤ E) : T.SizeLE E := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    exact ⟨h.1.trans hDE, h.2.1.trans hDE, h.2.2.1.trans hDE, ihL h.2.2.2.1, ihR h.2.2.2.2⟩

/-- Compensation adds exactly four labels per bottom leaf per level. -/
theorem buildMovingSlotData_size {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (A B : ℕ) (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B) :
    (buildMovingSlotData n t small bulk samples).SizeLE (2 ^ n * (A + B + 4 * n + 4)) := by
  induction samples generalizing A B with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have hp : 0 < 2 ^ n := by positivity
    have hleft := ihL t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
      bulk.1 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.1) hbulk.1
    have hright := ihR t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
      bulk.2 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.2) hbulk.2
    have hD : 2 ^ n * (4 + A + B + 4 * n + 4) ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hbase : 2 ^ n * A + 2 ^ n * B ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hcomp : 2 ^ n * 4 ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    refine ⟨?_, ?_, ?_, hleft.mono hD, hright.mono hD⟩
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.1)
        (moving_flatten_length_le n _ B hbulk.1)).trans hbase
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.2)
        (moving_flatten_length_le n _ B hbulk.2)).trans hbase
    · exact (moving_flatten_length_le n _ 4 (moving_compensation_length n samples)).trans hcomp

theorem MovingSlotData.occurrence_size {σ : Type*} {n D : ℕ}
    (T : MovingSlotData σ n) (hT : T.SizeLE D) :
    ∀ o ∈ T.occurrences,
      o.current.lengthLE D ∧ ∀ s ∈ o.path, s.lengthLE D := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    have hb (b : Bool) : (step s CL CR u left right b).lengthLE D :=
      ⟨hT.2.1, hT.1, hT.2.2.1⟩
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨hb false, by simp⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihL hT.2.2.2.1 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb true
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihR hT.2.2.2.2 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem measurable_movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun z : ℝ × ℝ => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G z.1 z.2) := by
  have h0 := measurable_movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  have h1 := measurable_movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  exact h0.mul (Complex.continuous_conj.measurable.comp h1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalPolynomialFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

theorem reciprocalPolynomialFactor_original (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) (x X M : ℝ) (hX : X ≠ 0) (hM : M ≠ 0)
    (hP : P.eval x = M / X) (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    (reciprocalPolynomialFactor P hi hhi).value x = Complex.ofReal (X / M) := by
  rw [ClippedPolynomialFactor.value_of_mem _ x (by
    change P.eval x ∈ Set.Icc (1 : ℝ) hi
    rw [hP]
    exact hrange)]
  change Complex.ofReal ((P.eval x)⁻¹) = _
  rw [hP]
  congr 1
  field_simp

theorem reciprocalPolynomialFactor_budget (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    2 * (reciprocalPolynomialFactor P hi hhi).bound +
      (reciprocalPolynomialFactor P hi hhi).lip *
        ((reciprocalPolynomialFactor P hi hhi).hi - (reciprocalPolynomialFactor P hi hhi).lo) =
      hi + 1 := by
  dsimp only [reciprocalPolynomialFactor]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReciprocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

theorem giantReciprocalFactor_budget (P : Polynomial ℝ) (G : ℝ) :
    2 * (giantReciprocalFactor P G).bound + (giantReciprocalFactor P G).lip *
      ((giantReciprocalFactor P G).hi - (giantReciprocalFactor P G).lo) = 1 + Real.exp 2 := by
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_budget, add_comm]

theorem giantReciprocalFactor_value (P : Polynomial ℝ) (G x : ℝ)
    (hx : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1))) :
    (Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x = (Real.exp G / P.eval x : ℝ) := by
  have hlo : 0 < Real.exp (G - 1) := Real.exp_pos _
  have hp : 0 < P.eval x := hlo.trans_le hx.1
  have hrange : P.eval x / Real.exp (G - 1) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
    refine ⟨(one_le_div hlo).mpr hx.1, ?_⟩
    calc
      _ ≤ Real.exp (G + 1) / Real.exp (G - 1) := div_le_div_of_nonneg_right hx.2 hlo.le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_original _ _ _ x
    (Real.exp (G - 1)) (P.eval x) hlo.ne' hp.ne'
    (by simp only [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_comm]) hrange,
    ← Complex.ofReal_mul]
  apply congrArg (fun a : ℝ => (a : ℂ))
  rw [← mul_div_assoc, ← Real.exp_add, show 1 + (G - 1) = G by ring]

/-- Multiplication by the actual giant cutoff makes the clipped reciprocal
identical to the manuscript's reciprocal everywhere, including zero terms. -/
theorem giantReciprocalFactor_cutoff (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value x *
      ((Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x) =
        (positiveLogCutoff φ G (P.eval x) : ℂ) * (Real.exp G / P.eval x : ℝ) := by
  rw [logCutoffPolynomialFactor_value P φ G B D hB hD hφ hlip hout x]
  by_cases hz : positiveLogCutoff φ G (P.eval x) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have hx : 0 < P.eval x := by
      by_contra hn
      exact hz (by simp only [positiveLogCutoff, ite_eq_right hn])
    have hn : φ (Real.log (P.eval x) - G) ≠ 0 := by
      simpa only [positiveLogCutoff, ite_eq_left hx] using hz
    have hr : |Real.log (P.eval x) - G| < 1 := lt_of_not_ge (fun h => hn (hout _ h))
    have hbounds : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1)) := by
      have h := abs_lt.mp hr
      constructor
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
    rw [giantReciprocalFactor_value P G x hbounds]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

/-- Both actual cutoff priors are retained. In the diagonal environment the
remaining factor is precisely exp(G_R)/R, including all off-support zeros. -/
theorem giantOuterFactors_value (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    (giantOuterScalar diagonal : ℂ) *
      smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x =
        (positiveLogCutoff φ Jleft (L.eval x) : ℂ) * (positiveLogCutoff φ Jright (R.eval x) : ℂ) *
          (if diagonal then ((Real.exp Jright / R.eval x : ℝ) : ℂ) else 1) := by
  have hL := logCutoffPolynomialFactor_value L φ Jleft B D hB hD hφ hlip hout x
  have hR := logCutoffPolynomialFactor_value R φ Jright B D hB hD hφ hlip hout x
  have hone : onePolynomialFactor.value x = 1 := rfl
  have hrec := giantReciprocalFactor_cutoff R φ Jright B D hB hD hφ hlip hout x
  cases diagonal
  · simp only [giantOuterScalar, Bool.false_eq_true, ite_false, if_false, Complex.ofReal_one,
      giantOuterFactors, smoothPolynomialWeight, Fin.prod_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, one_mul, hL, hR, hone]
  · simp only [giantOuterScalar, ite_true, if_true, giantOuterFactors, smoothPolynomialWeight,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    calc
      _ = (logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip).value x *
          ((logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip).value x *
            ((Real.exp 1 : ℂ) * (giantReciprocalFactor R Jright).value x)) := by ring
      _ = _ := by rw [hL, hrec]; ring

theorem giantOuterFactors_budget (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) :
    smoothPolynomialBudget (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) =
      (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2) := by
  have hL := logCutoffPolynomialFactor_budget L φ Jleft B D hB hD hφ hlip
  have hR := logCutoffPolynomialFactor_budget R φ Jright B D hB hD hφ hlip
  cases diagonal
  · simp only [giantOuterFactors, Bool.false_eq_true, ite_false, if_false, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, onePolynomialFactor]
    rw [hL, hR]
    ring
  · simp only [giantOuterFactors, ite_true, if_true, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    rw [hL, hR, giantReciprocalFactor_budget]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem giantOuterWeight_polynomial (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    giantOuterWeight φ Jleft Jright diagonal (L.eval x) (R.eval x) =
      (giantOuterScalar diagonal : ℂ) *
        smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x :=
  (giantOuterFactors_value L R φ Jleft Jright B D hB hD hφ hlip hout diagonal x).symm

theorem giantOuterWeight_norm (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖giantOuterWeight φ Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
        (if diagonal then 1 + Real.exp 2 else 2) := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv := giantOuterWeight_polynomial (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D
    hB hD hφ hlip hout diagonal 0
  simp only [Polynomial.eval_C] at hv
  rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := mul_le_mul_of_nonneg_left (smoothPolynomialWeight_norm
    (giantOuterFactors (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D hB hD hφ hlip diagonal) 0) hs
  rw [giantOuterFactors_budget] at h
  simpa only [mul_assoc] using h

theorem measurable_giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => giantOuterWeight φ Jleft Jright diagonal z.1 z.2) := by
  have hc (J : ℝ) : Measurable (fun x => (positiveLogCutoff φ J x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ J B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ J B D hB hD hφ hlip).continuous_value.congr he).measurable
  have hratio : Measurable (fun z : ℝ × ℝ => if diagonal then ((Real.exp Jright / z.2 : ℝ) : ℂ) else 1) := by
    cases diagonal
    · exact measurable_const
    · exact Complex.continuous_ofReal.measurable.comp (measurable_const.div measurable_snd)
  exact ((hc Jleft).comp measurable_fst |>.mul ((hc Jright).comp measurable_snd)).mul hratio

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

theorem movingModularSpectator_norm {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    ‖movingModularSpectator value q g D T x y‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf => simpa only [movingModularSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingModularSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeOccurrences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous occurrences of one actual internal prime in both histories -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimeOccurrences_card {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) :
    Fintype.card (MovingPrimeOccurrences value T p) ≤ 2 * (2 ^ n - 1) := by
  have h (side : Bool) : Fintype.card {j : Fin (T side).occurrences.length //
      ∃ i ∈ ((T side).occurrences.get j).current.compensationSlots, value i = p} ≤ 2 ^ n - 1 := by
    calc
      _ ≤ Fintype.card (Fin (T side).occurrences.length) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by rw [Fintype.card_fin, MovingSlotData.occurrences_length]
  rw [Fintype.card_sigma, Fintype.sum_bool]
  have h0 := h false
  have h1 := h true
  omega

theorem movingInternalLocalSupport_occurrences {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod (p ^ 2)) :
    (∀ side, movingInternalLocalSupport value (T side) p x y) ↔
      ∀ j : MovingPrimeOccurrences value T p,
        let L := movingPrimeOccurrenceLine value T p j
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        squareReduction p (φ L.a * x + φ L.b * y) = 0 ∧ φ L.a * x + φ L.b * y ≠ 0 := by
  constructor
  · intro h j
    obtain ⟨i, hi, hpi⟩ := j.2.property
    exact h j.1 _ (List.get_mem _ _) i hi hpi
  · intro h side o ho i hi hpi
    obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
    let j : MovingPrimeOccurrences value T p :=
      ⟨side, ⟨⟨k, hk⟩, by simpa only [List.get_eq_getElem, hko] using ⟨i, hi, hpi⟩⟩⟩
    simpa only [movingPrimeOccurrenceLine, movingPrimeOccurrence, j, List.get_eq_getElem, hko] using h j

/-- Every row used by the simultaneous lift estimate is nonzero, by the
actual prime tiers and frequencies of its original occurrence. -/
theorem movingPrimeOccurrenceLine_nonzero {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (j : MovingPrimeOccurrences value T p) :
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a ≠ 0 ∨ φ L.b ≠ 0 := by
  obtain ⟨i, hi, hpi⟩ := j.2.property
  subst p
  let : Fact (value i).Prime := ⟨hprime i⟩
  let o := movingPrimeOccurrence value T (value i) j
  have hu := (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    o (List.get_mem _ _) i
    ((T j.1).occurrence_compensation_level tier (hlevels j.1) o (List.get_mem _ _) i hi) (hf j.1)
  change MovingSlotReversal.naturalReduction (value i) value (movingSlotLine o.path o.current).a ≠ 0 ∨
    MovingSlotReversal.naturalReduction (value i) value (movingSlotLine o.path o.current).b ≠ 0
  apply movingHistoryLine_nonzero (o.path.map MovingSlotReversal.polynomial)
    o.current.polynomial.v o.current.polynomial.w (MovingSlotReversal.naturalReduction (value i) value)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hu.1 t ht
  · exact hu.2.1
  · exact hu.2.2

/-- Ancestor denominators are also units at the current internal prime. -/
theorem movingPrimeOccurrenceLine_denominator_ne_zero {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (j : MovingPrimeOccurrences value T p) :
    MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).denominator ≠ 0 := by
  obtain ⟨i, hi, hpi⟩ := j.2.property
  subst p
  let : Fact (value i).Prime := ⟨hprime i⟩
  let o := movingPrimeOccurrence value T (value i) j
  have hu := (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    o (List.get_mem _ _) i
    ((T j.1).occurrence_compensation_level tier (hlevels j.1) o (List.get_mem _ _) i hi) (hf j.1)
  apply movingPolynomialAncestors_denominator (o.path.map MovingSlotReversal.polynomial)
    (MovingSlotReversal.naturalReduction (value i) value)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (hu.1 t ht).2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalBaseAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual internal-prime averages after removing their square exclusions -/

namespace Ostmann
open scoped Classical BigOperators

/-- The field average is the exact simultaneous line probability for all
occurrences of the prime in both original histories. -/
theorem movingInternalBaseFactor_average {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod p × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2) =
    (internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) : ℂ) := by
  classical
  let P := fun z : ZMod p × (ZMod p)ˣ => ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * z.1 + φ L.b * z.2 = 0
  have hs : (∑ z : ZMod p × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2) =
      (Fintype.card {z : ZMod p × (ZMod p)ˣ // P z} : ℂ) := by
    rw [Fintype.card_subtype]
    simp only [movingInternalBaseFactor, P, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  dsimp only [P] at hs
  rw [hs]
  simp only [internalLineProbability, ite_true, if_true, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [mul_comm, ← div_eq_mul_inv]
  simp only [← Nat.card_eq_fintype_card]

/-- All rows and all cleared denominators in this line probability come from
the actual moving trees. Thus the polynomial flags used later are exact. -/
theorem movingInternalBaseProbability_eq_flags {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (base : MovingPrimeOccurrences value T p) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) =
      internalLineFlagWeight true p (fun s => arithmeticTestFlag
        (MovingSlotReversal.naturalReduction p value
          (lineTestPolynomials (movingPrimeOccurrenceLine value T p) base s) = 0)) := by
  classical
  let φ := MovingSlotReversal.naturalReduction p value
  let L := movingPrimeOccurrenceLine value T p
  have hd := movingPrimeOccurrenceLine_denominator_ne_zero tier value hprime hdisjoint T hlevels p hf
  have hr := movingPrimeOccurrenceLine_nonzero tier value hprime hdisjoint T hlevels p hf base
  have he (x y : ZMod p) : (∀ j, φ (L j).a * x + φ (L j).b * y = 0) ↔
      (∀ j, ((L j).normalized φ).1 * x + ((L j).normalized φ).2 * y = 0) := by
    apply forall_congr'
    intro j
    simp only [PolynomialGiantLine.normalized]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff, or_iff_left (hd j)]
  have hc := Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : ZMod p × (ZMod p)ˣ => he z.1 z.2))
  have hr' : ((L base).normalized φ).1 ≠ 0 ∨ ((L base).normalized φ).2 ≠ 0 := by
    have hz := (L base).normalized_zero_iff φ (hd base)
    exact hr.imp (fun h h0 => h (hz.1.mp h0)) (fun h h0 => h (hz.2.mp h0))
  have hext := external_lineSystem_integral_eq_flags L base φ hd hr'
  unfold internalLineProbability
  simp only [ite_true, if_true, ← Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card] at hext
  change (Nat.card {z : ZMod p × (ZMod p)ˣ //
    ∀ j, φ (L j).a * z.1 + φ (L j).b * z.2 = 0} : ℝ) /
      Nat.card (ZMod p × (ZMod p)ˣ) = _
  rw [hc]
  exact hext

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRepresentativeLineSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed occurrence systems for a representative sampled prime -/

namespace Ostmann
open scoped Classical BigOperators

/-- On samples with distinct prime values, all occurrences of the selected
prime are precisely the fixed occurrences of its representative slot. -/
theorem movingPrimeLineSystem_representative_iff {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    (hunique : ∀ i, value i = value rep → i = rep)
    (x y : ZMod (value rep)) :
    (∀ j : MovingPrimeOccurrences value T (value rep),
      let φ := MovingSlotReversal.naturalReduction (value rep) value
      let L := movingPrimeOccurrenceLine value T (value rep) j
      φ L.a * x + φ L.b * y = 0) ↔
    (∀ j : MovingPairRepresentativeOccurrences T rep,
      let φ := MovingSlotReversal.naturalReduction (value rep) value
      let L := movingRepresentativeLine T rep j
      φ L.a * x + φ L.b * y = 0) := by
  constructor
  · intro h j
    let k : MovingPrimeOccurrences value T (value rep) :=
      ⟨j.1, ⟨j.2.val, ⟨rep, j.2.property, rfl⟩⟩⟩
    exact h k
  · intro h j
    obtain ⟨i, hi, hv⟩ := j.2.property
    have he : i = rep := hunique i hv
    subst i
    let k : MovingPairRepresentativeOccurrences T rep := ⟨j.1, ⟨j.2.val, hi⟩⟩
    exact h k

/-- This reindexing fixes the polynomial family before the prime values are
sampled, as required by the joint small-prime coincidence theorem. -/
theorem movingInternalBaseProbability_representative {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingRepresentativeLine T rep j).b) := by
  unfold internalLineProbability
  simp only [ite_true, if_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod (value rep) × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : ZMod (value rep) × (ZMod (value rep))ˣ =>
      movingPrimeLineSystem_representative_iff value T rep hunique z.1 z.2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIndexedLineSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite index for every representative's actual line system -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPairOccurrenceIndex_card {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) :
    Fintype.card (MovingPairOccurrenceIndex T) = 2 * (2 ^ n - 1) := by
  simp only [MovingPairOccurrenceIndex, Fintype.card_sigma, Fintype.card_fin,
    Fintype.sum_bool, MovingSlotData.occurrences_length]
  omega

theorem movingRepresentativeIndex_surjective {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) :
    Function.Surjective (movingRepresentativeIndex T rep base) := by
  intro j
  refine ⟨⟨j.1, j.2.val⟩, ?_⟩
  simp only [movingRepresentativeIndex, dite_eq_left j.2.property]

theorem movingIndexedOccurrence_absent {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (∀ s ∈ (movingIndexedOccurrence T rep base o).path,
      rep ∉ s.leftSlots ∧ rep ∉ s.rightSlots ∧ rep ∉ s.compensationSlots) ∧
      rep ∉ (movingIndexedOccurrence T rep base o).current.leftSlots ∧
      rep ∉ (movingIndexedOccurrence T rep base o).current.rightSlots := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  have hbound := (T j.1).occurrence_bounds tier (hlevels j.1) t ht
  have hrep := (T j.1).occurrence_compensation_level tier (hlevels j.1) t ht rep j.2.property
  exact t.absent_of_level tier hbound.2.2 rep hrep

theorem movingIndexedOccurrence_path_length {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (movingIndexedOccurrence T rep base o).path.length ≤ n := by
  let j := movingRepresentativeIndex T rep base o
  have h := (T j.1).occurrence_bounds tier (hlevels j.1)
    ((T j.1).occurrences.get j.2.val) (List.get_mem _ _)
  exact (Nat.le_add_left _ _).trans h.2.1

theorem movingIndexedOccurrence_units {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0))
    (o : MovingPairOccurrenceIndex T) :
    let φ := MovingSlotReversal.naturalReduction (value rep) value
    let t := movingIndexedOccurrence T rep base o
    (∀ s ∈ t.path, φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0) ∧
      φ t.current.polynomial.v ≠ 0 ∧ φ t.current.polynomial.w ≠ 0 := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  exact (T j.1).occurrence_units_of_prime_types tier value hprime hdisjoint (hlevels j.1)
    t ht rep ((T j.1).occurrence_compensation_level tier (hlevels j.1) t ht rep j.2.property)
    (hf j.1)

theorem movingIndexedOccurrence_size {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (d : ℕ) (F : ℝ)
    (hsize : ∀ side, (T side).SizeLE d)
    (hfreq : ∀ side, (T side).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep) (o : MovingPairOccurrenceIndex T) :
    (∀ s ∈ (movingIndexedOccurrence T rep base o).path, s.lengthLE d ∧ s.frequencyLE F) ∧
      (movingIndexedOccurrence T rep base o).current.lengthLE d ∧
      (movingIndexedOccurrence T rep base o).current.frequencyLE F := by
  let j := movingRepresentativeIndex T rep base o
  let t := (T j.1).occurrences.get j.2.val
  have ht : t ∈ (T j.1).occurrences := List.get_mem _ _
  have hs := (T j.1).occurrence_size (hsize j.1) t ht
  have hf := (T j.1).occurrence_frequencies _ (hfreq j.1) t ht
  exact ⟨fun s h => ⟨hs.2 s h, hf.2 s h⟩, hs.1, hf.1⟩

theorem movingInternalBaseProbability_indexed {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (rep : σ)
    [Fact (value rep).Prime] (hunique : ∀ i, value i = value rep → i = rep)
    (base : MovingPairRepresentativeOccurrences T rep) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingIndexedLine T rep base j).b) := by
  rw [movingInternalBaseProbability_representative value T rep hunique]
  have he (x y : ZMod (value rep)) :
      (∀ j : MovingPairRepresentativeOccurrences T rep,
        let φ := MovingSlotReversal.naturalReduction (value rep) value
        let L := movingRepresentativeLine T rep j
        φ L.a * x + φ L.b * y = 0) ↔
      (∀ o : MovingPairOccurrenceIndex T,
        let φ := MovingSlotReversal.naturalReduction (value rep) value
        let L := movingIndexedLine T rep base o
        φ L.a * x + φ L.b * y = 0) :=
    (movingRepresentativeIndex_surjective T rep base).forall
  unfold internalLineProbability
  simp only [ite_true, if_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod (value rep) × (ZMod (value rep))ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun z : ZMod (value rep) × (ZMod (value rep))ˣ => he z.1 z.2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIndexedProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the fixed occurrence system for the small-prime comparison -/

namespace Ostmann
open scoped Classical

theorem externalLineProbability_normalized {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    internalLineProbability true (fun j => φ (L j).a) (fun j => φ (L j).b) =
      internalLineProbability true (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) := by
  have he (x y : ZMod p) : (∀ j, φ (L j).a * x + φ (L j).b * y = 0) ↔
      (∀ j, ((L j).normalized φ).1 * x + ((L j).normalized φ).2 * y = 0) := by
    apply forall_congr'
    intro j
    simp only [PolynomialGiantLine.normalized]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff, or_iff_left (hd j)]
  unfold internalLineProbability
  simp only [ite_true, if_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod p × (ZMod p)ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun z : ZMod p × (ZMod p)ˣ => he z.1 z.2))

theorem movingIndexedLine_denominator_ne_zero {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) (base : MovingPairRepresentativeOccurrences T rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0))
    (o : MovingPairOccurrenceIndex T) :
    MovingSlotReversal.naturalReduction (value rep) value
      (movingIndexedLine T rep base o).denominator ≠ 0 := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  have hu := movingIndexedOccurrence_units T tier value hprime hdisjoint hlevels rep base hf o
  change MovingSlotReversal.naturalReduction (value rep) value
    (movingPolynomialAncestors
      ((movingIndexedOccurrence T rep base o).path.map MovingSlotReversal.polynomial)).denominator ≠ 0
  apply movingPolynomialAncestors_denominator
    ((movingIndexedOccurrence T rep base o).path.map MovingSlotReversal.polynomial)
    (MovingSlotReversal.naturalReduction (value rep) value)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (hu.1 t ht).2.2

theorem movingInternalBaseProbability_indexed_normalized {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : σ) [Fact (value rep).Prime] (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, value i = value rep → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).a)
      (fun j => MovingSlotReversal.naturalReduction (value rep) value
        (movingPrimeOccurrenceLine value T (value rep) j).b) =
      internalLineProbability true
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).1)
        (fun j => ((movingIndexedLine T rep base j).normalized
          (MovingSlotReversal.naturalReduction (value rep) value)).2) := by
  rw [movingInternalBaseProbability_indexed value T rep hunique base]
  exact externalLineProbability_normalized (movingIndexedLine T rep base)
    (MovingSlotReversal.naturalReduction (value rep) value)
    (movingIndexedLine_denominator_ne_zero T tier value hprime hdisjoint hlevels rep base hf)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledIndexedProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime samples in the fixed line-probability coordinates -/

namespace Ostmann
open scoped Classical

theorem movingSampledIndexedProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (x : Fin N → A)
    (T : Bool → MovingSlotData (Fin N) n) (tier : Fin N → ℕ)
    (hdisjoint : ∀ i j, tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : Fin N) (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, prime (x i) = prime (x rep) → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (prime (x rep))) ≠ 0)) :
    letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b) =
      movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
        (fun o => (movingIndexedOccurrence T rep base o).path)
        (fun o => (movingIndexedOccurrence T rep base o).current) true x (x rep) := by
  let : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  have h := movingInternalBaseProbability_indexed_normalized T tier (fun i => prime (x i))
    (fun i => hprime (x i)) hdisjoint hlevels rep base hunique hf
  simpa only [movingSlotLineProbability, integerLineReduction,
    MovingSlotReversal.naturalReduction, Int.cast_natCast, movingIndexedLine] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingActualLineComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symbolic replacement for the actual two-history internal line factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_actual_line_product_comparison {A J : Type*}
    [Fintype A] [Nonempty A] [Fintype J] {N n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin (N + 1)) n) (tier : Fin (N + 1) → ℕ)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : J → Fin (N + 1)) (base : ∀ j, MovingPairRepresentativeOccurrences T (rep j))
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ side, (T side).SizeLE d)
    (hfreq : ∀ side, (T side).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : Fin (N + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (rep j) a ≤ β)
    (hprimeSize : ∀ j a, μ (rep j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (weight : (Fin (N + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ x, ‖weight x‖ * ∏ j, internalLineScalar true (prime (x (rep j))) ≤ B)
    (hdisjoint : ∀ x, weight x ≠ 0 → ∀ i j,
      tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hunique : ∀ x, weight x ≠ 0 → ∀ j i, prime (x i) = prime (x (rep j)) → i = rep j)
    (hfmod : ∀ x, weight x ≠ 0 → ∀ j side,
      (T side).Frequencies (fun s => (s : ZMod (prime (x (rep j)))) ≠ 0)) :
    ‖∑ x, (productPrior μ x : ℂ) * weight x *
      ((∏ j, (movingSampledInternalProbability prime hprime T x (rep j) : ℂ)) -
       ∏ j, (internalLineFlagWeight true (prime (x (rep j)))
         (fun s => arithmeticTestFlag (lineTestPolynomials
           (movingIndexedLine T (rep j) (base j)) ⟨(base j).1, (base j).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card (MovingPairOccurrenceIndex T))) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  let path := fun j o => (movingIndexedOccurrence T (rep j) (base j) o).path
  let current := fun j o => (movingIndexedOccurrence T (rep j) (base j) o).current
  let b : J → MovingPairOccurrenceIndex T := fun j => ⟨(base j).1, (base j).2.val⟩
  have hi : Function.Injective (fun a => (prime a : ℤ)) := by
    intro a b h
    apply hpInj
    exact Int.ofNat.inj h
  have hu (x : Fin (N + 1) → A) (hx : weight x ≠ 0) (j : J) (o : MovingPairOccurrenceIndex T) :=
    movingIndexedOccurrence_units T tier (fun i => prime (x i)) (fun i => hprime (x i))
      (hdisjoint x hx) hlevels (rep j) (base j) (hfmod x hx j) o
  have h := moving_slot_line_product_comparison (fun a => (prime a : ℤ)) hi prime hpInj hprime
    path current b rep (fun _ => true) n d F U hF hU
    (fun j o => movingIndexedOccurrence_path_length T tier hlevels (rep j) (base j) o)
    (fun j o => movingIndexedOccurrence_size T d F hsize hfreq (rep j) (base j) o)
    (fun j o => movingIndexedOccurrence_absent T tier hlevels (rep j) (base j) o)
    hvalues μ hμ hmass α β V hα hβ hV hmax hpmax hprimeSize weight B hB hweight
    (by
      intro x hx j o s hs
      simpa only [integerLineReduction, MovingSlotReversal.naturalReduction, Int.cast_natCast] using
        (hu x hx j o).1 s hs)
    (by
      intro x hx j
      simpa only [integerLineReduction, MovingSlotReversal.naturalReduction, Int.cast_natCast] using
        (hu x hx j (b j)).2)
  have he (x : Fin (N + 1) → A) :
      weight x * (∏ j, (movingSampledInternalProbability prime hprime T x (rep j) : ℂ)) =
      weight x * ∏ j, (movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
        (path j) (current j) true x (x (rep j)) : ℂ) := by
    by_cases hx : weight x = 0
    · simp only [hx, zero_mul]
    · congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg (fun r : ℝ => (r : ℂ))
        (movingSampledIndexedProbability prime hprime x T tier (hdisjoint x hx) hlevels
          (rep j) (base j) (hunique x hx j) (hfmod x hx j))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_assoc, mul_sub, he, ← mul_sub, ← mul_assoc]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem card_movingSampleIndex (n : ℕ) : Fintype.card (MovingSampleIndex n) = 2 * n * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card ((TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n)) = _
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fin, card_treeLeafIndex, ih, pow_succ]
      ring

theorem movingCompensationPrior_indexed {A : Type*} (μ : A → ℝ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationPrior μ n a =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      change (∏ j : Fin 4, μ (a j)) = ∏ _t : Unit, ∏ j : Fin 4, μ (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      change movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2 =
        ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
          ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type, ih, ih]
      rfl

/-- The tree law is precisely the product of the original coordinate priors.
This identity permits the proved equality-pattern comparison to be applied
without replacing the law by a conditioned or uniform distribution. -/
theorem movingSamplesPrior_coordinates {A : Type*} (μ : ℕ → A → ℝ) (n : ℕ)
    (a : MovingSampleSlots A n) :
    movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n, μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change movingCompensationPrior (μ n) n u * movingSamplesPrior μ l * movingSamplesPrior μ r =
        ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool,
        movingCompensationPrior_indexed, hl, hr]
      simp only [movingSampleTier, movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact compensation factors in the original history weight

Every sampled prime occurs once in the factor `u` at the node where it is
sampled. Its subsequent appearances in descendants do not add factors of `u`.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationProduct_indexed {A : Type*} (value : A → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      simp only [flattenMovingSlots, movingCompensationSlots, MovingSlotReversal.naturalProduct,
        List.map_ofFn, List.prod_ofFn]
      change (∏ j : Fin 4, value (a j)) = ∏ _t : Unit, ∏ j : Fin 4, value (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      simp only [movingCompensationSlots, flattenMovingSlots, movingNaturalProduct_append, ih]
      change _ = ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
        ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type]
      rfl

theorem movingSampleProduct_coordinates {A : Type*} (value : A → ℕ) {n : ℕ}
    (a : MovingSampleSlots A n) :
    movingSampleProduct value a =
      ∏ i : MovingSampleIndex n, value (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change _ = ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool]
      rw [movingSampleProduct, movingCompensationProduct_indexed, hl, hr]
      simp only [movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

/-- Prior times compensation is precisely the dependent pattern weight
used in the internal-line comparison, before any coincidences are collapsed. -/
theorem movingSamples_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) {n : ℕ} (a : MovingSampleSlots A n) :
    (movingSampleProduct value a : ℝ) * movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n,
        (value (movingSampleCoordinates A n a i) : ℝ) *
          μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  rw [movingSampleProduct_coordinates, movingSamplesPrior_coordinates,
    Nat.cast_prod, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality patterns of the two actual internal sample trees -/

namespace Ostmann
open scoped Classical BigOperators

/-- The two histories have exactly `4*n*2^n` independent internal draws,
irrespective of the number of protected bulk positions. -/
theorem card_movingSamplePairIndex (n : ℕ) :
    Fintype.card (Bool × MovingSampleIndex n) = 4 * n * 2 ^ n := by
  rw [Fintype.card_prod, Fintype.card_bool, card_movingSampleIndex]
  ring

theorem movingSamplePair_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) (n : ℕ) (x : Bool × MovingSampleIndex n → A) :
    let a := (movingSamplePairCoordinates A n).symm x
    ((movingSampleProduct value a.1 : ℝ) * movingSamplesPrior μ a.1) *
      ((movingSampleProduct value a.2 : ℝ) * movingSamplesPrior μ a.2) =
        ∏ i : Bool × MovingSampleIndex n, (value (x i) : ℝ) * μ (movingSampleTier i.2) (x i) := by
  dsimp only
  rw [movingSamples_compensated_prior, movingSamples_compensated_prior,
    Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [movingSamplePairCoordinates_left, movingSamplePairCoordinates_right]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePatternBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying representative-prior domination to the literal sampled pair -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPairCompensatedMass_pattern {A C : Type*} (μ : ℕ → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C) (x : C → A) :
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm (x ∘ pattern)) =
      internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime x := by
  rw [movingPairCompensatedMass, movingSamplePair_compensated_prior]
  rfl

/-- The weight bound needed by the proved symbolic-line comparison now
applies to the original two sample trees, including each node's `u` factor. -/
theorem movingPairCompensatedMass_pattern_bound {A C : Type*} [Fintype C]
    (μ : ℕ → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (C → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ x, ‖G x‖ ≤ B) (x : C → A) :
    ‖(movingPairCompensatedMass μ prime
        ((movingSamplePairCoordinates A n).symm (x ∘ pattern)) : ℂ) * G x‖ *
      (∏ c, (prime (x c) : ℝ)⁻¹) ≤
        (B * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
          ∏ c, μ (movingSampleTier (rep c).val.2) (x c) := by
  rw [movingPairCompensatedMass_pattern]
  have h := internalPatternWeight_complex_bound pattern rep
    (fun i => μ (movingSampleTier i.2)) prime E hprime
    (fun i a => hμ _ a) (fun i a => hbound _ a) G B hB hG x
  simpa only [card_movingSamplePairIndex] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticSumRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original arithmetic error after summing all equality patterns -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingInternalArithmeticError_nonneg (n c d : ℕ) (F U α β V : ℝ)
    (hF : 1 ≤ F) (hU : 1 ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 ≤ V) :
    0 ≤ movingInternalArithmeticError n c d F U α β V := by
  have hbase : 1 ≤ 2 * (F * U ^ d) := by
    have hh := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hU (n := d))
    linarith
  have hh := one_le_pow₀ (one_le_pow₀ hbase (n := n + 1)) (n := 2)
  have hlog : 0 ≤ Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) :=
    Real.log_nonneg (by linarith)
  unfold movingInternalArithmeticError
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedPrimeFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bulk and nonbulk decomposition of the original finite prime law -/

namespace Ostmann
open scoped Classical BigOperators

theorem finite_prior_selected_fubini {σ J A : Type*}
    [Fintype σ] [Fintype J] [Fintype A]
    (slot : J ↪ σ) (μ : σ → A → ℝ) (F : (σ → A) → ℂ) :
    (∑ x : σ → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x) =
      ∑ y : {i : σ // i ∉ Set.range slot} → A,
        ((∏ i : {i : σ // i ∉ Set.range slot}, μ i (y i) : ℝ) : ℂ) *
          ∑ x : J → A, ((∏ j, μ (slot j) (x j) : ℝ) : ℂ) * F (joinBulkNonbulk slot x y) := by
  rw [← finite_prior_reindex (selectedIndexEquiv slot) μ F]
  let e := Equiv.sumArrowEquivProdArrow J {i : σ // i ∉ Set.range slot} A
  have he := e.symm.sum_comp (fun x =>
    ((∏ i, μ (selectedIndexEquiv slot i) (x i) : ℝ) : ℂ) *
      F (x ∘ (selectedIndexEquiv slot).symm))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  have hs := Fintype.sum_prod_type (fun x : (J → A) × ({i : σ // i ∉ Set.range slot} → A) =>
    ((∏ i, μ (selectedIndexEquiv slot i) (e.symm x i) : ℝ) : ℂ) *
      F (e.symm x ∘ (selectedIndexEquiv slot).symm))
  simp only [finite_univ_canonical] at hs
  rw [hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hp := Fintype.prod_sum_type (fun i : J ⊕ {i : σ // i ∉ Set.range slot} =>
    μ (selectedIndexEquiv slot i) (e.symm (x, y) i))
  simp only [finite_univ_canonical] at hp
  rw [hp]
  simp only [selectedIndexEquiv_inl, selectedIndexEquiv_inr,
    e, Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr,
    Complex.ofReal_mul]
  change _ * F (joinBulkNonbulk slot x y) = _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalOuterWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

theorem inactiveRegularDensity_bounds {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (reg : J → σ) (active : J → Bool) (x : σ → A) :
    0 ≤ inactiveRegularDensity prime reg active x ∧
      inactiveRegularDensity prime reg active x ≤ 1 := by
  have hlocal (j : J) : 0 ≤ (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ∧
      (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ≤ 1 := by
    have hp : (1 : ℝ) ≤ prime (x (reg j)) := by exact_mod_cast (hprime _).one_le
    cases active j
    · simp only [Bool.false_eq_true, ite_false, if_false]
      exact ⟨sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hp),
        sub_le_self _ (by positivity)⟩
    · simp
  exact ⟨Finset.prod_nonneg (fun j _ => (hlocal j).1),
    Finset.prod_le_one (fun j _ => (hlocal j).1) (fun j _ => (hlocal j).2)⟩

/-- Inactive factors use only the fixed nonbulk coordinates. -/
theorem inactiveRegularDensity_joinBulkNonbulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (x : σ → A) (z : K → A) :
    inactiveRegularDensity prime reg active (joinBulkNonbulk slot z (fun i => x i)) =
      inactiveRegularDensity prime reg active x := by
  apply Finset.prod_congr rfl
  intro j _
  cases ha : active j
  · have hj : reg j ∉ Set.range slot := hfixed j ha
    have he := joinBulkNonbulk_nonbulk slot z (fun i => x i) ⟨reg j, hj⟩
    simp only [Bool.false_eq_true, ite_false, if_false]
    rw [he]
  · simp only [ite_true, if_true]

theorem diagonalOuterMajorant_pos (B D : ℝ) (diagonal : Bool) :
    0 < diagonalOuterMajorant B D diagonal := by
  unfold diagonalOuterMajorant
  have hs : 0 ≤ giantOuterScalar diagonal := by
    cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hh : 0 ≤ (if diagonal then 1 + Real.exp 2 else (2 : ℝ)) := by
    cases diagonal <;> positivity
  positivity

theorem movingDiagonalOuterWeight_norm {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    ‖movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x‖ ≤ 1 := by
  have hc := diagonalOuterMajorant_pos B D diagonal
  have hd := inactiveRegularDensity_bounds prime hprime reg active x
  have ho := giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal
    (Real.exp u) (Real.exp v)
  unfold movingDiagonalOuterWeight
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.1,
    Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply (div_le_one hc).mpr
  calc
    _ ≤ ‖giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v)‖ * 1 :=
      mul_le_mul_of_nonneg_left hd.2 (norm_nonneg _)
    _ ≤ diagonalOuterMajorant B D diagonal := by
      rw [mul_one]
      exact ho.trans (by unfold diagonalOuterMajorant; linarith)

theorem movingDiagonalOuterWeight_measurable {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : σ → A) :
    Measurable (fun z : ℝ × ℝ => movingDiagonalOuterWeight prime reg active φ
      Jleft Jright B D diagonal z.1 z.2 x) := by
  have hm := (measurable_giantOuterWeight φ Jleft Jright B D hB hD hφ hlip hout diagonal).comp
    ((Real.continuous_exp.measurable.comp measurable_fst).prodMk
      (Real.continuous_exp.measurable.comp measurable_snd))
  exact (hm.mul_const _).div_const _

theorem movingDiagonalOuterWeight_bulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) (z : K → A) :
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v
      (joinBulkNonbulk slot z (fun i => x i)) =
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x := by
  unfold movingDiagonalOuterWeight
  rw [inactiveRegularDensity_joinBulkNonbulk prime reg active slot hfixed]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternExternalPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original external priors joined to the internal equality-pattern law

Only internal occurrences incur the repetition loss; the bound is uniform
in the number of external and protected bulk coordinates.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_external_prior_bound {A B C : Type*} [Fintype B] [Fintype C]
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (B ⊕ C → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : B ⊕ C → A) :
    ‖((∏ b, ν b (x (.inl b)) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (.inr (pattern i)))) : ℂ) * G x‖ *
      (∏ c, (prime (x (.inr c)) : ℝ)⁻¹) ≤
    (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
      ∏ i : B ⊕ C,
        (Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) i) (x i) := by
  let ext : B → A := fun b => x (.inl b)
  let inside : C → A := fun c => x (.inr c)
  have hx : Sum.elim ext inside = x := by
    funext i
    cases i <;> rfl
  have h := movingPairCompensatedMass_pattern_bound μ prime n pattern rep E hprime hμ hbound
    (fun y => G (Sum.elim ext y)) D hD (fun y => hG _) inside
  rw [hx] at h
  have he : 0 ≤ ∏ b, ν b (ext b) := Finset.prod_nonneg (fun b _ => hν b _)
  have hh := mul_le_mul_of_nonneg_left h he
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg he]
  simp only [norm_mul] at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [ext, inside, Function.comp_def] <;> ring)

/-- The same original-law bound in the exact finite coordinates of the
symbolic-line comparison. External coordinates do not enter the loss. -/
theorem movingPattern_fin_prior_bound {A B C : Type*} [Fintype B] [Fintype C]
    {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ) (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : Fin (N + 1) → A) :
    ‖((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x‖ *
      (∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) ≤
    (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
      productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  let y : B ⊕ C → A := x ∘ e.symm
  have hy : y ∘ e = x := by funext i; exact congrArg x (e.symm_apply_apply i)
  have h := movingPattern_external_prior_bound μ ν prime n pattern rep E hprime hμ hν hbound
    (fun z => G (z ∘ e)) D hD (fun z => hG _) y
  rw [hy] at h
  have hp := e.prod_comp (fun j =>
    (Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) j) (y j))
  simp only [y, Function.comp_apply, Equiv.symm_apply_apply] at hp
  dsimp only [y, Function.comp_apply] at h
  rw [← hp] at h
  simpa only [y, Function.comp_apply, internalLineScalar, ite_true, if_true, productPrior] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coordinates for the actual internal-pattern tree pair -/

namespace Ostmann
open scoped Classical

/-- Original class injectivity and separation from external slots imply the
unique-prime condition required by the simultaneous line comparison. -/
theorem movingPatternFin_unique {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hinj : Function.Injective prime)
    (x : Fin (N + 1) → A)
    (hclasses : Function.Injective (fun c => x (e.symm (.inr c))))
    (hcross : ∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (c : C) (i : Fin (N + 1)) (hi : prime (x i) = prime (x (e.symm (.inr c)))) :
    i = e.symm (.inr c) := by
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  cases j with
  | inl b => exact False.elim (hcross b c hi)
  | inr d => exact congrArg (fun c => e.symm (.inr c)) (hclasses (hinj hi))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalPatternSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original pattern weights and their exact zero extension -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternInjectionGuard_norm {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D) (x : Fin (N + 1) → A) :
    ‖movingPatternInjectionGuard e G x‖ ≤ D := by
  unfold movingPatternInjectionGuard
  split_ifs
  · exact hG x
  · simpa only [norm_zero] using hD

theorem movingPatternInjectionGuard_nonzero {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (G : (Fin (N + 1) → A) → ℂ)
    (x : Fin (N + 1) → A) (hx : movingPatternInjectionGuard e G x ≠ 0) :
    Function.Injective (fun c => x (e.symm (.inr c))) ∧ G x ≠ 0 := by
  unfold movingPatternInjectionGuard at hx
  split_ifs at hx with h
  · exact ⟨h, hx⟩
  · exact False.elim (hx rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPairSquareLoss
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-exclusion loss for both actual moving histories -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_on_fiber {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x₀ y₀ : ZMod p)
    (hbase : ∀ j : MovingPrimeOccurrences value T p,
      let φ := MovingSlotReversal.naturalReduction p value
      let L := movingPrimeOccurrenceLine value T p j
      φ L.a * x₀ + φ L.b * y₀ = 0)
    (v : SquareLiftPairs p x₀ y₀) :
    movingInternalPairFactor value T p v.1.1 v.2.1 =
      if ∀ j : MovingPrimeOccurrences value T p,
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        let L := movingPrimeOccurrenceLine value T p j
        φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 then 1 else 0 := by
  have hz (j : MovingPrimeOccurrences value T p) :
      let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
      let L := movingPrimeOccurrenceLine value T p j
      squareReduction p (φ L.a * v.1.1 + φ L.b * v.2.1) = 0 := by
    simpa only [map_add, map_mul, naturalReduction_square, v.1.property, v.2.property] using hbase j
  have hs : (∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1) ↔
      ∀ j : MovingPrimeOccurrences value T p,
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        let L := movingPrimeOccurrenceLine value T p j
        φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 := by
    refine (movingInternalLocalSupport_occurrences value T p v.1.1 v.2.1).trans ?_
    exact ⟨fun h j => (h j).2, fun h j => ⟨hz j, h j⟩⟩
  by_cases h : ∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1
  · simp only [movingInternalPairFactor, ite_eq_left h, ite_eq_left (hs.mp h)]
  · have hn := fun hn => h (hs.mpr hn)
    simp only [movingInternalPairFactor, ite_eq_right h, ite_eq_right hn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExternalSquareFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disintegration into the two giant prime-square lift fibers -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original uniform mixed law first chooses its residues modulo `p`,
then chooses uniformly among the `p²` lifts of that pair. -/
theorem externalSquare_average (p : ℕ) [Fact p.Prime]
    (F : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ → ℂ) :
    (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ * (∑ z, F z) =
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p),
            F ((externalSquareDecompose p).symm ⟨z, v⟩) := by
  let e := externalSquareDecompose p
  have hc : Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) =
      Fintype.card (ZMod p × (ZMod p)ˣ) * p ^ 2 := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [squareLiftPairs_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hs := e.symm.sum_comp F
  rw [Fintype.sum_sigma] at hs
  rw [← hs, hc, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, ← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative local square loss above the actual simultaneous line system -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_fiber {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x₀ y₀ : ZMod p) (v : SquareLiftPairs p x₀ y₀) :
    movingInternalPairFactor value T p v.1.1 v.2.1 =
      movingInternalBaseFactor value T p x₀ y₀ *
        (if ∀ j : MovingPrimeOccurrences value T p,
          let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
          let L := movingPrimeOccurrenceLine value T p j
          φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 then 1 else 0) := by
  let A := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * x₀ + φ L.b * y₀ = 0
  let B := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0
  have hs : (∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1) ↔ A ∧ B := by
    rw [movingInternalLocalSupport_occurrences]
    simp only [map_add, map_mul, naturalReduction_square, v.1.property, v.2.property]
    exact forall_and
  change (if ∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1 then 1 else 0) =
    (if A then 1 else 0) * (if B then 1 else 0)
  by_cases ha : A
  · by_cases hb : B
    · simp only [ite_eq_left (hs.mpr ⟨ha, hb⟩), ite_eq_left ha, ite_eq_left hb, mul_one]
    · simp only [ite_eq_right (fun h => hb (hs.mp h).2), ite_eq_left ha, ite_eq_right hb, mul_zero]
  · simp only [ite_eq_right (fun h => ha (hs.mp h).1), ite_eq_right ha, zero_mul]

/-- The square loss is relative to the base line event. The number of
forbidden zero lifts is bounded by the number of nodes in the two histories. -/
theorem movingInternalPairFactor_fiber_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0)
    (hbase : ∀ j : MovingPrimeOccurrences value T p,
      let φ := MovingSlotReversal.naturalReduction p value
      let L := movingPrimeOccurrenceLine value T p j
      φ L.a * x₀ + φ L.b * y₀ = 0) :
    ((p : ℝ) ^ 2)⁻¹ *
      ‖(∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
        (p : ℂ) ^ 2‖ ≤ 2 * (2 ^ n - 1 : ℕ) / (p : ℝ) := by
  let J := MovingPrimeOccurrences value T p
  let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
  let L := movingPrimeOccurrenceLine value T p
  let bad := fun v : SquareLiftPairs p x₀ y₀ => ∃ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 = 0
  have hr (j : J) : squareReduction p (φ (L j).a) ≠ 0 ∨ squareReduction p (φ (L j).b) ≠ 0 := by
    simp only [φ, naturalReduction_square]
    exact movingPrimeOccurrenceLine_nonzero tier value hprime hdisjoint T hlevels p hf j
  have hlocal := square_lift_nonzero_rows_removed_mass_le
    (fun j : J => φ (L j).a) (fun j : J => φ (L j).b) x₀ y₀ hy hr
    (by simpa only [φ, naturalReduction_square] using hbase)
    (fun _ => (1 : ℂ)) 1 (by norm_num) (by simp)
  have hid (v : SquareLiftPairs p x₀ y₀) :
      movingInternalPairFactor value T p v.1.1 v.2.1 - 1 = -(if bad v then 1 else 0) := by
    rw [movingInternalPairFactor_on_fiber value T p x₀ y₀ hbase]
    change (if ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 then 1 else 0) - 1 =
      -(if bad v then 1 else 0)
    by_cases h : bad v
    · have hn : ¬ ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 := by
        obtain ⟨j, hj⟩ := h
        exact fun hall => hall j hj
      simp only [ite_eq_right hn, ite_eq_left h, zero_sub]
    · have hg : ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 := not_exists.mp h
      simp only [ite_eq_left hg, ite_eq_right h, sub_self, neg_zero]
  have hsum : (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
      (p : ℂ) ^ 2 = -(∑ v ∈ Finset.univ.filter bad, (1 : ℂ)) := by
    calc
      _ = ∑ v : SquareLiftPairs p x₀ y₀, (movingInternalPairFactor value T p v.1.1 v.2.1 - 1) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, squareLiftPairs_card, Nat.cast_pow]
      _ = ∑ v : SquareLiftPairs p x₀ y₀, -(if bad v then 1 else 0) := Finset.sum_congr rfl (fun v _ => hid v)
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_filter]
  rw [hsum, norm_neg]
  have hbound : (Fintype.card J : ℝ) / p ≤ 2 * (2 ^ n - 1 : ℕ) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast movingPrimeOccurrences_card value T p
  have he : ((p : ℝ) ^ 2)⁻¹ * ‖∑ v ∈ Finset.univ.filter bad, (1 : ℂ)‖ ≤
      (Fintype.card J : ℝ) / p := by
    simpa only [bad, φ, L, J, one_mul, div_eq_mul_inv, mul_comm] using hlocal
  exact he.trans hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExternalSquareCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original coordinates of the exact square-fiber disintegration -/

namespace Ostmann
open scoped Classical BigOperators

theorem externalSquareFiberEquiv_symm_values (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
    (((externalSquareFiberEquiv p z).symm v).val.1,
      (((externalSquareFiberEquiv p z).symm v).val.2 : ZMod (p ^ 2))) =
      (v.1.val, v.2.val) := by
  exact congrArg (fun w : SquareLiftPairs p z.1 (z.2 : ZMod p) => (w.1.val, w.2.val))
    ((externalSquareFiberEquiv p z).apply_symm_apply v)

theorem externalSquareDecompose_symm_values (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
    (((externalSquareDecompose p).symm ⟨z, v⟩).1,
      (((externalSquareDecompose p).symm ⟨z, v⟩).2 : ZMod (p ^ 2))) =
      (v.1.val, v.2.val) :=
  externalSquareFiberEquiv_symm_values p z v

/-- The disintegration formula with the two raw residue coordinates exposed. -/
theorem externalSquare_raw_average (p : ℕ) [Fact p.Prime]
    (F : ZMod (p ^ 2) → ZMod (p ^ 2) → ℂ) :
    (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, F z.1 z.2) =
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p), F v.1.val v.2.val := by
  have h := externalSquare_average p
    (fun z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ => F z.1 z.2)
  have he (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
      F ((externalSquareDecompose p).symm ⟨z, v⟩).1
          ((externalSquareDecompose p).symm ⟨z, v⟩).2 = F v.1.val v.2.val :=
    congrArg (fun a : ZMod (p ^ 2) × ZMod (p ^ 2) => F a.1 a.2)
      (externalSquareDecompose_symm_values p z v)
  simpa only [he] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalAverageError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The relative square error in the original local Haar average -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_fiber_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime]
    (x₀ y₀ : ZMod p) (v : SquareLiftPairs p x₀ y₀) :
    ‖movingInternalPairFactor value T p v.1.val v.2.val‖ ≤
      ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  rw [movingInternalPairFactor_fiber, norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  split_ifs <;> norm_num

theorem movingInternalPairFactor_normalized_fiber_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime]
    (x₀ y₀ : ZMod p) :
    ‖((p : ℂ) ^ 2)⁻¹ *
        (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.val v.2.val)‖ ≤
      ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  have hp : (p : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((p : ℝ) ^ 2)⁻¹ * ∑ _v : SquareLiftPairs p x₀ y₀,
        ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ =>
        movingInternalPairFactor_fiber_norm_le value T p x₀ y₀ v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        squareLiftPairs_card, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem movingInternalPairFactor_normalized_fiber_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0) :
    ‖((p : ℂ) ^ 2)⁻¹ *
        (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
        movingInternalBaseFactor value T p x₀ y₀‖ ≤
      (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) * ‖movingInternalBaseFactor value T p x₀ y₀‖ := by
  let A := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * x₀ + φ L.b * y₀ = 0
  by_cases h : A
  · have hval : movingInternalBaseFactor value T p x₀ y₀ = 1 := ite_eq_left h
    have hb := movingInternalPairFactor_fiber_error tier value hprime hdisjoint T hlevels p hf x₀ y₀ hy h
    have hp : (p : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have he (z : ℂ) : ((p : ℂ) ^ 2)⁻¹ * z - 1 = ((p : ℂ) ^ 2)⁻¹ * (z - (p : ℂ) ^ 2) := by
      rw [mul_sub, inv_mul_cancel₀ hp]
    rw [hval, norm_one, mul_one, he, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    exact hb
  · have hval : movingInternalBaseFactor value T p x₀ y₀ = 0 := ite_eq_right h
    have hz (v : SquareLiftPairs p x₀ y₀) : movingInternalPairFactor value T p v.1.1 v.2.1 = 0 := by
      rw [movingInternalPairFactor_fiber, hval, zero_mul]
    simp only [hz, Finset.sum_const_zero, mul_zero, hval, sub_self, norm_zero, le_refl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalHaarError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the relative square loss under the original mixed Haar law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_haar_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2)‖ ≤
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖ := by
  rw [externalSquare_raw_average p (movingInternalPairFactor value T p), norm_mul,
    norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ =>
    movingInternalPairFactor_normalized_fiber_norm_le value T p z.1 z.2)

theorem movingInternalPairFactor_haar_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0)) :
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) -
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod p × (ZMod p)ˣ, movingInternalBaseFactor value T p z.1 z.2)‖ ≤
      (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) *
        ((Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
          ∑ z : ZMod p × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖) := by
  let c : ℂ := (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹
  let w : ℝ := (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹
  let K : ℝ := 2 * (2 ^ n - 1 : ℕ) / (p : ℝ)
  let H := fun z : ZMod p × (ZMod p)ˣ => ((p : ℂ) ^ 2)⁻¹ *
    ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p), movingInternalPairFactor value T p v.1.1 v.2.1
  let G := fun z : ZMod p × (ZMod p)ˣ => movingInternalBaseFactor value T p z.1 z.2
  have havg : (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) =
      c * ∑ z, H z := by
    exact externalSquare_raw_average p (movingInternalPairFactor value T p)
  have he (z : ZMod p × (ZMod p)ˣ) : ‖H z - G z‖ ≤ K * ‖G z‖ :=
    movingInternalPairFactor_normalized_fiber_error tier value hprime hdisjoint T hlevels p hf
      z.1 z.2 (Units.ne_zero z.2)
  have hc : ‖c‖ = w := by simp only [c, w, norm_inv, Complex.norm_natCast]
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [havg]
  change ‖c * (∑ z, H z) - c * (∑ z, G z)‖ ≤ K * (w * ∑ z, ‖G z‖)
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, hc]
  calc
    w * ‖∑ z, (H z - G z)‖ ≤ w * ∑ z, ‖H z - G z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ ≤ w * ∑ z, K * ‖G z‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => he z) hw
    _ = _ := by rw [← Finset.mul_sum]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalProbabilityError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square error retains the one-over-prime line factor -/

namespace Ostmann
open scoped Classical BigOperators

/-- The base coefficient is a nonnegative indicator, so its absolute average
is exactly its simultaneous line probability. -/
theorem movingInternalBaseFactor_norm_average {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
      (∑ z : ZMod p × (ZMod p)ˣ, ‖movingInternalBaseFactor value T p z.1 z.2‖) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b) := by
  have he (z : ZMod p × (ZMod p)ˣ) :
      (movingInternalBaseFactor value T p z.1 z.2).re =
        ‖movingInternalBaseFactor value T p z.1 z.2‖ := by
    unfold movingInternalBaseFactor
    split_ifs <;> simp
  have h := congrArg Complex.re (movingInternalBaseFactor_average value T p)
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, he] using h

theorem movingInternalPairFactor_probability_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0)) :
    let prob := internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value T p j).b)
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2) -
        (prob : ℂ)‖ ≤ (2 * (2 ^ n - 1 : ℕ) / (p : ℝ)) * prob := by
  have h := movingInternalPairFactor_haar_error tier value hprime hdisjoint T hlevels p hf
  rw [movingInternalBaseFactor_average, movingInternalBaseFactor_norm_average] at h
  exact h

theorem movingInternalPairFactor_probability_norm_le {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    ‖(Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, movingInternalPairFactor value T p z.1 z.2)‖ ≤
      internalLineProbability true
        (fun j => MovingSlotReversal.naturalReduction p value
          (movingPrimeOccurrenceLine value T p j).a)
        (fun j => MovingSlotReversal.naturalReduction p value
          (movingPrimeOccurrenceLine value T p j).b) := by
  have h := movingInternalPairFactor_haar_norm_le value T p
  rwa [movingInternalBaseFactor_norm_average] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteRelativeProductError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative errors in the finite product of internal-prime averages -/

namespace Ostmann
open scoped BigOperators

/-- A common local majorant retains the full product scale in the error. -/
theorem finite_relative_product_error {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ) (B K : ι → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ B i) (hg : ∀ i ∈ S, ‖g i‖ ≤ B i)
    (hdiff : ∀ i ∈ S, ‖f i - g i‖ ≤ K i * B i) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤
      (∑ i ∈ S, K i) * ∏ i ∈ S, B i := by
  classical
  revert hB hK hf hg hdiff
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    intro hB hK hf hg hdiff
    have hs (j : ι) (hj : j ∈ S) : j ∈ insert i S := Finset.mem_insert_of_mem hj
    have herr := ih (fun j hj => hB j (hs j hj)) (fun j hj => hK j (hs j hj))
      (fun j hj => hf j (hs j hj)) (fun j hj => hg j (hs j hj))
      (fun j hj => hdiff j (hs j hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ ∏ j ∈ S, B j := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j hj => hg j (hs j hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi,
      Finset.prod_insert hi]
    rw [show f i * (∏ j ∈ S, f j) - g i * (∏ j ∈ S, g j) =
      f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
        (f i - g i) * ∏ j ∈ S, g j by ring]
    calc
      _ ≤ ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)‖ +
          ‖(f i - g i) * ∏ j ∈ S, g j‖ := norm_add_le _ _
      _ ≤ B i * ((∑ j ∈ S, K j) * ∏ j ∈ S, B j) +
          (K i * B i) * ∏ j ∈ S, B j := by
        rw [norm_mul, norm_mul]
        apply add_le_add
        · exact mul_le_mul (hf i (Finset.mem_insert_self _ _)) herr
            (norm_nonneg _) (hB i (Finset.mem_insert_self _ _))
        · exact mul_le_mul (hdiff i (Finset.mem_insert_self _ _)) hprod
            (norm_nonneg _) (mul_nonneg (hK i (Finset.mem_insert_self _ _))
              (hB i (Finset.mem_insert_self _ _)))
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalProductError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous square removal with the full internal-prime scale -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalLineProbability_nonneg {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    0 ≤ movingInternalLineProbability value T p := internalLineProbability_nonneg _ _ _

theorem movingInternalLineProbability_le_inv {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (base : MovingPrimeOccurrences value T p) :
    movingInternalLineProbability value T p ≤ (p : ℝ)⁻¹ := by
  unfold movingInternalLineProbability
  rw [movingInternalBaseProbability_eq_flags tier value hprime hdisjoint T hlevels p hf base]
  unfold internalLineFlagWeight internalLineScalar
  simp only [ite_true, if_true]
  split_ifs
  · rfl
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSquareError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square exclusions under the original pattern priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The relative square error for the actual class-indexed collection of
internal primes. Every class has a proved occurrence in the history pair. -/
theorem movingRepresentativeProduct_error {σ C : Type*} [Fintype C]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ b, (T b).Levels tier)
    (rep : C → σ) (base : ∀ c, MovingPairRepresentativeOccurrences T (rep c))
    (hf : ∀ c b, (T b).Frequencies (fun s => (s : ZMod (value (rep c))) ≠ 0))
    (V : ℝ) (hsize : ∀ c, Real.exp V ≤ value (rep c)) :
    letI : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
    ‖(∏ c, movingInternalHaarAverage value T (value (rep c))) -
      ∏ c, (movingInternalLineProbability value T (value (rep c)) : ℂ)‖ ≤
        ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) *
          ∏ c, (value (rep c) : ℝ)⁻¹ := by
  let _ : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
  have hprob (c) : 0 ≤ movingInternalLineProbability value T (value (rep c)) :=
    movingInternalLineProbability_nonneg value T _
  have hline (c) : movingInternalLineProbability value T (value (rep c)) ≤
      (value (rep c) : ℝ)⁻¹ := by
    let j : MovingPrimeOccurrences value T (value (rep c)) :=
      ⟨(base c).1, ⟨(base c).2.val, ⟨rep c, (base c).2.property, rfl⟩⟩⟩
    exact movingInternalLineProbability_le_inv tier value hprime hdisjoint T hlevels _ (hf c) j
  have hs : (∑ c, (value (rep c) : ℝ)⁻¹) ≤ (Fintype.card C : ℝ) * Real.exp (-V) := by
    calc
      _ ≤ ∑ _c : C, Real.exp (-V) := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos V) (hsize c)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := finite_relative_product_error (Finset.univ : Finset C)
    (fun c => movingInternalHaarAverage value T (value (rep c)))
    (fun c => (movingInternalLineProbability value T (value (rep c)) : ℂ))
    (fun c => movingInternalLineProbability value T (value (rep c)))
    (fun c => 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ))
    (fun c _ => hprob c) (fun c _ => by positivity)
    (fun c _ => movingInternalPairFactor_probability_norm_le value T _)
    (fun c _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hprob c)])
    (fun c _ => movingInternalPairFactor_probability_error tier value hprime hdisjoint T hlevels _ (hf c))
  have hp : (∏ c, movingInternalLineProbability value T (value (rep c))) ≤
      ∏ c, (value (rep c) : ℝ)⁻¹ :=
    Finset.prod_le_prod (fun c _ => hprob c) (fun c _ => hline c)
  have hk : (∑ c, 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ)) ≤
      (2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V) := by
    simp only [div_eq_mul_inv, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  exact h.trans (mul_le_mul hk hp (Finset.prod_nonneg (fun c _ => hprob c)) (by positivity))

/-- Integrating a relative local error uses the original normalized prior,
not a conditioned law. The retained scale may include every internal class. -/
theorem productPrior_relative_error {A : Type*} [Fintype A] {N : ℕ}
    (μ : Fin N → A → ℝ) (hmass : ∀ i, ∑ a, μ i a = 1)
    (weight err : (Fin N → A) → ℂ) (scale : (Fin N → A) → ℝ)
    (B K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ x, ‖weight x‖ * scale x ≤ B * productPrior μ x)
    (herr : ∀ x, weight x ≠ 0 → ‖err x‖ ≤ K * scale x) :
    ‖∑ x, weight x * err x‖ ≤ B * K := by
  calc
    _ ≤ ∑ x, ‖weight x * err x‖ := norm_sum_le _ _
    _ ≤ ∑ x, K * (B * productPrior μ x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hz : weight x = 0
      · have hb := hweight x
        rw [hz, norm_zero, zero_mul] at hb
        simpa only [hz, zero_mul, norm_zero] using mul_nonneg hK hb
      · rw [norm_mul]
        calc
          _ ≤ ‖weight x‖ * (K * scale x) :=
            mul_le_mul_of_nonneg_left (herr x hz) (norm_nonneg _)
          _ = K * (‖weight x‖ * scale x) := by ring
          _ ≤ K * (B * productPrior μ x) := mul_le_mul_of_nonneg_left (hweight x) hK
    _ = B * K := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, productPrior_mass μ hmass]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternAveragedSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square-exclusion error averaged under original pattern weights -/

namespace Ostmann
open scoped Classical BigOperators

/-- All square exclusions can be removed under the literal dependent pattern
law. The loss keeps the inverse-prime scale from every internal class. -/
theorem movingPattern_averaged_square_error {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E V : ℝ) (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let W := fun x : Fin (N + 1) → A =>
      ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
    ‖∑ x, W x * movingPatternSquareDifference e prime hprime n t small bulk pattern x‖ ≤
      (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) := by
  dsimp only
  let T := movingPatternFinData e n t small bulk pattern
  let prior := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let W := fun x : Fin (N + 1) → A =>
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
  have hm (i) : ∑ a, prior i a = 1 := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hdom (x) : ‖W x‖ *
      (∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) ≤
      (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior prior x :=
    movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound G D hD hG x
  apply productPrior_relative_error prior hm W
    (movingPatternSquareDifference e prime hprime n t small bulk pattern)
    (fun x => ∏ c, internalLineScalar true (prime (x (e.symm (.inr c)))))
    (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)))
    ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) (by positivity)
    hdom
  intro x hx
  have hg : G x ≠ 0 := by
    intro hz
    exact hx (by simp only [W, hz, mul_zero])
  have hscalar : 0 < ∏ c, internalLineScalar true (prime (x (e.symm (.inr c)))) := by
    apply Finset.prod_pos
    intro c _
    simp only [internalLineScalar, ite_true, if_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr (hprime _).pos)
  have hprior : productPrior prior x ≠ 0 := by
    intro hz
    have hh := hdom x
    rw [hz, mul_zero] at hh
    exact (not_le_of_gt (mul_pos (norm_pos_iff.mpr hx) hscalar)) hh
  have hsample (c) : μ (movingSampleTier (rep c).val.2) (x (e.symm (.inr c))) ≠ 0 := by
    have hh := (Finset.prod_ne_zero_iff.mp hprior) (e.symm (.inr c)) (Finset.mem_univ _)
    simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using hh
  have h := movingRepresentativeProduct_error ((Sum.elim tierB tierC) ∘ e)
    (fun i => prime (x i)) (fun i => hprime _) (hdisjoint x hg) T
    (movingPatternFinData_levels e tierB tierC n t small bulk pattern hsmall hbulk htier)
    (fun c => e.symm (.inr c)) (movingPatternFinRepresentative e n t small bulk pattern rep)
    (hfmod x hg) V (fun c => hprimeSize c _ (hsample c))
  simpa only [movingPatternSquareDifference, movingInternalLineProbability,
    movingSampledInternalProbability, internalLineScalar, ite_true, if_true] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDominatedLineComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symbolic line comparison under the dominated equality-pattern law -/

namespace Ostmann
open scoped Classical BigOperators

/-- The complete original pattern weight may be used directly once its product
of line scalars is dominated by the representative priors. In particular, the
pattern law is not assumed to be independent. -/
theorem moving_dominated_line_product_comparison {A J : Type*}
    [Fintype A] [Nonempty A] [Fintype J] {N n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin (N + 1)) n) (tier : Fin (N + 1) → ℕ)
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : J → Fin (N + 1)) (base : ∀ j, MovingPairRepresentativeOccurrences T (rep j))
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ side, (T side).SizeLE d)
    (hfreq : ∀ side, (T side).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : Fin (N + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (rep j) a ≤ β)
    (hprimeSize : ∀ j a, μ (rep j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (weight : (Fin (N + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ x, ‖weight x‖ * ∏ j, internalLineScalar true (prime (x (rep j))) ≤ B * productPrior μ x)
    (hdisjoint : ∀ x, weight x ≠ 0 → ∀ i j,
      tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hunique : ∀ x, weight x ≠ 0 → ∀ j i, prime (x i) = prime (x (rep j)) → i = rep j)
    (hfmod : ∀ x, weight x ≠ 0 → ∀ j side,
      (T side).Frequencies (fun s => (s : ZMod (prime (x (rep j)))) ≠ 0)) :
    ‖∑ x, weight x *
      ((∏ j, (movingSampledInternalProbability prime hprime T x (rep j) : ℂ)) -
       ∏ j, (internalLineFlagWeight true (prime (x (rep j)))
         (fun s => arithmeticTestFlag (lineTestPolynomials
           (movingIndexedLine T (rep j) (base j)) ⟨(base j).1, (base j).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card (MovingPairOccurrenceIndex T))) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  let prior := fun x : Fin (N + 1) → A => productPrior μ x
  let c := fun x : Fin (N + 1) → A =>
    ∏ j, internalLineScalar true (prime (x (rep j)))
  have hc (x : Fin (N + 1) → A) : 0 < c x := by
    apply Finset.prod_pos
    intro j _
    simp only [internalLineScalar, ite_true, if_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr (hprime (x (rep j))).pos)
  have hprior (x : Fin (N + 1) → A) : 0 ≤ prior x := productPrior_nonneg μ hμ x
  have hd (x : Fin (N + 1) → A) : finitePriorDensity prior weight x ≠ 0 → weight x ≠ 0 :=
    finitePriorDensity_ne_zero prior weight x
  have h := moving_actual_line_product_comparison prime hpInj hprime T tier hlevels rep base
    d F U hF hU hsize hfreq hvalues μ hμ hmass α β V hα hβ hV hmax hpmax hprimeSize
    (finitePriorDensity prior weight) B hB
    (finitePriorDensity_bound prior weight c B hprior hB hweight)
    (fun x hx => hdisjoint x (hd x hx)) (fun x hx => hunique x (hd x hx))
    (fun x hx => hfmod x (hd x hx))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [finitePriorDensity_cancel prior weight c B hc hweight x]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLineComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original internal-pattern law in the simultaneous line comparison -/

namespace Ostmann
open scoped Classical BigOperators

/-- Apply the proved comparison to the actual pattern tree and its original
external priors. All occurrence rows and unique representatives are derived
from that constructor. The loss involves internal classes, not bulk size. -/
theorem movingPattern_line_comparison {A B C : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ b, (movingPatternFinData e n t small bulk pattern b).SizeLE d)
    (hfreq : ∀ b, (movingPatternFinData e n t small bulk pattern b).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E α β V : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hmax : ∀ j a, μ j a ≤ α) (hnmax : ∀ j a, ν j a ≤ α)
    (hpmax : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≤ β)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      V ≤ Real.log (prime a : ℝ))
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hclasses : ∀ x, G x ≠ 0 → Function.Injective (fun c => x (e.symm (.inr c))))
    (hcross : ∀ x, G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let T := movingPatternFinData e n t small bulk pattern
    let base := movingPatternFinRepresentative e n t small bulk pattern rep
    let W := fun x : Fin (N + 1) → A =>
      ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
        (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
          (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
    ‖∑ x, W x *
      ((∏ c, (movingSampledInternalProbability prime hprime T x (e.symm (.inr c)) : ℂ)) -
        ∏ c, (internalLineFlagWeight true (prime (x (e.symm (.inr c))))
          (fun s => arithmeticTestFlag (lineTestPolynomials
            (movingIndexedLine T (e.symm (.inr c)) (base c))
            ⟨(base c).1, (base c).2.val⟩ s = 0)) : ℂ))‖ ≤
      2 * (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
        ((2 * ((n + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β) := by
  dsimp only
  let T := movingPatternFinData e n t small bulk pattern
  let prior := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let W := fun x : Fin (N + 1) → A =>
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * G x
  have hnz (x) (hx : W x ≠ 0) : G x ≠ 0 := by
    intro hz
    exact hx (by simp only [W, hz, mul_zero])
  have hprior (i a) : 0 ≤ prior i a := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hν b a
    | inr c => exact hμ _ a
  have hmass' (i) : ∑ a, prior i a = 1 := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hmax' (i a) : prior i a ≤ α := by
    dsimp only [prior]
    cases e i with
    | inl b => exact hnmax b a
    | inr c => exact hmax _ a
  have hpmax' (c a) : prior (e.symm (.inr c)) a ≤ β := by
    simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using hpmax c a
  have h := moving_dominated_line_product_comparison prime hpInj hprime T
    ((Sum.elim tierB tierC) ∘ e)
    (movingPatternFinData_levels e tierB tierC n t small bulk pattern hsmall hbulk htier)
    (fun c => e.symm (.inr c)) (movingPatternFinRepresentative e n t small bulk pattern rep)
    d F U hF hU hsize hfreq hvalues prior hprior hmass' α β V hα hβ hV hmax' hpmax'
    (fun c a ha => hprimeSize c a (by
      simpa only [prior, Equiv.apply_symm_apply, Sum.elim_inr] using ha)) W (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)))
    (by positivity)
    (fun x => movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound G D hD hG x)
    (fun x hx => hdisjoint x (hnz x hx))
    (fun x hx c i hi => movingPatternFin_unique e prime hpInj x
      (hclasses x (hnz x hx)) (hcross x (hnz x hx)) c i hi)
    (fun x hx c b => hfmod x (hnz x hx) c b)
  simpa only [movingPairOccurrenceIndex_card, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternArithmeticComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original internal arithmetic coefficient versus symbolic flags -/

namespace Ostmann
open scoped Classical BigOperators

/-- Remove the actual prime-square exclusions and replace the remaining
simultaneous line probabilities by their symbolic flags under the original
pattern law. No injectivity assumption is imposed on the sampling measure. -/
theorem movingPattern_arithmetic_comparison {A B C : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ b, (movingPatternFinData e n t small bulk pattern b).SizeLE d)
    (hfreq : ∀ b, (movingPatternFinData e n t small bulk pattern b).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E α β V : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hmax : ∀ j a, μ j a ≤ α) (hnmax : ∀ j a, ν j a ≤ α)
    (hpmax : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≤ β)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hcross : ∀ x, G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let κ := D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x)‖ ≤
      κ * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) := by
  let H := movingPatternInjectionGuard e G
  have hH : ∀ x, ‖H x‖ ≤ D := movingPatternInjectionGuard_norm e G D hD hG
  have hsupp (x) (hx : H x ≠ 0) : G x ≠ 0 :=
    (movingPatternInjectionGuard_nonzero e G x hx).2
  have hsq := movingPattern_averaged_square_error e prime hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier μ ν hμ hν hmass hnmass E V hbound hprimeSize H D hD hH
    (fun x hx => hdisjoint x (hsupp x hx)) (fun x hx => hfmod x (hsupp x hx))
  have hline := movingPattern_line_comparison e prime hpInj hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass E α β V
    hE hα hβ hV hbound hmax hnmax hpmax
    (fun c a ha => (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (hprime a).pos)).mpr
      (hprimeSize c a ha))
    H D hD hH (fun x hx => hdisjoint x (hsupp x hx))
    (fun x hx => (movingPatternInjectionGuard_nonzero e G x hx).1)
    (fun x hx => hcross x (hsupp x hx)) (fun x hx => hfmod x (hsupp x hx))
  dsimp only at hsq hline ⊢
  have heq : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x)) =
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternSquareDifference e prime hprime n t small bulk pattern x) +
    ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternLineProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    unfold movingPatternHaarProduct movingPatternSquareDifference movingPatternLineProduct
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ _ + _ := add_le_add hsq hline
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternCoefficientMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern coefficients as a finite signed linear functional -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingOriginalPatternWeight_eq_coefficient_mul {A B C : Type*} [Fintype B] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern G x =
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x * G x := by
  unfold movingOriginalPatternWeight movingPatternInjectionGuard
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalIntegralScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the harmless constant normalization of the diagonal multiplier -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingDiagonalOuterWeight_denormalize {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    (diagonalOuterMajorant B D diagonal : ℂ) *
      movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x =
      giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v) *
        (inactiveRegularDensity prime reg active x : ℂ) := by
  unfold movingDiagonalOuterWeight
  have hc : (diagonalOuterMajorant B D diagonal : ℂ) ≠ 0 := by
    exact_mod_cast (diagonalOuterMajorant_pos B D diagonal).ne'
  exact mul_div_cancel₀ _ hc

/-- The normalized multiplier costs only its fixed outer majorant after both
integrals and the original signed pattern average. -/
theorem movingPattern_diagonal_integral_norm {A B C J : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype J] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright Bφ Dφ : ℝ) (diagonal : Bool)
    (raw : ℝ → ℝ → (Fin (N + 1) → A) → ℂ)
    (haar : (Fin (N + 1) → A) → ℂ) (u v a b center bound : ℝ)
    (hbound : ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤ bound) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * bound := by
  let K := diagonalOuterMajorant Bφ Dφ diagonal
  have hK : 0 ≤ K := (diagonalOuterMajorant_pos Bφ Dφ diagonal).le
  have he (x) :
      (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) =
      (K : ℂ) * (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [← movingDiagonalOuterWeight_denormalize prime reg active φ Jleft Jright Bφ Dφ diagonal z y x]
    change (((K : ℂ) * _) * _) * _ / _ = _
    ring
  let original := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
      (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
        (Real.exp (z - center) : ℂ) / (y : ℂ)
  let normalized := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
      raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x‖ ≤ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x‖ ≤ bound at hbound
  have hsum : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x) =
      (K : ℂ) * ∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    conv_lhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    conv_rhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    change _ * (original x) * _ = _ * (_ * normalized x * _)
    have hi : original x = (K : ℂ) * normalized x := he x
    rw [hi]
    ring
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hbound hK

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measure transport for the concrete bounded moving kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical SchwartzMap

theorem measurable_exp_pair_mul (K : ℝ → ℝ → ℂ)
    (hK : Measurable (Function.uncurry K)) (c : ℂ) :
    Measurable (Function.uncurry (fun x y => c * K (Real.exp x) (Real.exp y))) := by
  have he : Measurable (fun z : ℝ × ℝ => (Real.exp z.1, Real.exp z.2)) :=
    (Real.continuous_exp.comp continuous_fst).measurable.prodMk
      (Real.continuous_exp.comp continuous_snd).measurable
  exact measurable_const.mul (hK.comp he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realSlotProduct_nat {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    realSlotProduct (fun j => (value j : ℝ)) slots =
      (MovingSlotReversal.naturalProduct value slots : ℝ) := by
  induction slots with
  | nil => simp [realSlotProduct, MovingSlotReversal.naturalProduct]
  | cons j slots ih => simpa only [realSlotProduct, MovingSlotReversal.naturalProduct,
      List.map_cons, List.prod_cons, Nat.cast_mul] using congrArg ((value j : ℝ) * ·) ih

theorem MovingSlotReversal.realValuePivot_nat {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (L R : ℝ) :
    s.realValuePivot (fun j => (value j : ℝ)) L R = s.realPivot value L R := by
  simp only [realValuePivot, realPivot, realSlotProduct_nat]

theorem MovingSlotData.realValueLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) (j : TreeLeafIndex n) :
    T.realValueLeafModuli (fun i => (value i : ℝ)) L R j = T.realLeafModuli value L R j := by
  induction T generalizing L R with
  | leaf => simp only [realValueLeafModuli, realLeafModuli, realSlotProduct_nat]
  | node s CL CR u left right ihL ihR =>
    cases j with
    | inl j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihL]
    | inr j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihR]

theorem realValueNodeCutoff_nat {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    realValueNodeCutoff (fun i => (value i : ℝ)) φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, movingRealNodeCutoff, MovingSlotReversal.realValuePivot_nat, ihL, ihR]

/-- The extension agrees exactly with the original function at every natural
prime tuple, including points where a cutoff vanishes. -/
theorem realValueSmoothWeight_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (fun i => (value i : ℝ)) T ψ X lo hi hlo hhi φ G L R =
      movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R := by
  simp only [realValueSmoothWeight, movingRealSmoothWeight, realValueFourierWeight,
    movingRealFourierWeight, realValueNodeCutoff_nat, MovingSlotData.realValueLeafModuli_nat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

theorem movingLeafLengthLE_map {A B : Type*} (f : A → B) (n : ℕ)
    (x : TreeLeafTuple (List A) n) (r : ℕ) (hx : MovingLeafLengthLE n x r) :
    MovingLeafLengthLE n (treeLeafMap (List.map f) n x) r := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length {A : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingLeafLengthLE n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => simp [bulkSlotLeaves, MovingLeafLengthLE, treeLeafTupleEquiv]
  | succ n ih =>
    change MovingLeafLengthLE n
      (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthLE n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingPatternFinBulkData_size {B C : Type*} {N n m r : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).SizeLE
      (2 ^ n * (r + m + 4 * n + 4)) := by
  rw [movingPatternFinBulkData_build]
  apply buildMovingSlotData_size n (t b) _ _ _ r m
    (movingLeafLengthLE_map _ n (small b) r (hsmall b))
  cases b <;> exact bulkSlotLeaves_length n m _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverageNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete norm budgets for the retained arithmetic averages -/

namespace Ostmann
open scoped Classical BigOperators

private theorem finiteMean_norm_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ B := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem pageGiantWeight_norm_le_two (input : PublishedProgressionInput) (Q q a : ℕ)
    (y : ℝ) (hy : 0 ≤ y) : ‖pageGiantWeight input Q q a y‖ ≤ 2 := by
  have h := pageMultiplier_bounds
    (fun a => pageCoefficient (pageAtModulus q (selectedPageZero input Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero input Q))) y
    (pageCoefficient_abs_le_one _) (pageBeta_le_one _) hy a
  rw [pageGiantWeight, Complex.norm_real, Real.norm_of_nonneg h.1]
  exact h.2

theorem movingFrequencyPageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyPageAverage value outside F E T nodes R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  apply finiteMean_norm_le
  intro z
  have hf : ‖movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val‖ ≤
      ‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖ := by
    unfold movingFrequencyPairFactor
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, le_refl]
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0) ▸ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) * 2 :=
      mul_le_mul hf (pageGiantWeight_norm_le_two input Q r z.2.val.val y hy)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_comm _ _

theorem movingSpectatorHaarAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ z, ‖g z‖ ≤ B) :
    ‖movingSpectatorHaarAverage value q g D T‖ ≤ B ^ (2 ^ (n + 1)) := by
  apply finiteMean_norm_le
  intro z
  rw [movingSpectatorPairFactor, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
      mul_le_mul (movingModularSpectator_norm value q g (D false) B hB hg (T false) z.1 z.2)
        (movingModularSpectator_norm value q g (D true) B hB hg (T true) z.1 z.2)
        (norm_nonneg _) (pow_nonneg hB _)
    _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem centeredDensity_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, centeredDensity S x ^ 2) = (p : ℝ) * residueVariance S := by
  let σ := residueDensity S
  have hsq (x : ZMod p) : centeredDensity S x ^ 2 =
      (if x ∈ S then 1 - 2 * σ else 0) + σ ^ 2 := by
    dsimp [centeredDensity, σ, residueDensity]
    split <;> ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x : ZMod p, if x ∈ S then (1 - 2 * σ) else 0) = S.card * (1 - 2 * σ) := by simp; ring
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hσ : (p : ℝ) * σ = S.card := by dsimp [σ, residueDensity]; field_simp
  change _ = (p : ℝ) * (σ * (1 - σ))
  rw [← hσ]
  ring

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFrozenMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symbolic internal factors are constant under selected bulk resampling -/

namespace Ostmann
open scoped Classical BigOperators

/-- The only value-dependent part of the symbolic factor is one reciprocal
prime per class. All feasibility decisions are formal polynomial identities. -/
theorem movingPatternFlagProduct_eq {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (x : Fin (N + 1) → A) :
    movingPatternFlagProduct e prime n t small bulk pattern rep x =
      if movingPatternFeasible e n t small bulk pattern rep then
        ∏ c : C, ((prime (x (e.symm (.inr c))) : ℝ)⁻¹ : ℂ) else 0 := by
  by_cases h : movingPatternFeasible e n t small bulk pattern rep
  · rw [ite_eq_left h]
    unfold movingPatternFlagProduct
    apply Finset.prod_congr rfl
    intro c _
    simp only [internalLineFlagWeight, h c, ite_true, if_true, internalLineScalar, Complex.ofReal_inv]
  · rw [ite_eq_right h]
    obtain ⟨c, hc⟩ := not_forall.mp h
    unfold movingPatternFlagProduct
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [internalLineFlagWeight, hc, ite_false, if_false, Complex.ofReal_zero]

theorem movingPatternFlagProduct_congr {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : Fin (N + 1) → A) (h : ∀ c, x (e.symm (.inr c)) = y (e.symm (.inr c))) :
    movingPatternFlagProduct e prime n t small bulk pattern rep x =
      movingPatternFlagProduct e prime n t small bulk pattern rep y := by
  rw [movingPatternFlagProduct_eq, movingPatternFlagProduct_eq]
  simp only [h]

/-- In the exact Fubini decomposition of the original law, these factors
belong wholly to the fixed nonbulk coefficient. -/
theorem movingPatternFlagProduct_bulk_frozen {A B C : Type*} [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a) =
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a) := by
  apply movingPatternFlagProduct_congr
  intro c
  exact (joinBulkNonbulk_nonbulk _ x a
    ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩).trans
      (joinBulkNonbulk_nonbulk _ y a
        ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩).symm

theorem movingPairCompensatedMass_bulk_frozen {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a (e.symm (.inr (pattern i))))) =
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a (e.symm (.inr (pattern i))))) := by
  congr 2
  funext i
  exact (joinBulkNonbulk_nonbulk _ x a
    ⟨e.symm (.inr (pattern i)), movingPatternBulkEmbedding_internal_absent e slot (pattern i)⟩).trans
      (joinBulkNonbulk_nonbulk _ y a
        ⟨e.symm (.inr (pattern i)), movingPatternBulkEmbedding_internal_absent e slot (pattern i)⟩).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed bulk sum under the actual compensated pattern law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternExternalLaw_product {A B C : Type*} [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ) (x : Fin (N + 1) → A) :
    (∏ i, movingPatternExternalLaw e ν i (x i)) =
      ∏ b, ν b (x (e.symm (.inl b))) := by
  have h := e.prod_comp (fun j => Sum.elim ν (fun _ _ => 1) j (x (e.symm j)))
  simpa only [Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl,
    Sum.elim_inr, Finset.prod_const_one, mul_one, movingPatternExternalLaw] using h

theorem movingPatternBulkMultiplier_frozen {A B C : Type*} [Fintype A] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x y : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternBulkMultiplier e μ prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) x a) =
      movingPatternBulkMultiplier e μ prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) y a) := by
  unfold movingPatternBulkMultiplier
  rw [movingPairCompensatedMass_bulk_frozen e μ prime slot pattern x y a,
    movingPatternFlagProduct_bulk_frozen e prime t small slot perm pattern rep x y a]

theorem movingPattern_original_bulk_fubini {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (G : (Fin (N + 1) → A) → ℂ) (seed : TreeLeafIndex n × Fin m → A) :
    let bulk := movingPatternBulkLeaves n m slot perm
    let lift := movingPatternBulkEmbedding e slot
    let law := movingPatternExternalLaw e ν
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small bulk pattern rep x) =
      ∑ a : {i : Fin (N + 1) // i ∉ Set.range lift} → A,
        ((∏ i : {i : Fin (N + 1) // i ∉ Set.range lift}, law i (a i) : ℝ) : ℂ) *
          (movingPatternBulkMultiplier e μ prime n t small bulk pattern rep (joinBulkNonbulk lift seed a) *
            ∑ x : TreeLeafIndex n × Fin m → A,
              ((∏ j, ν (slot j) (x j) : ℝ) : ℂ) *
                movingPatternInjectionGuard e G (joinBulkNonbulk lift x a)) := by
  dsimp only
  let lift := movingPatternBulkEmbedding e slot
  let law := movingPatternExternalLaw e ν
  let bulk := movingPatternBulkLeaves n m slot perm
  let M := movingPatternBulkMultiplier e μ prime n t small bulk pattern rep
  have heq : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small bulk pattern rep x) =
      ∑ x, ((∏ i, law i (x i) : ℝ) : ℂ) * (M x * movingPatternInjectionGuard e G x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show (∏ i, law i (x i)) = ∏ b, ν b (x (e.symm (.inl b))) from
      movingPatternExternalLaw_product e ν x]
    unfold movingOriginalPatternWeight M movingPatternBulkMultiplier
    ring
  rw [heq]
  have hsplit := finite_prior_selected_fubini lift law
    (fun x => M x * movingPatternInjectionGuard e G x)
  simp only [finite_univ_canonical] at hsplit ⊢
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hm := movingPatternBulkMultiplier_frozen e μ prime t small slot perm pattern rep x seed a
  change M (joinBulkNonbulk lift x a) = M (joinBulkNonbulk lift seed a) at hm
  rw [hm]
  have hlaw (j : TreeLeafIndex n × Fin m) : law (lift j) (x j) = ν (slot j) (x j) := by
    change Sum.elim ν (fun _ _ => 1) (e (e.symm (.inl (slot j)))) (x j) = _
    rw [Equiv.apply_symm_apply]
    rfl
  simp only [hlaw]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFlagBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining symbolic factor retains the representative-prior bound -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_flagged_weight_bound {A B C : Type*} [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern G x *
        movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      (D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν
          (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  have h := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (movingPatternInjectionGuard e G) D hD (movingPatternInjectionGuard_norm e G D hD hG) x
  change ‖movingOriginalPatternWeight e μ ν prime n pattern G x‖ *
    (∏ c, internalLineScalar true (prime (x (e.symm (.inr c))))) ≤ _ at h
  apply le_trans _ h
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold movingPatternFlagProduct
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro c _
    exact norm_nonneg _
  · intro c _
    rw [Complex.norm_real, Real.norm_of_nonneg (internalLineFlagWeight_nonneg _ _ _)]
    exact internalLineFlagWeight_le_scalar _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting signed cancellation in the original bulk mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternBulkMean_join {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (G : (Fin (N + 1) → A) → ℂ)
    (z : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternBulkMean e ν slot G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) =
      ∑ w : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (w j) : ℝ) : ℂ) *
        G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) w a) := by
  have h : (fun i : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} =>
      joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a i) = a := by
    funext i
    exact joinBulkNonbulk_nonbulk _ z a i
  unfold movingPatternBulkMean
  rw [h]

theorem movingPatternInjectionGuard_join {A B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (G : (Fin (N + 1) → A) → ℂ) (z : TreeLeafIndex n × Fin m → A)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    movingPatternInjectionGuard e G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) =
      if Function.Injective (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩)
      then G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) else 0 := by
  have h : (fun c => joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a (e.symm (.inr c))) =
      (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩) := by
    funext c
    exact joinBulkNonbulk_nonbulk _ z a
      ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩
  unfold movingPatternInjectionGuard
  rw [h]

private theorem movingPatternBulkMean_guard_average {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (hmass : ∀ j, ∑ a, ν j a = 1) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (G : (Fin (N + 1) → A) → ℂ)
    (a : {i : Fin (N + 1) // i ∉ Set.range (movingPatternBulkEmbedding e slot)} → A) :
    (∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
      movingPatternInjectionGuard e (movingPatternBulkMean e ν slot G)
        (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a)) =
    ∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ) *
      movingPatternInjectionGuard e G (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z a) := by
  have hmR : (∑ z : TreeLeafIndex n × Fin m → A, ∏ j, ν (slot j) (z j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  have hm : (∑ z : TreeLeafIndex n × Fin m → A, ((∏ j, ν (slot j) (z j) : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hmR
  simp_rw [movingPatternInjectionGuard_join, movingPatternBulkMean_join]
  by_cases h : Function.Injective
      (fun c => a ⟨e.symm (.inr c), movingPatternBulkEmbedding_internal_absent e slot c⟩)
  · simp only [h, ite_true, if_true]
    rw [← Finset.sum_mul, hm, one_mul]
  · simp only [h, ite_false, if_false, mul_zero, Finset.sum_const_zero]

/-- Averaging only selected bulk coordinates preserves the original signed
pattern expression, including the class-injectivity guard. -/
theorem movingPattern_original_bulk_mean_eq {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (hmass : ∀ j, ∑ a, ν j a = 1)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (G : (Fin (N + 1) → A) → ℂ) (seed : TreeLeafIndex n × Fin m → A) :
    (∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x) =
    ∑ x, movingOriginalPatternWeight e μ ν prime n pattern (movingPatternBulkMean e ν slot G) x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x := by
  rw [movingPattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep G seed,
    movingPattern_original_bulk_fubini e μ ν prime t small slot perm pattern rep
      (movingPatternBulkMean e ν slot G) seed]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingPatternBulkMean_guard_average e ν hmass slot G a]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkMajorant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating nonuniform errors under the original pattern law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_flagged_pointwise_bound {A B C : Type*}
    [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      (‖G x‖ * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))) *
        productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  have h := movingPattern_flagged_weight_bound e μ ν prime n t small bulk pattern rep E hprime hμ hν hbound
    (fun _ => G x) ‖G x‖ (norm_nonneg _) (fun _ => le_rfl) x
  by_cases hi : Function.Injective (fun c => x (e.symm (.inr c))) <;>
    simpa only [movingOriginalPatternWeight, movingPatternInjectionGuard, hi, ite_true, if_true, ite_false, if_false] using h

/-- A variable bound for the literal signed bulk mean is integrated against
the original external and representative priors. In particular the large
pointwise spectator error is averaged, rather than replaced by its supremum. -/
theorem movingPattern_signed_bulk_majorant {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ) (hE : 0 ≤ E)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : (Fin (N + 1) → A) → ℝ)
    (hG : ∀ x, ‖movingPatternBulkMean e ν slot G x‖ ≤ D x)
    (seed : TreeLeafIndex n × Fin m → A) :
    let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) *
        ∑ x, productPrior law x * D x := by
  intro law
  let κ := (2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
  have hκ : 0 ≤ κ := mul_nonneg (by positivity) (pow_nonneg hE _)
  have hlaw (i : Fin (N + 1)) (a : A) : 0 ≤ law i a := by
    dsimp only [law]
    cases e i with
    | inl b => exact hν b a
    | inr c => exact hμ _ a
  rw [movingPattern_original_bulk_mean_eq e μ ν prime hnmass t small slot perm pattern rep G seed]
  calc
    _ ≤ ∑ x, (D x * κ) * productPrior law x := norm_sum_le_of_le _ (fun x _ =>
      (movingPattern_flagged_pointwise_bound e μ ν prime n t small
        (movingPatternBulkLeaves n m slot perm) pattern rep E hprime hμ hν hbound
        (movingPatternBulkMean e ν slot G) x).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hG x) hκ)
          (productPrior_nonneg law hlaw x)))
    _ = κ * ∑ x, productPrior law x * D x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining factors independent of the selected bulk draws -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternBulkMean_weight {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (W G : (Fin (N + 1) → A) → ℂ)
    (hW : ∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x)
    (x : Fin (N + 1) → A) :
    movingPatternBulkMean e ν slot (fun x => W x * G x) x =
      W x * movingPatternBulkMean e ν slot G x := by
  unfold movingPatternBulkMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [hW x z]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryRealEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

theorem realEval_bind {σ τ : Type*} (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (x : τ → ℝ) : (F.bind f).realEval x = F.realEval (fun i => (f i).realEval x) := by
  induction F with
  | prime i => simp only [bind, realEval_prime]
  | external z => simp only [bind, realEval_external]
  | product l r hl hr => simp only [bind, realEval_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, realEval_solve, hl, hr]

theorem realEval_listProduct {σ : Type*} (fs : List (HistoryFormula σ)) (x : σ → ℝ) :
    (listProduct fs).realEval x = (fs.map (fun F => F.realEval x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, realEval_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_realEval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (s.giantFormula value hs hu L R).realEval x =
      s.realValuePivot (fun i => (value i : ℝ)) (L.realEval x) (R.realEval x) := by
  simp only [giantFormula, HistoryFormula.realEval_solve, HistoryFormula.realEval_product,
    HistoryFormula.realEval_external, Int.cast_mul, Int.cast_natCast, realValuePivot,
    realSlotProduct_nat]
  ring

theorem movingNodeGuard_realEval (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).archimedeanAt x ↔
      1 ≤ ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ∧
      ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ≤ pivotBound ∧
      ((2 * pivotBound * childBound + 1 : ℕ) : ℝ) ≤ R.realEval x * CR := by
  simp only [movingNodeGuard, wordTransferGuard, WordTransferGuard.archimedeanAt,
    HistoryFormula.realEval_bind, HistoryPivotStep.formula, wordTransferStep, movingNodeWord,
    HistoryFormula.realEval_solve, HistoryFormula.realEval_listProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, HistoryFormula.realEval_prime, Bool.false_eq_true, ite_false, if_false,
    ite_true, if_true, HistoryFormula.realEval_product, HistoryFormula.realEval_external, Int.cast_natCast, mul_one]
  ring_nf

/-- Exact agreement with all original archimedean formula-node tests. -/
theorem realValueNodeSupport_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    movingArchimedeanGate (T.formulaNodes value hvalue childBound pivotBound hf L R) x ↔
      realValueNodeSupport (fun i => (value i : ℝ)) childBound pivotBound T (L.realEval x) (R.realEval x) := by
  induction T generalizing L R with
  | leaf => simp [MovingSlotData.formulaNodes, movingArchimedeanGate, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.formulaNodes, movingArchimedeanGate, List.forall_mem_cons,
      List.forall_mem_append, realValueNodeSupport]
    rw [show (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) L, f.guard.archimedeanAt x) ↔ _ from
      ihL hf.2.1 _ L,
      show (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) R, f.guard.archimedeanAt x) ↔ _ from
      ihR hf.2.2 _ R]
    rw [movingNodeGuard_realEval]
    simp only [MovingSlotReversal.giantFormula_realEval, MovingSlotReversal.realCompositePivot,
      MovingSlotData.step, realSlotProduct_nat]
    tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- The real extension has precisely the old arithmetic gates and windows. -/
theorem realValueSupportFlag_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (X lo hi L R : ℝ) :
    realValueSupportFlag (fun i => (value i : ℝ)) childBound pivotBound T X lo hi L R =
      movingRealGateWeight value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        X lo hi (topGiantReal L R) := by
  have hn := realValueNodeSupport_nat value hv childBound pivotBound T hf
    (.prime false) (.prime true) (topGiantReal L R)
  simp only [HistoryFormula.realEval_prime, topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hn
  simp only [realValueSupportFlag, realValueFullSupport, movingRealGateWeight,
    movingArchimedeanFlag, movingRealWindowFlag, MovingSlotData.realValueLeafModuli_nat,
    topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hn]
  split_ifs <;> simp_all

theorem realValueKernel_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernel (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernel value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernel, realValueSupportFlag_nat value hv childBound pivotBound T hf,
    realValueSmoothWeight_nat]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise cost of the actual normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueTransform_norm_le_sqrt {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ Real.sqrt (p : ℝ) := by
  have hx : ‖normalizedResidueTransform S x‖ ^ 2 ≤
      ∑ y : ZMod p, ‖normalizedResidueTransform S y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y : ZMod p => ‖normalizedResidueTransform S y‖ ^ 2)
      (fun y _ => sq_nonneg _) (Finset.mem_univ x)
  rw [normalizedResidueTransform_energy S hS hSp] at hx
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p),
    Real.sqrt_nonneg (p : ℝ), norm_nonneg (normalizedResidueTransform S x)]

theorem normalizedResidueTransform_norm_le_prime {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ p := by
  apply (normalizedResidueTransform_norm_le_sqrt S hS hSp x).trans
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p), Real.sqrt_nonneg (p : ℝ)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realValueKernelPair_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernelPair (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernelPair, realValueKernel_nat value hv childBound pivotBound (T false) (hf false),
    realValueKernel_nat value hv childBound pivotBound (T true) (hf true)]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit size of the actual sharp bulk kernel -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- The bound used in prime replacement is explicit, rather than an
unspecified boundedness constant of the constructed integrand. -/
theorem realValueKernelPair_norm_le {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hcomp : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have hb (b) := realValueKernel_norm value i childBound pivotBound (T b) (hcomp b)
    ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
  have hpos := (norm_nonneg _).trans (hb false)
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) hpos

theorem movingPattern_kernel_norm_le {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound
      (movingPatternFinBulkData e n m t small slot perm pattern) ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_le value (movingPatternBulkEmbedding e slot j₀) childBound pivotBound _
    (fun b => movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j₀)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  have hv : ∀ i, value i ≠ 0 := fun i => (hp i).ne_zero
  have hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (data b).formulaNodes value hv childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk : ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U‖ ≤ W := by
    rw [← realValueKernelPair_nat value hv childBound pivotBound data hf]
    exact movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
      (fun i => (value i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
  have hfr : ‖movingFrequencyPageAverage value outside F E data nodes R r P Q y‖ ≤ amp :=
    movingFrequencyPageAverage_norm_le value outside F E data nodes R r P Q y hy
  have hs : ‖∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data‖ ≤
      ∏ i, Kspec i ^ (2 ^ (n + 1)) := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ =>
      movingSpectatorHaarAverage_norm_le value (p i) (g i) (twist i) data
        (Kspec i) (hKspec i) (hgnorm i))
  change ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ W * (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) :=
      mul_le_mul hk (mul_le_mul hfr hs (norm_nonneg _) (by dsimp only [amp]; positivity))
        (by positivity) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternLogPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hn : 0 ≤ ∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) :=
    Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
  have hle : (∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
      (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
  change ‖((_ : ℝ) : ℂ) * movingPatternPrimeBulkHaar e t small slot perm pattern base
    primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U x‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  apply (mul_le_of_le_one_left (norm_nonneg _) hle).trans
  exact movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    base primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U hy Kspec hKspec hgnorm x

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

theorem movingPatternLogPrimeObservable_join (base : Fin (N + 1) → primes)
    (z : TreeLeafIndex n × Fin m → primes) :
    movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb
      (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => base i)) =
    movingPatternLogPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
      hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
      R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb z := by
  have hv : (fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
      (fun j => base j) i : ℕ)) =
      primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk, primeBulkValues_at]
    · rw [joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun j => base j) ⟨i, hi⟩, primeBulkValues_off _ _ _ i hi]
  let eval : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} → ℂ := fun v =>
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes v.val v.property childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    ((∏ j, bulkLogCutoffWeight (fun i => (v.val i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
      (movingRealKernelPair v.val data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPageAverage v.val outside F E data nodes R r P Q y *
        ∏ i, movingSpectatorHaarAverage v.val (p i) (g i) (twist i) data))
  let left : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
        (fun j => base j) i : ℕ),
      fun i => (hprimes _ ((joinBulkNonbulk (A := primes)
        (movingPatternBulkEmbedding e slot) z (fun j => base j)) i).property).ne_zero⟩
  let right : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z,
      fun i => (primeBulkValues_prime (fun i => (base i : ℕ))
        (movingPatternBulkEmbedding e slot) z hprimes
        (fun i _ => hprimes _ (base i).property) i).ne_zero⟩
  change eval left = eval right
  exact congrArg eval (Subtype.ext hv)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeObservableCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual observable and its uniform pointwise arithmetic cost -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
theorem movingPatternLogPrimeObservable_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : Fin (N + 1) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y
      ψ X lo hi hlo hhi φ G L U logSlots cb x‖ ≤ (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  dsimp only
  let z := fun j => x (movingPatternBulkEmbedding e slot j)
  have heq : joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i) = x := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk]
    · exact joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun i => x i) ⟨i, hi⟩
  have ho := movingPatternLogPrimeObservable_join e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U logSlots cb x z
  rw [heq] at ho
  rw [ho]
  exact movingPatternLogPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (x i : ℕ)) primes hprimes (fun i _ => hprimes _ (x i).property)
    childBound pivotBound hfreq F E outside R r p g twist P Q y j₀ ψ X lo hi V hlo hhi hV
    φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U logSlots cb hy Kspec hKspec hgnorm z

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic comparison restricted to the original product support -/

namespace Ostmann
open scoped Classical BigOperators

/-- Vanishing representative prior forces the original compensated coefficient
it dominates to vanish as well. -/
theorem movingPattern_coefficient_zero_of_prior {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0) :
    ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) = 0 := by
  have hd := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (fun _ => 1) 1 (by norm_num) (fun _ => by norm_num) x
  rw [hx, mul_zero] at hd
  simp only [mul_one] at hd
  have hscalar : 0 < ∏ c, internalLineScalar true (prime (x (e.symm (.inr c)))) := by
    apply Finset.prod_pos
    intro c _
    simp only [internalLineScalar, ite_true, if_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr (hprime _).pos)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
    (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) : ℂ))]

/-- Restricting the observable to the representative product support preserves
its exact original, compensated pattern weight. -/
theorem movingOriginalPatternWeight_support_restrict {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => if productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0 then 0 else G x) x =
      movingOriginalPatternWeight e μ ν prime n pattern G x := by
  by_cases hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x = 0
  · have hz := movingPattern_coefficient_zero_of_prior e μ ν prime pattern rep E
      hprime hμ hν hbound x hx
    simp only [movingOriginalPatternWeight, hz, zero_mul]
  · unfold movingOriginalPatternWeight movingPatternInjectionGuard
    split_ifs <;> simp only [hx, ite_false, if_false]

theorem movingPattern_arithmetic_comparison_on_support {A B C : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ b, (movingPatternFinData e n t small bulk pattern b).SizeLE d)
    (hfreq : ∀ b, (movingPatternFinData e n t small bulk pattern b).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E α β V : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hmax : ∀ j a, μ j a ≤ α) (hnmax : ∀ j a, ν j a ≤ α)
    (hpmax : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≤ β)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hcross : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) :
    let κ := D * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C))
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x)‖ ≤
      κ * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let H := fun x => if productPrior law x = 0 then 0 else G x
  have hsupp (x) (hx : H x ≠ 0) : productPrior law x ≠ 0 ∧ G x ≠ 0 := by
    dsimp only [H] at hx
    split_ifs at hx with hz
    · exact False.elim (hx rfl)
    · exact ⟨hz, hx⟩
  have hH (x) : ‖H x‖ ≤ D := by
    dsimp only [H]
    split_ifs
    · simpa only [norm_zero] using hD
    · exact hG x
  have hh := movingPattern_arithmetic_comparison e prime hpInj hprime tierB tierC t small bulk
    pattern rep hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass
    E α β V hE hα hβ hV hbound hmax hnmax hpmax hprimeSize H D hD hH
    (fun x hx => hdisjoint x (hsupp x hx).1 (hsupp x hx).2)
    (fun x hx => hcross x (hsupp x hx).1 (hsupp x hx).2)
    (fun x hx => hfmod x (hsupp x hx).1 (hsupp x hx).2)
  have heq (x) : movingOriginalPatternWeight e μ ν prime n pattern H x =
      movingOriginalPatternWeight e μ ν prime n pattern G x :=
    movingOriginalPatternWeight_support_restrict e μ ν prime pattern rep E hprime hμ hν hbound G x
  simp_rw [heq] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSupportedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed bulk estimates needed only on the original pattern prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- Invalid role assignments outside the original product law require no
analytic estimate. This retains the original harmonic priors when applying
an estimate proved with their precise prime ranges. -/
theorem movingPattern_signed_bulk_mean_on_support {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ) (hE : 0 ≤ E)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ)
    (hG : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      ‖movingPatternBulkMean e ν slot G x‖ ≤ D)
    (seed : TreeLeafIndex n × Fin m → A) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * D := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let minor := fun x => if productPrior law x = 0 then ‖movingPatternBulkMean e ν slot G x‖ else D
  have hminor (x) : ‖movingPatternBulkMean e ν slot G x‖ ≤ minor x := by
    dsimp only [minor]
    split_ifs with h
    · exact le_rfl
    · exact hG x h
  have hlaw (i) : ∑ a, law i a = 1 := by
    dsimp only [law]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hmean : (∑ x, productPrior law x * minor x) = D := by
    calc
      _ = ∑ x, productPrior law x * D := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [minor]
        split_ifs with h
        · simp only [h, zero_mul]
        · rfl
      _ = D := by rw [← Finset.sum_mul, productPrior_mass law hlaw, one_mul]
  have hh := movingPattern_signed_bulk_majorant e μ ν prime t small slot perm pattern rep E hE
    hprime hμ hν hnmass hbound G minor hminor seed
  dsimp only at hh
  dsimp only [law] at hmean
  rw [hmean] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSupportedArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining arithmetic and bulk cancellation on the original support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_signed_arithmetic_on_support {A B C : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (tierB : B → ℕ) (tierC : C → ℕ) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), n ≤ tierB i)
    (hbulk : ∀ b, ∀ i ∈ flattenMovingSlots n (bulk b), n ≤ tierB i)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (d : ℕ) (F U : ℝ) (hF : 1 ≤ F) (hU : 1 ≤ U)
    (hsize : ∀ b, (movingPatternFinData e n t small bulk pattern b).SizeLE d)
    (hfreq : ∀ b, (movingPatternFinData e n t small bulk pattern b).Frequencies (fun s => |(s : ℝ)| ≤ F))
    (hvalues : ∀ a, |((prime a : ℤ) : ℝ)| ≤ U)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (E α β V : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hmax : ∀ j a, μ j a ≤ α) (hnmax : ∀ j a, ν j a ≤ α)
    (hpmax : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≤ β)
    (hprimeSize : ∀ c a, μ (movingSampleTier (rep c).val.2) a ≠ 0 →
      Real.exp V ≤ prime a)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ) (hD : 0 ≤ D) (hG : ∀ x, ‖G x‖ ≤ D)
    (hdisjoint : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ i j,
      (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → prime (x i) ≠ prime (x j))
    (hcross : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ b c,
      prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hfmod : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      G x ≠ 0 → ∀ c b,
      (movingPatternFinData e n t small bulk pattern b).Frequencies
        (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0))
    (m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (hbulkEq : bulk = movingPatternBulkLeaves n m slot perm)
    (Dminor : ℝ)
    (hminor : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      ‖movingPatternBulkMean e ν slot G x‖ ≤ Dminor)
    (seed : TreeLeafIndex n × Fin m → A) :
    let κ := (2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternHaarProduct e prime hprime n t small bulk pattern x‖ ≤
      κ * (D * (((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) +
        2 * ((Fintype.card C * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
          ((2 * ((n + 1) * d) : ℕ) * α +
            (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)) + Dminor) := by
  have ha := movingPattern_arithmetic_comparison_on_support e prime hpInj hprime tierB tierC t small bulk pattern rep
    hsmall hbulk htier d F U hF hU hsize hfreq hvalues μ ν hμ hν hmass hnmass
    E α β V hE hα hβ hV hbound hmax hnmax hpmax hprimeSize G D hD hG hdisjoint hcross hfmod
  have hb : ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternFlagProduct e prime n t small bulk pattern rep x‖ ≤
      Dminor * ((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) := by
    rw [hbulkEq]
    simpa only [mul_comm] using
      movingPattern_signed_bulk_mean_on_support e μ ν prime t small slot perm pattern rep E hE
        hprime hμ hν hmass hnmass hbound G Dminor hminor seed
  dsimp only at ha ⊢
  let X := ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
    movingPatternHaarProduct e prime hprime n t small bulk pattern x
  let Y := ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
    movingPatternFlagProduct e prime n t small bulk pattern rep x
  have heq : X - Y = ∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      (movingPatternHaarProduct e prime hprime n t small bulk pattern x -
        movingPatternFlagProduct e prime n t small bulk pattern rep x) := by
    dsimp only [X, Y]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have htriangle : ‖X‖ ≤ ‖X - Y‖ + ‖Y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (X - Y) Y
  rw [heq] at htriangle
  exact htriangle.trans ((add_le_add ha hb).trans_eq (by ring))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogWindowArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete arithmetic bound under the original union-of-cells prior -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_weighted_arithmetic_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (W : (Fin (N + 1) → primes) → ℂ)
        (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G XL U logSlots cb
      let obs := fun x => W x * raw x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, ‖W x‖ ≤ 1) →
      (∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern obs x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_half_log_selected_prime_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate] with L hrate
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx _ _ Cell _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U u v deleted initial
    μ ν logSlots cb W Eprior αall βint Vint Uall hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hW hWbulk hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let raw := movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p
    (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
    y ψ X lo hi hlo hhi φ G XL U logSlots cb
  let obs := fun x => W x * raw x
  let cost := (2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖) *
    ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  have hraw (x) : ‖raw x‖ ≤ cost :=
    movingPatternLogPrimeObservable_norm e tierB tierC t small slot perm pattern hB htier
      primes hprimes childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y j₀
      ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U logSlots cb
      hy (fun i => (p i : ℝ)) (fun i => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
  have hpoint (x) : ‖obs x‖ ≤ cost := by
    change ‖W x * raw x‖ ≤ cost
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hW x) (norm_nonneg _)).trans (by simpa using hraw x)
  have hminor (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
      ‖movingPatternBulkMean e ν slot obs x‖ ≤
      Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
    rw [movingPatternBulkMean_weight e ν slot W raw hWbulk x, norm_mul]
    apply (mul_le_mul_of_nonneg_right (hW x) (norm_nonneg _)).trans
    simp only [one_mul]
    exact hrate lo hi hlo hhi hwidth Bidx Cidx Cell N e tierB tierC t small slot perm pattern primes hprimes x
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β Qfreq y X j₀ φ G XL U u v (deleted x) logSlots cb
      hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp (hsmallp x hx) (hsamplesp x hx)
      hgood hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
      hcard hu hulow huv hshort hsep hMcell hS (hdel x hx) hmass (hdelbase x hx) hout (hdelout x hx)
      c₀ initial hsub (hretain x hx) ν hν
  have hfinal := movingPattern_signed_arithmetic_on_support e (fun q : primes => (q : ℕ))
    Subtype.val_injective (fun q => hprimes _ q.property) tierB tierC t small
    (movingPatternBulkLeaves (n + 2) m slot perm) pattern rep
    (fun b j _ => hB j) (fun b j _ => hB j) htier
    (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall
    (Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))) hUall
    (movingPatternFinBulkData_size e t small slot perm pattern hsmallLen)
    (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hV)
    (fun q => by
      simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (q : ℕ) from Nat.cast_nonneg _)]
        using hvalues q)
    μ ν hμ0 hν0 hμmass hνmass Eprior αall βint Vint hEprior hαall hβint hVint
    hμbound hμall hνall hμmax hμmin obs cost (by dsimp only [cost]; positivity)
    hpoint hdisjoint hcross hfmod m slot perm rfl
    (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hminor
    (fun _ => Classical.arbitrary primes)
  simpa only [movingInternalArithmeticError, obs, raw, cost, data, m] using hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePairHaarRegularity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem continuous_pageGiantWeight (P : PublishedProgressionInput) (Q q a : ℕ) :
    Continuous (pageGiantWeight P Q q a) := by
  unfold pageGiantWeight pageMultiplier
  fun_prop

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedPairHaarRegularity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the retained mixed-prime mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem continuous_correctedMixedPairAverage (P : PublishedProgressionInput) (Q q : ℕ)
    [NeZero q] (c : ℕ → ℕ → ℂ) :
    Continuous (correctedMixedPairAverage P Q q c) := by
  unfold correctedMixedPairAverage
  apply continuous_const.mul
  apply continuous_finsetSum
  intro z _
  exact continuous_const.mul (continuous_pageGiantWeight P Q q _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedMeasurable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the original two-prime pattern integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

theorem movingPatternPrimeObservable_measurable
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : Fin (N + 1) → primes) :
    Measurable (fun z : ℝ × ℝ =>
      movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist input Q z.2
        ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) x) := by
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t small slot perm pattern
  let hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk := measurable_exp_pair_mul (movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G)
    (measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
      Bφ Dφ hBφ hDφ hφ hlip hout) (1 : ℂ)
  simp only [one_mul] at hk
  have ha := (continuous_correctedMixedPairAverage input Q r
    (fun a b => movingFrequencyPairFactor value outside F E T nodes R a b)).measurable.comp (show Measurable (Prod.snd : ℝ × ℝ → ℝ) from measurable_snd)
  change Measurable (fun z : ℝ × ℝ =>
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) *
      (movingFrequencyPageAverage value outside F E T nodes R r input Q z.2 *
        ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) T))
  exact hk.mul (ha.mul measurable_const)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternLogPrimeMeasurable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the original two-prime pattern integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

theorem movingPatternLogPrimeObservable_measurable
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ) (x : Fin (N + 1) → primes) :
    Measurable (fun z : ℝ × ℝ =>
      movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist input Q z.2
        ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) logSlots cb x) := by
  have h := movingPatternPrimeObservable_measurable e t small slot perm pattern
    primes hprimes childBound pivotBound hfreq F E outside R r p g twist input Q
    ψ X lo hi hlo hhi φ G Bφ Dφ hBφ hDφ hφ hlip hout x
  exact measurable_const.mul h

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedPairIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite signed averages under the original external integer density -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem finite_mixed_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s center C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hcenter : v ≤ center + 1) (hC : 0 ≤ C) (w : A → ℂ)
    (F : A → ℝ → ℝ → ℂ) (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)‖ ≤
      (2 * Real.exp 1 * C) / r := by
  let F' := fun a x y => ((x * Real.exp (x - center) : ℝ) : ℂ) * F a x y
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hv0 : 0 ≤ v := hu0.le.trans huv
  have he (x : ℝ) (hx : x ∈ Set.Ioc u v) :
      0 ≤ x * Real.exp (x - center) ∧ x * Real.exp (x - center) ≤ v * Real.exp 1 := by
    have hx0 : 0 ≤ x := hu0.le.trans hx.1.le
    refine ⟨mul_nonneg hx0 (Real.exp_nonneg _), ?_⟩
    exact mul_le_mul hx.2 (Real.exp_le_exp.mpr (by linarith [hx.2]))
      (Real.exp_nonneg _) hv0
  have hm (a : A) : Measurable (Function.uncurry (F' a)) := by
    have hscalar : Measurable (fun z : ℝ × ℝ => ((z.1 * Real.exp (z.1 - center) : ℝ) : ℂ)) := by
      fun_prop
    exact hscalar.mul (hmeas a)
  have hpoint (a : A) (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F' a x y‖ ≤ (v * Real.exp 1) * K a := by
    dsimp only [F']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hbound a x hx y hy) (norm_nonneg _) (by positivity)
  have hmean' (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖∑ a, w a * F' a x y‖ ≤ v * Real.exp 1 * C := by
    have hh : (∑ a, w a * F' a x y) =
        ((x * Real.exp (x - center) : ℝ) : ℂ) * ∑ a, w a * F a x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [F']
      ring
    rw [hh, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hmean x hx y hy) (norm_nonneg _) (by positivity)
  have hh := finite_harmonic_pair_sum_norm u v r s (v * Real.exp 1 * C)
    hu hr huv hrs hv hs (by positivity) w F' hm
    (fun a => (v * Real.exp 1) * K a) (fun a => mul_nonneg (by positivity) (hK a))
    hpoint hmean'
  have heq (a : A) : (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, F' a x y / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hu0.trans hx.1)
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hr0.trans hy.1)
    dsimp only [F']
    push_cast
    field_simp
  simp_rw [heq]
  apply hh.trans
  have hratio : v / u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith)
  calc
    v * Real.exp 1 * C / (u * r) = (v / u) * (Real.exp 1 * C / r) := by ring
    _ ≤ 2 * (Real.exp 1 * C / r) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg (mul_nonneg (Real.exp_nonneg _) hC) hr0.le)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedHarmonicIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the signed original-pattern bound through both giant cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingPattern_mixed_harmonic_integral_bound {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℝ → ℝ → ℂ)
    (hG : ∀ x, Measurable (Function.uncurry (G x)))
    (u v r s center D : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1) (hcenter : v ≤ center + 1) (hD : 0 ≤ D)
    (K : (Fin (N + 1) → A) → ℝ) (hK : ∀ x, 0 ≤ K x)
    (hbound : ∀ x a, a ∈ Set.Ioc u v → ∀ b, b ∈ Set.Ioc r s → ‖G x a b‖ ≤ K x)
    (hmean : ∀ a ∈ Set.Ioc u v, ∀ b ∈ Set.Ioc r s,
      ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x *
        movingPatternHaarProduct e prime hprime n t small bulk pattern x‖ ≤ D) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x *
      movingPatternHaarProduct e prime hprime n t small bulk pattern x‖ ≤ (2 * Real.exp 1 * D) / r := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1)
  let H := movingPatternHaarProduct e prime hprime n t small bulk pattern
  have hpoint (a : ℝ) (ha : a ∈ Set.Ioc u v) (b : ℝ) (hb : b ∈ Set.Ioc r s) :
      ‖∑ x, w x * (G x a b * H x)‖ ≤ D := by
    have he (x) : movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x =
        w x * (G x a b * H x) := by
      rw [movingOriginalPatternWeight_eq_coefficient_mul]
      exact mul_assoc _ _ _
    have hm := hmean a ha b hb
    change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x‖ ≤ D at hm
    simpa only [he] using hm
  have h := finite_mixed_pair_sum_norm u v r s center D hu hr huv hrs hv hs hcenter hD w
    (fun x a b => G x a b * H x) (fun x => (hG x).mul_const (H x))
    (fun x => K x * ‖H x‖) (fun x => mul_nonneg (hK x) (norm_nonneg _))
    (by
      intro x a ha b hb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x a ha b hb) (norm_nonneg _)) hpoint
  have he (x) : movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x * H x =
      w x * ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
        (G x a b * H x) * (Real.exp (a - center) : ℂ) / (b : ℂ) := by
    rw [movingOriginalPatternWeight_eq_coefficient_mul]
    simp_rw [show ∀ a b : ℝ, (G x a b * H x) * (Real.exp (a - center) : ℂ) / (b : ℂ) =
      (G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) * H x by intros; ring, integral_mul_const]
    exact mul_assoc _ _ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
    (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
      G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x * H x‖ ≤ _
  simpa only [he] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogWindowIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed quartet cancellation under both giant-cell integrals -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_weighted_mixed_integral_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (W : ℝ → ℝ → (Fin (N + 1) → primes) → ℂ)
        (Eprior αall βint Vint Uall uG vG rG sG center : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
      let obs := fun xg y x => W xg y x * raw xg y x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, Measurable (fun z : ℝ × ℝ => W z.1 z.2 x)) →
      (∀ xg y x, ‖W xg y x‖ ≤ 1) →
      (∀ xg y x z, W xg y (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W xg y x) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
          (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
            obs xg y x * (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      (2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_half_log_weighted_arithmetic_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate] with L hrate
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx _ _ Cell _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq X j₀ φ G u v deleted initial
    μ ν logSlots cb W Eprior αall βint Vint Uall uG vG rG sG center
    hslots huG hrG huvG hrsG hvG hsG hcenter hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hWmeas hW hWbulk hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p
    (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
    y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
  let obs := fun xg y x => W xg y x * raw xg y x
  let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  let bound := ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
    (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
      (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
    (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))))
  have hmean (xg : ℝ) (hxg : xg ∈ Set.Ioc uG vG) (y : ℝ) (hy : y ∈ Set.Ioc rG sG) :
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
          (obs xg y) x * movingPatternHaarProduct e (fun q : primes => (q : ℕ))
          (fun q => hprimes _ q.property) (n + 2) t small
          (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤ bound := by
    exact hrate lo hi hlo hhi hwidth Bidx Cidx Cell N e tierB tierC t small slot perm pattern rep primes hprimes
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β Qfreq y X j₀ φ G
      (Real.exp xg) (Real.exp y) u v deleted initial μ ν logSlots cb (W xg y) Eprior αall βint Vint Uall
      hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
      hdlo hdhi hsets hsetsp hβ hbias hamp (by linarith [hy.1]) hpupper hMQ hpage hφ hlip hφout
      hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
      hμbound hμall hνall hμmax hμmin hvalues (hW xg y) (hWbulk xg y)
      (hdisjoint xg hxg y hy) (hcross xg hxg y hy) (hfmod xg hxg y hy)
  have hcost : 0 ≤ cost := by dsimp only [cost, amp]; positivity
  have herr := movingInternalArithmeticError_nonneg (n + 2) (Fintype.card Cidx)
    (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint
    (Real.one_le_exp (mul_nonneg hA (Nat.cast_nonneg m))) hUall hαall hβint hVint.le
  have hbound : 0 ≤ bound := by dsimp only [bound]; positivity
  apply movingPattern_mixed_harmonic_integral_bound e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) μ ν t small (movingPatternBulkLeaves (n + 2) m slot perm)
    pattern (fun x xg y => obs xg y x) _ uG vG rG sG center bound huG hrG huvG hrsG hvG hsG hcenter
    hbound (fun _ => cost) (fun _ => hcost) _ hmean
  · intro x
    exact (hWmeas x).mul (movingPatternLogPrimeObservable_measurable e t small slot perm pattern
      primes hprimes childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
      ψ X lo hi hlo hhi φ G Bφ Dφ hBφ hDφ hφ hlip hφout logSlots cb x)
  · intro x xg hxg y hy
    have hh := movingPatternLogPrimeObservable_norm e tierB tierC t small slot perm pattern
      hB htier primes hprimes childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y j₀
      ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout (Real.exp xg) (Real.exp y) logSlots cb
      (by linarith [hy.1]) (fun i => (p i : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
    change ‖W xg y x * raw xg y x‖ ≤ cost
    rw [norm_mul]
    exact (mul_le_mul (hW xg y x) hh (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogGoodIdealIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original outer cutoff and regular density in the good matching estimate -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window_oai
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (Jidx : Type) [Fintype Jidx] (reg : Jidx → Fin (N + 1)) (active : Jidx → Bool)
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall uG vG rG sG center : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
      let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ Jleft Jright Bφ Dφ diagonal
      let obs := fun xg y x => W xg y x * raw xg y x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false → reg j ∉ Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
          (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
            ((giantOuterWeight φ Jleft Jright diagonal (Real.exp xg) (Real.exp y) *
              (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) * raw xg y x) * (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * ((2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_half_log_weighted_mixed_integral_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate] with L hrate
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx _ _ Cell _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq X j₀ φ G u v deleted initial
    μ ν logSlots cb Jidx _ reg active Jleft Jright diagonal Eprior αall βint Vint Uall uG vG rG sG center
    hslots huG hrG huvG hrsG hvG hsG hcenter hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p
    (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
    y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
  let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ
    Jleft Jright Bφ Dφ diagonal
  have hh := hrate lo hi hlo hhi hwidth Bidx Cidx Cell N e tierB tierC t small slot perm pattern rep primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β Qfreq X j₀ φ G
    u v deleted initial μ ν logSlots cb W Eprior αall βint Vint Uall uG vG rG sG center
    hslots huG hrG huvG hrsG hvG hsG hcenter hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues
    (movingDiagonalOuterWeight_measurable (fun q : primes => (q : ℕ)) reg active φ
      Jleft Jright Bφ Dφ hBφ hDφ hφ hlip hφout diagonal)
    (fun xg y x => movingDiagonalOuterWeight_norm (fun q : primes => (q : ℕ))
      (fun q => hprimes _ q.property) reg active φ Jleft Jright Bφ Dφ hBφ hDφ hφ hlip hφout
      diagonal xg y x)
    (fun xg y x z => movingDiagonalOuterWeight_bulk (fun q : primes => (q : ℕ)) reg active
      (movingPatternBulkEmbedding e slot) hfixed φ Jleft Jright Bφ Dφ diagonal xg y x z)
    hdisjoint hcross hfmod
  exact movingPattern_diagonal_integral_norm e (fun q : primes => (q : ℕ)) μ ν pattern
    reg active φ Jleft Jright Bφ Dφ diagonal raw
    (movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
      (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern)
    uG vG rG sG center _ hh

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window_oai := @OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window_oai
