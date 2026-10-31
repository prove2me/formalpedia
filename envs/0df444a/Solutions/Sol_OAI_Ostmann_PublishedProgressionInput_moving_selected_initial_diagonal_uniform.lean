-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:31:41.278485+00:00
-- url     : https://prove2.me/submissions/dc7b85ab-8b7f-4a6d-8f93-66c3199bc5b4

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_amplitude_regular_energy
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_symmetrized_energy

section
-- module Solutions.OAIQ095_OS.Compat
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

theorem large_prime_factors_coprime_frequency (H : ℕ) (v : ℤ) (hv : v ≠ 0)
    (hlarge : ∀ q, q.Prime → q ∣ H → v.natAbs < q) : H.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro q hq hqH hqv
  exact (not_le_of_gt (hlarge q hq hqH))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hqv)

/-- The zero numerator has only the equal-product, equal-frequency
diagonal when prime factors exceed the frequencies. -/
theorem diagonal_products_equal (HL HR : ℕ) (hHL : 0 < HL) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0) (hrel : v * HR = w * HL)
    (hL : ∀ q, q.Prime → q ∣ HL → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ HR → w.natAbs < q) : HL = HR ∧ v = w := by
  have hvH := large_prime_factors_coprime_frequency HL v hv hL
  have hwH := large_prime_factors_coprime_frequency HR w hw hR
  have habs := congrArg Int.natAbs hrel
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hdL : HL ∣ HR := hvH.dvd_of_dvd_mul_left (by
    rw [habs]
    exact dvd_mul_left HL w.natAbs)
  have hdR : HR ∣ HL := hwH.dvd_of_dvd_mul_left (by
    rw [← habs]
    exact dvd_mul_left HR v.natAbs)
  have heq : HL = HR := Nat.dvd_antisymm hdL hdR
  refine ⟨heq, ?_⟩
  rw [← heq] at hrel
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hHL) : (HL : ℤ) ≠ 0) hrel

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the transfer diagonal before expanding the square -/

namespace Ostmann

open scoped BigOperators Classical

/-- The key comprises the inherited product and its frequency. Ordered
arrangements with that key are summed inside the square. -/
theorem diagonal_grouped_identity {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℂ) :
    (∑ a : A, ∑ b : A, if key a = key b then w (key a) * z a * star (z b) else 0) =
      ∑ k : K, w k * groupedCoefficient key z k * star (groupedCoefficient key z k) := by
  rw [Finset.sum_comm]
  symm
  unfold groupedCoefficient
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, apply_ite, star_zero,
    ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key b = key a <;> simp [h]

theorem diagonal_real_eq_sum_sq {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) :
    (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re =
      ∑ k : K, w k * ‖groupedCoefficient key z k‖ ^ 2 := by
  rw [diagonal_grouped_identity key z (fun k => (w k : ℂ))]
  simp only [mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pivot_zero_numerator_iff (L R : ℕ) (hLpos : 0 < L) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hL : ∀ q, q.Prime → q ∣ L → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ R → w.natAbs < q) :
    v * R - w * L = 0 ↔ L = R ∧ v = w := by
  constructor
  · intro h
    exact diagonal_products_equal L R hLpos v w hv hw (sub_eq_zero.mp h) hL hR
  · rintro ⟨rfl, rfl⟩
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexPrimeWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_add (q a : ℕ) (u v t : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexPrimeInterval q a u v w + complexPrimeInterval q a v t w =
      complexPrimeInterval q a u t w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexIntegerInterval_add (q a : ℕ) (u v t G : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexIntegerInterval q a u v G w + complexIntegerInterval q a v t G w =
      complexIntegerInterval q a u t G w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

theorem buildMovingSlotData_regular_perm {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).regularSlots.Perm
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  cases samples with
  | leaf => exact List.Perm.refl _
  | @node n samples left right =>
    apply List.perm_iff_count.mpr
    intro a
    simp only [buildMovingSlotData, MovingSlotData.regularSlots, flattenMovingSlots,
      List.count_append]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.frequencies_isCoprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (x : ℤ) :
    T.Frequencies (fun s => IsCoprime x s) ↔ IsCoprime x T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [Frequencies, frequencyProduct, IsCoprime.mul_right_iff, ihL, ihR, and_assoc]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal distinct-prime products give the unique actual slot matching -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ ∏ i, p i) : ∃ i, q = p i := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hd
  exact ⟨i, ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one⟩

theorem prime_product_matching_exists_unique {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q)
    (hprod : (∏ i, p i) = ∏ j, q j) : ∃! e : I ≃ J, ∀ i, p i = q (e i) := by
  have hex : ∀ i, ∃ j, p i = q j := by
    intro i
    apply prime_dvd_prime_product q hq (p i) (hp i)
    rw [← hprod]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  let f : I → J := fun i => Classical.choose (hex i)
  have hf : ∀ i, p i = q (f i) := fun i => Classical.choose_spec (hex i)
  have hfi : Function.Injective f := by
    intro i i' he
    apply hinjp
    rw [hf i, hf i', he]
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := prime_dvd_prime_product p hp (q j) (hq j) (by
      rw [hprod]
      exact Finset.dvd_prod_of_mem q (Finset.mem_univ j))
    refine ⟨i, hinjq ?_⟩
    exact (hf i).symm.trans hi.symm
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf, ?_⟩
  intro e he
  apply Equiv.ext
  intro i
  exact hinjq ((he i).symm.trans (hf i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common Fourier multiplier on equal-product diagonal fibres -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem primeTuple_image_factors {J : Type*} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) :
    Finset.univ.image p = (∏ j, p j).primeFactors := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · intro hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hp j, Finset.dvd_prod_of_mem p (Finset.mem_univ j),
      (Finset.prod_pos (fun j _ => (hp j).pos)).ne'⟩
  · rintro ⟨hq, hd, _⟩
    obtain ⟨j, rfl⟩ := prime_dvd_prime_product p hp q hq hd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- Every distinct-prime arrangement has exactly the same transform on a
fixed product/frequency fibre. This justifies extracting it before taking
the squared modulus of the sum over arrangements. -/
theorem movingRegularTransform_eq_primeProduct {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hinj : Function.Injective p)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D : ℕ) (s : ℤ) :
    movingRegularTransform p (fun j => g (p j)) D s =
      primeProductTransform g D (∏ j, p j) s := by
  have hc (j : J) : tupleCofactor p j = (∏ i, p i) / p j := by
    rw [← tupleCofactor_mul p j]
    exact (Nat.mul_div_cancel_left _ (Fact.out : (p j).Prime).pos).symm
  unfold movingRegularTransform primeProductTransform
  rw [← primeTuple_image_factors p (fun j => Fact.out), Finset.prod_image]
  · exact Finset.prod_congr rfl (fun j _ => by rw [hc j])
  · intro i _ j _ hij
    exact hinj hij

/-- Grouping precedes the absolute value. The transform is constant on
each fibre, so its squared modulus is a nonnegative common multiplier. -/
theorem diagonal_common_transform {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (W : A → ℂ) (G : K → ℂ) :
    (∑ a, ∑ b, if key a = key b then
      (W a * G (key a)) * conj (W b * G (key b)) else 0).re =
      ∑ k, ‖G k‖ ^ 2 * ‖groupedCoefficient key W k‖ ^ 2 := by
  rw [← diagonal_real_eq_sum_sq key W (fun k => ‖G k‖ ^ 2)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key a = key b
  · rw [ite_eq_left h, ite_eq_left h, ← h, map_mul]
    have hn : G (key a) * conj (G (key a)) = (‖G (key a)‖ ^ 2 : ℝ) := by
      rw [Complex.mul_conj']
      norm_cast
    calc
      _ = (G (key a) * conj (G (key a))) * W a * conj (W b) := by ring
      _ = _ := by rw [hn]; rfl
  · rw [ite_eq_right h, ite_eq_right h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedNormTriangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite weighted square norm under divisor summation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_correlation_le_sqrt_energy {ι : Type*} (S : Finset ι)
    (μ : ι → ℝ) (f g : ι → ℂ) (hμ : ∀ s ∈ S, 0 ≤ μ s) :
    ‖∑ s ∈ S, (μ s : ℂ) * (f s * conj (g s))‖ ≤
      Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) *
      Real.sqrt (∑ s ∈ S, μ s * ‖g s‖ ^ 2) := by
  have he (a : ι → ℂ) : (∑ s ∈ S, (Real.sqrt (μ s) * ‖a s‖) ^ 2) =
      ∑ s ∈ S, μ s * ‖a s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (hμ s hs)]
  calc
    _ ≤ ∑ s ∈ S, μ s * (‖f s‖ * ‖g s‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro s hs
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hμ s hs), Complex.norm_conj]
    _ = ∑ s ∈ S, (Real.sqrt (μ s) * ‖f s‖) * (Real.sqrt (μ s) * ‖g s‖) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (hμ s hs)]
    _ ≤ _ := by
      simpa only [he] using Real.sum_mul_le_sqrt_mul_sqrt S
        (fun s => Real.sqrt (μ s) * ‖f s‖) (fun s => Real.sqrt (μ s) * ‖g s‖)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal with its common transform and original prior -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Only the finitely many attained keys are used; products and frequencies
need not have finite ambient types. -/
theorem finite_diagonal_common_transform {A K : Type*} [Fintype A] [DecidableEq K]
    (key : A → K) (W : A → ℂ) (G : K → ℂ) :
    (∑ a, ∑ b, if key a = key b then
      (W a * G (key a)) * conj (W b * G (key b)) else 0).re =
      ∑ k ∈ Finset.univ.image key, ‖G k‖ ^ 2 * ‖groupedCoefficient key W k‖ ^ 2 := by
  let T := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have h := diagonal_common_transform k W (fun x => G x.val)
  have hgroup (x : T) : groupedCoefficient k W x = groupedCoefficient key W x.val := by
    unfold groupedCoefficient
    apply Finset.sum_congr rfl
    intro a _
    rw [show k a = x ↔ key a = x.val from Subtype.ext_iff]
  calc
    _ = ∑ x : T, ‖G x.val‖ ^ 2 * ‖groupedCoefficient key W x.val‖ ^ 2 := by
      simpa only [hgroup, k, Subtype.mk.injEq] using h
    _ = _ := by
      simpa only [T] using Finset.sum_coe_sort T
        (fun x : K => ‖G x‖ ^ 2 * ‖groupedCoefficient key W x‖ ^ 2)

/-- Cauchy on one fibre retains its original prior and charges the other
branch only through that fibre's original mass. -/
theorem grouped_weighted_norm_sq_le {A K : Type*} [Fintype A]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (k : K) (θ : ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : (∑ a, if key a = k then μ a else 0) ≤ θ) :
    ‖groupedCoefficient key (fun a => (μ a : ℂ) * W a) k‖ ^ 2 ≤
      θ * ∑ a, if key a = k then μ a * ‖W a‖ ^ 2 else 0 := by
  let S := Finset.univ.filter (fun a => key a = k)
  have h := weighted_correlation_le_sqrt_energy S μ W (fun _ => 1)
    (fun a _ => hμ a)
  simp only [map_one, mul_one, norm_one, one_pow] at h
  have hE : 0 ≤ ∑ a ∈ S, μ a * ‖W a‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hμ a) (sq_nonneg _)
  have hM : 0 ≤ ∑ a ∈ S, μ a := Finset.sum_nonneg fun a _ => hμ a
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hM] at hsq
  have hmass' : (∑ a ∈ S, μ a) ≤ θ := by simpa only [S, Finset.sum_filter] using hmass
  have hb := hsq.trans (mul_le_mul_of_nonneg_left hmass' hE)
  simpa only [S, Finset.sum_filter, groupedCoefficient, mul_comm] using hb

/-- The diagonal energy after grouping, suitable for the prior atom bound
and the subsequent regular-prime cancellation. -/
theorem weighted_diagonal_common_transform_le {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ a, ∑ b, if key a = key b then
      ((μ a : ℂ) * W a * G (key a)) * conj ((μ b : ℂ) * W b * G (key b)) else 0).re ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  rw [diagonal_common_transform key (fun a => (μ a : ℂ) * W a) G]
  calc
    _ ≤ ∑ k, ‖G k‖ ^ 2 * (θ k * ∑ a, if key a = k then μ a * ‖W a‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (grouped_weighted_norm_sq_le key μ W k (θ k) hμ (hmass k))
        (sq_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (key a)]
      · simp only [ite_true, if_true, norm_mul, mul_pow]
        ring
      · intro k _ hk
        rw [ite_eq_right (Ne.symm hk), mul_zero, mul_zero]
      · simp

/-- The same fibre estimate for unbounded integer product/frequency keys.
Only the finite image of the sample space is introduced as a finite type. -/
theorem finite_weighted_diagonal_common_transform_le {A K : Type*}
    [Fintype A] [DecidableEq K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ a, ∑ b, if key a = key b then
      ((μ a : ℂ) * W a * G (key a)) * conj ((μ b : ℂ) * W b * G (key b)) else 0).re ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  let T := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have h := weighted_diagonal_common_transform_le
    k μ W (fun x => G x.val) (fun x => θ x.val) hμ (fun x => by
      simpa only [Subtype.ext_iff, k] using hmass x.val)
  simpa only [k, Subtype.mk.injEq] using h

theorem finite_grouped_weighted_energy_le {A K : Type*}
    [Fintype A] [DecidableEq K]
    (key : A → K) (μ : A → ℝ) (W : A → ℂ) (G : K → ℂ) (θ : K → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∀ k, (∑ a, if key a = k then μ a else 0) ≤ θ k) :
    (∑ k ∈ Finset.univ.image key, ‖G k‖ ^ 2 *
      ‖groupedCoefficient key (fun a => (μ a : ℂ) * W a) k‖ ^ 2) ≤
      ∑ a, μ a * θ (key a) * ‖W a * G (key a)‖ ^ 2 := by
  rw [← finite_diagonal_common_transform]
  exact finite_weighted_diagonal_common_transform_le key μ W G θ hμ hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_node {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR : ℕ) :
    let T := MovingSlotData.node s CL CR u l r
    let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
    movingFullSupport value outside T XL XR ↔
      movingLocalSupport value outside ⟨n + 1, T, XL, XR⟩ ∧
      movingFullSupport value outside l p XL ∧ movingFullSupport value outside r p XR := by
  simp only [movingFullSupport, movingLocalSupport, movingFullOutsidePairwise, movingNaturalGiantUnits]
  tauto

theorem movingSlotCutoff_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E) x s v w =
      if movingLocalSupport value outside x then
        movingSlotCutoff value childBound pivotBound E x s v w else 0 := by
  unfold movingSlotCutoff movingGuardedExtra
  split_ifs <;> rfl

/-- The fully supported original history coefficient equals the recursive
coefficient with the literal local support test at each node and leaf. -/
theorem movingSupportedWeight_recursive {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
      n ⟨n, T, XL, XR⟩ t =
        movingSupportedWeight value outside T XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n ⟨n, T, XL, XR⟩ t) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutg := movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)
  induction T generalizing XL XR with
  | leaf s regular => rfl
  | @node n s CL CR u l r hl hr =>
      let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u l r, XL, XR⟩
      let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
      have hp : P / MovingSlotReversal.naturalProduct value u = p := by
        simp only [P, p, historyPivot, sys, movingSlotSystem, x, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, MovingSlotReversal.naturalPivot, MovingSlotData.step,
          movingGiantPivot, Nat.mul_one, ← hT.1, ← hT.2.1.root, ← hT.2.2.root]
      by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node sys _ cutg n x t P hv]
        change (cutg x t.1 _ _ : ℂ) *
            recursiveTransferWeight sys _ cutg n ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ t.2.1 *
            star (recursiveTransferWeight sys _ cutg n ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ t.2.2) = _
        rw [hp, hl t.2.1 hT.2.1 p XL, hr t.2.2 hT.2.2 p XR]
        have hg := movingSlotCutoff_guarded value outside childBound pivotBound E x
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        change cutg x t.1 _ _ = if movingLocalSupport value outside x then cut x t.1 _ _ else 0 at hg
        rw [hg]
        unfold movingSupportedWeight
        have hs := movingFullSupport_node value outside s CL CR u l r XL XR
        dsimp only at hs
        rw [hs]
        rw [recursiveTransferWeight_node sys F cut n x t P hv]
        have hleft : sys.leftState x P =
            ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ := rfl
        have hright : sys.rightState x P =
            ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ := rfl
        rw [hleft, hright, hp]
        by_cases hA : movingLocalSupport value outside x <;>
          by_cases hB : movingFullSupport value outside l p XL <;>
          by_cases hC : movingFullSupport value outside r p XR
        all_goals dsimp only [x, p] at hA hB hC ⊢
        all_goals simp only [hA, hB, hC, and_true, and_false,
          ite_true, if_true, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero, star_zero]
        rfl
      · have hz₁ : recursiveTransferWeight sys (movingGuardedLeaf value outside F) cutg
            (n + 1) x t = 0 := by simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
          simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        rw [hz₁, hz₂]
        unfold movingSupportedWeight
        split_ifs <;> rfl

theorem movingFrequencySkeleton_frequencyTree (σ : Type*) (n : ℕ)
    (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).frequencyTree = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [movingFrequencySkeleton, MovingSlotData.frequencyTree, ih]
    rfl

theorem MovingSlotData.skeleton_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) :
    (movingFrequencySkeleton σ n T.frequencyTree).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r hl hr =>
    simp only [MovingSlotData.frequencyTree, movingFrequencySkeleton, frequencyProduct, hl, hr]

theorem MovingSlotData.rootData_regularSlots {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.regularSlots = T.regularSlots := by
  cases T <;> rfl

theorem MovingSlotData.rootData_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.frequencyProduct = T.frequencyProduct := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, frequencyProduct, skeleton_frequencyProduct]

theorem MovingSlotData.rootData_idempotent {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.rootData = T.rootData := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, movingFrequencySkeleton_frequencyTree]

theorem movingLocalSupport_rootData {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) :
    movingLocalSupport value outside ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ ↔
      movingLocalSupport value outside x := by
  simp only [movingLocalSupport, MovingSlotData.currentSlots, movingLocalGiantUnits,
    MovingSlotData.rootData_regularSlots, MovingSlotData.rootData_frequencyProduct]

theorem movingLocalExtra_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingGuardedExtra value outside (movingLocalExtra E)) =
      movingGuardedExtra value outside (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingGuardedExtra, movingLocalSupport_rootData,
    MovingSlotData.rootData_idempotent]

/-- The sample expansion of the fully supported original coefficient. Every
sample retains its original weight, including samples whose support fails. -/
theorem movingSampledWeight_supported {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra E)) n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
        movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  unfold movingSampledWeight
  rw [movingLocalExtra_guarded]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedWeight_recursive value outside childBound pivotBound F (movingLocalExtra E)
    _ t (buildMovingSlotData_follows n t small bulk a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSlotCutoff_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E) x s v w =
      (x.compensation value : ℝ) * movingSlotCutoff value childBound pivotBound E x s v w := by
  unfold movingSlotCutoff movingCompensatedExtra
  split_ifs <;> simp only [mul_zero]

theorem MovingSlotState.compensation_rootData {σ : Type*} (value : σ → ℕ)
    (x : MovingSlotState σ) :
    (⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ : MovingSlotState σ).compensation value =
      x.compensation value := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingLocalExtra_compensated {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingCompensatedExtra value E) =
      movingCompensatedExtra value (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingCompensatedExtra, MovingSlotState.compensation_rootData]

/-- Each node contributes its newly sampled compensation exactly once,
including off-support samples where both sides vanish. -/
theorem movingRecursiveWeight_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t =
        (movingSampleProduct value a : ℂ) *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutc := movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)
  induction a generalizing XL XR with
  | leaf => simp only [movingSampleProduct, Nat.cast_one, one_mul, recursiveTransferWeight]
  | @node n a l r hl hr =>
    let x : MovingSlotState σ :=
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys F cutc n x t P hv,
        recursiveTransferWeight_node sys F cut n x t P hv]
      change (cutc x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.1 *
        star (recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.2) = _
      simp only [ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      rw [hl, hr]
      have hc : cutc x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
          (x.compensation value : ℝ) * cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) :=
        movingSlotCutoff_compensated value childBound pivotBound E x _ _ _
      rw [hc]
      simp only [movingSampleProduct, Complex.ofReal_mul, Complex.ofReal_natCast,
        Nat.cast_mul, star_mul, star_natCast]
      change _ = (x.compensation value : ℂ) * _ * _ * _
      simp only [sys, movingSlotSystem, MovingSlotState.child, x, buildMovingSlotData,
        ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      ring
    · have hz₁ : recursiveTransferWeight sys F cutc (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      rw [hz₁, hz₂, mul_zero]

theorem movingSupportedWeight_mul {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (c z : ℂ) :
    movingSupportedWeight value outside T XL XR (c * z) =
      c * movingSupportedWeight value outside T XL XR z := by
  unfold movingSupportedWeight
  split_ifs <;> simp only [mul_zero]

/-- Exact compensated prior times the supported coefficient with node
compensations removed. This is the scalar used by the pattern comparison. -/
theorem movingSampledWeight_compensated_supported {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
      n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n,
        (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) *
          movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
            (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
              (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
              ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  rw [movingSampledWeight_supported]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingLocalExtra_compensated, movingRecursiveWeight_compensated,
    movingSupportedWeight_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduledFrequencyRootEquiv_history (V : ℕ → ℕ) (n : ℕ)
    (t : ScheduledFrequencyIndex V n) :
    scheduledFrequencyHistory V n t =
      movingRootedFrequencyTree V n (scheduledFrequencyRootEquiv V n t).1.val
        (scheduledFrequencyRootEquiv V n t).2 := by
  cases n <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePrimeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact sample expansion inside the actual giant-prime averages -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexPrimeInterval_const_mul (q a : ℕ) (u v : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => c * F x) =
      c * complexPrimeInterval q a u v F := by
  unfold complexPrimeInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [mul_assoc, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MovingZeroFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero frequencies vanish in the original sampled histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem recursiveTransferWeight_nonzero_frequencies {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (hleaf : ∀ x, leaf x 0 = 0)
    (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n generalizing x with
  | zero =>
    intro s hs
    have hst : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro hz
    subst t
    exact ht (hleaf x)
  | succ n ih =>
    obtain ⟨P, hP, _, _⟩ := recursiveTransferWeight_nonzero_valid sys leaf cutoff _ x t ht
    rw [recursiveTransferWeight_node sys leaf cutoff n x t P hP] at ht
    have hL : recursiveTransferWeight sys leaf cutoff n (sys.leftState x P) t.2.1 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, mul_zero, zero_mul])
    have hR : recursiveTransferWeight sys leaf cutoff n (sys.rightState x P) t.2.2 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, star_zero, mul_zero])
    intro s hs
    simp only [allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact hP.root_ne_zero
    · exact ih _ _ hL s hs
    · exact ih _ _ hR s hs

theorem movingSupportedSampledWeight_zero_frequency {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (hF : ∀ x, F x 0 = 0)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR = 0 := by
  unfold movingSupportedSampledWeight movingSampledWeight
  apply Finset.sum_eq_zero
  intro a _
  suffices h : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound
        (movingLocalExtra
          (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))))
      n ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t = 0 by
    rw [h, mul_zero]
  by_contra hn
  apply hz
  apply recursiveTransferWeight_nonzero_frequencies _ _ _ _ n _ t hn
  intro x
  simp only [movingGuardedLeaf, hF, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularMultiplierIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal multiplier is the squared regular Fourier product -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalRegularMultiplier_eq_transform_norm {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (D : ℕ) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i))) g XL XR =
      ‖movingRegularTransform p (fun i x => if active i then g i x else 1)
        (D * XL * XR) s‖ ^ 2 := by
  rw [movingRegularTransform, norm_prod, ← Finset.prod_pow]
  unfold naturalRegularMultiplier
  apply Finset.prod_congr rfl
  intro i _
  cases ha : active i
  · simp only [Bool.false_eq_true, ite_false, if_false, norm_one, one_pow]
  · simp only [ite_true, if_true]
    congr 2
    simp only [div_eq_mul_inv, Nat.cast_mul]
    congr 2
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleDiagonalExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact sample expansion in the mixed prime/integer diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexIntegerInterval_const_mul (q a : ℕ) (u v G : ℝ)
    (c : ℂ) (F : ℝ → ℂ) :
    complexIntegerInterval q a u v G (fun x => c * F x) =
      c * complexIntegerInterval q a u v G F := by
  unfold complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact mul_assoc _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting only the selected bulk coordinates in the original law -/

namespace Ostmann
open scoped Classical BigOperators

/-- Only the selected coordinates need identical distributions. -/
theorem selectedBulkSample_prior {B J A : Type*} [Fintype B]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (y : B → A) :
    (∏ i, ν i (selectedBulkSample slot e y i)) = ∏ i, ν i (y i) := by
  have hpres (i : B) : ν i = ν ((selectedBulkPerm slot e).symm i) := by
    obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
    cases j with
    | inl j => simpa using hν j (e.symm j)
    | inr i => simp [i.property]
  calc
    _ = ∏ i, ν ((selectedBulkPerm slot e).symm i)
        (y ((selectedBulkPerm slot e).symm i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hpres i]
      rfl
    _ = _ := (selectedBulkPerm slot e).symm.prod_comp (fun i => ν i (y i))

theorem selectedBulkSample_sum {B J A : Type*} [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (F : (B → A) → ℂ) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F (selectedBulkSample slot e y)) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F y := by
  have h := (bulkArrayEquiv (A := A) (selectedBulkPerm slot e)).sum_comp
    (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * F y)
  change (∑ y, ((∏ i, ν i (selectedBulkSample slot e y i) : ℝ) : ℂ) *
    F (selectedBulkSample slot e y)) = _ at h
  simpa only [selectedBulkSample_prior slot e ν hν] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GroupedBulkSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk averaging inside the original product and frequency fibres -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkAverage_statistic {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (G W : (B → A) → ℂ)
    (hG : ∀ e y, G (selectedBulkSample slot e y) = G y) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y *
      mixedBulkSymmetrize n m slot (fun _ y _ _ => W y) 0 y 0 0) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W y := by
  have hc : (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W (selectedBulkSample slot e y)) =
        ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W y := by
    have h := selectedBulkSample_sum slot e ν hν (fun y => G y * W y)
    simpa only [hG, mul_assoc] using h
  unfold mixedBulkSymmetrize finiteFamilyAverage
  simp only [Finset.mul_sum]
  simp_rw [show ∀ (y : B → A) (e : Equiv.Perm (TreeLeafIndex n × Fin m)),
    ((∏ i, ν i (y i) : ℝ) : ℂ) * G y *
      ((Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ)⁻¹ *
        W (selectedBulkSample slot e⁻¹ y)) =
    (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℂ)⁻¹ *
      (((∏ i, ν i (y i) : ℝ) : ℂ) * G y * W (selectedBulkSample slot e⁻¹ y)) by intros; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- All pointwise cutoffs may remain inside the coefficient. Only the key
and the original independent bulk law are invariant under reassignment. -/
theorem groupedCoefficient_bulk_average {B A K : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (key : (B → A) → K) (hkey : ∀ e y, key (selectedBulkSample slot e y) = key y)
    (W : (B → A) → ℂ) (k : K) :
    groupedCoefficient key (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) *
      mixedBulkSymmetrize n m slot (fun _ y _ _ => W y) 0 y 0 0) k =
    groupedCoefficient key (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * W y) k := by
  have h := selectedBulkAverage_statistic n m slot ν hν
    (fun y => if key y = k then 1 else 0) W (fun e y => by rw [hkey e y])
  simpa only [groupedCoefficient, mul_ite, mul_one, mul_zero, ite_mul, zero_mul] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact smooth harmonic giant prior from (7.3) -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_nonneg (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (p : P) : 0 ≤ smoothGiantPrior P φ G p :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ _)) (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrimeRange_prime (G : ℝ) :
    ∀ p ∈ smoothGiantPrimeRange G, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantIntervalBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized giant prior and its complete logarithmic cell -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiant_nonzero_in_log_cell (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hφ : φ (Real.log p - G) ≠ 0) :
    p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊ := by
  have hh : |Real.log p - G| < 1 := by
    by_contra h
    exact hφ (hout _ (le_of_not_gt h))
  have hh' := abs_lt.mp hh
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
    exact (Real.lt_log_iff_exp_lt hp').mp (by linarith)
  · apply Nat.le_floor
    exact (Real.log_le_iff_le_exp hp').mp (by linarith)

/-- The finite support may include extra endpoints, but those have zero
smooth weight; every contributing prime lies in the complete cell. -/
theorem smoothGiant_unnormalized_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p ∈ smoothGiantPrimeRange G,
      (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) =
    complexPrimeInterval 1 0 (G - 1) (G + 1)
      (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  let Q := (Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊).filter Nat.Prime
  have hQP : Q ⊆ smoothGiantPrimeRange G := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hprime.pos, ?_⟩, hprime⟩
    have hu : (p : ℝ) ≤ Real.exp (G + 1) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans (Nat.floor_le (Real.exp_nonneg _))
    exact_mod_cast hu.trans (Nat.le_ceil (Real.exp (G + 1)))
  have hs := Finset.sum_subset (f := fun (p : ℕ) =>
    (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) hQP (fun p hp hn => by
    have hz : φ (Real.log p - G) = 0 := by
      by_contra hz
      apply hn
      exact Finset.mem_filter.mpr ⟨smoothGiant_nonzero_in_log_cell φ G hout p
        (smoothGiantPrimeRange_prime G p hp).pos hz, smoothGiantPrimeRange_prime G p hp⟩
    simp only [hz, Complex.ofReal_zero, zero_mul])
  rw [← hs]
  dsimp only [Q]
  rw [Finset.sum_filter]
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  simp only [Nat.modEq_one, and_true, Real.exp_log hp', Nat.floor_natCast]

/-- The normalizer is retained explicitly when the original giant law is
written as a prime logarithmic integral. -/
theorem smoothGiantPrior_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p : smoothGiantPrimeRange G,
      (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      complexPrimeInterval 1 0 (G - 1) (G + 1)
        (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  rw [← smoothGiant_unnormalized_interval φ G hout F, Finset.mul_sum]
  have he := Finset.sum_coe_sort (smoothGiantPrimeRange G) (fun p =>
    ((Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      ((φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smoothGiantPrior, Complex.ofReal_div, Complex.ofReal_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRootedSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact grouping of the two independent child frequency sums -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootedFrequencyTree_root (V : ℕ → ℕ) (n : ℕ) (s : ℤ)
    (a : MovingDescendantFrequencyIndex V n) :
    frequencyRoot n (movingRootedFrequencyTree V n s a) = s := by
  cases n <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeCoefficientNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete coefficient recursion at actual top primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyCoefficient_zero {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n 0 small bulk XL XR = 0 := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_eq_zero
  intro t _
  apply movingSupportedSampledWeight_zero_frequency value outside μ childBound pivotBound
    F _ hF n _ small bulk XL XR
  intro h
  apply h 0
  · cases n with
    | zero => exact List.mem_singleton_self _
    | succ n => exact List.mem_cons_self
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Current support inherited from the original summed coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_local {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullSupport value outside T XL XR) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  cases T with
  | leaf => exact h
  | node => exact ⟨h.1.1, h.2.1⟩

/-- A nonzero finite average contains a supported original sample. No
positivity, normalization, or conditioning of the prime prior is needed. -/
theorem movingSupportedSampledWeight_nonzero_support {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR ≠ 0) :
    ∃ a : MovingSampleSlots σ n,
      movingFullSupport value outside (buildMovingSlotData n t small bulk a) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingCompensatedAverage] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ht : movingSupportedSampleTerm value outside childBound pivotBound F E
      n t small bulk XL XR a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  unfold movingSupportedSampleTerm movingSupportedWeight at ht
  refine ⟨a, ?_⟩
  by_contra hs
  exact ht (ite_eq_right hs)

/-- The root sum still has the actual current pairwise support and both
root-frequency units. These are the only support facts needed to attach the
original coefficient to the full Fourier transfer. -/
theorem movingFrequencyCoefficient_nonzero_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s small bulk XL XR ≠ 0) :
    (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)).Pairwise Nat.Coprime ∧
      IsCoprime (XL : ℤ) s ∧ IsCoprime (XR : ℤ) s := by
  rw [movingFrequencyCoefficient] at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a, ha⟩ := movingSupportedSampledWeight_nonzero_support value outside μ childBound
    pivotBound F (movingOriginalNode value childBound pivotBound φ G) n
    (movingRootedFrequencyTree V n s t) small bulk XL XR ht
  let T := buildMovingSlotData n (movingRootedFrequencyTree V n s t) small bulk a
  have hlocal := movingFullSupport_local value outside T XL XR ha
  have hreg := buildMovingSlotData_regular_perm n (movingRootedFrequencyTree V n s t) small bulk a
  have hp : (T.currentSlots value XL XR ++ outside).Perm
      (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)) := by
    simpa only [MovingSlotData.currentSlots, List.cons_append] using
      (((hreg.map value).cons XR).cons XL).append_right outside
  have hpair := (hp.pairwise_iff (fun h => h.symm)).mp hlocal.1
  have hfreq : T.frequency = s := by
    rw [(buildMovingSlotData_follows n _ small bulk a).root, movingRootedFrequencyTree_root]
  have hL := ((T.frequencies_isCoprime (XL : ℤ)).mpr hlocal.2.1).root
  have hR := ((T.frequencies_isCoprime (XR : ℤ)).mpr hlocal.2.2.1).root
  exact ⟨hpair, hfreq ▸ hL, hfreq ▸ hR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegularSlot_card (n r m : ℕ) :
    Fintype.card (MovingRegularSlot n r m) = 2 ^ n * (r + m) := by
  simp only [MovingRegularSlot, Fintype.card_prod, card_treeLeafIndex, Fintype.card_sum,
    Fintype.card_fin]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged independent prime law under one template restoration -/

namespace Ostmann
open scoped Classical BigOperators

/-- This is literal finite Fubini; neither distinctness nor any history
support is conditioned into the prime law. -/
theorem movingReverseTemplate_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A,
        ((∏ i, ν (movingReverseTemplate n r m (.inl i)) (u i) : ℝ) : ℂ) *
        ∑ y : MovingRegularSlot n r m → A,
          ((∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i) : ℝ) : ℂ) *
          F (movingRestoreSample n r m u y) := by
  have hr := finite_prior_reindex (movingReverseTemplate n r m) ν F
  simp only [finite_univ_canonical] at hr ⊢
  rw [← hr]
  let e := Equiv.sumArrowEquivProdArrow (TreeLeafIndex n × Fin 4) (MovingRegularSlot n r m) A
  have he := e.symm.sum_comp (fun x =>
    ((∏ i, ν (movingReverseTemplate n r m i) (x i) : ℝ) : ℂ) *
      F (x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  have hs := Fintype.sum_prod_type (fun x :
      (TreeLeafIndex n × Fin 4 → A) × (MovingRegularSlot n r m → A) =>
    ((∏ i, ν (movingReverseTemplate n r m i) (e.symm x i) : ℝ) : ℂ) *
      F (e.symm x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hp := Fintype.prod_sum_type (fun i :
      (TreeLeafIndex n × Fin 4) ⊕ MovingRegularSlot n r m =>
    ν (movingReverseTemplate n r m i) (e.symm (u, y) i))
  simp only [finite_univ_canonical] at hp
  rw [hp]
  simp only [e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  change _ * F (movingRestoreSample n r m u y) = _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal regular template and its full Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

private theorem prime_pairwise_list_nodup (L : List ℕ) (hp : ∀ p ∈ L, p.Prime)
    (h : L.Pairwise Nat.Coprime) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons p L ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) ht⟩
    intro hmem
    have h1 : p = 1 := by simpa only [Nat.coprime_self] using hh p hmem
    exact (hp p List.mem_cons_self).ne_one h1

/-- The support of the actual coefficient forces every prime in the full
regular template to be distinct. -/
theorem movingTemplateCoefficient_nonzero_injective {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hprime : ∀ i, (value (y i)).Prime)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y XL XR ≠ 0) :
    Function.Injective (value ∘ y) := by
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound pivotBound V
    F φ G n s _ _ XL XR h).1
  have hr : ((movingTemplateSlotList n r m).map (value ∘ y) ++ outside).Pairwise Nat.Coprime := by
    simpa only [flattenMovingSlots_map, List.map_append, List.map_map, Function.comp_def,
      movingTemplateSlotList, List.tail_cons] using hs.tail.tail
  have hnd : ((movingTemplateSlotList n r m).map (value ∘ y)).Nodup := by
    apply prime_pairwise_list_nodup _ _ (List.pairwise_append.mp hr).1
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact hprime i
  intro i j hij
  exact List.inj_on_of_nodup_map hnd (mem_movingTemplateSlotList n r m i)
    (mem_movingTemplateSlotList n r m j) hij

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original pivot, compensation, and surviving slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- Reindexing changes neither the cofactor nor its local transform. -/
theorem movingRegularTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (g : ∀ j, ZMod (p j) → ℂ) (D : ℕ) (s : ℤ) :
    let _ : ∀ i, NeZero (p (e i)) := fun _i => inferInstance
    movingRegularTransform (fun i => p (e i)) (fun i => g (e i)) D s =
      movingRegularTransform p g D s := by
  dsimp only
  unfold movingRegularTransform
  simp_rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j))]
  exact e.prod_comp (fun j => g j ((s : ZMod (p j)) *
    ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

/-- The reindexing inserts precisely the same sampled compensation vector
which appears in the two child coefficients. -/
theorem movingTransferSlotEquiv_values {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) (XL XR : ℕ) :
    (fun i => Sum.elim (fun b => if b then XL else XR)
      (value ∘ movingRestoreSample n r m u y) (movingTransferSlotEquiv n r m i)) =
    Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ u))
      (Sum.elim (fun _ : Unit => XR) (value ∘ y)) := by
  funext i
  rcases i with ((j | j) | (j | j))
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inl j))) = value (u j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inr j))) = value (y j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateTransferSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer support derived from nonzero original template coefficients -/

namespace Ostmann
open scoped Classical BigOperators

private theorem indexed_coprime_of_list {I : Type*} (p : I → ℕ) (L : List I)
    (hcover : ∀ i, i ∈ L) (h : (L.map p).Pairwise Nat.Coprime) :
    Pairwise (fun i j => (p i).Coprime (p j)) := by
  have h' : L.Pairwise (fun i j => i ≠ j → (p i).Coprime (p j)) :=
    (List.pairwise_map.mp h).imp (fun {i j} hij (_ : i ≠ j) => hij)
  have hflip : L.Pairwise (flip (fun i j => i ≠ j → (p i).Coprime (p j))) :=
    h'.imp (fun {i j} hij (hji : j ≠ i) => (hij hji.symm).symm)
  intro i j hij
  exact h'.forall_of_forall_of_flip (fun a _ haa => (haa rfl).elim) hflip
    (hcover i) (hcover j) hij

/-- The complete current Fourier slots inherit pairwise and outside
coprimality directly from the support of their coefficient. -/
theorem movingTemplateCoefficient_transfer_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (q : Bool → ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y (q true) (q false) ≠ 0) :
    Pairwise (fun i j => (Sum.elim q (value ∘ y) i).Coprime (Sum.elim q (value ∘ y) j)) ∧
      ∀ i, outside.prod.Coprime (Sum.elim q (value ∘ y) i) := by
  let L : List (Bool ⊕ MovingRegularSlot n r m) :=
    [.inl true, .inl false] ++ (movingTemplateSlotList n r m).map Sum.inr
  let p := Sum.elim q (value ∘ y)
  have hcover : ∀ i, i ∈ L := by
    intro i
    cases i with
    | inl b => cases b <;> simp [L]
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr
        ⟨i, mem_movingTemplateSlotList n r m i, rfl⟩)
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound
    pivotBound V F φ G n s _ _ (q true) (q false) h).1
  have hs' : (L.map p ++ outside).Pairwise Nat.Coprime := by
    simpa only [L, p, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.cons_append, List.nil_append, Sum.elim_inl, Sum.elim_inr,
      movingTemplateSlotList, flattenMovingSlots_map, Function.comp_def] using hs
  obtain ⟨hp, _, ho⟩ := List.pairwise_append.mp hs'
  refine ⟨indexed_coprime_of_list p L hcover hp, ?_⟩
  intro i
  apply Nat.coprime_list_prod_left_iff.mpr
  intro d hd
  exact (ho (p i) (List.mem_map.mpr ⟨i, hcover i, rfl⟩) d hd).symm

/-- Restrict the full support to the two pieces of a restored child.
This supplies the exact support fields of the giant transfer. -/
theorem movingTemplateCoefficient_restored_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (y : MovingRegularSlot n r m → σ)
    (p X : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u y) p X ≠ 0) :
    let Q := Sum.elim (fun _ : Unit => p) (value ∘ u)
    let L := Sum.elim (fun _ : Unit => X) (value ∘ y)
    Pairwise (fun i j => (Q i).Coprime (Q j)) ∧
      (∀ i, outside.prod.Coprime (Q i)) ∧
      Pairwise (fun i j => (L i).Coprime (L j)) ∧
      (∏ i, L i).Coprime (∏ i, Q i) ∧
      (∀ i, outside.prod.Coprime (L i)) := by
  let q : Bool → ℕ := fun b => if b then p else X
  have hs := movingTemplateCoefficient_transfer_support value outside μ childBound pivotBound V
    F φ G n (4 + r) m s (movingRestoreSample n r m u y) q h
  have he := movingTransferSlotEquiv_values value n r m u y p X
  let f := Sum.elim (Sum.elim (fun _ : Unit => p) (value ∘ u))
    (Sum.elim (fun _ : Unit => X) (value ∘ y))
  have hp : Pairwise (fun i j => (f i).Coprime (f j)) := by
    intro i j hij
    have hx := hs.1 ((movingTransferSlotEquiv n r m).injective.ne hij)
    change (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m i)).Coprime
      (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m j)) at hx
    rw [congrFun he i, congrFun he j] at hx
    exact hx
  have hd : ∀ i, outside.prod.Coprime (f i) := by
    intro i
    have hx := hs.2 (movingTransferSlotEquiv n r m i)
    rw [congrFun he i] at hx
    exact hx
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp (fun he => hij (Sum.inl.inj he))
  · intro i
    exact hd (.inl i)
  · intro i j hij
    exact hp (fun he => hij (Sum.inr.inj he))
  · apply Nat.coprime_prod_left_iff.mpr
    intro i _
    apply Nat.coprime_prod_right_iff.mpr
    intro j _
    exact hp (Sum.inr_ne_inl)
  · intro i
    exact hd (.inr i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual diagonal and integer off-diagonal of a prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingOneGiant_transform_tagged {I : Type*} [Fintype I]
    (X : ℕ) (p : I → ℕ) [NeZero X] [∀ i, NeZero (p i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (movingOneGiantModuli X p)
      (movingOneGiantFactors X p greg ggiant favorable) D s =
    movingTaggedTransform (movingOneGiantModuli X p)
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicProductFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product fibres on the actual regular-slot index type -/

namespace Ostmann
open scoped Classical BigOperators

theorem card_indexed_distinct_prime_product_fiber {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) :
    ((Finset.univ : Finset (I → P)).filter
      (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)).card ≤
        (Fintype.card I).factorial := by
  let S := (Finset.univ : Finset (I → P)).filter
    (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hx' := (Finset.mem_filter.mp hx).2
    have hex (y : S) : ∃ e : Equiv.Perm I, ∀ i, (x i : ℕ) = (y.val (e i) : ℕ) := by
      have hy := (Finset.mem_filter.mp y.property).2
      obtain ⟨e, he, _⟩ := prime_product_matching_exists_unique
        (fun i => (x i : ℕ)) (fun i => (y.val i : ℕ))
        (fun i => hP _ (x i).property) (fun i => hP _ (y.val i).property)
        (fun i j h => hx'.1 (Subtype.ext h))
        (fun i j h => hy.1 (Subtype.ext h)) (hx'.2.trans hy.2.symm)
      exact ⟨e, he⟩
    let f : S → Equiv.Perm I := fun y => Classical.choose (hex y)
    have hf (y : S) (i : I) : (x i : ℕ) = (y.val (f y i) : ℕ) :=
      Classical.choose_spec (hex y) i
    have hinj : Function.Injective f := by
      intro y z he
      apply Subtype.ext
      funext j
      obtain ⟨i, rfl⟩ := (f y).surjective j
      apply Subtype.ext
      rw [← hf y i, he]
      exact hf z i
    have hc := Fintype.card_le_of_injective f hinj
    simpa only [S, Fintype.card_coe, Fintype.card_perm] using hc
  · change S.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _

theorem indexed_harmonic_product_point_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) (Q : I → Finset ℕ) (x : I → P) :
    (∏ i, primeSubsetPrior P (Q i) (x i)) ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ := by
  have hi (i : I) : primeSubsetPrior P (Q i) (x i) ≤
      (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x i : ℝ)⁻¹ := by
    unfold primeSubsetPrior
    split_ifs
    · rw [div_eq_mul_inv, mul_comm]
    · positivity
  have h : (∏ i, primeSubsetPrior P (Q i) (x i)) ≤
      ∏ i, ((∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x i : ℝ)⁻¹) :=
    Finset.prod_le_prod (fun i _ => primeSubsetPrior_nonneg P (Q i) (x i))
    (fun i _ => hi i)
  simpa only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] using h

/-- Reindexing the regular roles changes neither the original harmonic
normalizers nor the factorial cost of a distinct-prime product fibre. -/
theorem indexed_harmonic_distinct_product_mass {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (S : Finset (I → P)) (hS : ∀ x ∈ S, Function.Injective x) (M : ℕ) :
    (∑ x ∈ S.filter (fun x : I → P => (∏ i, (x i : ℕ)) = M),
      (∏ i, primeSubsetPrior P (Q i) (x i))) ≤
      ((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
  let T := S.filter (fun x : I → P => (∏ i, (x i : ℕ)) = M)
  have hc : T.card ≤ (Fintype.card I).factorial := by
    apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (I → P)).filter
      (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M) from ?_)).trans
      (card_indexed_distinct_prime_product_fiber P hP M)
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hxS, hxM⟩
  calc
    _ ≤ ∑ _x ∈ T, (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2
      simpa only [he] using indexed_harmonic_product_point_bound P Q x
    _ = (T.card : ℝ) * ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hc' : (T.card : ℝ) ≤ (Fintype.card I).factorial := by exact_mod_cast hc
      calc
        _ ≤ ((Fintype.card I).factorial : ℝ) *
            ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
        _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicKeyMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original harmonic mass of a giant/product/frequency fibre -/

namespace Ostmann
open scoped Classical BigOperators

/-- On a fixed giant and frequency, the regular tuple determines the row.
Zero rows are discarded exactly; the other rows retain their original mass. -/
theorem indexed_harmonic_key_mass {A I : Type*} [Fintype A] [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (X : A → ℕ) (y : A → I → P) (v : A → ℤ) (μ : A → ℝ)
    (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hrow : ∀ a b, X a = X b → y a = y b → v a = v b → a = b)
    (hinj : ∀ a, μ a ≠ 0 → Function.Injective (y a))
    (hpoint : ∀ a, μ a ≠ 0 →
      μ a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i))
    (k : ℕ × ℕ × ℤ) :
    (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ a else 0) ≤
      g k.1 * ((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹ := by
  let S := Finset.univ.filter (fun a =>
    (X a, (∏ i, (y a i : ℕ)), v a) = k ∧ μ a ≠ 0)
  let T := (Finset.univ : Finset (I → P)).filter
    (fun z : I → P => Function.Injective z)
  let U := T.filter (fun z : I → P => (∏ i, (z i : ℕ)) = k.2.1)
  have hs : (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ a else 0) =
      ∑ a ∈ S, μ a := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hk : (X a, (∏ i, (y a i : ℕ)), v a) = k <;>
      by_cases hm : μ a = 0 <;> simp [hk, hm]
  have hkey a (ha : a ∈ S) :
      X a = k.1 ∧ (∏ i, (y a i : ℕ)) = k.2.1 ∧ v a = k.2.2 := by
    have h := (Finset.mem_filter.mp ha).2.1
    simpa only [Prod.ext_iff] using h
  have hm a (ha : a ∈ S) : μ a ≠ 0 := (Finset.mem_filter.mp ha).2.2
  have hmap : Set.InjOn y S := by
    intro a ha b hb hab
    exact hrow a b ((hkey a ha).1.trans (hkey b hb).1.symm) hab
      ((hkey a ha).2.2.trans (hkey b hb).2.2.symm)
  have hmem : Set.MapsTo y S U := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hinj a (hm a ha)⟩, (hkey a ha).2.1⟩
  calc
    _ = ∑ a ∈ S, μ a := hs
    _ ≤ ∑ z ∈ U, g k.1 * ∏ i, primeSubsetPrior P (Q i) (z i) := by
      apply OAI.sum_le_sum_of_injOn y hmap (by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact hmem ha)
      · intro a ha
        simpa only [(hkey a ha).1] using hpoint a (hm a ha)
      · intro z _ _
        exact mul_nonneg (hg _) (Finset.prod_nonneg
          (fun i _ => primeSubsetPrior_nonneg P (Q i) (z i)))
    _ = g k.1 * ∑ z ∈ U, ∏ i, primeSubsetPrior P (Q i) (z i) := by
      rw [Finset.mul_sum]
    _ ≤ g k.1 * (((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (hg _)
      exact indexed_harmonic_distinct_product_mass P hP Q T
        (fun z hz => (Finset.mem_filter.mp hz).2) k.2.1
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOneGiantDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the single giant on a product/frequency diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- A prime in the giant range cannot be exchanged with any of the
regular primes when two complete products agree. -/
theorem oneGiant_product_eq {J : Type*} [Fintype J]
    (X Y : ℕ) (hX : X.Prime) (hY : Y.Prime)
    (p q : J → ℕ) (hq : ∀ i, (q i).Prime)
    (hsep : ∀ i, X ≠ q i)
    (he : X * ∏ i, p i = Y * ∏ i, q i) :
    X = Y ∧ (∏ i, p i) = ∏ i, q i := by
  have hd : X ∣ Y * ∏ i, q i := he ▸ Nat.dvd_mul_right X (∏ i, p i)
  have hXY : X ∣ Y := by
    rcases hX.dvd_mul.mp hd with h | h
    · exact h
    · obtain ⟨i, hi⟩ := prime_dvd_prime_product q hq X hX h
      exact (hsep i hi).elim
  have h := (Nat.dvd_prime hY).mp hXY
  have hEq : X = Y := h.resolve_left hX.ne_one
  exact ⟨hEq, Nat.eq_of_mul_eq_mul_left hX.pos (hEq ▸ he)⟩

local instance oneGiantDiagonalSum_neZero_r72408e_1 {J I : Type*} (Q : J → ℕ) (L : I → ℕ)
    [∀ j, NeZero (Q j)] [∀ i, NeZero (L i)] (i : J ⊕ I) :
    NeZero (Sum.elim Q L i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance
/-- The full one-giant Fourier factor splits with its exact CRT cofactor.
The regular part is expressed only by its prime product. -/
theorem movingOneGiant_transform_product {J : Type*} [Fintype J]
    (X : ℕ) [Fact X.Prime] (p : J → ℕ) [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : ℤ) :
    movingRegularTransform (movingOneGiantModuli X p)
        (movingOneGiantFactors X p greg ggiant favorable) D v =
      (if favorable X then
        complexUnitPhase (ggiant X ((v : ZMod X) * ((D * ∏ i, p i : ℕ) : ZMod X)⁻¹))
       else 0) * primeProductTransform greg (D * X) (∏ i, p i) v := by
  calc
    _ = movingRegularTransform (fun _ : Unit => X)
        (fun _ t => if favorable X then complexUnitPhase (ggiant X t) else 0)
        (D * ∏ i, p i) v *
        movingRegularTransform p (fun j => greg (p j)) (D * ∏ _ : Unit, X) v := by
      convert moving_regular_transform_split (fun _ : Unit => X) p
        (fun _ t => if favorable X then complexUnitPhase (ggiant X t) else 0)
        (fun j => greg (p j)) D v using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := by
      rw [movingRegularTransform_eq_primeProduct p hp]
      simp only [movingRegularTransform, tupleCofactor, Finset.univ_unique,
        Finset.erase_singleton, Finset.prod_empty, Finset.prod_singleton, mul_one]

/-- The surviving giant is constant on every supported diagonal fibre.
Its unit phase can therefore be removed after grouping; the regular
prime-product transform and the original grouped coefficient remain. -/
theorem movingOneGiant_pivot_diagonal_le {A J : Type*} [Fintype A] [Fintype J]
    (X : A → ℕ) [∀ a, Fact (X a).Prime]
    (p : A → J → ℕ) [∀ a i, Fact (p a i).Prime]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : A → ℤ) (W : A → ℂ)
    (hinj : ∀ a, W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, W a ≠ 0 → ∀ i, (v a).natAbs < p a i)
    (hsep : ∀ a b, W a ≠ 0 → W b ≠ 0 → ∀ i, X a ≠ p b i) :
    (pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a))).re ≤
    ∑ k ∈ Finset.univ.image (fun a => (X a, (∏ i, p a i), v a)),
      ‖primeProductTransform greg (D * k.1) k.2.1 k.2.2‖ ^ 2 *
        ‖groupedCoefficient (fun a => (X a, (∏ i, p a i), v a)) W k‖ ^ 2 := by
  let key := fun a => (X a, (∏ i, p a i), v a)
  let phase := fun k : ℕ × ℕ × ℤ =>
    if favorable k.1 then
      complexUnitPhase (ggiant k.1
        ((k.2.2 : ZMod k.1) * ((D * k.2.1 : ℕ) : ZMod k.1)⁻¹))
    else 0
  let regular := fun k : ℕ × ℕ × ℤ => primeProductTransform greg (D * k.1) k.2.1 k.2.2
  have hphase (k : ℕ × ℕ × ℤ) : ‖phase k‖ ≤ 1 := by
    dsimp only [phase]
    split_ifs
    · exact complexUnitPhase_norm_le _
    · simp only [norm_zero, zero_le_one]
  have hsmall a (ha : W a ≠ 0) q (hq : q.Prime) (hd : q ∣ X a * ∏ i, p a i) :
      (v a).natAbs < q := by
    rcases hq.dvd_mul.mp hd with hd | hd
    · have he := (Nat.dvd_prime (Fact.out : (X a).Prime)).mp hd
      rw [he.resolve_left hq.ne_one]
      exact hvg a ha
    · obtain ⟨i, rfl⟩ := prime_dvd_prime_product (p a) (fun i => Fact.out) q hq hd
      exact hvr a ha i
  have he : pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a)) =
      ∑ a, ∑ b, if key a = key b then
        (W a * (phase (key a) * regular (key a))) *
          conj (W b * (phase (key b) * regular (key b))) else 0 := by
    unfold pivotDiagonal
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ha : W a = 0
    · simp only [ha, zero_mul, ite_self]
    by_cases hb : W b = 0
    · simp only [hb, zero_mul, map_zero, mul_zero, ite_self]
    have hz := pivot_zero_numerator_iff (X a * ∏ i, p a i) (X b * ∏ i, p b i)
      (Nat.mul_pos (Fact.out : (X a).Prime).pos
        (Finset.prod_pos (fun i _ => (Fact.out : (p a i).Prime).pos)))
      (v a) (v b) (hv a ha) (hv b hb) (hsmall a ha) (hsmall b hb)
    have hk : ((X a * ∏ i, p a i) = X b * ∏ i, p b i) ∧ v a = v b ↔ key a = key b := by
      constructor
      · rintro ⟨hp, hv⟩
        obtain ⟨hX, hR⟩ := oneGiant_product_eq (X a) (X b) Fact.out Fact.out
          (p a) (p b) (fun i => Fact.out) (hsep a b ha hb) hp
        exact Prod.ext hX (Prod.ext hR hv)
      · intro h
        have h' : X a = X b ∧ (∏ i, p a i) = ∏ i, p b i ∧ v a = v b := by
          simpa only [key, Prod.mk.injEq] using h
        exact ⟨by rw [h'.1, h'.2.1], h'.2.2⟩
    simp only [hz.trans hk]
    rw [movingOneGiant_transform_product (X a) (p a) (hinj a ha),
      movingOneGiant_transform_product (X b) (p b) (hinj b hb)]
  rw [he, finite_diagonal_common_transform key W (fun k => phase k * regular k)]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (hphase k))

/-- Cauchy on the identified fibre charges exactly its original prior mass.
There is no extra frequency cardinality or bound on each giant factor before
the diagonal has been grouped. -/
theorem movingOneGiant_weighted_pivot_diagonal_le {A J : Type*} [Fintype A] [Fintype J]
    (X : A → ℕ) [∀ a, Fact (X a).Prime]
    (p : A → J → ℕ) [∀ a i, Fact (p a i).Prime]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : A → ℤ) (μ : A → ℝ) (W : A → ℂ) (θ : ℕ × ℕ × ℤ → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, (μ a : ℂ) * W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < p a i)
    (hsep : ∀ a b, (μ a : ℂ) * W a ≠ 0 → (μ b : ℂ) * W b ≠ 0 → ∀ i, X a ≠ p b i)
    (hmass : ∀ k, (∑ a, if (X a, (∏ i, p a i), v a) = k then μ a else 0) ≤ θ k) :
    (pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => (μ a : ℂ) * W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a))).re ≤
    ∑ a, μ a * θ (X a, (∏ i, p a i), v a) *
      ‖W a * primeProductTransform greg (D * X a) (∏ i, p a i) (v a)‖ ^ 2 := by
  exact (movingOneGiant_pivot_diagonal_le X p greg ggiant favorable D v
    (fun a => (μ a : ℂ) * W a) hinj hv hvg hvr hsep).trans
    (finite_grouped_weighted_energy_le (fun a => (X a, (∏ i, p a i), v a)) μ W
      (fun k => primeProductTransform greg (D * k.1) k.2.1 k.2.2) θ hμ hmass)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-giant diagonal with its original harmonic mass -/

namespace Ostmann
open scoped Classical BigOperators

/-- Distinctness is forced by the coefficient, rather than imposed on the
sampling law. The harmonic fibre estimate therefore applies without changing
either the original diagonal or its single-branch energy. -/
theorem movingOneGiant_harmonic_diagonal_le {A I : Type*} [Fintype A] [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → I → P) (v : A → ℤ) (μ : A → ℝ) (W : A → ℂ)
    (hμ : ∀ a, 0 ≤ μ a) (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hrow : ∀ a b, X a = X b → y a = y b → v a = v b → a = b)
    (hpoint : ∀ a, μ a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i))
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (y a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, (μ a : ℂ) * W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < (y a i : ℕ))
    (hsep : ∀ a b, (μ a : ℂ) * W a ≠ 0 → (μ b : ℂ) * W b ≠ 0 →
      ∀ i, X a ≠ (y b i : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (μ a : ℂ) * W a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, μ a * θ (X a, (∏ i, (y a i : ℕ)), v a) *
        ‖W a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
  let μ' := fun a => if Function.Injective (y a) then μ a else 0
  let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
    (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
  have hμ' a : 0 ≤ μ' a := by
    dsimp only [μ']
    split_ifs
    · exact hμ a
    · exact le_rfl
  have he a : (μ' a : ℂ) * W a = (μ a : ℂ) * W a := by
    by_cases hi : Function.Injective (y a)
    · simp only [μ', ite_eq_left hi]
    · have hz : (μ a : ℂ) * W a = 0 := by
        by_contra h
        exact hi (hinj a h)
      simp only [μ', ite_eq_right hi, Complex.ofReal_zero, zero_mul, hz]
  have hmass k : (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ' a else 0) ≤ θ k := by
    apply indexed_harmonic_key_mass P hP Q X y v μ' g hg hrow
    · intro a ha
      by_contra hi
      simp only [μ', ite_eq_right hi, ne_eq, not_true_eq_false] at ha
    · intro a _
      by_cases hi : Function.Injective (y a)
      · simpa only [μ', ite_eq_left hi] using hpoint a
      · simp only [μ', ite_eq_right hi]
        exact mul_nonneg (hg _) (Finset.prod_nonneg
          (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have ht := movingOneGiant_weighted_pivot_diagonal_le X (fun a i => (y a i : ℕ))
    greg ggiant favorable D v μ' W θ hμ'
    (fun a ha i j hij => hinj a (by simpa only [he] using ha) (Subtype.ext hij))
    (fun a ha => hv a (by simpa only [he] using ha))
    (fun a ha => hvg a (by simpa only [he] using ha))
    (fun a ha => hvr a (by simpa only [he] using ha))
    (fun a b ha hb => hsep a b (by simpa only [he] using ha) (by simpa only [he] using hb)) hmass
  simp only [he] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : Function.Injective (y a)
  · simp only [μ', ite_eq_left hi, θ]
  · have hz : (μ a : ℂ) * W a = 0 := by
      by_contra h
      exact hi (hinj a h)
    rcases mul_eq_zero.mp hz with hm | hW
    · have hm' : μ a = 0 := by exact_mod_cast hm
      simp only [μ', ite_eq_right hi, hm', zero_mul]
    · simp only [μ', ite_eq_right hi, hW, zero_mul, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfListWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

theorem initialLogSumWeight_nonneg {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    0 ≤ initialLogSumWeight value c x := logCellProfile_nonneg _

theorem initialLogSumWeight_le_one {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    initialLogSumWeight value c x ≤ 1 := logCellProfile_le_one _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmallProductLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the actual small-cell contribution to the regular modulus -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_small_product_lower {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (y : MovingRegularSlot n r m → A)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) :
    Real.exp (∑ j, lower j) ≤
      ((∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2)) : ℕ) : ℝ) := by
  rw [Real.exp_sum, Nat.cast_prod]
  exact Finset.prod_le_prod (fun j _ => Real.exp_nonneg _) (fun j _ => hlower j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullHarmonicCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterpart cost retaining every actual small-cell endpoint -/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_harmonic_full_counterpart_le (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (cg Gmin totalLower : ℝ)
    (X : ℕ) (y : MovingRegularSlot n r m → ℕ)
    (hX : Real.exp Gmin ≤ (X : ℝ))
    (hy : Real.exp (totalLower) ≤ ((∏ i, y i : ℕ) : ℝ)) :
    (Real.exp cg / X) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, y i : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - totalLower) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  let K := ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
    (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
      (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)))))
  have hp : 0 < Real.exp Gmin * Real.exp (totalLower) := by positivity
  have hden : Real.exp Gmin * Real.exp (totalLower) ≤
      (X : ℝ) * ((∏ i, y i : ℕ) : ℝ) :=
    mul_le_mul hX hy (Real.exp_nonneg _) (Nat.cast_nonneg _)
  calc
    _ = (Real.exp cg / ((X : ℝ) * ((∏ i, y i : ℕ) : ℝ))) * K := by
      dsimp only [K]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (Real.exp cg / (Real.exp Gmin * Real.exp (totalLower))) * K :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (Real.exp_nonneg _) hp hden) hK
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_sub]
      rw [show cg - (Gmin + totalLower) =
        cg - Gmin - totalLower by ring]
      dsimp only [K]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero bulk averages inherit the original support of one assignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedBulkSymmetrize_ne_zero {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (s : ℤ) (y : B → A) (x z : ℝ)
    (h : mixedBulkSymmetrize n m slot F s y x z ≠ 0) :
    ∃ e : Equiv.Perm (TreeLeafIndex n × Fin m), F s (selectedBulkSample slot e y) x z ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp only [mixedBulkSymmetrize, finiteFamilyAverage, hn, Finset.sum_const_zero, mul_zero]

theorem selectedBulkSample_injective_iff {B J A C : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (value : A → C) (y : B → A) :
    Function.Injective (value ∘ selectedBulkSample slot e y) ↔ Function.Injective (value ∘ y) := by
  let E := selectedBulkPerm slot e
  constructor
  · intro h i j hij
    apply E.injective
    apply h
    simpa only [Function.comp_apply, selectedBulkSample, E, Equiv.symm_apply_apply] using hij
  · intro h i j hij
    exact E.symm.injective (h hij)

theorem selectedBulkSample_template_small {A : Type*} (n r m : ℕ)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : MovingRegularSlot n r m → A)
    (j : TreeLeafIndex n × Fin r) :
    selectedBulkSample (movingTemplateBulk n r m) e y (j.1, .inl j.2) = y (j.1, .inl j.2) := by
  apply selectedBulkSample_nonbulk
  rintro ⟨i, hi⟩
  have he := congrArg (fun a : MovingRegularSlot n r m => a.2) hi
  cases he

theorem movingRestoreSample_bulk_action {A : Type*} (n r m : ℕ)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    selectedBulkSample (movingTemplateBulk n (4 + r) m) e (movingRestoreSample n r m u y) =
      movingRestoreSample n r m u (selectedBulkSample (movingTemplateBulk n r m) e y) := by
  funext i
  obtain ⟨j, a⟩ := i
  cases a with
  | inl a =>
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · calc
        _ = movingRestoreSample n r m u y (j, .inl (a.castAdd r)) :=
          selectedBulkSample_template_small n (4 + r) m e _ (j, a.castAdd r)
        _ = u (j, a) := movingRestoreSample_compensation n r m u y (j, a)
        _ = _ := (movingRestoreSample_compensation n r m u
          (selectedBulkSample (movingTemplateBulk n r m) e y) (j, a)).symm
    · calc
        _ = movingRestoreSample n r m u y (j, .inl (a.natAdd 4)) :=
          selectedBulkSample_template_small n (4 + r) m e _ (j, a.natAdd 4)
        _ = y (j, .inl a) := movingRestoreSample_small n r m u y j a
        _ = selectedBulkSample (movingTemplateBulk n r m) e y (j, .inl a) :=
          (selectedBulkSample_template_small n r m e y (j, a)).symm
        _ = _ := (movingRestoreSample_small n r m u
          (selectedBulkSample (movingTemplateBulk n r m) e y) j a).symm
  | inr a =>
    change selectedBulkSample (movingTemplateBulk n (4 + r) m) e (movingRestoreSample n r m u y)
      (movingTemplateBulk n (4 + r) m (j, a)) =
      movingRestoreSample n r m u (selectedBulkSample (movingTemplateBulk n r m) e y)
        (movingTemplateBulk n (4 + r) m (j, a))
    rw [selectedBulkSample_bulk, movingRestoreSample_bulk, movingRestoreSample_bulk,
      selectedBulkSample_bulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedProductLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full harmonic denominator survives bulk symmetrization -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkSample_prod {B J A M : Type*} [Fintype B] [CommMonoid M]
    (slot : J ↪ B) (e : Equiv.Perm J) (value : A → M) (y : B → A) :
    (∏ i, value (selectedBulkSample slot e y i)) = ∏ i, value (y i) := by
  exact (selectedBulkPerm slot e).symm.prod_comp (fun i => value (y i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGroupedBulkAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the regular bulk inside the full giant and frequency fibre -/

namespace Ostmann
open scoped Classical BigOperators

theorem grouped_three_bulk_average {B A X S K : Type*}
    [Fintype B] [Fintype A] [Fintype X] [Fintype S]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k)) (ρ : X → ℝ)
    (key : X → (B → A) → S → K)
    (hkey : ∀ x s e y, key x (selectedBulkSample slot e y) s = key x y s)
    (W : X → (B → A) → S → ℂ) (k : K) :
    groupedCoefficient (fun a : X × ((B → A) × S) => key a.1 a.2.1 a.2.2)
      (fun a => ((ρ a.1 * ∏ i, ν i (a.2.1 i) : ℝ) : ℂ) *
        mixedBulkSymmetrize n m slot (fun _ y _ _ => W a.1 y a.2.2) 0 a.2.1 0 0) k =
    groupedCoefficient (fun a : X × ((B → A) × S) => key a.1 a.2.1 a.2.2)
      (fun a => ((ρ a.1 * ∏ i, ν i (a.2.1 i) : ℝ) : ℂ) * W a.1 a.2.1 a.2.2) k := by
  unfold groupedCoefficient
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun y s => if key x y s = k then _ else 0)]
  apply Finset.sum_congr rfl
  intro s _
  have h := groupedCoefficient_bulk_average n m slot ν hν (fun y => key x y s)
    (hkey x s) (fun y => W x y s) k
  have hh := congrArg (fun z : ℂ => (ρ x : ℂ) * z) h
  simpa only [groupedCoefficient, Complex.ofReal_mul, Finset.mul_sum, mul_ite,
    mul_zero, mul_assoc] using hh

theorem movingAmplitude_grouped_bulk_average
    (P Pg : Finset ℕ) (n r m : ℕ) (V : ℕ → ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ j k : TreeLeafIndex n × Fin m,
      ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (W : MovingAmplitudeIndex P Pg n r m V → ℂ) (k : ℕ × ℕ × ℤ) :
    groupedCoefficient
      (fun a : MovingAmplitudeIndex P Pg n r m V => ((a.1 : ℕ), (∏ i, (a.2.1 i : ℕ)), a.2.2.val))
      (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) *
        mixedBulkSymmetrize n m (movingTemplateBulk n r m)
          (fun _ y _ _ => W (a.1, y, a.2.2)) 0 a.2.1 0 0) k =
    groupedCoefficient
      (fun a : MovingAmplitudeIndex P Pg n r m V => ((a.1 : ℕ), (∏ i, (a.2.1 i : ℕ)), a.2.2.val))
      (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) * W a) k := by
  have hkey (x : Pg) (s : transferFrequencyRange (V n))
      (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : MovingRegularSlot n r m → P) :
      ((x : ℕ), (∏ i, (selectedBulkSample (A := P) (movingTemplateBulk n r m) e y i : ℕ)), s.val) =
        ((x : ℕ), (∏ i, (y i : ℕ)), s.val) := by
    exact Prod.ext rfl (Prod.ext
      ((selectedBulkPerm (movingTemplateBulk n r m) e).symm.prod_comp (fun i => (y i : ℕ))) rfl)
  have h := grouped_three_bulk_average
    (B := MovingRegularSlot n r m) (A := P) (X := Pg)
    (S := transferFrequencyRange (V n)) (K := ℕ × ℕ × ℤ)
    n m (movingTemplateBulk n r m) ν hν ρ
    (fun x y s => ((x : ℕ), (∏ i, (y i : ℕ)), s.val)) hkey
    (fun x y s => W (x, y, s)) k
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [movingAmplitudePrior, groupedCoefficient, MovingAmplitudeIndex, finite_univ_canonical, Prod.eta])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicGroupedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping and bulk averaging precede the harmonic Cauchy estimate -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingOneGiant_harmonic_grouped_diagonal_le {A I : Type*} [Fintype A] [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → I → P) (v : A → ℤ) (μ : A → ℝ) (W Wnew : A → ℂ)
    (hμ : ∀ a, 0 ≤ μ a) (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hrow : ∀ a b, X a = X b → y a = y b → v a = v b → a = b)
    (hpoint : ∀ a, μ a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i))
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (y a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, (μ a : ℂ) * W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < (y a i : ℕ))
    (hsep : ∀ a b, (μ a : ℂ) * W a ≠ 0 → (μ b : ℂ) * W b ≠ 0 →
      ∀ i, X a ≠ (y b i : ℕ))
    (hgroup : ∀ k : ℕ × ℕ × ℤ,
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (μ a : ℂ) * W a) k =
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (μ a : ℂ) * Wnew a) k)
    (hnewinj : ∀ a, (μ a : ℂ) * Wnew a ≠ 0 → Function.Injective (y a))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (μ a : ℂ) * W a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, μ a * θ (X a, (∏ i, (y a i : ℕ)), v a) *
        ‖Wnew a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
  let μ' := fun a => if Function.Injective (y a) then μ a else 0
  let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
    (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
  have hμ' a : 0 ≤ μ' a := by
    dsimp only [μ']
    split_ifs
    · exact hμ a
    · exact le_rfl
  have he a : (μ' a : ℂ) * Wnew a = (μ a : ℂ) * Wnew a := by
    by_cases hi : Function.Injective (y a)
    · simp only [μ', ite_eq_left hi]
    · have hz : (μ a : ℂ) * Wnew a = 0 := by
        by_contra h
        exact hi (hnewinj a h)
      simp only [μ', ite_eq_right hi, Complex.ofReal_zero, zero_mul, hz]
  have hmass k : (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ' a else 0) ≤ θ k := by
    apply indexed_harmonic_key_mass P hP Q X y v μ' g hg hrow
    · intro a ha
      by_contra hi
      simp only [μ', ite_eq_right hi, ne_eq, not_true_eq_false] at ha
    · intro a _
      by_cases hi : Function.Injective (y a)
      · simpa only [μ', ite_eq_left hi] using hpoint a
      · simp only [μ', ite_eq_right hi]
        exact mul_nonneg (hg _) (Finset.prod_nonneg
          (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have hd := movingOneGiant_pivot_diagonal_le X (fun a i => (y a i : ℕ))
    greg ggiant favorable D v (fun a => (μ a : ℂ) * W a)
    (fun a ha i j hij => hinj a ha (Subtype.ext hij)) hv hvg hvr hsep
  have ht := finite_grouped_weighted_energy_le
    (fun a => (X a, (∏ i, (y a i : ℕ)), v a)) μ' Wnew
    (fun k => primeProductTransform greg (D * k.1) k.2.1 k.2.2) θ hμ' hmass
  have hgroup' (k : ℕ × ℕ × ℤ) :
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (μ a : ℂ) * W a) k =
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (μ' a : ℂ) * Wnew a) k := by
    rw [hgroup k]
    simp only [he]
  simp only [hgroup'] at hd
  have hfinal := hd.trans ht
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : Function.Injective (y a)
  · simp only [μ', ite_eq_left hi, θ]
  · have hz : (μ a : ℂ) * Wnew a = 0 := by
      by_contra h
      exact hi (hnewinj a h)
    rcases mul_eq_zero.mp hz with hm | hW
    · have hm' : μ a = 0 := by exact_mod_cast hm
      simp only [μ', ite_eq_right hi, hm', zero_mul]
    · simp only [μ', ite_eq_right hi, hW, zero_mul, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored diagonal under the original giant and regular priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original harmonic product law pays the giant atom and a single
factorial product-fibre cost. The frequency range contributes no cardinality
factor, because the diagonal key includes the frequency itself. -/
theorem movingTemplate_symmetrized_harmonic_diagonal_live
    (P Pg : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (cg : ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hν : ∀ j k : TreeLeafIndex n × Fin m,
      primeSubsetPrior P (Q (movingTemplateBulk n r m j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n r m k)))
    (u : TreeLeafIndex n × Fin 4 → P) (p : ℕ)
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ cg q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ cg q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let A := Pg × ((MovingRegularSlot n r m → P) × transferFrequencyRange (V n))
    let X := fun a : A => (a.1 : ℕ)
    let y := fun a : A => a.2.1
    let v := fun a : A => (a.2.2 : ℤ)
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hPg _ a.1.property⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let α := fun a : A => smoothGiantPrior Pg φ cg a.1 *
      ∏ i, primeSubsetPrior P (Q i) (y a i)
    let C := fun a : A => movingTemplateCoefficient (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n (4 + r) m (v a)
        (movingRestoreSample n r m u (y a)) p (X a)
    let Csym := fun a : A => mixedBulkSymmetrize n m (movingTemplateBulk n r m)
      (fun _ z _ _ => C (a.1, z, a.2.2)) 0 (y a) 0 0
    let θ := fun a : A => (Real.exp (smoothGiantLogNormalizer Pg φ cg) / X a) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (y a i : ℕ)) : ℝ)⁻¹
    let D := p * (∏ i, (u i : ℕ)) * outside.prod
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (α a : ℂ) * C a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, α a * θ a *
        ‖Csym a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  intro A X y v instX instY α C Csym θ D
  let g := fun q : ℕ => Real.exp (smoothGiantLogNormalizer Pg φ cg) / q
  have hg q : 0 ≤ g q := div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
  have hα a : 0 ≤ α a :=
    mul_nonneg (smoothGiantPrior_nonneg Pg φ cg hφ0 a.1)
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have hpoint a : α a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i) := by
    apply mul_le_mul_of_nonneg_right _
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
    change Real.exp (smoothGiantLogNormalizer Pg φ cg) * φ (Real.log (a.1 : ℕ) - cg) /
      (a.1 : ℕ) ≤ Real.exp (smoothGiantLogNormalizer Pg φ cg) / (a.1 : ℕ)
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (Real.exp_nonneg _) (hφ1 _)) (Nat.cast_nonneg _)
  have hrow (a b : A) (hx : X a = X b) (hy : y a = y b) (hv : v a = v b) : a = b :=
    Prod.ext (Subtype.ext hx) (Prod.ext hy (Subtype.ext hv))
  have hc a (ha : (α a : ℂ) * C a ≠ 0) : C a ≠ 0 := right_ne_zero_of_mul ha
  have hinjC a (ha : C a ≠ 0) : Function.Injective (y a) := by
    have hs := movingTemplateCoefficient_restored_support (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n r m (v a) u (y a) p (X a) ha
    intro i j hij
    by_contra hne
    have hh := hs.2.2.1 (show (Sum.inr i : Unit ⊕ MovingRegularSlot n r m) ≠ .inr j from
      fun he => hne (Sum.inr.inj he))
    change (y a i : ℕ).Coprime (y a j : ℕ) at hh
    rw [hij] at hh
    exact (hP _ (y a j).property).ne_one (by simpa only [Nat.coprime_self] using hh)
  have hinj a (ha : (α a : ℂ) * C a ≠ 0) := hinjC a (hc a ha)
  have hnewinj a (ha : (α a : ℂ) * Csym a ≠ 0) : Function.Injective (y a) := by
    obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m)
      (fun _ z _ _ => C (a.1, z, a.2.2)) 0 (y a) 0 0 (right_ne_zero_of_mul ha)
    have hi := hinjC (a.1, selectedBulkSample (movingTemplateBulk n r m) e (y a), a.2.2) he
    exact (selectedBulkSample_injective_iff (movingTemplateBulk n r m) e id (y a)).mp hi
  have hgroup (k : ℕ × ℕ × ℤ) :
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (α a : ℂ) * C a) k =
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (α a : ℂ) * Csym a) k := by
    exact (movingAmplitude_grouped_bulk_average P Pg n r m V
      (smoothGiantPrior Pg φ cg) (fun i => primeSubsetPrior P (Q i)) hν C k).symm
  have hz a (ha : (α a : ℂ) * C a ≠ 0) : v a ≠ 0 := by
    intro he
    apply hc a ha
    simpa only [C, movingTemplateCoefficient, he] using
      movingFrequencyCoefficient_zero (fun q : P => (q : ℕ)) outside μ
        childBound pivotBound V F hF φ G n
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (movingTemplateSmall n (4 + r) m))
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))) p (X a)
  have hsupp (a : A) (ha : (α a : ℂ) * C a ≠ 0) : smoothGiantPrior Pg φ cg a.1 ≠ 0 := by
    have ha' : α a ≠ 0 := by exact_mod_cast left_ne_zero_of_mul ha
    exact left_ne_zero_of_mul ha'
  have hprior (a : A) (ha : (α a : ℂ) * C a ≠ 0) (i) :
      primeSubsetPrior P (Q i) (y a i) ≠ 0 := by
    have hα : α a ≠ 0 := by exact_mod_cast left_ne_zero_of_mul ha
    exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hα) i (Finset.mem_univ i)
  have h := movingOneGiant_harmonic_grouped_diagonal_le P hP Q X
    (fun a => hPg _ a.1.property) y v α C Csym hα g hg hrow hpoint hinj hz
    (fun a ha => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt (hvg a.1 (hsupp a ha)))
    (fun a ha i => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt
      (hvr i (y a i) (hprior a ha i)))
    (fun a b ha hb i => hsep a.1 (hsupp a ha) i (y b i) (hprior b hb i)) hgroup hnewinj greg ggiant favorable D
  simpa only [g, θ, Nat.cast_prod] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeLiveSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product-fibre control of the whole prime amplitude diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_symmetrized_harmonic_diagonal_live
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hν : ∀ j k : TreeLeafIndex n × Fin m,
      primeSubsetPrior P (Q (movingTemplateBulk n r m j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n r m k)))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let ν := fun i => primeSubsetPrior P (Q i)
    let A := MovingAmplitudeIndex P Pg n r m V
    let α := fun a : A => movingAmplitudePrior Pg n r m V ρ ν a
    let θ := fun a : A =>
      (Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1))) / (a.1 : ℕ)) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (a.2.1 i : ℕ)) : ℝ)⁻¹
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable ≤
    ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
      ∑ p ∈ I, φ (Real.log p - G (n + 1)) * ∑ a : A, α a * θ a *
        ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
          n r m a.2.2.val u a.2.1 p a.1 *
          primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
            (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖ ^ 2 := by
  intro ρ ν A α θ
  unfold movingAmplitudeDiagonal
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ0 _)
  have hd := movingTemplate_symmetrized_harmonic_diagonal_live P Pg hP hPg outside μ childBound pivotBound V
    F hF φ hφ0 hφ1 G (G (n + 1)) n r m Q hν u p hvg hvr hsep greg ggiant favorable
  dsimp only at hd
  let : ∀ a : A, Fact (a.1 : ℕ).Prime := fun a => ⟨hPg _ a.1.property⟩
  let : ∀ a : A, ∀ i, Fact (a.2.1 i : ℕ).Prime := fun a i => ⟨hP _ (a.2.1 i).property⟩
  simpa only [movingSymmetrizedTemplateCoefficient, movingTemplateTransferWeight, movingAmplitudePrior, movingOneGiant_transform_tagged,
    ρ, ν, α, θ, Nat.cast_prod, Function.comp_def]
    using hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeLiveCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic cost for live priors and the literal coefficient support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_symmetrized_full_harmonic_cost_live
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ)
    (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hidentical : ∀ j k : TreeLeafIndex n × Fin m,
      primeSubsetPrior P (Q (movingTemplateBulk n r m j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n r m k)))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (totalLower : ℝ)
    (hproduct : ∀ (u : TreeLeafIndex n × Fin 4 → P), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (a : MovingAmplitudeIndex P Pg n r m V),
      (∀ i, primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0) →
      ∀ p : ℕ, movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m a.2.2.val u a.2.1 p a.1 ≠ 0 →
      Real.exp totalLower ≤ ((∏ i, (a.2.1 i : ℕ) : ℕ) : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      totalLower) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n r m Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg := by
  intro K
  have hdiag := movingAmplitude_symmetrized_harmonic_diagonal_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V F hF φ hφ0 hφ1 G n r m Q hidentical hvg hvr hsep greg ggiant favorable
  apply hdiag.trans
  dsimp only at hdiag ⊢
  unfold movingAmplitudeSymmetrizedRegularEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, mul_zero, Finset.sum_const_zero, le_refl]
  have hU : 0 ≤ (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ0 a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  by_cases ha : α = 0
  · simp only [show movingAmplitudePrior Pg n r m V (smoothGiantPrior Pg φ (G (n + 1)))
      (fun i => primeSubsetPrior P (Q i)) a = 0 from ha, zero_mul, mul_zero, le_refl]
  have hν i : primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) i (Finset.mem_univ i)
  by_cases hc : movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m a.2.2.val u a.2.1 p a.1 = 0
  · simp only [hc, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hcost := moving_harmonic_full_counterpart_le n r m Q
    (smoothGiantLogNormalizer Pg φ (G (n + 1))) Gmin totalLower
    (a.1 : ℕ) (fun i => (a.2.1 i : ℕ)) (hX a.1 (left_ne_zero_of_mul ha))
    (hproduct u hu a hν p hc)
  have hpos := mul_nonneg hU (hφ0 (Real.log p - G (n + 1)))
  have hcost' := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (mul_nonneg hpos hα) (sq_nonneg
      ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m a.2.2.val u a.2.1 p a.1 *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
          (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖))
  dsimp only [α] at hcost'
  simp only [Nat.cast_prod] at hcost'
  dsimp only [K]
  simp only [Nat.cast_prod]
  first | (convert hcost' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hcost'.trans (le_of_eq (by ring)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveHarmonic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary harmonic diagonal uses only nonzero regular support -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original harmonic product law pays the giant atom and a single
factorial product-fibre cost. The frequency range contributes no cardinality
factor, because the diagonal key includes the frequency itself. -/
theorem movingTemplate_harmonic_diagonal_live
    (P Pg : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (cg : ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (u : TreeLeafIndex n × Fin 4 → P) (p : ℕ)
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ cg q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ cg q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let A := Pg × ((MovingRegularSlot n r m → P) × transferFrequencyRange (V n))
    let X := fun a : A => (a.1 : ℕ)
    let y := fun a : A => a.2.1
    let v := fun a : A => (a.2.2 : ℤ)
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hPg _ a.1.property⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let α := fun a : A => smoothGiantPrior Pg φ cg a.1 *
      ∏ i, primeSubsetPrior P (Q i) (y a i)
    let C := fun a : A => movingTemplateCoefficient (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n (4 + r) m (v a)
        (movingRestoreSample n r m u (y a)) p (X a)
    let θ := fun a : A => (Real.exp (smoothGiantLogNormalizer Pg φ cg) / X a) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (y a i : ℕ)) : ℝ)⁻¹
    let D := p * (∏ i, (u i : ℕ)) * outside.prod
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (α a : ℂ) * C a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, α a * θ a *
        ‖C a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  intro A X y v instX instY α C θ D
  let g := fun q : ℕ => Real.exp (smoothGiantLogNormalizer Pg φ cg) / q
  have hg q : 0 ≤ g q := div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
  have hα a : 0 ≤ α a :=
    mul_nonneg (smoothGiantPrior_nonneg Pg φ cg hφ0 a.1)
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have hpoint a : α a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i) := by
    apply mul_le_mul_of_nonneg_right _
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
    change Real.exp (smoothGiantLogNormalizer Pg φ cg) * φ (Real.log (a.1 : ℕ) - cg) /
      (a.1 : ℕ) ≤ Real.exp (smoothGiantLogNormalizer Pg φ cg) / (a.1 : ℕ)
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (Real.exp_nonneg _) (hφ1 _)) (Nat.cast_nonneg _)
  have hrow (a b : A) (hx : X a = X b) (hy : y a = y b) (hv : v a = v b) : a = b :=
    Prod.ext (Subtype.ext hx) (Prod.ext hy (Subtype.ext hv))
  have hc a (ha : (α a : ℂ) * C a ≠ 0) : C a ≠ 0 := right_ne_zero_of_mul ha
  have hinj a (ha : (α a : ℂ) * C a ≠ 0) : Function.Injective (y a) := by
    have hs := movingTemplateCoefficient_restored_support (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n r m (v a) u (y a) p (X a) (hc a ha)
    intro i j hij
    by_contra hne
    have hh := hs.2.2.1 (show (Sum.inr i : Unit ⊕ MovingRegularSlot n r m) ≠ .inr j from
      fun he => hne (Sum.inr.inj he))
    change (y a i : ℕ).Coprime (y a j : ℕ) at hh
    rw [hij] at hh
    exact (hP _ (y a j).property).ne_one (by simpa only [Nat.coprime_self] using hh)
  have hz a (ha : (α a : ℂ) * C a ≠ 0) : v a ≠ 0 := by
    intro he
    apply hc a ha
    simpa only [C, movingTemplateCoefficient, he] using
      movingFrequencyCoefficient_zero (fun q : P => (q : ℕ)) outside μ
        childBound pivotBound V F hF φ G n
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (movingTemplateSmall n (4 + r) m))
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))) p (X a)
  have hsupp (a : A) (ha : (α a : ℂ) * C a ≠ 0) : smoothGiantPrior Pg φ cg a.1 ≠ 0 := by
    have ha' : α a ≠ 0 := by exact_mod_cast left_ne_zero_of_mul ha
    exact left_ne_zero_of_mul ha'
  have hregular (a : A) (ha : (α a : ℂ) * C a ≠ 0) (i) :
      primeSubsetPrior P (Q i) (y a i) ≠ 0 := by
    have ha' : α a ≠ 0 := by exact_mod_cast left_ne_zero_of_mul ha
    exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha') i (Finset.mem_univ i)
  have h := movingOneGiant_harmonic_diagonal_le P hP Q X
    (fun a => hPg _ a.1.property) y v α C hα g hg hrow hpoint hinj hz
    (fun a ha => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt (hvg a.1 (hsupp a ha)))
    (fun a ha i => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt
      (hvr i (y a i) (hregular a ha i)))
    (fun a b ha hb i => hsep a.1 (hsupp a ha) i (y b i) (hregular b hb i)) greg ggiant favorable D
  simpa only [g, θ, Nat.cast_prod] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeLiveHarmonic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product-fibre control of the whole prime amplitude diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitude_harmonic_diagonal_live
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let ν := fun i => primeSubsetPrior P (Q i)
    let A := MovingAmplitudeIndex P Pg n r m V
    let α := fun a : A => movingAmplitudePrior Pg n r m V ρ ν a
    let θ := fun a : A =>
      (Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1))) / (a.1 : ℕ)) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (a.2.1 i : ℕ)) : ℝ)⁻¹
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable ≤
    ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
      ∑ p ∈ I, φ (Real.log p - G (n + 1)) * ∑ a : A, α a * θ a *
        ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
          n (4 + r) m a.2.2.val (movingRestoreSample n r m u a.2.1) p a.1 *
          primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
            (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖ ^ 2 := by
  intro ρ ν A α θ
  unfold movingAmplitudeDiagonal
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ0 _)
  have hd := movingTemplate_harmonic_diagonal_live P Pg hP hPg outside μ childBound pivotBound V
    F hF φ hφ0 hφ1 G (G (n + 1)) n r m Q u p hvg hvr hsep greg ggiant favorable
  dsimp only at hd
  let : ∀ a : A, Fact (a.1 : ℕ).Prime := fun a => ⟨hPg _ a.1.property⟩
  let : ∀ a : A, ∀ i, Fact (a.2.1 i : ℕ).Prime := fun a i => ⟨hP _ (a.2.1 i).property⟩
  simpa only [movingTemplateTransferWeight, movingAmplitudePrior, movingOneGiant_transform_tagged,
    ρ, ν, α, θ, Nat.cast_prod, Function.comp_def]
    using hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving Fourier factors in the restored compensation coordinates -/

namespace Ostmann
open scoped Classical BigOperators

/-- The restored masked transform is exactly the surviving transform, with
the same sampled compensation product in its outside denominator. -/
theorem movingRegularTransform_restored_active {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, NeZero ((value ∘ x) i) := fun i => ⟨(hprime (x i)).ne_zero⟩
    let _ : ∀ i, NeZero ((value ∘ y) i) := fun i => ⟨(hprime (y i)).ne_zero⟩
    movingRegularTransform (value ∘ x)
      (fun i z => if movingRestoredActive n r m i then g (value (x i)) z else 1) D s =
      movingRegularTransform (value ∘ y) (fun i => g (value (y i)))
        (D * ∏ i, value (u i)) s := by
  dsimp only
  let x := movingRestoreSample n r m u y
  let p := value ∘ x
  let _ : ∀ i, NeZero (p i) := fun i => ⟨(hprime (x i)).ne_zero⟩
  let _ : ∀ i, Fact (value (u i)).Prime := fun _ => ⟨hprime _⟩
  let _ : ∀ i, Fact (value (y i)).Prime := fun _ => ⟨hprime _⟩
  have he := movingRegularTransform_equiv (movingReverseTemplate n r m) p
    (fun i z => if movingRestoredActive n r m i then g (p i) z else 1) D s
  dsimp only at he
  apply he.symm.trans
  have hp : (fun i => p (movingReverseTemplate n r m i)) =
      Sum.elim (value ∘ u) (value ∘ y) := by
    funext i
    simp only [p, x, Function.comp_apply, movingRestoreSample, Equiv.symm_apply_apply]
    cases i <;> rfl
  -- Reindexing the cofactor product directly avoids transporting dependent functions.
  unfold movingRegularTransform
  rw [Fintype.prod_sum_type]
  have hu : (∏ i : TreeLeafIndex n × Fin 4,
      (if movingRestoredActive n r m (movingReverseTemplate n r m (.inl i)) then
        g (p (movingReverseTemplate n r m (.inl i)))
          ((s : ZMod (p (movingReverseTemplate n r m (.inl i)))) *
            ((D * tupleCofactor (fun j => p (movingReverseTemplate n r m j)) (.inl i) : ℕ) :
              ZMod (p (movingReverseTemplate n r m (.inl i))))⁻¹)
      else 1)) = 1 := by simp only [movingRestoredActive_compensation, Bool.false_eq_true,
        ite_false, if_false, Finset.prod_const_one]
  rw [hu, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  simp only [movingRestoredActive_surviving, ite_true, if_true]
  have hc : tupleCofactor (fun j => p (movingReverseTemplate n r m j)) (.inr i) =
      (∏ j, value (u j)) * tupleCofactor (value ∘ y) i := by
    rw [hp, tupleCofactor_sum_right (value ∘ u) (value ∘ y) i (hprime (y i)).ne_zero]
    rfl
  rw [hc]
  let T (a : A) (M : ℕ) : ℂ :=
    g (value a) ((s : ZMod (value a)) * (M : ZMod (value a))⁻¹)
  change T (Sum.elim u y ((movingReverseTemplate n r m).symm
      (movingReverseTemplate n r m (.inr i))))
      (D * ((∏ j, value (u j)) * tupleCofactor (value ∘ y) i)) =
    T (y i) ((D * ∏ j, value (u j)) * tupleCofactor (value ∘ y) i)
  rw [Equiv.symm_apply_apply]
  congr 1
  ac_rfl

/-- The arithmetic multiplier with inactive compensation slots gives the
same surviving transform, retaining every compensation prime in its denominator. -/
theorem naturalRegularMultiplier_restored_active {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun i => ⟨hprime (x i)⟩
    let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime (y i)⟩
    naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s
      (fun i => ((D * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR =
    ‖movingRegularTransform (value ∘ y) (fun i => g (value (y i)))
      (D * XL * XR * ∏ i, value (u i)) s‖ ^ 2 := by
  dsimp only
  let _ : ∀ i, Fact ((value ∘ movingRestoreSample n r m u y) i).Prime :=
    fun i => ⟨hprime _⟩
  let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime _⟩
  rw [naturalRegularMultiplier_eq_transform_norm]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_restored_active value hprime n r m u y g (D * XL * XR) s)

/-- Distinct surviving primes put the same identity in product coordinates. -/
theorem naturalRegularMultiplier_restored_primeProduct {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (hy : Function.Injective (value ∘ y))
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let x := movingRestoreSample n r m u y
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun i => ⟨hprime (x i)⟩
    naturalRegularMultiplier (value ∘ x) (movingRestoredActive n r m) s
      (fun i => ((D * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR =
    ‖primeProductTransform g (D * XL * XR * ∏ i, value (u i)) (∏ i, value (y i)) s‖ ^ 2 := by
  dsimp only
  let _ : ∀ i, Fact ((value ∘ movingRestoreSample n r m u y) i).Prime :=
    fun i => ⟨hprime _⟩
  let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime _⟩
  rw [naturalRegularMultiplier_restored_active value hprime]
  simpa only [Function.comp_def] using congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_eq_primeProduct (value ∘ y) hy g
      (D * XL * XR * ∏ i, value (u i)) s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged restored prior and the masked one-branch energy -/

namespace Ostmann
open scoped Classical BigOperators

/-- Real-valued finite Fubini in exactly the restored template coordinates. -/
theorem movingReverseTemplate_average_real {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℝ) :
    (∑ x, (∏ i, ν i (x i)) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A,
        (∏ i, ν (movingReverseTemplate n r m (.inl i)) (u i)) *
        ∑ y : MovingRegularSlot n r m → A,
          (∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i)) *
          F (movingRestoreSample n r m u y) := by
  have h := movingReverseTemplate_average n r m ν (fun x => (F x : ℂ))
  exact_mod_cast h

/-- Restoring slots changes neither the compensation law nor the surviving law. -/
theorem movingTemplateRestoredPrior_average_real {A : Type} [Fintype A] (n r m : ℕ)
    (μ : A → ℝ) (ν : MovingRegularSlot n r m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℝ) :
    (∑ x, (∏ i, movingTemplateRestoredPrior n r m μ ν i (x i)) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A, (∏ i, μ (u i)) *
        ∑ y : MovingRegularSlot n r m → A, (∏ i, ν i (y i)) *
          F (movingRestoreSample n r m u y) := by
  simpa only [movingTemplateRestoredPrior, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr] using
    movingReverseTemplate_average_real n r m (movingTemplateRestoredPrior n r m μ ν) F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMaskedTemplateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-branch energy with its actual compensation mask -/

namespace Ostmann
open scoped Classical BigOperators

/-- The compensation product is bounded using only the support of the same
original prior. All four draws at every leaf are counted. -/
theorem movingRestoredCompensationProduct_le_exp
    (P : Finset ℕ) (μ : P → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (b : ℝ)
    (hb : ∀ a, μ a ≠ 0 → (a : ℝ) ≤ Real.exp b)
    (x : MovingRegularSlot n (4 + r) m → P)
    (hx : (∏ i, movingTemplateRestoredPrior n r m μ ν i (x i)) ≠ 0) :
    (movingRestoredCompensationProduct Subtype.val n r m x : ℝ) ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) := by
  have hm (i : TreeLeafIndex n × Fin 4) :
      μ (x (movingReverseTemplate n r m (.inl i))) ≠ 0 := by
    have h := Finset.prod_ne_zero_iff.mp hx (movingReverseTemplate n r m (.inl i))
      (Finset.mem_univ _)
    simpa only [movingTemplateRestoredPrior, Equiv.symm_apply_apply, Sum.elim_inl] using h
  calc
    (movingRestoredCompensationProduct Subtype.val n r m x : ℝ) =
        ∏ i : TreeLeafIndex n × Fin 4, (x (movingReverseTemplate n r m (.inl i)) : ℝ) := by
      simp only [movingRestoredCompensationProduct, Nat.cast_prod]
    _ ≤ ∏ _i : TreeLeafIndex n × Fin 4, Real.exp b := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact hb _ (hm i)
    _ = Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, card_treeLeafIndex,
        Fintype.card_fin, ← Real.exp_nat_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored multiplier of the actual bulk-averaged coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingBulkAveragedTemplateCoefficient_restore {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) (XL XR : ℕ) :
    movingBulkAveragedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u y) XL XR =
    movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s u y XL XR := by
  simp only [movingBulkAveragedTemplateCoefficient, movingSymmetrizedTemplateCoefficient,
    mixedBulkSymmetrize, finiteFamilyAverage, movingRestoreSample_bulk_action]

theorem movingBulkAveragedTemplateCoefficient_nonzero_injective {A : Type} [Fintype A]
    (value : A → ℕ) (hprime : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (x : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (h : movingBulkAveragedTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s x XL XR ≠ 0) : Function.Injective (value ∘ x) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m) _ 0 x 0 0 h
  have hi := movingTemplateCoefficient_nonzero_injective value outside μ childBound pivotBound V
    F φ G n r m s (selectedBulkSample (movingTemplateBulk n r m) e x) XL XR
    (fun i => hprime _) he
  exact (selectedBulkSample_injective_iff (movingTemplateBulk n r m) e value x).mp hi

theorem movingSymmetrizedMaskedTemplateKernel_restore
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n r m → P)
    (p X : ℕ) (s : ℤ) :
    movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg
      (movingRestoreSample n r m u y) p X s =
    ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m s u y p X *
      primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * X)
        (∏ i, (y i : ℕ)) s‖ ^ 2 := by
  unfold movingSymmetrizedMaskedTemplateKernel
  dsimp only
  rw [movingBulkAveragedTemplateCoefficient_restore]
  by_cases hC : movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      F φ G n r m s u y p X = 0
  · simp only [hC, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hfull : Function.Injective (Subtype.val ∘ movingRestoreSample n r m u y) :=
    movingBulkAveragedTemplateCoefficient_nonzero_injective Subtype.val
      (fun a => hP _ a.property) outside μ childBound pivotBound V F φ G n (4 + r) m s
      (movingRestoreSample n r m u y) p X (by rwa [movingBulkAveragedTemplateCoefficient_restore])
  have hy : Function.Injective (Subtype.val ∘ y) := by
    intro i j hij
    apply Sum.inr.inj
    apply (movingReverseTemplate n r m).injective
    apply hfull
    simpa only [Function.comp_apply, movingRestoreSample, Equiv.symm_apply_apply,
      Sum.elim_inr] using hij
  have he := naturalRegularMultiplier_restored_primeProduct Subtype.val
    (fun a : P => hP _ a.property) n r m u y hy greg outside.prod p X s
  dsimp only at he
  simp only [Function.comp_def] at he
  rw [he, norm_mul, mul_pow]
  congr 3
  ac_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bulk-averaged masked energy under the original restored prior -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSymmetrizedMaskedTemplateKernel_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) :
    0 ≤ movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s := by
  unfold movingSymmetrizedMaskedTemplateKernel
  dsimp only
  apply mul_nonneg (sq_nonneg _)
  unfold naturalRegularMultiplier
  apply Finset.prod_nonneg
  intro i _
  split <;> positivity

/-- A bound on the original support suffices: no support is conditioned into
or removed from the independent restored law. -/
theorem movingSymmetrizedMaskedTemplateEnergy_weight_le
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) (B : ℝ)
    (hweight : ∀ x, (∏ i, movingTemplateRestoredPrior n r m (μ n)
      (fun i => primeSubsetPrior P (Q i)) i (x i)) ≠ 0 → weight x ≤ B) :
    movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg weight ≤
      B * movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg (fun _ => 1) := by
  unfold movingSymmetrizedMaskedTemplateEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  let mass := ∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)
  have hm : 0 ≤ mass := by
    apply Finset.prod_nonneg
    intro i _
    unfold movingTemplateRestoredPrior
    cases he : (movingReverseTemplate n r m).symm i with
    | inl j => exact hμ n (x i)
    | inr j => exact primeSubsetPrior_nonneg P (Q j) (x i)
  by_cases hz : mass = 0
  · change mass * _ ≤ B * (mass * _)
    simp only [hz, zero_mul, mul_zero, le_refl]
  have hE : 0 ≤ ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
        ∑ s : transferFrequencyRange (V n),
          movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s.val := by
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (hφ _)
    apply Finset.sum_nonneg
    intro X _
    apply mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ X)
    exact Finset.sum_nonneg (fun s _ => movingSymmetrizedMaskedTemplateKernel_nonneg P hP outside μ
      childBound pivotBound V F φ G n r m greg x p X s.val)
  have ht := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hweight x hz) hE) hm
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeSymmetrizedMasked
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-branch amplitude energy in restored arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators

private theorem amplitude_energy_fubini_p1 {U T X Y S : Type}
    [Fintype U] [Fintype X] [Fintype Y] [Fintype S]
    (I : Finset T) (M : U → ℝ) (w : T → ℝ) (ρ : X → ℝ) (ν : Y → ℝ)
    (F : U → T → X → Y → S → ℝ) :
    (∑ u, M u * ∑ p ∈ I, w p * ∑ a : X × (Y × S),
      (ρ a.1 * ν a.2.1) * F u p a.1 a.2.1 a.2.2) =
    ∑ u, M u * ∑ y, ν y * ∑ p ∈ I, w p * ∑ x, ρ x * ∑ s, F u p x y s := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The compensation draw and the surviving draw are independent original
priors; this reordering introduces no frequency probability factor. -/
theorem movingAmplitudeSymmetrizedRegularEnergy_fubini
    (P Pg I : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg =
    ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
      ∑ y : MovingRegularSlot n r m → P, (∏ i, primeSubsetPrior P (Q i) (y i)) *
        ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
          ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
            ∑ s : transferFrequencyRange (V n),
              ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
                n r m s.val u y p X *
                primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (X : ℕ))
                  (∏ i, (y i : ℕ)) s.val‖ ^ 2 := by
  unfold movingAmplitudeSymmetrizedRegularEnergy
  dsimp only
  have h := amplitude_energy_fubini_p1
    (U := TreeLeafIndex n × Fin 4 → P) (X := Pg)
    (Y := MovingRegularSlot n r m → P) (S := transferFrequencyRange (V n)) I
    (fun u => (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ))
    (fun p => φ (Real.log p - G (n + 1)))
    (smoothGiantPrior Pg φ (G (n + 1)))
    (fun y => ∏ i, primeSubsetPrior P (Q i) (y i))
    (fun u p X y s =>
      ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
        n r m s.val u y p X *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (X : ℕ))
          (∏ i, (y i : ℕ)) s.val‖ ^ 2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [movingAmplitudePrior, Nat.cast_prod]

/-- This is the literal arithmetic energy under the original restored prior.
The extracted compensation product is a weight, not a change of measure. -/
theorem movingAmplitudeSymmetrizedRegularEnergy_eq_masked
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg =
      movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
        (fun x => (movingRestoredCompensationProduct Subtype.val n r m x : ℝ)) := by
  rw [movingAmplitudeSymmetrizedRegularEnergy_fubini]
  unfold movingSymmetrizedMaskedTemplateEnergy
  rw [movingTemplateRestoredPrior_average_real]
  simp only [movingRestoredCompensationProduct_restore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro s _
  rw [movingSymmetrizedMaskedTemplateKernel_restore]
  ring

/-- The compensation cost is now explicit, with the same original prior in
both energies. The bound is used only after the nonnegative diagonal reduction. -/
theorem movingAmplitudeSymmetrizedRegularEnergy_le_masked
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (b : ℝ) (hb : ∀ a, μ n a ≠ 0 → (a : ℝ) ≤ Real.exp b) :
    movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G n r m Q greg ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b) *
        movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
          (fun _ => 1) := by
  rw [movingAmplitudeSymmetrizedRegularEnergy_eq_masked P Pg I hP]
  apply movingSymmetrizedMaskedTemplateEnergy_weight_le P Pg I hP outside μ hμ
    childBound pivotBound V F φ hφ G n r m Q greg
  intro x hx
  exact movingRestoredCompensationProduct_le_exp P (μ n) n r m
    (fun i => primeSubsetPrior P (Q i)) b hb x hx

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantMixedInterval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of the smooth integer/prime pair, with both scale factors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The integer coordinate has its original counting weight. Passing to the
logarithmic cell introduces exactly the displayed exponential scale. -/
theorem smoothInteger_interval (φ : ℝ → ℝ) (G center : ℝ) (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
      (φ (Real.log p - G) : ℂ) * F p) =
    (Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
      (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  unfold complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  simp only [integerResidueAtom, Nat.modEq_one, ite_true, if_true, Real.exp_log hp0, Nat.floor_natCast]
  have he : (Real.exp center : ℂ) * (Real.exp (-center) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = ((φ (Real.log p - G) : ℂ) * F p) * 1 := (mul_one _).symm
    _ = ((φ (Real.log p - G) : ℂ) * F p) *
        ((Real.exp center : ℂ) * (Real.exp (-center) : ℂ)) := by rw [he]
    _ = _ := by ring

/-- The remaining giant is averaged with its original normalized harmonic
prior; no endpoint prime is deleted. -/
theorem smoothGiant_integer_interval (φ : ℝ → ℝ) (G H center : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℕ → ℂ) :
    (∑ q : smoothGiantPrimeRange H,
      (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
        ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
          (φ (Real.log p - G) : ℂ) * F p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + center) : ℂ) *
      complexPrimeInterval 1 0 (H - 1) (H + 1) (fun y =>
        complexIntegerInterval 1 0 (G - 1) (G + 1) center (fun x =>
          (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
  rw [smoothGiantPrior_interval φ H hout (fun q =>
    ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
      (φ (Real.log p - G) : ℂ) * F p q)]
  have hp (q : ℕ) := smoothInteger_interval φ G center (fun p => F p q)
  simp_rw [hp]
  have hf : (fun y => (φ (y - H) : ℂ) *
      ((Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
        (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) =
    (fun y => (Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
        (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
    funext y
    rw [show (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊) =
        (fun x => (φ (y - H) : ℂ) * ((φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) from
      funext (fun _ => by ring), complexIntegerInterval_const_mul]
    ring
  rw [hf, complexPrimeInterval_const_mul, Real.exp_add, Complex.ofReal_mul]
  ring

/-- Finite Fubini retains the original regular law and counting measure on
frequencies, as well as the exact giant and integer normalizations. -/
theorem smoothGiant_mixed_external_interval {A B : Type*} [Fintype A] [Fintype B]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H center : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (F : ℤ → (B → A) → ℕ → ℕ → ℂ) :
    (∑ s : transferFrequencyRange N, ∑ x : B → A, ((∏ i, ν i (x i) : ℝ) : ℂ) *
      ∑ q : smoothGiantPrimeRange H,
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
          ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
            (φ (Real.log p - G) : ℂ) * F s.val x p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + center) : ℂ) *
      mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center
        (fun s x z y => (φ (z - G) : ℂ) * (φ (y - H) : ℂ) *
          F s x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊) := by
  unfold mixedExternalAverage
  have hpair (s : ℤ) (x : B → A) := smoothGiant_integer_interval φ G H center hout (F s x)
  simp_rw [hpair]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The masked energy with its exact integer and harmonic-prime scales -/

namespace Ostmann
open scoped Classical BigOperators

private theorem masked_energy_fubini_p1 {S A X T : Type}
    [Fintype S] [Fintype A] [Fintype X]
    (I : Finset T) (M : A → ℂ) (w : T → ℂ) (ρ : X → ℂ)
    (F : S → A → T → X → ℂ) :
    (∑ a, M a * ∑ p ∈ I, w p * ∑ x, ρ x * ∑ s, F s a p x) =
    ∑ s, ∑ a, M a * ∑ x, ρ x * ∑ p ∈ I, w p * F s a p x := by
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext p
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem movingSymmetrizedMaskedTemplateEnergy_interval
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center : ℝ) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let I := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    (movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg
      (fun _ => 1) : ℂ) =
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) *
      mixedExternalAverage ν (V n) (H - 1) (H + 1) (H - 1) (H + 1) center
        (fun s x z y => (φ (z - H) : ℂ) * (φ (y - H) : ℂ) *
          (movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg
            x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s : ℝ)) := by
  intro H Pg I ν
  have h := smoothGiant_mixed_external_interval ν (V n) φ H H center hout
    (fun s x p q => (movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
      n r m greg x p q s : ℝ))
  apply Eq.trans _ h
  unfold movingSymmetrizedMaskedTemplateEnergy
  simp only [one_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  have hf := masked_energy_fubini_p1 (S := transferFrequencyRange (V n))
    (A := MovingRegularSlot n (4 + r) m → P) (X := Pg) (T := ℕ) I
    (fun x => ((∏ i, ν i (x i) : ℝ) : ℂ))
    (fun p => (φ (Real.log p - H) : ℂ))
    (fun q : Pg => (smoothGiantPrior Pg φ H q : ℂ))
    (fun s x p q => (movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
      n r m greg x p q s.val : ℝ))
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pg, I, finite_univ_canonical]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNormalizedSymmetrizedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of the original bulk-averaged masked energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSymmetrizedMaskedTemplateKernel_original_integral
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (n r m : ℕ) (ν : MovingRegularSlot n (4 + r) m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (H : ℝ) (u v a b center : ℝ) :
    mixedExternalAverage ν (V n) u v a b center
      (fun s x z y => (φ (z - H) : ℂ) * (φ (y - H) : ℂ) *
        (movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
          n r m greg x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s : ℝ)) =
    movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n (4 + r) m ν (movingRestoredActive n r m) greg H H false u v a b center := by
  unfold movingTemplateMaskedSymmetrizedEnergy mixedExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro Xg hXg
  split_ifs
  · congr 1
    unfold complexIntegerInterval
    apply Finset.sum_congr rfl
    intro piv hpiv
    congr 1
    have hp : (0 : ℝ) < piv := by
      exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hpiv).1
    have hq : (0 : ℝ) < Xg := by
      exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hXg).1
    simp only [Real.exp_log hp, Real.exp_log hq, Nat.floor_natCast,
      movingSymmetrizedMaskedTemplateKernel, movingTemplateExternalMultiplier,
      giantOuterWeight, positiveLogCutoff, ite_eq_left hp, ite_eq_left hq,
      Bool.false_eq_true, ite_false, if_false, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · rfl

theorem movingSymmetrizedMaskedTemplateEnergy_original_interval
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center : ℝ) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let I := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    (movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G
      n r m Q greg (fun _ => 1) : ℂ) =
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) *
      movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n (4 + r) m ν (movingRestoredActive n r m) greg H H false
        (H - 1) (H + 1) (H - 1) (H + 1) center := by
  dsimp only
  rw [movingSymmetrizedMaskedTemplateEnergy_interval P hP outside μ childBound pivotBound V
    F φ hout G n r m Q greg center]
  rw [movingSymmetrizedMaskedTemplateKernel_original_integral]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeSymmetrizedNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original diagonal reduces to its masked symmetrized integral -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingAmplitudeSymmetrizedRegularEnergy_norm_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (n r m : ℕ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center b : ℝ)
    (hb : ∀ a, μ n a ≠ 0 → (a : ℝ) ≤ Real.exp b) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let Pivots := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    movingAmplitudeSymmetrizedRegularEnergy P Pg Pivots outside μ childBound pivotBound V
      F φ G n r m Q greg ≤
    Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b + smoothGiantLogNormalizer Pg φ H + center) *
      ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n (4 + r) m ν (movingRestoredActive n r m) greg H H false
        (H - 1) (H + 1) (H - 1) (H + 1) center‖ := by
  intro H Pg Pivots ν
  have hid := movingSymmetrizedMaskedTemplateEnergy_original_interval P hP outside μ
    childBound pivotBound V F φ hout G n r m Q greg center
  dsimp only at hid
  have hn := congrArg norm hid
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := (le_abs_self _).trans_eq hn
  have he := movingAmplitudeSymmetrizedRegularEnergy_le_masked P Pg Pivots hP outside μ hμ
    childBound pivotBound V F φ hφ G n r m Q greg b hb
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans_eq
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BadMatchingHarmonicBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bad matching count after its original harmonic normalization -/

namespace Ostmann
open scoped BigOperators Classical

theorem factorial_harmonic_entropy (r m : ℕ) (L z : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    (m.factorial : ℝ) ^ r * (L⁻¹) ^ (r * m) ≤
      Real.exp (Real.log z * (r * m : ℕ)) := by
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hratio : (m : ℝ) * L⁻¹ ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hL.le)
    simpa only [mul_assoc, mul_inv_cancel₀ hL.ne', mul_one] using hh
  calc
    _ ≤ ((m : ℝ) ^ m) ^ r * (L⁻¹) ^ (r * m) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfac r) (by positivity)
    _ = ((m : ℝ) * L⁻¹) ^ (r * m) := by rw [← pow_mul, Nat.mul_comm m r, mul_pow]
    _ ≤ z ^ (r * m) := pow_le_pow_left₀ (by positivity) hratio _
    _ = _ := by
      rw [← Real.exp_log hz, ← Real.exp_nat_mul]
      congr 1
      simp only [Real.log_exp]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicMassBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full factorial cost with the original bulk harmonic masses -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegular_inverse_mass_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L C : ℝ) (hL : 0 < L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    (∏ i, (mass i)⁻¹) ≤
      (L⁻¹) ^ (2 ^ n * m) * Real.exp (C * L * (2 ^ n * s : ℕ)) := by
  have hpoint (j : TreeLeafIndex n) (i : Fin s ⊕ Fin m) :
      (mass (j, i))⁻¹ ≤ Sum.elim (fun _ => Real.exp (C * L)) (fun _ => L⁻¹) i := by
    cases i with
    | inl i =>
      have h := one_div_le_one_div_of_le (Real.exp_pos (-C * L)) (hsmall (j, i))
      simpa only [Sum.elim_inl, one_div, show -C * L = -(C * L) by ring, Real.exp_neg, inv_inv] using h
    | inr i => simpa only [Sum.elim_inr, one_div] using one_div_le_one_div_of_le hL (hbulk (j, i))
  have hnonneg (i : MovingRegularSlot n s m) : 0 ≤ (mass i)⁻¹ := by
    rcases i with ⟨j, i | i⟩
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr (hL.le.trans (hbulk (j, i)))
  apply (Finset.prod_le_prod (fun i _ => hnonneg i) (fun i _ => hpoint i.1 i.2)).trans_eq
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, card_treeLeafIndex]
  rw [mul_pow, ← pow_mul, ← pow_mul, ← Real.exp_nat_mul]
  push_cast
  rw [show (s : ℝ) * 2 ^ n * (C * L) = C * L * (2 ^ n * s) by ring]
  ring

theorem factorial_split_upper (N S : ℕ) :
    ((N + S).factorial : ℝ) ≤ 2 ^ (N + S) * (N.factorial : ℝ) * (S.factorial : ℝ) := by
  have h := Nat.mul_le_mul_right (S.factorial)
    (Nat.mul_le_mul_right (N.factorial) (Nat.choose_le_two_pow (N + S) N))
  have hf : (N + S).choose N * N.factorial * S.factorial = (N + S).factorial := by
    simpa only [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right N S)
  rw [hf] at h
  exact_mod_cast h

theorem movingRegular_factorial_harmonic_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
      (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ)) := by
  have hf := factorial_split_upper (2 ^ n * m) (2 ^ n * s)
  have hp := movingRegular_inverse_mass_bound n s m mass L C hL hsmall hbulk
  have hnorm := factorial_harmonic_entropy 1 (2 ^ n * m) L ((2 ^ n : ℕ) * z) hL
    (mul_pos (by positivity) hz) (by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 ^ n by positivity)])
  simp only [pow_one, one_mul] at hnorm
  have hp0 : 0 ≤ ∏ i, (mass i)⁻¹ := by
    apply Finset.prod_nonneg
    rintro ⟨j, i | i⟩ _
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr (hL.le.trans (hbulk (j, i)))
  rw [movingRegularSlot_card, Nat.mul_add, Nat.add_comm (2 ^ n * s)]
  calc
    _ ≤ (2 ^ (2 ^ n * m + 2 ^ n * s) * ((2 ^ n * m).factorial : ℝ) *
        ((2 ^ n * s).factorial : ℝ)) *
        ((L⁻¹) ^ (2 ^ n * m) * Real.exp (C * L * (2 ^ n * s : ℕ))) :=
      mul_le_mul hf hp hp0 (by positivity)
    _ = (2 ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ))) *
        (2 ^ (2 ^ n * m) * (((2 ^ n * m).factorial : ℝ) * (L⁻¹) ^ (2 ^ n * m))) := by
      rw [pow_add]
      ring
    _ ≤ (2 ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ))) *
        (2 ^ (2 ^ n * m) * Real.exp (Real.log ((2 ^ n : ℕ) * z) * (2 ^ n * m : ℕ))) := by
      gcongr
    _ = _ := by
      rw [Real.log_mul (by positivity : ((2 ^ n : ℕ) : ℝ) ≠ 0) hz.ne']
      have ht : (2 : ℝ) ^ (2 ^ n * m) = Real.exp ((2 ^ n * m : ℕ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [ht, ← Real.exp_add]
      congr 2
      ring

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

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ)) atTop atTop := by
  have hk0 : 0 < (k : ℝ) ^ 4 := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) / (k : ℝ) ^ 4)] with L hL
  have h := (div_le_iff₀ hk0).mp hL
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBadHarmonicBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bad-arrangement saving in the complete diagonal normalization -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem moving_bad_full_harmonic_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    ((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4))) *
        (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹)) ≤
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ) / 4 + 5 / 4) * (2 ^ n * m : ℕ)) := by
  have h := mul_le_mul_of_nonneg_left
    (movingRegular_factorial_harmonic_bound n s m mass L z C hL hz hm hsmall hbulk)
    (show 0 ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) by positivity)
  apply h.trans_eq
  unfold movingNonbulkCost
  rw [show ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) =
    ((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4) by push_cast; ring]
  have he : Real.exp (((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
      Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ)) =
      Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ) / 4 + 5 / 4) * (2 ^ n * m : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) *
        (Real.exp (((2 ^ n * m : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ))) := by
      unfold movingNonbulkCost
      ring
    _ = _ := by rw [he]; rfl

theorem eventual_moving_nonbulk_cost (n s k : ℕ) (hk : 0 < k) (C ε : ℝ)
    (hε : 0 < ε) (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop,
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) ≤
        Real.exp (ε * (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ)) := by
  let F := movingNonbulkCost n s
  let r : ℝ := (2 ^ n : ℕ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hF : 0 < F := by dsimp [F, movingNonbulkCost]; positivity
  have hk4 : 0 < (k : ℝ) ^ 4 := by positivity
  have ht := (spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (2 * Real.log F / (ε * r)))
  filter_upwards [ht, eventually_ge_atTop (4 / (k : ℝ) ^ 4), eventually_ge_atTop (0 : ℝ)]
    with L hL hscale hL0
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm L] using (div_le_iff₀ hk4).mp hscale
  have hhalf := spectatorBulkCount_half k L hscale'
  have hc : C * L * (2 ^ n * s : ℕ) ≤ ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbudget hL0) hr.le
    have hm := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hε.le hr.le)
    dsimp only [r] at hm hb ⊢
    push_cast at hm hb ⊢
    nlinarith
  have hlog : Real.log F ≤ ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hh := (div_le_iff₀ (mul_pos hε hr)).mp hL
    nlinarith
  change F * _ ≤ _
  rw [← Real.exp_log hF, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBadHarmonicScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bad-arrangement normalization at the selected bulk scale -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_moving_bad_harmonic_scale (n s k : ℕ) (hk : 0 < k)
    (C a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ mass : MovingRegularSlot n s m → ℝ,
      (∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2)) →
      (∀ j : TreeLeafIndex n × Fin m, a * L ≤ mass (j.1, .inr j.2)) →
      ((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4))) *
          (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹)) ≤
        Real.exp ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / a) +
          Real.log (2 ^ n : ℕ) / 4 + 5 / 4 + ε) * (2 ^ n * m : ℕ)) := by
  filter_upwards [eventual_moving_nonbulk_cost n s k hk C ε hε hbudget,
    eventually_gt_atTop (0 : ℝ)] with L hcost hL
  dsimp only
  intro mass hsmall hbulk
  have hscale : (spectatorBulkCount k L : ℝ) ≤ ((k : ℝ) ^ 4 / a) * (a * L) := by
    convert spectatorBulkCount_upper k L hL.le using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hid : -(C / a) * (a * L) = -C * L := by field_simp
  have he := moving_bad_full_harmonic_bound n s (spectatorBulkCount k L) mass
    (a * L) ((k : ℝ) ^ 4 / a) (C / a) (mul_pos ha hL) (by positivity) hscale
    (by simpa only [hid] using hsmall) hbulk
  have hid' : (C / a) * (a * L) = C * L := by field_simp
  rw [hid'] at he
  apply he.trans
  apply (mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalGapBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal exponent and the parameter order in (7.1), (9.6)–(9.8) -/

namespace Ostmann

theorem spectator_diagonal_exponent (Bs BD Bz z r m C : ℝ) :
    -spectatorStepGap BD Bz z r m +
      r * (spectatorBaseGap Bs z m + (Real.log z + Real.log r / 4 + C) * m) =
    (Bs - BD + (9 - Bz) * Real.log z - (3 / 20 : ℝ) * Real.log r + C) * r * m := by
  unfold spectatorBaseGap spectatorStepGap
  ring

theorem spectator_diagonal_exponent_bound (Bs BD Bz z r m C B : ℝ)
    (hz : 1 ≤ z) (hr : 1 ≤ r) (hm : 0 ≤ m)
    (hBz : 9 ≤ Bz) (hBD : Bs + 2 * B + C + 6 ≤ BD) :
    -spectatorStepGap BD Bz z r m +
      r * (spectatorBaseGap Bs z m + (Real.log z + Real.log r / 4 + C) * m) ≤
        -(2 * B + 6) * r * m := by
  rw [spectator_diagonal_exponent]
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hzterm : (9 - Bz) * Real.log z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hzlog
  have hcoeff : Bs - BD + (9 - Bz) * Real.log z - (3 / 20 : ℝ) * Real.log r + C ≤
      -(2 * B + 6) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by linarith)) hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBadDiagonalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bad part of the actual logarithmic diagonal at the chosen gaps -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_moving_bad_diagonal_rate (n s k : ℕ) (hk : 0 < k)
    (Bs BD Bz B C a ε εdiag : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B + (Real.log 2 - Real.log a + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let r : ℝ := (2 ^ n : ℕ)
      let Δ := spectatorBaseGap Bs z m
      ∀ mass : MovingRegularSlot n s m → ℝ,
      (∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2)) →
      (∀ j : TreeLeafIndex n × Fin m, a * L ≤ mass (j.1, .inr j.2)) →
      ∀ arch : ℝ, arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch *
        (((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))) *
            (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹))) *
        Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) ≤
          Real.exp (-(2 * B + 6) * r * m) := by
  filter_upwards [eventual_moving_bad_harmonic_scale n s k hk C a ε ha hε hbudget,
    eventually_gt_atTop (0 : ℝ)] with L hmass hL
  dsimp only at hmass ⊢
  intro mass hsmall hbulk arch harch
  let m := spectatorBulkCount k L
  let z := (k : ℝ) ^ 4
  let r : ℝ := (2 ^ n : ℕ)
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast (Nat.one_le_two_pow)
  have hz : 1 ≤ z := by
    dsimp [z]
    exact one_le_pow₀ (by exact_mod_cast hk)
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log ((k : ℝ) ^ 4 / a) = Real.log z - Real.log a :=
    Real.log_div (by positivity) ha.ne'
  have hnorm := hmass mass hsmall hbulk
  rw [hlog] at hnorm
  have hp : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by simp
  rw [hp] at hnorm
  have hmass0 : 0 ≤ ∏ i, (mass i)⁻¹ := by
    apply Finset.prod_nonneg
    rintro ⟨j, i | i⟩ _
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr ((mul_pos ha hL).le.trans (hbulk (j, i)))
  have hdiag : r * spectatorBaseGap Bs z m + (Real.log 12 + 1) * r * m + εdiag * m ≤
      r * spectatorBaseGap Bs z m + (Real.log 12 + 1 + εdiag) * r * m := by
    nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hεdiag hm)]
  have hgap := spectator_diagonal_exponent_bound Bs BD Bz z r m
    (Real.log 2 - Real.log a + 5 / 4 + ε + Real.log 12 + 1 + εdiag) B
    hz hr hm hBz hBD
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul harch hnorm (mul_nonneg (by positivity)
      (mul_nonneg (Nat.cast_nonneg _) hmass0)) (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [r] at hdiag hgap ⊢
  push_cast at hdiag hgap ⊢
  nlinarith only [hdiag, hgap]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingScheduledLeafCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only the scheduled bottom frequencies evaluate a leaf multiplier -/
namespace Ostmann
open scoped Classical BigOperators

theorem recursiveTransferWeight_scheduled_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (x : State) (t : ScheduledFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (scheduledFrequencyHistory V n t) =
      recursiveTransferWeight sys H cutoff n x (scheduledFrequencyHistory V n t) := by
  induction n generalizing x with
  | zero => exact hF x t.val ((mem_transferFrequencyRange _ _).mp t.property)
  | succ n ih =>
    simp only [scheduledFrequencyHistory, recursiveTransferWeight]
    rw [ih _ t.2.1, ih _ t.2.2]

theorem recursiveTransferWeight_rooted_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n) (x : State)
    (t : MovingDescendantFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (movingRootedFrequencyTree V n s t) =
      recursiveTransferWeight sys H cutoff n x (movingRootedFrequencyTree V n s t) := by
  let root : transferFrequencyRange (V n) := ⟨s, (mem_transferFrequencyRange _ _).mpr hs⟩
  let d := (scheduledFrequencyRootEquiv V n).symm (root, t)
  have he : scheduledFrequencyHistory V n d = movingRootedFrequencyTree V n s t := by
    rw [scheduledFrequencyRootEquiv_history]
    simp only [d, Equiv.apply_symm_apply, root]
  rw [← he]
  exact recursiveTransferWeight_scheduled_leaf_congr sys F H cutoff V hF n x d

theorem movingFrequencyCoefficient_leaf_congr {P : Type} [Fintype P]
    (value : P → ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F H : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List P) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small bulk XL XR =
      movingFrequencyCoefficient value outside μ childBound pivotBound V H φ G n s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_congr rfl
  intro t _
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold movingSupportedSampleTerm
  rw [recursiveTransferWeight_rooted_leaf_congr _ F H _ V hF n s hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompactLeaf
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact leaf multipliers preserve the scheduled statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingCompactLeaf_zero (V : ℕ) : movingCompactLeaf V 0 = 0 := by
  simp [movingCompactLeaf]

theorem movingCompactLeaf_norm (V : ℕ) (s : ℤ) :
    ‖movingCompactLeaf V s‖ ≤ if s.natAbs ≤ V then 1 else 0 := by
  unfold movingCompactLeaf
  split_ifs <;> simp

theorem movingOriginalLeaf_congr {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (f h : ℤ → ℂ) (s : ℤ) (hs : f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi x s =
      movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi x s := by
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, hs]

theorem movingFrequencyCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s small bulk XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n s small bulk XL XR := by
  apply movingFrequencyCoefficient_leaf_congr value outside μ childBound pivotBound V
    _ _ _ φ G n s hs small bulk XL XR
  intro x z hz
  exact movingOriginalLeaf_congr value q f h z (hf z hz) g Dq S ψ X lo hi x

theorem movingTemplateCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n r m s y XL XR :=
  movingFrequencyCoefficient_original_leaf_congr value q outside μ childBound pivotBound V
    f h hf g Dq S ψ X lo hi φ G n s hs _ _ XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalErrorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained comparison errors in the full diagonal estimate -/

namespace Ostmann
open Filter

theorem moving_diagonal_four_term_bound (A bad D g e E : ℝ)
    (hA : 0 ≤ A) (hbad0 : 0 ≤ bad) (heD : e ≤ D) (heg : e ≤ g)
    (hbad : A * bad * D ≤ E) (hgood : A * g ≤ E) :
    A * (4 * (bad * (D + 5 * e) + g + 5 * e)) ≤ 48 * E := by
  have hb := mul_le_mul_of_nonneg_left heD (mul_nonneg hA hbad0)
  have hg := mul_le_mul_of_nonneg_left heg hA
  nlinarith only [hb, hg, hbad, hgood]

theorem eventual_moving_comparison_error (k : ℕ) (gain : ℝ) (hgain : 0 ≤ gain) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
        Real.exp (-gain * (spectatorBulkCount k L : ℝ)) := by
  filter_upwards [arithmetic_exponent_absorption 0 (12 / 10000) 0
    (gain * (k : ℝ) ^ 4) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L h hL
  have hm := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL) hgain
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at h
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg hgain (pow_nonneg (Nat.cast_nonneg k) 4)) hL]

theorem moving_diagonal_reserve (B r m E : ℝ) (hrm : Real.log 48 ≤ 3 * r * m)
    (hE : E ≤ 48 * Real.exp (-(2 * B + 6) * r * m)) :
    E ≤ Real.exp (-(2 * B + 3) * r * m) := by
  apply hE.trans
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 48), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full counterpart normalization grows only exponentially in bulk size -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_moving_harmonic_scale (n s k : ℕ) (hk : 0 < k)
    (C a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hbudget : 4 * C * s ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ mass : MovingRegularSlot n s m → ℝ,
      (∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2)) →
      (∀ j : TreeLeafIndex n × Fin m, a * L ≤ mass (j.1, .inr j.2)) →
      ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
        Real.exp ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / a) +
          Real.log (2 ^ n : ℕ) + ε) * (2 ^ n * m : ℕ)) := by
  filter_upwards [eventual_moving_nonbulk_cost n s k hk C ε hε hbudget,
    eventually_gt_atTop (0 : ℝ)] with L hcost hL
  dsimp only
  intro mass hsmall hbulk
  have hscale : (spectatorBulkCount k L : ℝ) ≤ ((k : ℝ) ^ 4 / a) * (a * L) := by
    convert spectatorBulkCount_upper k L hL.le using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hid : -(C / a) * (a * L) = -C * L := by field_simp
  have he := movingRegular_factorial_harmonic_bound n s (spectatorBulkCount k L) mass
    (a * L) ((k : ℝ) ^ 4 / a) (C / a) (mul_pos ha hL) (by positivity) hscale
    (by simpa only [hid] using hsmall) hbulk
  have hid' : (C / a) * (a * L) = C * L := by field_simp
  rw [hid'] at he
  have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by positivity :
      (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) ≠ 0))
  have hpre : (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
      Real.exp (C * L * (2 ^ n * s : ℕ)) ≤
      movingNonbulkCost n s * Real.exp (C * L * (2 ^ n * s : ℕ)) := by
    have hh := mul_le_mul_of_nonneg_right hA (show 0 ≤
      (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ)) by positivity)
    simpa only [movingNonbulkCost, one_mul, mul_assoc] using hh
  apply he.trans
  apply (mul_le_mul_of_nonneg_right (hpre.trans hcost) (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalLeafMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar multipliers in the original terminal coefficient -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalLeaf_zero {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q F g Dq S ψ X lo hi x 0 = 0 := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  split <;> simp only [hF, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredPrimeLaws
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime sets and tiers in restored coordinates -/

namespace Ostmann
open scoped Classical

theorem movingRestoredPrimeSets_prior (P : Finset ℕ) (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) :
    (fun i => primeSubsetPrior P (movingRestoredPrimeSets n r m Qμ Qν i)) =
      movingTemplateRestoredPrior n r m (primeSubsetPrior P Qμ) (fun i => primeSubsetPrior P (Qν i)) := by
  funext i a
  unfold movingTemplateRestoredPrior movingRestoredPrimeSets
  cases (movingReverseTemplate n r m).symm i <;> rfl

theorem movingRestoredTiers_lower (n r m : ℕ) (tier : MovingRegularSlot n r m → ℕ)
    (h : ∀ i, n ≤ tier i) : ∀ i, n ≤ movingRestoredTiers n r m tier i := by
  intro i
  unfold movingRestoredTiers
  cases (movingReverseTemplate n r m).symm i with
  | inl _ => exact le_rfl
  | inr j => exact h j

theorem movingRestoredPrimeSets_tier (P : Finset ℕ) (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (t : P → ℕ)
    (hμ : ∀ q : P, (q : ℕ) ∈ Qμ → t q = n)
    (hν : ∀ i (q : P), (q : ℕ) ∈ Qν i → t q = tier i) :
    ∀ i (q : P), (q : ℕ) ∈ movingRestoredPrimeSets n r m Qμ Qν i →
      t q = movingRestoredTiers n r m tier i := by
  intro i q
  unfold movingRestoredPrimeSets movingRestoredTiers
  cases (movingReverseTemplate n r m).symm i with
  | inl _ => exact hμ q
  | inr j => exact hν j q

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicFamilyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical bounds for the selected internal and external harmonic laws -/

namespace Ostmann
open scoped Classical BigOperators

/-- The fixed positive cell-mass constant changes the starting threshold,
not the coefficient of L in the normalizer. -/
theorem selected_cell_normalizer (c K L mass : ℝ) (hc : 0 < c)
    (hL : max 1 (-Real.log c) ≤ L)
    (hmass : c / Real.exp (K * L) ≤ mass) :
    0 < mass ∧ mass⁻¹ ≤ Real.exp ((K + 1) * L) := by
  have hm : 0 < mass := lt_of_lt_of_le (div_pos hc (Real.exp_pos _)) hmass
  have hsmall : Real.exp (-L) ≤ c := by
    calc
      _ ≤ Real.exp (Real.log c) :=
        Real.exp_le_exp.mpr (by linarith only [(le_max_right 1 (-Real.log c)).trans hL])
      _ = _ := Real.exp_log hc
  have hci : c⁻¹ ≤ Real.exp L := by
    have hh := inv_anti₀ (Real.exp_pos (-L)) hsmall
    simpa only [Real.exp_neg, inv_inv] using hh
  refine ⟨hm, (inv_anti₀ (div_pos hc (Real.exp_pos _)) hmass).trans ?_⟩
  calc
    (c / Real.exp (K * L))⁻¹ = Real.exp (K * L) * c⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ Real.exp (K * L) * Real.exp L :=
      mul_le_mul_of_nonneg_left hci (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initialRegularFromList_mapped {P : Type*} (b r : ℕ) (fallback : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialRegularFromList b r fallback ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = y := by
  funext i
  unfold initialRegularFromList
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map] using ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).isLt)]
  rw [List.getElem_map]
  change y ((movingTemplateSlotList 0 (r + r) (b + b)).get
    ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i)) = y i
  rw [← movingTemplateListEquiv_apply, Equiv.apply_symm_apply]

theorem initialMovingDataCutoff_zero {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) {n : ℕ} (T : MovingSlotData P n) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T 0 = 0 := by
  simp only [initialMovingDataCutoff, ↓reduceIte]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds retained by the two original half-list cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

private theorem initialLogSumWeight_live {P : Type*} {n : ℕ} (value : P → ℕ)
    (c : ℝ) (x : Fin n → P) (hx : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact hx (logCellProfile_zero_outside _ (le_of_not_gt hn))

theorem initialMovingCutoffWeight_norm_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    ‖initialMovingCutoffWeight value b d r cb cd sl sr y‖ ≤ 1 := by
  have h (x : Fin b → P) (s : Fin d → P) :
      ‖((initialLogSumWeight value cb x * initialLogSumWeight value cd s : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg
      (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))]
    exact (mul_le_mul (initialLogSumWeight_le_one _ _ _) (initialLogSumWeight_le_one _ _ _)
      (initialLogSumWeight_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  unfold initialMovingCutoffWeight
  rw [norm_mul]
  exact (mul_le_mul (h _ _) (h _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem initialMovingCutoffWeight_live_sums {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    |(∑ i : Fin (b + b), Real.log (value (y ((), .inr i)) : ℝ)) - 2 * cb| < 2 ∧
      |(∑ i : Fin (d + d), Real.log (value (Fin.append sl sr i) : ℝ)) - 2 * cd| < 2 := by
  have hl := left_ne_zero_of_mul hy
  have hr := right_ne_zero_of_mul hy
  have hl' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
      initialLogSumWeight value cd sl ≠ 0 := by exact_mod_cast hl
  have hr' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
      initialLogSumWeight value cd sr ≠ 0 := by exact_mod_cast hr
  have hbl := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hl')
  have hbr := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hr')
  have hdl := initialLogSumWeight_live value cd sl (right_ne_zero_of_mul hl')
  have hdr := initialLogSumWeight_live value cd sr (right_ne_zero_of_mul hr')
  constructor
  · rw [Fin.sum_univ_add]
    obtain ⟨hbl, hbl'⟩ := abs_lt.mp hbl
    obtain ⟨hbr, hbr'⟩ := abs_lt.mp hbr
    apply abs_lt.mpr
    constructor <;> linarith only [hbl, hbl', hbr, hbr']
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    obtain ⟨hdl, hdl'⟩ := abs_lt.mp hdl
    obtain ⟨hdr, hdr'⟩ := abs_lt.mp hdr
    apply abs_lt.mpr
    constructor <;> linarith only [hdl, hdl', hdr, hdr']

theorem initialMovingCutoffWeight_bulk_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    Real.exp (2 * cb - 2) < (∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ)) := by
  have h := (abs_lt.mp (initialMovingCutoffWeight_live_sums value b d r cb cd sl sr y hy).1).1
  have hp : 0 < ∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hvalue (y ((), .inr i)))
  apply (Real.lt_log_iff_exp_lt hp).mp
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hvalue (y ((), .inr i))).ne')]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTreeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialMovingRealWeight_cast {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (initialMovingRealWeight value b d r cb cd sl sr y : ℂ) =
      initialMovingCutoffWeight value b d r cb cd sl sr y := by
  exact Complex.ofReal_mul _ _

theorem initialMovingRealWeight_bounds {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    0 ≤ initialMovingRealWeight value b d r cb cd sl sr y ∧
      initialMovingRealWeight value b d r cb cd sl sr y ≤ 1 := by
  have h0 : 0 ≤ initialMovingRealWeight value b d r cb cd sl sr y := by
    unfold initialMovingRealWeight
    exact mul_nonneg (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
      (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
  refine ⟨h0, ?_⟩
  have h := initialMovingCutoffWeight_norm_le_one value b d r cb cd sl sr y
  rw [← initialMovingRealWeight_cast, Complex.norm_real, Real.norm_of_nonneg h0] at h
  exact h

theorem initialMovingDataCutoff_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T s =
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback T.regularSlots) : ℂ) *
        (if s = 0 then 0 else 1) := by
  rw [initialMovingRealWeight_cast]
  unfold initialMovingDataCutoff
  split_ifs <;> simp only [mul_zero, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_bulk {P : Type*} (b r : ℕ) (fallback : P)
    (small : List P) (hsmall : small.length = r + r)
    (bulk : Fin (b + b) → P) (i : Fin (b + b)) :
    initialRegularFromList b r fallback (small ++ List.ofFn bulk) ((), .inr i) = bulk i := by
  let y : MovingRegularSlot 0 (r + r) (b + b) → P :=
    fun j => Sum.elim (fun z => small.get (Fin.cast hsmall.symm z)) bulk j.2
  have hlist : (movingTemplateSlotList 0 (r + r) (b + b)).map y =
      small ++ List.ofFn bulk := by
    simp only [movingTemplateSlotList, movingTemplateSmall, bulkSlotLeaves,
      treeLeafTupleEquiv, Equiv.coe_fn_symm_mk, flattenMovingSlots, List.map_append,
      List.map_ofFn, Function.comp_def, y, movingTemplateBulk, Sum.elim_inl,
      ]
    congr 1
    exact (List.ofFn_congr hsmall small.get).symm.trans (List.ofFn_get small)
  have h := congrFun (initialRegularFromList_mapped b r fallback y) ((), .inr i)
  simpa only [hlist, y, Sum.elim_inr] using h

theorem initialMovingRealWeight_list {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (small : List P) (hsmall : small.length = r + r) (bulk : Fin (b + b) → P) :
    initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback (small ++ List.ofFn bulk)) =
      initialHalfBulkWeight value b d cb cd sl sr bulk := by
  unfold initialMovingRealWeight initialHalfBulkWeight
  simp only [initialRegularFromList_bulk b r fallback small hsmall bulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

theorem moving_append_length_eq {P : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List P) n) (a b : ℕ)
    (hx : MovingLeafLengthEq n x a) (hy : MovingLeafLengthEq n y b) :
    MovingLeafLengthEq n (appendMovingSlotLeaves n x y) (a + b) := by
  induction n with
  | zero => exact (List.length_append).trans (congrArg₂ (· + ·) hx hy)
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length_eq {P : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → P) n) :
    MovingLeafLengthEq n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem initialMovingTreeWeight_sample {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P) (a : MovingSampleSlots P n)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r) :
    initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small (bulkSlotLeaves n (b + b) slot) a) =
      initialHalfBulkProduct value b d cb cd sl sr n slot := by
  induction a generalizing s with
  | leaf =>
    change initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback ((show List P from small) ++ List.ofFn (fun i => slot ((), i)))) = _
    exact initialMovingRealWeight_list value b d r cb cd sl sr fallback small
      (hsmall.trans (by omega)) _
  | @node n samples left right ihL ihR =>
    have hl : 4 + s + 4 * n = r + r := by omega
    change initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inl j.1, j.2))) left) *
      initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inr j.1, j.2))) right) = _
    rw [ihL _ _ _ _ (moving_append_length_eq n _ _ 4 s
      (moving_compensation_length_eq n samples) hsmall.1) hl,
      ihR _ _ _ _ (moving_append_length_eq n _ _ 4 s
        (moving_compensation_length_eq n samples) hsmall.2) hl]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfBulkProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower product bounds for the two genuine half-bulk cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfBulkWeight_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (bulk : Fin (b + b) → P)
    (h : initialHalfBulkWeight value b d cb cd sl sr bulk ≠ 0) :
    Real.exp (2 * cb - 2) ≤ ((∏ i, value (bulk i) : ℕ) : ℝ) := by
  let y : MovingRegularSlot 0 (0 + 0) (b + b) → P :=
    fun j => Sum.elim Fin.elim0 bulk j.2
  have he : (initialHalfBulkWeight value b d cb cd sl sr bulk : ℂ) =
      initialMovingCutoffWeight value b d 0 cb cd sl sr y := by
    exact Complex.ofReal_mul _ _
  have hh : initialMovingCutoffWeight value b d 0 cb cd sl sr y ≠ 0 := by
    rw [← he]
    exact Complex.ofReal_ne_zero.mpr h
  have hl := initialMovingCutoffWeight_bulk_product_lower value hvalue b d 0 cb cd sl sr y hh
  exact le_of_lt (by simpa only [y, Sum.elim_inr, Nat.cast_prod] using hl)

theorem initialHalfBulkProduct_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (h : initialHalfBulkProduct value b d cb cd sl sr n slot ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  induction n with
  | zero =>
    have hl := initialHalfBulkWeight_product_lower value hvalue b d cb cd sl sr
      (fun i => slot ((), i)) h
    have hp := Fintype.prod_prod_type (fun j : Unit × Fin (b + b) => value (slot j))
    simp only [Fintype.prod_unique] at hp
    rw [pow_zero, Nat.cast_one, one_mul]
    change Real.exp (2 * cb - 2) ≤ ↑(∏ j : Unit × Fin (b + b), value (slot j))
    simp only [finite_univ_canonical] at hp hl ⊢
    rw [hp]
    exact hl
  | succ n ih =>
    have hL := ih (fun j => slot (.inl j.1, j.2)) (left_ne_zero_of_mul h)
    have hR := ih (fun j => slot (.inr j.1, j.2)) (right_ne_zero_of_mul h)
    have he : Real.exp ((2 ^ (n + 1) : ℕ) * (2 * cb - 2)) =
        Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) * Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) := by
      rw [← Real.exp_add, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      congr 1
      ring
    rw [he]
    convert mul_le_mul hL hR (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
    all_goals try with_reducible_and_instances rfl
    rw [← Nat.cast_mul]
    congr 1
    have hp := Fintype.prod_prod_type
      (fun j : (TreeLeafIndex n ⊕ TreeLeafIndex n) × Fin (b + b) => value (slot j))
    have hs := Fintype.prod_sum_type
      (fun j : TreeLeafIndex n ⊕ TreeLeafIndex n => ∏ i : Fin (b + b), value (slot (j, i)))
    have hpL := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inl j.1, j.2)))
    have hpR := Fintype.prod_prod_type
      (fun j : TreeLeafIndex n × Fin (b + b) => value (slot (.inr j.1, j.2)))
    simp only [finite_univ_canonical] at hp hs hpL hpR ⊢
    exact hp.trans (hs.trans (congrArg₂ (· * ·) hpL.symm hpR.symm))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingRecursiveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_initial_halves {σ : Type*} (value : σ → ℕ) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → σ) (fallback : σ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
          (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          F cutoff n ⟨n, T, XL, XR⟩ t := by
  induction T generalizing XL XR with
  | leaf => rfl
  | @node n s CL CR U left right ihL ihR =>
    simp only [recursiveTransferWeight]
    split_ifs
    · simp only [movingSlotSystem, MovingSlotState.child, ite_true, if_true,
        Bool.false_eq_true, ite_false, if_false] at ihL ihR ⊢
      rw [ihL, ihR]
      simp only [initialMovingTreeWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficientFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact half-bulk factorization under the unchanged compensation law -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_initial_halves {P : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List P) n)
    (XL XR : ℕ) (a : MovingSampleSlots P n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small bulk XL XR a =
    (initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small bulk a) : ℂ) *
      movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_initial_halves]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

theorem movingSupportedSampledWeight_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedSampleTerm_initial_halves,
    initialMovingTreeWeight_sample value b d r cb cd sl sr fallback n s t small slot a hsmall hlen]
  ring

theorem movingFrequencyCoefficient_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n a : ℕ) (s : ℤ) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r)
    (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_initial_halves value b d r cb cd sl sr fallback
    outside μ childBound pivotBound F _ n a _ small slot hsmall hlen XL XR, Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingOriginalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the genuine half-list weights in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalLeaf_initial_halves {P I : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState P) (s : ℤ) :
    movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi x s =
    (initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_factor]
  split_ifs <;> ring

theorem movingFrequencyCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR := by
  have he : movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi = fun x s =>
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_initial_halves value b d r cb cd sl sr fallback q g Dq S ψ X lo hi x s
  rw [he]
  exact movingFrequencyCoefficient_initial_halves value b d r cb cd sl sr fallback outside μ
    childBound pivotBound V _ φ G n a s small slot hsmall hlen XL XR

theorem movingFrequencyCoefficient_original_initial_product_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤ ((∏ j, value (slot j) : ℕ) : ℝ) := by
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small slot hsmall hlen XL XR] at h
  apply initialHalfBulkProduct_product_lower value hvalue b d cb cd sl sr n slot
  exact Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTemplateProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product bounds from the literal two-half initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLeafLengthEq_map {P Q : Type*} (f : P → Q) (n : ℕ)
    (x : TreeLeafTuple (List P) n) (a : ℕ) (hx : MovingLeafLengthEq n x a) :
    MovingLeafLengthEq n (treeLeafMap (List.map f) n x) a := by
  induction n with
  | zero => simpa only [MovingLeafLengthEq, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length_eq {P : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → P) :
    MovingLeafLengthEq n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih =>
    change MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingTemplateCoefficient_original_initial_bulk_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) : ℕ) : ℝ) := by
  unfold movingTemplateCoefficient at h
  rw [bulkSlotLeaves_map] at h
  exact movingFrequencyCoefficient_original_initial_product_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s _ _
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR h

theorem movingTemplateCoefficient_original_initial_full_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n a (b + b) → P)
    (hlen : 4 + a + 4 * n = r + r)
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n (4 + a) (b + b) s
          (movingRestoreSample n a (b + b) u y) XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  have hb := movingTemplateCoefficient_original_initial_bulk_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n (4 + a) s
    (movingRestoreSample n a (b + b) u y) hlen XL XR h
  have he : (∏ j : TreeLeafIndex n × Fin (b + b),
      value (movingRestoreSample n a (b + b) u y (j.1, .inr j.2))) =
      ∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) := by
    apply Finset.prod_congr rfl
    intro j _
    change value (movingRestoreSample n a (b + b) u y
      (movingTemplateBulk n (4 + a) (b + b) j)) = _
    rw [movingRestoreSample_bulk]
    rfl
  rw [he] at hb
  have hs := movingTemplate_small_product_lower value n a (b + b) y lower hlower
  rw [Real.exp_add]
  convert mul_le_mul hs hb (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Nat.cast_mul]
  congr 1
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]

theorem movingSymmetrizedTemplateCoefficient_original_initial_full_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n a (b + b) → P)
    (hlen : 4 + a + 4 * n = r + r)
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) (XL XR : ℕ)
    (h : movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s u y XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n (b + b)
    (movingTemplateBulk n a (b + b)) _ 0 y 0 0 h
  have hl (j : TreeLeafIndex n × Fin a) : Real.exp (lower j) ≤
      (value (selectedBulkSample (movingTemplateBulk n a (b + b)) e y (j.1, .inl j.2)) : ℝ) := by
    rw [selectedBulkSample_template_small]
    exact hlower j
  have hp := movingTemplateCoefficient_original_initial_full_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s u
    (selectedBulkSample (movingTemplateBulk n a (b + b)) e y) hlen lower hl XL XR he
  rwa [selectedBulkSample_prod] at hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing only the nonnegative diagonal's actual half-cutoff weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initialHalfBulkWeight_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (bulk : Fin (b + b) → P) :
    0 ≤ initialHalfBulkWeight value b d cb cd sl sr bulk ∧
      initialHalfBulkWeight value b d cb cd sl sr bulk ≤ 1 := by
  exact initialMovingRealWeight_bounds value b d 0 cb cd sl sr
    (fun j => Sum.elim Fin.elim0 bulk j.2)

theorem initialHalfBulkProduct_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (n : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → P) :
    0 ≤ initialHalfBulkProduct value b d cb cd sl sr n slot ∧
      initialHalfBulkProduct value b d cb cd sl sr n slot ≤ 1 := by
  induction n with
  | zero => exact initialHalfBulkWeight_bounds value b d cb cd sl sr _
  | succ n ih =>
    obtain ⟨hl, hl1⟩ := ih (fun j => slot (.inl j.1, j.2))
    obtain ⟨hr, hr1⟩ := ih (fun j => slot (.inr j.1, j.2))
    exact ⟨mul_nonneg hl hr, (mul_le_mul hl1 hr1 hr zero_le_one).trans_eq (one_mul 1)⟩

theorem movingTemplateCoefficient_original_initial_norm_le {P J : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR‖ ≤
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n a (b + b) s y XL XR‖ := by
  unfold movingTemplateCoefficient
  rw [bulkSlotLeaves_map]
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s
    (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
    (y ∘ movingTemplateBulk n a (b + b))
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining both complete smooth cells in the mixed external average -/

namespace Ostmann
open scoped Classical BigOperators

private theorem primeInterval_function_add (u v : ℝ) (F H : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v (fun x => F x + H x) =
      complexPrimeInterval 1 0 u v F + complexPrimeInterval 1 0 u v H := by
  unfold complexPrimeInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem mixedExternalAverage_left_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v t r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (huv : u ≤ v) (hvt : v ≤ t) :
    mixedExternalAverage ν N u v r w center F + mixedExternalAverage ν N v t r w center F =
      mixedExternalAverage ν N u t r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← primeInterval_function_add]
  congr 1
  apply congrArg (complexPrimeInterval 1 0 r w)
  funext z
  exact complexIntegerInterval_add 1 0 u v t center _ huv hvt

theorem mixedExternalAverage_right_add {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r t w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hrt : r ≤ t) (htw : t ≤ w) :
    mixedExternalAverage ν N u v r t center F + mixedExternalAverage ν N u v t w center F =
      mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, complexPrimeInterval_add 1 0 r t w _ hrt htw]

theorem mixedExternalAverage_four_cells {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F =
      (mixedExternalAverage ν N (G - 1) G (H - 1) H center F +
        mixedExternalAverage ν N G (G + 1) (H - 1) H center F) +
      (mixedExternalAverage ν N (G - 1) G H (H + 1) center F +
        mixedExternalAverage ν N G (G + 1) H (H + 1) center F) := by
  rw [mixedExternalAverage_left_add ν N (G - 1) G (G + 1) (H - 1) H center F
      (by linarith) (by linarith),
    mixedExternalAverage_left_add ν N (G - 1) G (G + 1) H (H + 1) center F
      (by linarith) (by linarith),
    mixedExternalAverage_right_add ν N (G - 1) (G + 1) (H - 1) H (H + 1) center F
      (by linarith) (by linarith)]

theorem mixedExternalAverage_full_cell_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (G H center E : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ i j : Bool, ‖mixedExternalAverage ν N
      (if i then G else G - 1) ((if i then G else G - 1) + 1)
      (if j then H else H - 1) ((if j then H else H - 1) + 1) center F‖ ≤ E) :
    ‖mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center F‖ ≤ 4 * E := by
  rw [mixedExternalAverage_four_cells]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans
  have h00 := h false false
  have h10 := h true false
  have h01 := h false true
  have h11 := h true true
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, sub_add_cancel] at h00 h10 h01 h11
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedFullCell
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full smooth cell for the original symmetrized coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateMaskedSymmetrizedEnergy_full_cell_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (active : MovingRegularSlot n r m → Bool)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (H K center E : ℝ)
    (h : ∀ i j : Bool, ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal
      (if i then H else H - 1) ((if i then H else H - 1) + 1)
      (if j then K else K - 1) ((if j then K else K - 1) + 1) center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal (H - 1) (H + 1) (K - 1) (K + 1) center‖ ≤ 4 * E := by
  exact mixedExternalAverage_full_cell_bound ν (V n) H K center E _ h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialFullEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_full_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (H cb cd : ℝ),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
        H H false (H - 1) (H + 1) (H - 1) (H + 1) H‖ ≤
      4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hunit⟩ :=
    P.moving_selected_initial_symmetrized_energy C hM ψ n r₀ k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hunit] with L hunit
  intro b hsize
  have hunit := hunit b hsize
  dsimp only at hunit ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg H cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  apply movingTemplateMaskedSymmetrizedEnergy_full_cell_bound primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ G (n + 2) r₀ (b + b)
    (fun j => primeSubsetPrior primes (Qν j)) active (normalizedResidueFamily setsReg)
    H H false H H H _
  intro i j
  have hu : H - 1 ≤ (if i then H else H - 1) := by split <;> linarith
  have hr : H - 1 ≤ (if j then H else H - 1) := by split <;> linarith
  have hv : (if i then H else H - 1) ≤ H := by split <;> linarith
  exact hunit tierB primes hprimes d r sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg H H false
    (if i then H else H - 1) ((if i then H else H - 1) + 1)
    (if j then H else H - 1) ((if j then H else H - 1) + 1) H cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow (hH.trans hu) (hH.trans hr)
    (by linarith) (by linarith) le_rfl le_rfl (by linarith) hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp (hHbig.trans (by linarith)) (hHbig.trans hr)
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialAmplitudeEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained-log symmetrized amplitude with its original compensation law -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_amplitude_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ),
      let H := G ((n + 2) + 1)
      let slot := movingTemplateBulk (n + 2) r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      4 + r + 4 * (n + 2) = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ (n + 2), (q : ℝ) ≤ Real.exp btop) →
      movingAmplitudeSymmetrizedRegularEnergy primes (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊) outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m Qν (normalizedResidueFamily setsReg) ≤
      Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
      (4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, henergy⟩ :=
    P.moving_selected_initial_full_energy C hM ψ n (4 + r) k hk hn.le
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (0 : ℝ)] with L henergy hL
  intro b hsize
  have henergy := henergy b hsize
  dsimp only at henergy ⊢
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb
  let m := b + b
  let depth := n + 2
  let Qfull := movingRestoredPrimeSets depth r m (Qμ depth) Qν
  have hall (R : Finset ℕ → Prop) (h0 : R (Qμ depth)) (h1 : ∀ j, R (Qν j)) : ∀ j, R (Qfull j) := by
    intro j
    dsimp only [Qfull, movingRestoredPrimeSets]
    cases (movingReverseTemplate depth r m).symm j with
    | inl _ => exact h0
    | inr j => exact h1 j
  have hlow : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  have he := henergy (movingRestoredTiers depth r m tierB) primes hprimes
    d rinit sl sr fallback childBound pivotBound V outside p Dq sets β primeLo cutoff tier X Δ hi φ G
    (movingRestoredActive depth r m) global Qμ Qfull setsReg (G (depth + 1)) cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH (movingRestoredTiers_lower depth r m tierB hB)
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout
    (fun j => by simpa only [Qfull, m, depth, movingRestoredPrimeSets_bulk] using hν j)
    hμP (hall (fun Q => Q ⊆ primes) (hμP depth) hνP) hμmass
    (hall (fun Q => c / Real.exp (K * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹) (hμmass depth) hνmass)
    hμrange
    (hall (fun Q => ∀ q ∈ Q, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ))
      (fun q hq => hlow.trans (hμrange depth q hq)) hνrange)
    (movingRestoredActive_bulk depth r m)
    houtcover hinjp hHbig (fun j hj => hμtier j hj.le)
    (movingRestoredPrimeSets_tier primes depth r m (Qμ depth) Qν tierB tier (hμtier depth le_rfl) hνtier)
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep
    (fun z hz q hq => hall (fun Q => q ∉ Q) (hdeleteμ z hz q hq depth) (hdeleteν z hz q hq))
    hdeletebulk hsetsReg
  have hnrm := movingAmplitudeSymmetrizedRegularEnergy_norm_le primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a) depth r m
    childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ hφpos hφout G Qν (normalizedResidueFamily setsReg) (G (depth + 1)) btop
    (fun a ha => hb a (primeSubsetPrior_support _ _ a ha))
  dsimp only at hnrm
  rw [← movingRestoredPrimeSets_prior primes depth r m (Qμ depth) Qν] at hnrm
  exact hnrm.trans (mul_le_mul_of_nonneg_left he (Real.exp_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingHarmonicCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full harmonic diagonal cost for the genuine initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitude_initial_full_harmonic_cost {J : Type}
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n a : ℕ) (hlen : 4 + a + 4 * n = r + r)
    (Q : MovingRegularSlot n a (b + b) → Finset ℕ)
    (hidentical : ∀ j k : TreeLeafIndex n × Fin (b + b),
      primeSubsetPrior P (Q (movingTemplateBulk n a (b + b) j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n a (b + b) k)))
    (hvg : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 → V n < (p : ℕ))
    (hvr : ∀ i (p : P), primeSubsetPrior P (Q i) p ≠ 0 → V n < (p : ℕ))
    (hsep : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 →
      ∀ i (z : P), primeSubsetPrior P (Q i) z ≠ 0 → (p : ℕ) ≠ (z : ℕ))
    (Gmin : ℝ) (hX : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 →
      Real.exp Gmin ≤ (p : ℝ))
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin a, ∀ p : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) p ≠ 0 → Real.exp (lower j) ≤ (p : ℝ))
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq S ψ X lo hi
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
      ((Fintype.card (MovingRegularSlot n a (b + b))).factorial : ℝ) *
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n a (b + b)
      Pg I (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i))
      greg ggiant favorable ≤
    K * movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G
      n a (b + b) Q greg := by
  intro F K
  have hF (x) : F x 0 = 0 := movingOriginalLeaf_zero Subtype.val q
    (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
    (fun _ => initialMovingDataCutoff_zero Subtype.val b d r cb cd sl sr fallback _)
    g Dq S ψ X lo hi x
  apply movingAmplitude_symmetrized_full_harmonic_cost_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V F hF φ hφ0 hφ1 G n a (b + b) Q hidentical hvg hvr hsep Gmin hX
    ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) _ greg ggiant favorable
  intro u _ z hz p hp
  exact movingSymmetrizedTemplateCoefficient_original_initial_full_lower Subtype.val
    (fun p => (hP _ p.property).pos) b d r cb cd sl sr fallback q g Dq S ψ X lo hi
    outside μ childBound pivotBound V φ G n a z.2.2.val u z.2.1 hlen lower
    (fun j => hlower j _ (hz _)) p z.1 hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantActiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

theorem smoothGiantPrior_active_separation (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (N : ℕ) (hN : (N : ℝ) ≤ Real.exp (G - 1))
    (hQ : ∀ q : Q, (q : ℝ) ≤ Real.exp (G - 1)) :
    (∀ p : P, smoothGiantPrior P φ G p ≠ 0 → N < (p : ℕ)) ∧
      (∀ p : P, smoothGiantPrior P φ G p ≠ 0 → ∀ q : Q, (p : ℕ) ≠ (q : ℕ)) := by
  constructor
  · intro p hp
    exact_mod_cast hN.trans_lt (smoothGiantPrior_active_bounds P hP φ G hout p hp).1
  · intro p hp q heq
    have hb := (hQ q).trans_lt (smoothGiantPrior_active_bounds P hP φ G hout p hp).1
    exact (ne_of_lt hb) (by exact_mod_cast heq.symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal with the retained-log arithmetic saving -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_amplitude_diagonal
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex (n + 2) × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G ((n + 2) + 1)
      let slot := movingTemplateBulk (n + 2) r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      4 + r + 4 * (n + 2) = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ (n + 2), (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex (n + 2) × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V (n + 2) < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (2 * cb - 2))) *
        ((Fintype.card (MovingRegularSlot (n + 2) r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Qν i, (q : ℝ)⁻¹)⁻¹)) *
      (Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
      (4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, henergy⟩ :=
    P.moving_selected_initial_amplitude_energy C hM ψ n r k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (0 : ℝ)] with L henergy hL
  intro b hsize
  have henergy := henergy b hsize
  dsimp only at henergy ⊢
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep
  have he := henergy tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb
  let m := b + b
  let depth := n + 2
  let H := G (depth + 1)
  have hVbound : (V depth : ℝ) ≤ Real.exp (H - 1) := by
    apply (Nat.cast_le.mpr hNlo).trans
    apply hloReal.le.trans
    apply Real.exp_le_exp.mpr
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  have hvg (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) : V depth < (q : ℕ) := by
    have hq' := (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1
    exact_mod_cast hVbound.trans_lt hq'
  have hX (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) :
      Real.exp (H - 1) ≤ (q : ℝ) :=
    (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1.le
  have hcost := movingAmplitude_initial_full_harmonic_cost primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    hprimes (smoothGiantPrimeRange_prime H) b d rinit cb cd sl sr fallback
    p (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi
    outside (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a)
    childBound pivotBound V φ hφpos hφ1 G depth r hlen Qν
    (fun j l => by rw [hν j, hν l]) hvg
    (fun j q hq => hvr j q (primeSubsetPrior_support _ _ q hq))
    (fun q hq j z hz => hsep q hq j z (primeSubsetPrior_support _ _ z hz))
    (H - 1) hX lower (fun j q hq => hlower j q (primeSubsetPrior_support _ _ q hq))
    (normalizedResidueFamily setsReg) ggiant favorable
  dsimp only at hcost
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left he
  apply mul_nonneg
  · exact mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
      (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellLinearMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBadDiagonalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bad diagonal rate for the actual selected prime sets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem selected_prime_mass_exp_lower (c K L : ℝ) (hc : 0 < c)
    (hL : max 1 (-Real.log c) ≤ L) (Q : Finset ℕ)
    (hmass : c / Real.exp (K * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹) :
    Real.exp (-(K + 1) * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ := by
  obtain ⟨hp, hi⟩ := selected_cell_normalizer c K L _ hc hL hmass
  have h := inv_anti₀ (inv_pos.mpr hp) hi
  simpa only [inv_inv, ← Real.exp_neg, neg_mul] using h

theorem selected_bad_diagonal_rate {CM : ℝ} (hM : MertensEstimate CM)
    (n s k : ℕ) (hk : 0 < k) (c K Bs BD Bz B ε εdiag : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * (K + 1) * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let r : ℝ := (2 ^ n : ℕ)
      let Δ := spectatorBaseGap Bs z m
      ∀ (global : Finset ℕ) (Q : MovingRegularSlot n s m → Finset ℕ),
      (global.card : ℝ) ≤ Real.exp ((K + 1) * L) →
      (∀ j, Q (movingTemplateBulk n s m j) =
        primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ global) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Q j, (q : ℝ)⁻¹) →
      ∀ arch : ℝ, arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch *
        (((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))) *
            (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
              (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹))) *
        Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) ≤
          Real.exp (-(2 * B + 6) * r * m) := by
  filter_upwards [eventual_moving_bad_diagonal_rate n s k hk Bs BD Bz B (K + 1)
    (1 / 16000) ε εdiag (by norm_num) hε hεdiag hbudget hBz hBD,
    whole_shell_retained_linear_mass hM (K + 1) (by linarith),
    eventually_ge_atTop (max 1 (-Real.log c))] with L hbad hbulk hL
  dsimp only at hbad ⊢
  intro global Q hglobal hQ hmass arch harch
  apply hbad (fun i => ∑ q ∈ Q i, (q : ℝ)⁻¹)
  · intro j
    exact selected_prime_mass_exp_lower c K L hc hL _ (hmass _)
  · intro j
    change (1 / 16000 : ℝ) * L ≤ ∑ q ∈ Q (movingTemplateBulk n s (spectatorBulkCount k L) j), (q : ℝ)⁻¹
    rw [hQ j]
    convert hbulk global hglobal using 1 <;> first | rfl | ring
  · exact harch

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedDiagonalBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All terms of the selected logarithmic diagonal fit the iteration reserve -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem selected_diagonal_budget {CM : ℝ} (hM : MertensEstimate CM)
    (n s k : ℕ) (hk : 0 < k) (c K Bs BD Bz B ε εdiag : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD)
    (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * (K + 1) * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    let r : ℝ := (2 ^ n : ℕ)
    let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
      Real.log r + ε + 2 * B + 6) * r)
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let Δ := spectatorBaseGap Bs z m
      let bad := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))
      ∀ (global : Finset ℕ) (Q : MovingRegularSlot n s m → Finset ℕ),
      (global.card : ℝ) ≤ Real.exp ((K + 1) * L) →
      (∀ j, Q (movingTemplateBulk n s m j) =
        primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ global) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Q j, (q : ℝ)⁻¹) →
      ∀ arch : ℝ, 0 ≤ arch → arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch * (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)) *
        (4 * (bad * (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) ≤
          Real.exp (-(2 * B + 3) * r * m) := by
  intro r gain
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast Nat.one_le_two_pow
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hg0 : 0 ≤ gain := le_max_left _ _
  filter_upwards [selected_bad_diagonal_rate hM n s k hk c K Bs BD Bz B ε εdiag
      hc hK hε hεdiag hbudget hBz hBD,
    eventual_moving_harmonic_scale n s k hk (K + 1) (1 / 16000) ε (by norm_num) hε hbudget,
    whole_shell_retained_linear_mass hM (K + 1) (by linarith),
    eventual_moving_comparison_error k gain hg0,
    (spectatorBulkCount_tendsto k hk).eventually (eventually_ge_atTop (Real.log 48)),
    eventually_ge_atTop (max 1 (-Real.log c))] with L hbad hnorm hbulk herr hm hL
  dsimp only at hbad hnorm ⊢
  intro global Q hglobal hQ hmass arch harch0 harch
  let m := spectatorBulkCount k L
  let Z : ℝ := ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
    (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
  let D := Real.exp (r * spectatorBaseGap Bs ((k : ℝ) ^ 4) m +
    (Real.log 12 + 1) * r * m + εdiag * m)
  let bad := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
    Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))
  let E := Real.exp (-(2 * B + 6) * r * m)
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hb : (arch * Z) * bad * D ≤ E := by
    have h := hbad global Q hglobal hQ hmass arch harch
    change arch * (bad * Z) * D ≤ E at h
    convert h using 1 <;> first | rfl | ring
  have hmassBound := hnorm (fun i => ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (fun j => selected_prime_mass_exp_lower c K L hc hL _ (hmass _))
    (fun j => by rw [show (j.1, Sum.inr j.2) = movingTemplateBulk n s m j from rfl, hQ j]
                 convert hbulk global hglobal using 1; ring)
  let A := Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) + Real.log r + ε
  have hZ : Z ≤ Real.exp (A * r * m) := by
    simpa only [Z, A, r, m, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hmassBound
  have hstep : 0 ≤ spectatorStepGap BD Bz ((k : ℝ) ^ 4) r m := by
    unfold spectatorStepGap
    have hzlog := Real.log_nonneg hz
    have hrlog := Real.log_nonneg hr
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    positivity
  have harch1 : arch ≤ 1 := harch.trans ((Real.exp_le_one_iff.mpr (by linarith :
    -spectatorStepGap BD Bz ((k : ℝ) ^ 4) r m ≤ 0)))
  have hg : (arch * Z) * Real.exp (-gain * m) ≤ E := by
    apply (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right harch1 hZ0).trans (by simpa using hZ)) (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hgg : (A + 2 * B + 6) * r ≤ gain := le_max_right _ _
    have hgm := mul_le_mul_of_nonneg_right hgg (Nat.cast_nonneg m (α := ℝ))
    linarith
  have hD : 1 ≤ D := by
    apply Real.one_le_exp
    have hzlog := Real.log_nonneg hz
    have h12 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 12)
    dsimp only [D, spectatorBaseGap]
    positivity
  have heD : Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤ D :=
    (Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos ((12 / 10000 : ℝ) * L)])).trans hD
  apply moving_diagonal_reserve B r m _ (by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hr hm0])
  exact moving_diagonal_four_term_bound (arch * Z) bad D (Real.exp (-gain * m))
    (Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) E
    (mul_nonneg harch0 hZ0) (by dsimp [bad]; positivity) heD herr hb hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialDiagonalDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of the original selected diagonal from its explicit cell-gap inequality -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_diagonal_decay
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : 4 * (K + 1) * r ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex (n + 2) × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G ((n + 2) + 1)
      let slot := movingTemplateBulk (n + 2) r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      4 + r + 4 * (n + 2) = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ (n + 2), (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex (n + 2) × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V (n + 2) < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop -
          ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ (n + 2) : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ (n + 2) : ℕ) * m) := by
  let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
    Real.log (2 ^ (n + 2) : ℕ) + 1 + 2 * B + 6) * (2 ^ (n + 2) : ℕ))
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hdiag⟩ :=
    P.moving_selected_initial_amplitude_diagonal C hM ψ n r k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  have hnumeric := selected_diagonal_budget hM (n + 2) r k hk c K Bs BD Bz B 1 εdiag
    hc hK hBs hBD0 (by norm_num) hεdiag.le (by simpa only [one_mul] using hmassBudget) hBz hBD
  filter_upwards [hdiag, hnumeric] with L hdiag hnumeric
  intro b hsize
  have hdiag := hdiag b hsize
  dsimp only at hnumeric
  rw [hsize] at hnumeric
  dsimp only at hdiag ⊢
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep hgap
  have he := hdiag tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep
  let m := b + b
  let H := G ((n + 2) + 1)
  let arch := Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
    ((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop -
      ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (2 * cb - 2)))
  have hglobal : (global.card : ℝ) ≤ Real.exp ((K + 1) * L) := by
    apply le_trans _ hdel
    exact_mod_cast (show global.card ≤ global.card +
      (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) +
      outside.length by omega)
  have hnumer := hnumeric global Qν hglobal hν hνmass arch (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr hgap)
  apply he.trans
  have hexp :
      Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (2 * cb - 2))) *
      Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) = arch := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreassoc (a btop c d e : ℝ) : (a * btop * c) * (d * e) = (a * d) * (btop * c) * e := by ring
  rw [hreassoc, hexp]
  apply le_trans ?_ hnumer
  dsimp only [gain, arch, m, H]
  push_cast
  gcongr
  simpa only [Nat.cast_add] using hΔupper

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingEarlyCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first two diagonal costs retain both original half-cutoffs -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitude_initial_regular_harmonic_cost {J : Type}
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ)
    (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n r : ℕ) (hlen : 4 + r + 4 * n = rinit + rinit)
    (Q : MovingRegularSlot n r (b + b) → Finset ℕ)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin r, ∀ q : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) q ≠ 0 → Real.exp (lower j) ≤ (q : ℝ))
    (hvg : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → V n < (q : ℕ)) (hvr : ∀ i (q : P), primeSubsetPrior P (Q i) q ≠ 0 → V n < (q : ℕ))
    (hsep : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 →
      ∀ i (a : P), primeSubsetPrior P (Q i) a ≠ 0 → (q : ℕ) ≠ (a : ℕ))
    (Gmin : ℝ) (hX : ∀ q : Pg, smoothGiantPrior Pg φ (G (n + 1)) q ≠ 0 → Real.exp Gmin ≤ (q : ℝ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let Fw := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback) g Dq S ψ X lo hi
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) * ((Fintype.card (MovingRegularSlot n r (b + b))).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V Fw φ G n r (b + b) Pg I
      (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i)) greg ggiant favorable ≤
      K * movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V Fw φ G n r (b + b) Q greg := by
  intro Fw K
  have hFw x : Fw x 0 = 0 := movingOriginalLeaf_zero Subtype.val q
    (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
    (fun _ => initialMovingDataCutoff_zero Subtype.val b d rinit cb cd sl sr fallback _)
    g Dq S ψ X lo hi x
  have hdiag := movingAmplitude_harmonic_diagonal_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V Fw hFw φ hφ0 hφ1 G n r (b + b) Q hvg hvr hsep greg ggiant favorable
  apply hdiag.trans
  dsimp only at hdiag ⊢
  unfold movingAmplitudeRegularEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, mul_zero, Finset.sum_const_zero, le_refl]
  have hU : 0 ≤ (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ0 a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  by_cases ha : α = 0
  · simp only [show movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
      (fun i => primeSubsetPrior P (Q i)) a = 0 from ha, zero_mul, mul_zero, le_refl]
  have hν i : primeSubsetPrior P (Q i) (a.2.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ha) i (Finset.mem_univ i)
  by_cases hc : movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
      n (4 + r) (b + b) a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) p a.1 = 0
  · simp only [hc, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hprod := movingTemplateCoefficient_original_initial_full_lower Subtype.val
    (fun p => (hP _ p.property).pos) b d rinit cb cd sl sr fallback q g Dq S ψ X lo hi
    outside μ childBound pivotBound V φ G n r a.2.2.val u a.2.1 hlen lower
    (fun j => hlower j _ (hν _)) p a.1 hc
  have hcost := moving_harmonic_full_counterpart_le n r (b + b) Q
    (smoothGiantLogNormalizer Pg φ (G (n + 1))) Gmin
    ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) a.1
    (fun i => (a.2.1 i : ℕ)) (hX a.1 (left_ne_zero_of_mul ha)) hprod
  have hpos := mul_nonneg hU (hφ0 (Real.log p - G (n + 1)))
  have hcost' := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (mul_nonneg hpos hα) (sq_nonneg
      ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw φ G
        n (4 + r) (b + b) a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) p a.1 *
        primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
          (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖))
  dsimp only [α] at hcost'
  simp only [Nat.cast_prod] at hcost'
  dsimp only [K]
  simp only [Nat.cast_prod]
  first | (convert hcost' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hcost'.trans (le_of_eq (by ring)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingEarlyEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary energy with the genuine initial half-list cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitudeRegularEnergy_initial_le {J : Type}
    (P Pg I : Finset ℕ) (b d rinit : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n r : ℕ) (hlen : 4 + r + 4 * n = rinit + rinit)
    (Q : MovingRegularSlot n r (b + b) → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback) g Dq S ψ X lo hi)
      φ G n r (b + b) Q greg ≤
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ => movingCompactLeaf (V 0)) g Dq S ψ X lo hi)
      φ G n r (b + b) Q greg := by
  unfold movingAmplitudeRegularEnergy
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ _)
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  apply mul_le_mul_of_nonneg_left _ hα
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he := movingTemplateCoefficient_original_initial_norm_le Subtype.val b d rinit cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n (4 + r)
    a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) hlen p a.1
  rw [movingTemplateCoefficient_original_leaf_congr Subtype.val q outside μ
    childBound pivotBound V (fun s => if s = 0 then 0 else 1) (movingCompactLeaf (V 0))
    (fun s hs => by simp only [movingCompactLeaf, hs, ite_true, if_true]) g Dq S ψ X lo hi φ G
    n (4 + r) (b + b) a.2.2.val ((mem_transferFrequencyRange _ _).mp a.2.2.property)] at he
  exact he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialEarlyDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original first-step diagonals from the single-assignment arithmetic bound -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_early_log_diagonal
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n < k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ bsize : ℕ, spectatorBulkCount k L = bsize + bsize →
      let m := bsize + bsize
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd : ℝ) (lower : TreeLeafIndex n × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      4 + r + 4 * n = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, n ≤ tierB i) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp b) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex n × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ i (q : primes), (q : ℕ) ∈ Qν i → V n < (q : ℕ)) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val bsize d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G n r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Qν i, (q : ℝ)⁻¹)⁻¹)) *
      (Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
        (4 * (Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))))) := by
  filter_upwards [P.moving_selected_amplitude_regular_energy C hM ψ n r k hk hn.le
    A Wwin Bφ Dφ c K ε hA hWwin hBφ hDφ hc hK hε hdepth,
    eventually_ge_atTop (0 : ℝ)] with L henergy hL
  intro bsize hsize
  dsimp only at henergy ⊢
  rw [hsize] at henergy
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr
  have he := henergy tierB primes hprimes childBound pivotBound V (movingCompactLeaf (V 0)) outside p Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg
    hV (movingCompactLeaf_zero _) (movingCompactLeaf_norm _) hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb
  let m := bsize + bsize
  let H := G (n + 1)
  have hexp : Real.exp ((11 / 1000 : ℝ) * L) ≤ H - 1 := by
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  have hPbound (a : primes) : (a : ℝ) ≤ Real.exp (H - 1) :=
    (hupper a).trans (Real.exp_le_exp.mpr hexp)
  have hVbound : (V n : ℝ) ≤ Real.exp (H - 1) := by
    apply (Nat.cast_le.mpr hNlo).trans
    apply hloReal.le.trans
    apply Real.exp_le_exp.mpr
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  obtain ⟨hvg, hsep⟩ := smoothGiantPrior_active_separation (smoothGiantPrimeRange H) primes
    (smoothGiantPrimeRange_prime H) φ H hφout (V n) hVbound hPbound
  have hX (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) :
      Real.exp (H - 1) ≤ (q : ℝ) :=
    (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1.le
  have hcost := movingAmplitude_initial_regular_harmonic_cost primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    hprimes (smoothGiantPrimeRange_prime H) bsize d rinit cb cd sl sr fallback p
    (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi
    outside (fun j => primeSubsetPrior primes (Qμ j))
    (fun j a => primeSubsetPrior_nonneg _ _ a) childBound pivotBound V
    φ hφ0 hφ1 G n r hlen Qν lower
    (fun j q hq => hlower j q (primeSubsetPrior_support _ _ q hq))
    hvg (fun i q hq => hvr i q (primeSubsetPrior_support _ _ q hq))
    (fun q hq _ a _ => hsep q hq a) (H - 1) hX
    (normalizedResidueFamily setsReg) ggiant favorable
  have hplain := movingAmplitudeRegularEnergy_initial_le primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    bsize d rinit cb cd sl sr fallback p (fun i => normalizedResidueTransform (sets i))
    Dq Finset.univ ψ X (Real.exp Δ) hi outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a)
    childBound pivotBound V φ hφ0 G n r hlen Qν (normalizedResidueFamily setsReg)
  exact hcost.trans (mul_le_mul_of_nonneg_left (hplain.trans he) (by
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
        (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EarlyDiagonalBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two initial depths fit the same diagonal reserve -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem early_bad_multiplier_one_le (n : ℕ) (hn : n ≤ 1) (m : ℝ) (hm : 0 ≤ m) :
    1 ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℕ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) := by
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · norm_num only [pow_zero, Nat.cast_one, Real.log_one, mul_zero, zero_add,
      Nat.reduceAdd, Nat.reduceMul, one_pow, Nat.cast_ofNat, one_mul]
    have he : 1 ≤ Real.exp (m * (5 / 4)) := Real.one_le_exp (by positivity)
    linarith
  · norm_num only [pow_one, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat]
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have he : 1 ≤ Real.exp (2 * m * (-(3 / 4 : ℝ) * Real.log 2 + 5 / 4)) :=
      Real.one_le_exp (mul_nonneg (by positivity) (by linarith))
    linarith

theorem early_diagonal_energy_le (n : ℕ) (hn : n ≤ 1) (m main err tail : ℝ)
    (hm : 0 ≤ m) (hmain : 0 ≤ main) (herr : 0 ≤ err) (htail : 0 ≤ tail) :
    4 * (main + 5 * err) ≤
      4 * ((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℕ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) *
          (main + 5 * err) + tail + 5 * err) := by
  have h := mul_le_mul_of_nonneg_right (early_bad_multiplier_one_le n hn m hm)
    (show 0 ≤ main + 5 * err by positivity)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialEarlyDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual first two diagonals satisfy the iteration reserve -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_early_diagonal_decay
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n < k) (hearly : n ≤ 1)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : 4 * (K + 1) * r ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀ bsize : ℕ, spectatorBulkCount k L = bsize + bsize →
      let m := bsize + bsize
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd : ℝ) (lower : TreeLeafIndex n × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      4 + r + 4 * n = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, n ≤ tierB i) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp b) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex n × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ i (q : primes), (q : ℕ) ∈ Qν i → V n < (q : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ n * 4 : ℕ) : ℝ) * b -
          ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val bsize d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G n r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * m) := by
  let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
    Real.log (2 ^ n : ℕ) + 1 + 2 * B + 6) * (2 ^ n : ℕ))
  have hdiag := P.moving_selected_initial_early_log_diagonal C hM ψ n r k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth
  have hnumeric := selected_diagonal_budget hM n r k hk c K Bs BD Bz B 1 εdiag
    hc hK hBs hBD0 (by norm_num) hεdiag.le (by simpa only [one_mul] using hmassBudget) hBz hBD
  filter_upwards [hdiag, hnumeric] with L hdiag hnumeric
  intro bsize hsize
  have hdiag := hdiag bsize hsize
  dsimp only at hdiag hnumeric ⊢
  rw [hsize] at hnumeric
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr hgap
  have he := hdiag tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets
    primeLo cutoff tier X Δ hi b
    φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr
  let m := bsize + bsize
  let H := G (n + 1)
  let arch := Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
    ((2 ^ n * 4 : ℕ) : ℝ) * b -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)))
  have hglobal : (global.card : ℝ) ≤ Real.exp ((K + 1) * L) := by
    apply le_trans _ hdel
    exact_mod_cast (show global.card ≤ global.card +
      (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) +
      outside.length by omega)
  have hnumer := hnumeric global Qν hglobal hν hνmass arch (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr hgap)
  apply he.trans
  have hexp :
      Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) = arch := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreassoc (a b c d e : ℝ) : (a * b * c) * (d * e) = (a * d) * (b * c) * e := by ring
  rw [hreassoc, hexp]
  have henergy := early_diagonal_energy_le n hearly (m : ℝ)
    (Real.exp ((2 ^ n : ℕ) * Δ +
      (Real.log 12 + 1) * (2 ^ n : ℕ) * m + εdiag * m))
    (Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) (Real.exp (-gain * m))
    (Nat.cast_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _)
  apply (mul_le_mul_of_nonneg_left henergy (by positivity)).trans
  apply le_trans ?_ hnumer
  dsimp only [gain, arch, m, H]
  push_cast
  gcongr
  simpa only [Nat.cast_add] using hΔupper

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInitialDiagonalAll
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform diagonal formula for every used finite depth -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_diagonal_all
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n < k)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : 4 * (K + 1) * r ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex n × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      4 + r + 4 * n = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, n ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex n × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V n < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ n * 4 : ℕ) : ℝ) * btop -
          ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G n r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * m) := by
  by_cases hnsmall : n ≤ 1
  · have hearly := P.moving_selected_initial_early_diagonal_decay C hM ψ n r k hk hn hnsmall
      A Wwin Bφ Dφ c K εdiag Bs BD Bz B hA hWwin hBφ hDφ hc hK hεdiag hdepth
      hBs hBD0 hBz hmassBudget hBD
    refine ⟨1, by norm_num, le_rfl, 3, le_rfl, ?_⟩
    filter_upwards [hearly] with L hearly
    intro b hsize
    dsimp only at hearly ⊢
    intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
      primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
      hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
      hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
      hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
      hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
      hdeletebulk hsetsReg hb hφ1 hlower hvr hsep hgap
    exact hearly b hsize tierB primes hprimes d rinit sl sr fallback childBound pivotBound V
      outside p Dq sets primeLo cutoff tier X Δ hi btop φ G global Qμ Qν setsReg cb cd
      lower ggiant favorable hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
      (lt_of_lt_of_le zero_lt_one hm) hp hsets hsetsp hpupper hφpos hφ hlip hφout hShell
      hdel hout hν hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
      hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
      hsetsReg hb hφ1 hlower hvr hgap
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    exact P.moving_selected_initial_diagonal_decay C hM ψ j r k hk
      (by omega) A Wwin Bφ Dφ c K εdiag Bs BD Bz B hA hWwin hBφ hDφ hc hK hεdiag
      hdepth Dlog hDlog hloglip hBs hBD0 hBz hmassBudget hBD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInitialDiagonalUniform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One smallness parameter and prime cutoff for every used diagonal -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_diagonal_uniform_oai
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (r : Fin k → ℕ) (hk : 0 < k)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : ∀ i, 4 * (K + 1) * r i ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ depth : Fin k, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot depth.val (r depth) m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot depth.val (r depth) m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex depth.val × Fin (r depth) → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (depth.val + 1)
      let slot := movingTemplateBulk depth.val (r depth) m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V depth.val)).erase 0
      4 + (r depth) + 4 * depth.val = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V depth.val : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, depth.val ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot depth.val (4 + (r depth)) m) + 4 * depth.val * 2 ^ depth.val) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ depth.val → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V depth.val ≤ primeLo → V depth.val < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ depth.val, (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex depth.val × Fin (r depth), ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V depth.val < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ depth.val * 4 : ℕ) : ℝ) * btop -
          ((∑ j, lower j) + (2 ^ depth.val : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ depth.val : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G depth.val (r depth) m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ depth.val : ℕ) * m) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hdata (i : Fin k) := P.moving_selected_initial_diagonal_all C hM ψ i.val (r i) k hk i.isLt
    A Wwin Bφ Dφ c K εdiag Bs BD Bz B hA hWwin hBφ hDφ hc hK hεdiag hdepth
    Dlog hDlog hloglip hBs hBD0 hBz (hmassBudget i) hBD
  choose eps heps heps1 cutoff hcut hL using hdata
  let ε := Finset.univ.inf' Finset.univ_nonempty eps
  let p₀ := Finset.univ.sup cutoff
  have hε : 0 < ε := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    exact heps i
  have hεi (i : Fin k) : ε ≤ eps i := Finset.inf'_le eps (Finset.mem_univ i)
  have hpc (i : Fin k) : cutoff i ≤ p₀ := Finset.le_sup (Finset.mem_univ i)
  refine ⟨ε, hε, (hεi ⟨0, hk⟩).trans (heps1 _), p₀,
    (hcut ⟨0, hk⟩).trans (hpc _), ?_⟩
  filter_upwards [eventually_all.mpr hL] with L hL
  intro depth b hsize
  have hi := hL depth b hsize
  dsimp only at hi ⊢
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hiWin φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep hgap
  exact hi tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hiWin φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
    hm (fun j => (hpc depth).trans (hp j)) hsets hsetsp hpupper hdlo hdhi
    (fun j => (hβ j).trans (hεi depth)) hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep hgap

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform_oai := @OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform_oai
