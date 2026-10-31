-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:20:53.067067+00:00
-- url     : https://prove2.me/submissions/402ba881-66c8-44b5-8746-45939b1079eb

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_diagonal_ideal_integral_rate
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_pattern_diagonal_haar_rate

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

theorem arithmetic_error_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ n + C * L * Real.exp (a * L)) *
        Real.exp (-c * Real.exp (b * L)) ≤ Real.exp (-Real.exp (d * L)) := by
  filter_upwards [arithmetic_exponent_absorption a b d C c n hb hab hdb hc] with L hL
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSpectatorNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer pivot gives the spectator's rational reconstruction -/

namespace Ostmann

theorem spectator_frequency_ne_zero {q : ℕ} [Fact q.Prime] (s : ℤ)
    (hs : s ≠ 0) (hsmall : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz)
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hd)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitTreeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem pairFrequencySupportBound_nonneg (D : ℝ) (f : NodeFrequencies × NodeFrequencies) :
    0 ≤ pairFrequencySupportBound D f := by unfold pairFrequencySupportBound; positivity

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

theorem movingGiantFrequencyUnits_of_bounds {q n : ℕ} [Fact q.Prime]
    (t : FrequencyTree ℤ n)
    (h : ∀ s ∈ allFrequencyList n t, s ≠ 0 ∧ s.natAbs < q) :
    movingGiantFrequencyUnits q n t := by
  induction n with
  | zero =>
    have hs := h (frequencyRoot 0 t) (by simp [allFrequencyList, frequencyRoot])
    exact spectator_frequency_ne_zero _ hs.1 hs.2
  | succ n ih =>
    refine ⟨spectator_frequency_ne_zero _ (h t.1 (by simp [allFrequencyList])).1
      (h t.1 (by simp [allFrequencyList])).2, ?_, ?_⟩
    · apply ih t.2.1
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    · apply ih t.2.2
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSizes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the constructed Fourier variation bound -/

namespace Ostmann
open scoped SchwartzMap

/-- Uniform in moving endpoints whose width has the actual exponential scale. -/
theorem movingFourierVariationBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n : ℕ)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ≤
        Real.exp (C * (m + 1)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 ψ
  let D := SchwartzMap.seminorm ℝ 0 1 ψ
  let K := 3 * B + D
  let r : ℝ := (2 ^ n : ℕ)
  have hB : 0 ≤ B := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD : 0 ≤ D := schwartz_profile_lip_nonneg ψ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r * (K + A + H + 1), by positivity, ?_⟩
  intro m hm lo hi hhi hwidth
  have heA : 1 ≤ Real.exp (A * m) := Real.one_le_exp_iff.mpr (mul_nonneg hA hm)
  have heH : 1 ≤ Real.exp (H * m) := Real.one_le_exp_iff.mpr (mul_nonneg hH hm)
  have heAll : Real.exp (A * m) * Real.exp (H * m) = Real.exp ((A + H) * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hproduct : 1 ≤ Real.exp (A * m) * Real.exp (H * m) :=
    heH.trans (le_mul_of_one_le_left (Real.exp_nonneg _) heA)
  have hHproduct : Real.exp (H * m) ≤ Real.exp (A * m) * Real.exp (H * m) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) heA
  have hpoly : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      K * Real.exp ((A + H) * m) := by
    calc
      _ ≤ 2 * B + (B + D * Real.exp (A * m)) * Real.exp (H * m) := by gcongr
      _ ≤ K * (Real.exp (A * m) * Real.exp (H * m)) := by
        dsimp only [K]
        nlinarith [mul_le_mul_of_nonneg_left hproduct hB,
          mul_le_mul_of_nonneg_left hHproduct hB]
      _ = _ := by rw [heAll]
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hbase : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      Real.exp (K + (A + H) * m) := by
    rw [Real.exp_add]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _))
  unfold movingFourierVariationBudget
  change (2 * B + (B + D * Real.exp (A * m)) * (hi - lo)) ^ (2 ^ n) ≤ _
  apply (pow_le_pow_left₀ (by positivity) hbase (2 ^ n)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change r * (K + (A + H) * m) ≤ r * (K + A + H + 1) * (m + 1)
  nlinarith [mul_nonneg hK hm]

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmallFrequencyUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-prime frequency tests follow from the actual range separation -/

namespace Ostmann

theorem MovingSlotData.Frequencies.mono {σ : Type*} {P Q : ℤ → Prop}
    {n : ℕ} {T : MovingSlotData σ n} (h : T.Frequencies P) (hPQ : ∀ s, P s → Q s) :
    T.Frequencies Q := by
  induction T with
  | leaf => exact hPQ _ h
  | node s CL CR U left right ihL ihR => exact ⟨hPQ s h.1, ihL h.2.1, ihR h.2.2⟩

theorem small_prime_frequency_unit (p : ℕ) (hp : p.Prime) (s : ℤ)
    (hs : s ≠ 0) (hsp : s.natAbs < p) : IsCoprime s (p : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hs) hsp)).symm

theorem MovingSlotData.small_frequency_units {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)) := by
  intro i
  induction T with
  | leaf s regular => exact small_prime_frequency_unit (value i) (hprime i) s hf (hV.trans_lt (hlarge i))
  | node s CL CR U left right ihL ihR =>
    exact ⟨small_prime_frequency_unit (value i) (hprime i) s hf.1 (hV.1.trans_lt (hlarge i)),
      ihL hf.2.1 hV.2.1, ihR hf.2.2 hV.2.2⟩

theorem MovingSlotData.small_frequency_residues {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0) := by
  intro i
  let : Fact (value i).Prime := ⟨hprime i⟩
  apply (T.small_frequency_units value hprime V hlarge hf hV i).mono
  intro s hs
  have hu : IsUnit (s : ZMod (value i)) := by
    apply isCoprime_zero_right.mp
    simpa only [Int.cast_natCast, ZMod.natCast_self] using hs.intCast (R := ZMod (value i))
  exact hu.ne_zero

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ConductorDeletion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor support after deleting one large prime

For each exceptional conductor choose one prime divisor above the threshold,
if there is one, and exclude that value from the nongiant priors. A conductor
that still divides the arithmetic modulus is then supported on its frequency
block, with full prime-power multiplicity.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem deletedConductorPrime_spec {D T p : ℕ}
    (h : deletedConductorPrime D T = some p) : p.Prime ∧ p ∣ D ∧ T ≤ p := by
  unfold deletedConductorPrime at h
  split at h
  next hex =>
    have hp : hex.choose = p := Option.some.inj h
    exact hp ▸ hex.choose_spec
  next => simp at h

/-- If the chosen large divisor was excluded, any surviving conductor divides
only the small frequency modulus. No squarefree assumption on the conductor
or on either modulus is needed. -/
theorem conductor_dvd_frequency_of_deletion (D Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hdeleted : ∀ p, deletedConductorPrime D T = some p → ¬p ∣ R)
    (hD : D ∣ Q * R) : D ∣ Q := by
  by_cases hlarge : ∃ p, p.Prime ∧ p ∣ D ∧ T ≤ p
  · have hsel : deletedConductorPrime D T = some hlarge.choose := by
      simp [deletedConductorPrime, hlarge]
    obtain ⟨hp, hpD, hpT⟩ := hlarge.choose_spec
    have hpQR := dvd_trans hpD hD
    rcases hp.dvd_mul.mp hpQR with hpQ | hpR
    · exact False.elim ((not_lt_of_ge hpT) (hQ _ hp hpQ))
    · exact False.elim (hdeleted _ hsel hpR)
  · have hcop : D.Coprime R := Nat.coprime_of_dvd fun p hp hpD hpR =>
      hlarge ⟨p, hp, hpD, hR p hp hpR⟩
    exact hcop.dvd_of_dvd_mul_left (by simpa only [Nat.mul_comm] using hD)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageConductorProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected Page correction factors through the frequency modulus -/

namespace Ostmann

open Classical

/-- After excluding a selected large conductor prime, the correction on
the full modulus is exactly its correction on the frequency modulus. -/
theorem pageAtModulus_mul_eq (z : Option PrimitiveRealZero) (Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ R) :
    pageAtModulus (Q * R) z = pageAtModulus Q z := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ Q * R
    · have hf := conductor_dvd_frequency_of_deletion e.modulus Q R T hQ hR
        (hexcluded e rfl) hd
      simp [pageAtModulus, hd, hf]
    · have hf : ¬e.modulus ∣ Q := fun h => hd (dvd_mul_of_dvd_left h R)
      simp [pageAtModulus, hd, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate the nonperiodic prime coincidences from frequency support -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The only nonperiodic part of this factor consists of the explicit
regular-prime coincidence tests. The remaining node bounds are independent
of the numerical bulk values. -/
theorem movingFrequencyPairFactor_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R x y : ℤ) :
    movingFrequencyPairFactor value outside F E T nodes R x y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCore value F E T R x y := by
  have he : movingFrequencyPairSupport value outside T nodes R x y ↔
      (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) ∧
      (∀ b, movingFrequencyGate value R (T b) x y) := by
    simp only [movingFrequencyPairSupport, Bool.forall_bool]
    tauto
  unfold movingFrequencyPairFactor movingFrequencyCore
  rw [he]
  by_cases hs : ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)
  · by_cases hc : ∀ b, movingFrequencyGate value R (T b) x y
    · rw [ite_eq_left ⟨hs, hc⟩, ite_eq_left hs, ite_eq_left hc, one_mul]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_left hs, ite_eq_right hc, mul_zero]
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

theorem frequencyLeafWeight_nonneg {A : Type} (W : A → ℝ) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyLeafWeight W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (ih _) (ih _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The modulus attached to one fixed frequency history -/

namespace Ostmann

open scoped BigOperators Classical

theorem historyFrequencyProduct_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyProduct S n t := by
  induction n with
  | zero => exact Int.natAbs_pos.mpr (hS _ t.property)
  | succ n ih =>
      exact Nat.mul_pos
        (Nat.mul_pos (Int.natAbs_pos.mpr (hS _ t.1.property)) (ih _)) (ih _)

theorem historyFrequencyProduct_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n : ℕ) (t : FrequencyTree S n) :
    historyFrequencyProduct S n t ≤ N ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simpa [historyFrequencyProduct] using hS _ t.property
  | succ n ih =>
    have he : 2 ^ (n + 1 + 1) - 1 = 1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1) := by
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    calc
      _ ≤ N * N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hS _ t.1.property) (ih _)) (ih _)
      _ = _ := by rw [he]; simp only [pow_add, pow_one]

/-- All actual primes exceed the frequency range. Consequently they are
units for the full history modulus, including its precision exponent. -/
theorem prime_coprime_historyFrequencyModulus (S : Finset ℤ) (N p : ℕ)
    (hp : p.Prime) (hpN : N < p)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    p.Coprime (historyFrequencyModulus S n k t) := by
  have hfreq (s : S) : p.Coprime (s : ℤ).natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hpos : 0 < (s : ℤ).natAbs := Int.natAbs_pos.mpr (hS _ s.property).1
    have hle := Nat.le_of_dvd hpos hd
    have hbound := (hS _ s.property).2
    omega
  have hprod : p.Coprime (historyFrequencyProduct S n t) := by
    induction n with
    | zero => exact hfreq t
    | succ n ih => exact (hfreq t.1).mul_right (ih t.2.1) |>.mul_right (ih t.2.2)
  exact hprod.pow_right (k + 2)

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageRegularAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page term in the actual regular-prime average -/

namespace Ostmann
open scoped Classical BigOperators

/-- The deletion prescribed before the nongiant priors prevents an exceptional
conductor from using any prime in the regular block, including its powers. -/
theorem pageAtModulus_regular_factor (z : Option PrimitiveRealZero) (C R T : ℕ)
    (hC : ∀ p, p.Prime → p ∣ C → T ≤ p)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ C * R) :
    pageAtModulus (C * R) z = pageAtModulus R z := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ C * R
    · have hr : e.modulus ∣ R := by
        by_cases hlarge : ∃ p, p.Prime ∧ p ∣ e.modulus ∧ T ≤ p
        · have hp : deletedConductorPrime e.modulus T = some hlarge.choose := by
            simp [deletedConductorPrime, hlarge]
          exact False.elim (hexcluded e rfl _ hp (hlarge.choose_spec.2.1.trans hd))
        · have hc : e.modulus.Coprime C := Nat.coprime_of_dvd fun p hp hpe hpc =>
            hlarge ⟨p, hp, hpe, hC p hp hpc⟩
          exact hc.dvd_of_dvd_mul_left hd
      simp [pageAtModulus, hd, hr]
    · have hr : ¬ e.modulus ∣ R := fun h => hd (dvd_mul_of_dvd_right h C)
      simp [pageAtModulus, hd, hr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem modulus_le_exp_bulk_endpoint {M : ℕ} {L u : ℝ}
    (hM : M ≤ bulkProgressionCutoff L) (hL : 0 ≤ L)
    (hu : Real.exp ((39 / 10000 : ℝ) * L) ≤ u) :
    (M : ℝ) ≤ Real.exp u := by
  apply (Nat.cast_le.mpr hM).trans
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  exact (Real.exp_le_exp.mpr (by linarith)).trans hu

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

theorem movingSampleTier_lt {n : ℕ} (i : MovingSampleIndex n) : movingSampleTier i < n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
      rcases i with i | ⟨b, i⟩
      · exact Nat.lt_succ_self n
      · exact (ih i).trans (Nat.lt_succ_self n)

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A modulus using only the frequencies of the two fixed histories -/

namespace Ostmann
open scoped Classical

theorem frequencyModelBase_pos (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) : 0 < frequencyModelBase S n t :=
  Nat.mul_pos (historyFrequencyProduct_pos S hS n _) (historyFrequencyProduct_pos S hS n _)

theorem frequencyModelBase_le (S : Finset ℤ) (n N : ℕ) (t : FrequencyTree (S × S) n)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) :
    frequencyModelBase S n t ≤ N ^ (2 * (2 ^ (n + 1) - 1)) := by
  calc
    _ ≤ N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
      Nat.mul_le_mul (historyFrequencyProduct_le S N hN n _) (historyFrequencyProduct_le S N hN n _)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem buildMovingSlotData_frequencyProduct_abs {σ : Type*}
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a).frequencyProduct.natAbs =
      historyFrequencyProduct S n t := by
  induction a with
  | leaf => rfl
  | @node n u l r ihL ihR =>
    simp only [buildMovingSlotData, frequencyTreeMap, MovingSlotData.frequencyProduct,
      Int.natAbs_mul, historyFrequencyProduct, ihL, ihR]

theorem frequencyModelModulus_precision (R n : ℕ) :
    (R : ℤ) ^ (n + 1) ∣ ((R ^ (n - 1 + 2) : ℕ) : ℤ) := by
  rw [Nat.cast_pow]
  exact pow_dvd_pow (R : ℤ) (by omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeGridSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grid covers exactly the original prime interval -/

namespace Ostmann

open scoped Classical

theorem mem_gridPrimeSupport_iff (N q : ℕ) [NeZero q] (s h : ℝ) (hh : 0 ≤ h) (p : ℕ) :
    p ∈ primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h) ↔
      p.Prime ∧ p.Coprime q ∧ Real.log (p : ℝ) ∈ Set.Ioc s (s + N * h) := by
  constructor
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hres, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hc
    have heq := (ZMod.natCast_eq_natCast_iff p (gridResidue c) q).mpr hres
    simp only [gridResidue, ZMod.natCast_zmod_val] at heq
    have hcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp (by
      rw [heq]
      exact c.2.isUnit)
    have hj : (c.1 : ℝ) + 1 ≤ N := by
      exact_mod_cast (show c.1.val + 1 ≤ N from c.1.isLt)
    have hj0 : (0 : ℝ) ≤ c.1 := by positivity
    dsimp [gridLower, gridUpper] at hlo hhi
    exact ⟨hprime, hcop, by nlinarith, by nlinarith⟩
  · rintro ⟨hprime, hcop, hlog⟩
    have hmem : Real.log (p : ℝ) ∈
        Set.Ioc ((fun j : ℕ => s + j * h) 0) ((fun j : ℕ => s + j * h) N) := by
      simpa using hlog
    have hu := Ioc_subset_biUnion_Ioc N (fun j : ℕ => s + j * h) hmem
    simp only [Set.mem_iUnion] at hu
    obtain ⟨j, hj, hbound⟩ := hu
    let c : Fin N × (ZMod q)ˣ := (⟨j, Finset.mem_range.mp hj⟩, ZMod.unitOfCoprime p hcop)
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, mem_primeLogCellSet_iff.mpr ⟨hprime, ?_, ?_⟩⟩
    · apply (ZMod.natCast_eq_natCast_iff p (gridResidue c) q).mp
      simp [c, gridResidue]
    · simpa only [c, gridLower, gridUpper, Nat.cast_add, Nat.cast_one] using hbound

/-- At these scales the modulus is below every sampled prime, so every
prime in the log interval appears in the unit-residue grid. -/
theorem mem_gridPrimeSupport_iff_prime (N q : ℕ) [NeZero q] (s h : ℝ)
    (hh : 0 ≤ h) (hq : (q : ℝ) ≤ Real.exp s) (p : ℕ) :
    p ∈ primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h) ↔
      p.Prime ∧ Real.log (p : ℝ) ∈ Set.Ioc s (s + N * h) := by
  rw [mem_gridPrimeSupport_iff N q s h hh p]
  constructor
  · exact fun hp => ⟨hp.1, hp.2.2⟩
  · rintro ⟨hp, hlog⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hqp : q < p := by
      exact_mod_cast hq.trans_lt ((Real.lt_log_iff_exp_lt hp0).mp hlog.1)
    have hcop := hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqp)
    exact ⟨hp, hcop, hlog⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticModuli_product {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) :
    (∏ b, movingArithmeticModuli r q P S b) =
      r * ((∏ p ∈ P, p) ^ 2 * ∏ i ∈ S, q i) := by
  simp only [Fintype.prod_sum_type, movingArithmeticModuli, Fintype.prod_unique,
    Finset.prod_coe_sort, Finset.prod_pow]
  have hp : (∏ x : P, (x : ℕ)) = ∏ p ∈ P, p := Finset.prod_coe_sort P (fun p : ℕ => p)
  rw [hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality of the concrete arithmetic blocks -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticModuli_ne_zero {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) (hr : r ≠ 0)
    (hp : ∀ p ∈ P, p.Prime) (hq : ∀ i ∈ S, (q i).Prime)
    (b : MovingArithmeticBlocks P S) : movingArithmeticModuli r q P S b ≠ 0 := by
  rcases b with u | (p | i)
  · exact hr
  · exact pow_ne_zero _ (hp p.val p.property).ne_zero
  · exact (hq i.val i.property).ne_zero

theorem movingArithmeticModuli_coprime {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I)
    (hp : ∀ p ∈ P, p.Prime) (hq : ∀ i ∈ S, (q i).Prime)
    (hinj : Set.InjOn q S)
    (hrp : ∀ p ∈ P, r.Coprime p) (hrq : ∀ i ∈ S, r.Coprime (q i))
    (hd : ∀ p ∈ P, ∀ i ∈ S, p ≠ q i) :
    Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
      (movingArithmeticModuli r q P S c)) := by
  rintro (u | (p | i)) (v | (t | j)) hne
  · cases u; cases v
    exact False.elim (hne rfl)
  · exact (hrp t.val t.property).pow_right 2
  · exact hrq j.val j.property
  · exact (hrp p.val p.property).symm.pow_left 2
  · have hpt : p.val ≠ t.val := fun h => hne (by rw [Subtype.ext h])
    exact (((Nat.coprime_primes (hp p.val p.property) (hp t.val t.property)).mpr hpt).pow_left 2).pow_right 2
  · exact ((Nat.coprime_primes (hp p.val p.property) (hq j.val j.property)).mpr
      (hd p.val p.property j.val j.property)).pow_left 2
  · exact (hrq i.val i.property).symm
  · exact ((Nat.coprime_primes (hp t.val t.property) (hq i.val i.property)).mpr
      (hd t.val t.property i.val i.property)).symm.pow_right 2
  · have hij : q i.val ≠ q j.val := fun h =>
      hne (by rw [Subtype.ext (hinj i.property j.property h)])
    exact (Nat.coprime_primes (hq i.val i.property) (hq j.val j.property)).mpr hij

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenFrequencyAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency/Page average on the fixed bulk residue representative -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingFrequencyPageAverage_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  simp only [movingFrequencyPageAverage, movingFrequencyPairFactor_core,
    movingFrequencyCorePageAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternUniformBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform costs of the actual internal equality patterns -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_class_card_le {C : Type*} [Fintype C] (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) :
    Fintype.card C ≤ 4 * n * 2 ^ n := by
  have hinj : Function.Injective (fun c => (rep c).val) := by
    intro c d h
    have hh := congrArg pattern h
    simpa only [(rep c).property, (rep d).property] using hh
  simpa only [card_movingSamplePairIndex] using Fintype.card_le_of_injective _ hinj

/-- The representative-prior loss is bounded independently of how the
internal slots coincide. -/
theorem movingPattern_loss_le (n r : ℕ) (hr : r ≤ 4 * n * 2 ^ n)
    (E : ℝ) (hE : 0 ≤ E) :
    (2 : ℝ) ^ r * E ^ (4 * n * 2 ^ n - r) ≤
      (max 2 E) ^ (4 * n * 2 ^ n) := by
  have hK : 0 ≤ max (2 : ℝ) E := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  calc
    _ ≤ (max 2 E) ^ r * (max 2 E) ^ (4 * n * 2 ^ n - r) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) (le_max_left _ _) r)
        (pow_le_pow_left₀ hE (le_max_right _ _) _) (by positivity) (pow_nonneg hK _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternCostRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual equality-pattern cost fits the source's error budget -/

namespace Ostmann
open Filter

/-- All equality patterns and representative-prior losses contribute only a
fixed-depth exponential in L when p times its prior is at most exp(C L). -/
theorem movingPattern_total_cost_le_exp (n : ℕ) (C L : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L) :
    (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n) ≤
      Real.exp ((((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * C * L) := by
  let J := 4 * n * 2 ^ n
  have hCL : 1 ≤ C * L := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ C * L := mul_le_mul hC hL (by norm_num) (by linarith)
  have he : (2 : ℝ) ≤ Real.exp (C * L) := by
    have h := Real.add_one_le_exp (C * L)
    linarith
  rw [max_eq_right he]
  calc
    _ ≤ (Real.exp (C * L)) ^ (J ^ 2) * (Real.exp (C * L)) ^ J :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he _) (by positivity)
    _ = Real.exp (((J ^ 2 + J : ℕ) : ℝ) * C * L) := by
      rw [← pow_add, ← Real.exp_nat_mul]
      congr 1
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalErrorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual internal arithmetic error at the source's prime scales -/

namespace Ostmann
open Filter

/-- The logarithm of the polynomial height, before the prime-divisor count.
Only the sampled-coordinate lower cutoff will divide this expression. -/
theorem moving_internal_log_height (n d : ℕ) (F U C D L : ℝ)
    (hF : 1 ≤ F) (hU : 1 ≤ U) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hfreq : Real.log F ≤ C * L) (hdegree : (d : ℝ) ≤ D * L)
    (hvalue : Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L)) :
    Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) ≤
      (1 + 2 * ((n : ℝ) + 1) * (1 + C + D)) * L *
        Real.exp ((12 / 1000 : ℝ) * L) := by
  have hF0 : 0 < F := lt_of_lt_of_le (by norm_num) hF
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hexp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have heq : Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) =
      Real.log 2 + 2 * ((n : ℝ) + 1) *
        (Real.log 2 + Real.log F + (d : ℝ) * Real.log U) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_mul hF0.ne' (pow_ne_zero _ hU0.ne'), Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hd : (d : ℝ) * Real.log U ≤ D * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    mul_le_mul hdegree hvalue (Real.log_nonneg hU) (by positivity)
  have hCL : C * L ≤ C * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    le_mul_of_one_le_right (by positivity) hexp
  have hunit : 1 ≤ L * Real.exp ((12 / 1000 : ℝ) * L) :=
    one_le_mul_of_one_le_of_one_le hL hexp
  have hinn : Real.log 2 + Real.log F + (d : ℝ) * Real.log U ≤
      (1 + C + D) * L * Real.exp ((12 / 1000 : ℝ) * L) := by
    nlinarith
  rw [heq]
  have hm := mul_le_mul_of_nonneg_left hinn
    (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
  nlinarith

/-- The source's three internal errors have a common exponential saving.
The prime-divisor term is evaluated with the internal-prime cutoff. -/
theorem moving_internal_error_small (n c : ℕ) (C D E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : ℕ) (F U α β : ℝ),
      1 ≤ F → 1 ≤ U → 0 ≤ α →
      α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) → 0 ≤ β →
      Real.log F ≤ C * L → (d : ℝ) ≤ D * L →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      movingInternalArithmeticError n c d F U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
      Real.exp (-((1 / 2 : ℝ) * Real.exp ((39 / 10000 : ℝ) * L))) := by
  let K : ℝ := 1 + 2 * ((n : ℝ) + 1) * (1 + C + D)
  let a : ℝ := (2 * (2 ^ n - 1 : ℕ)) * c
  let b : ℝ := 2 * (c * (2 + 2 * (2 ^ n - 1)) : ℕ)
  let H : ℝ := a + b * (2 * ((n : ℝ) + 1) * D + K)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hrate := arithmetic_exponent_absorption 0 (39 / 10000) 0
    (H + E + 12 / 1000) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hrate, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  have hheight := moving_internal_log_height n d F U C D L hF hU hC hD hL hfreq hdegree hvalue
  have hV : 1 ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hheight0 : 0 ≤ Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) := by
    apply Real.log_nonneg
    have hbase : 1 ≤ 2 * (F * U ^ d) := by
      have := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hU (n := d))
      linarith
    have := one_le_pow₀ (one_le_pow₀ hbase (n := n + 1)) (n := 2)
    linarith
  have hquot : Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
      Real.exp ((1 / 100 : ℝ) * L) ≤ K * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    (div_le_self hheight0 hV).trans hheight
  have hdeg : ((2 * ((n + 1) * d) : ℕ) : ℝ) ≤ 2 * ((n : ℝ) + 1) * D * L := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
    nlinarith
  have hsave : Real.exp ((39 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hβcommon : β ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
    hβbound.trans (Real.exp_le_exp.mpr (by linarith))
  have hexp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hunit : 1 ≤ L * Real.exp ((12 / 1000 : ℝ) * L) :=
    one_le_mul_of_one_le_of_one_le hL hexp
  have he0 : 0 ≤ E * L := mul_nonneg hE (by linarith)
  have he : Real.exp (-Real.exp ((1 / 100 : ℝ) * L)) ≤
      Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hterms :
      a * Real.exp (-Real.exp ((1 / 100 : ℝ) * L)) +
        b * (((2 * ((n + 1) * d) : ℕ) : ℝ) * α +
          Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
            Real.exp ((1 / 100 : ℝ) * L) * β) ≤
      H * L * Real.exp ((12 / 1000 : ℝ) * L) *
        Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) := by
    have hdeg' : 2 * ((n : ℝ) + 1) * D * L ≤
        2 * ((n : ℝ) + 1) * D * L * Real.exp ((12 / 1000 : ℝ) * L) :=
      le_mul_of_one_le_right (by positivity) hexp
    have hαterm := mul_le_mul hdeg hα hα0 (by positivity)
    have hβterm := mul_le_mul hquot hβcommon hβ (by positivity)
    have hsum := add_le_add hαterm hβterm
    have hsum' :
        ((2 * ((n + 1) * d) : ℕ) : ℝ) * α +
            Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
              Real.exp ((1 / 100 : ℝ) * L) * β ≤
        (2 * ((n : ℝ) + 1) * D * L + K * L * Real.exp ((12 / 1000 : ℝ) * L)) *
          Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
      hsum.trans_eq (by ring)
    have hbm := mul_le_mul_of_nonneg_left
      (hsum'.trans (mul_le_mul_of_nonneg_right (add_le_add hdeg' le_rfl) (Real.exp_nonneg _))) hb
    have ham := mul_le_mul_of_nonneg_left he ha
    have ha' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hunit ha)
      (Real.exp_nonneg (E * L - Real.exp ((39 / 10000 : ℝ) * L)))
    simp only [mul_one] at ha'
    exact (add_le_add (ham.trans ha') hbm).trans_eq (by dsimp only [H]; ring)
  change a * _ + b * _ ≤ _
  apply hterms.trans
  have hpref : H * L ≤ Real.exp (H * L) := by
    linarith [Real.add_one_le_exp (H * L)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg ((12 / 1000 : ℝ) * L)))
    (Real.exp_nonneg (E * L - Real.exp ((39 / 10000 : ℝ) * L)))
  apply hh.trans
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one] at hrate
  have : (H + E + 12 / 1000) * L ≤ (1 / 2 : ℝ) * Real.exp ((39 / 10000 : ℝ) * L) := by
    have hc : 0 ≤ (H + E + 12 / 1000) * L := by positivity
    nlinarith
  linarith

/-- Summing equality patterns and paying the true pointwise kernel/spectator
cost still leaves the stated internal-prime error. -/
theorem moving_internal_error_with_cost (n c : ℕ) (C D E Cprior B : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hCprior : 1 ≤ Cprior) (_hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : ℕ) (F U α β : ℝ),
      1 ≤ F → 1 ≤ U → 0 ≤ α →
      α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) → 0 ≤ β →
      Real.log F ≤ C * L → (d : ℝ) ≤ D * L →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        movingInternalArithmeticError n c d F U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  let J : ℝ := ((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ)
  let B' := B + J * Cprior
  filter_upwards [moving_internal_error_small n c C D E hC hD hE,
    arithmetic_error_absorption (1 / 1000) (39 / 10000) (2 / 1000) B' (1 / 2) 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hsmall hcost hL
  intro d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  have hJ : 0 ≤ J := by positivity
  have hJL : J * Cprior * L ≤ J * Cprior * L ^ 2 := by
    have hC0 : 0 ≤ Cprior := by linarith
    exact mul_le_mul_of_nonneg_left (by nlinarith : L ≤ L ^ 2) (mul_nonneg hJ hC0)
  have hrest : B * L * Real.exp ((1 / 1000 : ℝ) * L) ≤
      B' * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    dsimp only [B']
    nlinarith [mul_nonneg hJ (show 0 ≤ Cprior by linarith)]
  have hbudget :
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) ≤
      Real.exp (B' * L ^ 2 + B' * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul_of_nonneg_right
      (movingPattern_total_cost_le_exp n Cprior L hCprior hL) (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [B']
    nlinarith
  have hs := hsmall d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  exact ((mul_le_mul_of_nonneg_left hs (by positivity)).trans
    (mul_le_mul_of_nonneg_right hbudget (Real.exp_nonneg _))).trans
      (by simpa only [neg_mul] using hcost)

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

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

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

theorem movingInternalArithmeticError_card (n c d : ℕ) (F U α β V : ℝ) :
    movingInternalArithmeticError n c d F U α β V =
      c * movingInternalArithmeticError n 1 d F U α β V := by
  simp only [movingInternalArithmeticError, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem movingInternalArithmeticError_mono_card (n c c' d : ℕ) (F U α β V : ℝ)
    (hcc : c ≤ c') (hF : 1 ≤ F) (hU : 1 ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 ≤ V) :
    movingInternalArithmeticError n c d F U α β V ≤
      movingInternalArithmeticError n c' d F U α β V := by
  rw [movingInternalArithmeticError_card n c, movingInternalArithmeticError_card n c']
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcc)
    (movingInternalArithmeticError_nonneg n 1 d F U α β V hF hU hα hβ hV)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compensation coincidences vanish on both original and arithmetic support -/

namespace Ostmann
open scoped Classical

theorem movingRegularOutsidePairwise_root {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (h : movingRegularOutsidePairwise value outside T) :
    (T.regularSlots.map value).Pairwise Nat.Coprime := by
  have hr : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
    cases T with
    | leaf => exact h
    | node => exact h.1
  exact (List.pairwise_append.mp hr).1

theorem movingFullOutsidePairwise_regular {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullOutsidePairwise value outside T XL XR) :
    movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf s regular =>
    exact h.tail.tail
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.1.tail.tail, ihL _ _ h.2.1, ihR _ _ h.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantErrorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant comparison error after the actual coefficient mass -/

namespace Ostmann
open Filter

/-- The upper prime cutoff costs one factor per internal class. Even at the
full permitted small-prime scale, the two giant errors remain negligible. -/
theorem movingPattern_giant_error_rate (n : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ c : ℕ, c ≤ 4 * n * 2 ^ n → ∀ E U : ℝ,
      0 ≤ E → E ≤ Real.exp (C * L) → 0 ≤ U → U ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      ((2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c) * U ^ c) *
        (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  let J := 4 * n * 2 ^ n
  let K : ℝ := ((J ^ 2 + J : ℕ) : ℝ) * C
  let H : ℝ := K + J + 1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  filter_upwards [arithmetic_error_absorption (12 / 1000) (1225 / 100000) (2 / 1000)
    H 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L herr hL c hc E U hE hEC hU hUC
  have hL0 : 0 ≤ L := by linarith
  have hExp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hprior : (2 : ℝ) ^ c * E ^ (J - c) ≤ Real.exp (K * L) := by
    calc
      _ ≤ (max 2 E) ^ J := movingPattern_loss_le n c hc E hE
      _ ≤ (max 2 (Real.exp (C * L))) ^ J :=
        pow_le_pow_left₀ (by positivity) (max_le_max_left _ hEC) J
      _ ≤ (2 : ℝ) ^ (J ^ 2) * (max 2 (Real.exp (C * L))) ^ J :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ ≤ _ := movingPattern_total_cost_le_exp n C L hC hL
  have hU' : U ^ c ≤ Real.exp ((J : ℝ) * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      _ ≤ (Real.exp (Real.exp ((12 / 1000 : ℝ) * L))) ^ c := pow_le_pow_left₀ hU hUC c
      _ ≤ (Real.exp (Real.exp ((12 / 1000 : ℝ) * L))) ^ J :=
        pow_le_pow_right₀ (Real.one_le_exp_iff.mpr (Real.exp_pos _).le) hc
      _ = _ := (Real.exp_nat_mul _ J).symm
  let mass := (2 : ℝ) ^ c * E ^ (J - c) * U ^ c
  have hmass0 : 0 ≤ mass := by dsimp only [mass]; positivity
  have hmass : mass ≤ Real.exp (K * L + (J : ℝ) * Real.exp ((12 / 1000 : ℝ) * L)) := by
    simpa only [Real.exp_add] using mul_le_mul hprior hU' (pow_nonneg hU _) (Real.exp_nonneg _)
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hdouble : 2 * mass ≤ Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul htwo hmass hmass0 (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hJL : (J : ℝ) ≤ (J : ℝ) * L := le_mul_of_one_le_right (Nat.cast_nonneg _) hL
    have hHJ : (J : ℝ) ≤ H := by dsimp only [H]; linarith
    have hJHL : (J : ℝ) ≤ H * L := hJL.trans (mul_le_mul_of_nonneg_right hHJ hL0)
    have he := mul_le_mul_of_nonneg_right hJHL (Real.exp_nonneg ((12 / 1000 : ℝ) * L))
    dsimp only [H] at *
    nlinarith
  have hsmall : Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    have hh : (1225 / 100000 : ℝ) * L ≤ (125 / 10000 : ℝ) * L := by linarith
    linarith [Real.exp_le_exp.mpr hh]
  change mass * _ ≤ _
  calc
    _ ≤ (2 * mass) * Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
      have h := mul_le_mul_of_nonneg_left hsmall hmass0
      nlinarith only [h]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hdouble (Real.exp_nonneg _)).trans
      (by simpa only [pow_one, one_mul, neg_mul] using herr)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the actual sharp pattern kernel -/

namespace Ostmann
open scoped SchwartzMap

theorem movingFourierVariationBudget_nonneg (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hhi : lo ≤ hi) :
    0 ≤ movingFourierVariationBudget ψ V lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hW := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  positivity

theorem movingPatternKernelBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hV⟩ := movingFourierVariationBudget_exp_window ψ n A H hA hH
  let c := (2 ^ n + (2 ^ n - 1)) + (3 * (2 ^ n - 1) + 2 * 2 ^ n)
  let a := 2 * c * (2 * n + 1) * 2 ^ n
  let b := 2 * c * (2 * n * (2 ^ n * (r₀ + 4 * n + 4)) +
    2 ^ n * (r₀ + 4 * n)) + 1
  let K : ℝ := a + b
  let H : ℝ := ((2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hK : 0 < K := by dsimp only [K, b]; positivity
  have hH : 0 ≤ H := sq_nonneg _
  refine ⟨K + 2 * C + H, by positivity, ?_⟩
  intro m lo hi hhi hwidth
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount :
      2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n))) +
        ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n)))) + 1 = a * m + b := by
    dsimp only [a, b, c]
    ring
  have hroot : ((a * m + b : ℕ) : ℝ) ≤ Real.exp (K * ((m : ℝ) + 1)) := by
    have hab : ((a * m + b : ℕ) : ℝ) ≤ K * ((m : ℝ) + 1) := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hm]
    exact hab.trans (by linarith [Real.add_one_le_exp (K * ((m : ℝ) + 1))])
  have hv0 := movingFourierVariationBudget_nonneg ψ (Real.exp (A * m)) lo hi n
    (Real.exp_nonneg _) hhi
  have hv2 := pow_le_pow_left₀ hv0 (hV m hm lo hi hhi hwidth) 2
  have hh : H ≤ Real.exp (H * ((m : ℝ) + 1)) := by
    have : H ≤ H * ((m : ℝ) + 1) := by nlinarith [mul_nonneg hH hm]
    exact this.trans (by linarith [Real.add_one_le_exp (H * ((m : ℝ) + 1))])
  unfold bulkKernelPairComparisonBudget
  rw [hcount, mul_pow]
  change ((a * m + b : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ^ 2 * H) ≤ _
  calc
    _ ≤ Real.exp (K * ((m : ℝ) + 1)) *
        ((Real.exp (C * ((m : ℝ) + 1))) ^ 2 * Real.exp (H * ((m : ℝ) + 1))) := by
      gcongr
    _ = Real.exp ((K + 2 * C + H) * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem movingPatternKernelBudget_spectatorScale_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C, hC, hb⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨C * ((k : ℝ) ^ 4 + 1) + 1, ?_, ?_⟩
  · have : 0 ≤ C * ((k : ℝ) ^ 4 + 1) := by positivity
    linarith
  intro L hL
  dsimp only
  intro lo hi hhi hwidth
  apply (hb _ lo hi hhi hwidth).trans
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hscale : (spectatorBulkCount k L : ℝ) + 1 ≤ ((k : ℝ) ^ 4 + 1) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLsq (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)
    nlinarith
  have := mul_le_mul_of_nonneg_left hscale hC.le
  nlinarith [sq_nonneg L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet gain absorbs the actual sharp-kernel main term -/

namespace Ostmann
open scoped SchwartzMap

theorem bulkKernelPair_smooth_le_budget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) :
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
    bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let c := 2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
    ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)))
  have hc : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 c
  exact le_mul_of_one_le_left (sq_nonneg _) hc

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

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

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

/-- A common prime upper bound controls all actual pointwise spectator
factors. This cost is retained in the cell error, separate from signed gain. -/
theorem moving_spectator_product_cost (n m : ℕ) (p : Fin m → ℕ)
    (V : ℝ) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * V) := by
  calc
    _ ≤ ∏ _i : Fin m, (Real.exp V) ^ (2 ^ (n + 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp i) _
    _ = _ := by
      simp only [← Real.exp_nat_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ring

theorem moving_spectator_linear_cost (n m : ℕ) (p : Fin m → ℕ)
    (K L A : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hm : (m : ℝ) ≤ K * L) (hamp : A ≤ Real.exp (K * L))
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) :
    A * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K * L *
        Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ Real.exp (K * L) *
        Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L)) :=
      mul_le_mul hamp (moving_spectator_product_cost n m p _ hp)
        (Finset.prod_nonneg fun i _ => by positivity) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (2 ^ (n + 1))))
        (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
      have hKL := mul_le_mul_of_nonneg_left hE (mul_nonneg hK hL)
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform giant variation cost at the selected-prime scales -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFourierVariationBudget_mono_frequency (ψ : 𝓢(ℝ, ℂ))
    (V W lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hVW : V ≤ W) (hhi : lo ≤ hi) :
    movingFourierVariationBudget ψ V lo hi n ≤ movingFourierVariationBudget ψ W lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hwidth := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  gcongr

/-- The complete pointwise cost needed for both giant integrations is bounded
before choosing the Fourier window, its frequencies, or the spectator primes. -/
theorem movingPattern_pointwise_cost_budget (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi : ℝ), 0 ≤ V → V ≤ Real.exp (A * m) →
      lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
          (movingFourierVariationBudget ψ V lo hi n *
            (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale_window
    ψ n r₀ k A Wwin B D hA hWwin
  let K := (k : ℝ) ^ 4 + 4
  let Cs := (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K
  let C := max Cw Cs
  have hK : 4 ≤ K := by
    dsimp only [K]
    linarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hCwC : Cw ≤ C := le_max_left _ _
  have hCsC : Cs ≤ C := le_max_right _ _
  refine ⟨C, hCw.trans hCwC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi hV hVA hhi hwidth hp
  let m := spectatorBulkCount k L
  have hL0 : 0 ≤ L := by linarith
  have hm : (m : ℝ) ≤ K * L := (spectatorBulkCount_upper k L hL0).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hL0)
  have hKL : 4 ≤ K * L := by nlinarith
  have hamp : (4 : ℝ) ≤ Real.exp (K * L) := by
    linarith [Real.add_one_le_exp (K * L)]
  have hspec := moving_spectator_linear_cost n m p K L 4 (by linarith) hL0 (by norm_num) hm hamp hp
  have hprod : (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 = ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, pow_succ]
  have hspec' : 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    rw [hprod]
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    change Cs * L * Real.exp ((1 / 1000 : ℝ) * L) ≤ _
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hCsC hL0
    · exact Real.exp_le_exp.mpr (by nlinarith)
    · exact Real.exp_nonneg _
    · exact mul_nonneg (by linarith [hCw.trans hCwC]) hL0
  have hvar := movingFourierVariationBudget_mono_frequency ψ V (Real.exp (A * m)) lo hi n hV hVA hhi
  have hsmooth :
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
      Real.exp (C * L ^ 2) := by
    have hpow :
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (movingFourierVariationBudget_nonneg ψ V lo hi n hV hhi) hvar 2)
        (sq_nonneg _)
    exact hpow.trans ((bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
      ((hkernel L hL lo hi hhi hwidth).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))))
  calc
    _ ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) * Real.exp (C * L ^ 2) :=
      mul_le_mul hspec' hsmooth (sq_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternInternalError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The internal-prime error for the literal moving pattern cost -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- All internal class counts and moving windows share the same eventual
error bound. Only the original point-mass bounds on the priors are used. -/
theorem movingPattern_internal_arithmetic_error_rate (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D E : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hE : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (c : ℕ) (U α β amp lo hi : ℝ),
      c ≤ 4 * n * 2 ^ n → 1 ≤ U →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 ≤ α → α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      0 ≤ β → β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      0 ≤ amp → amp ≤ 4 → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ((amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2) *
        movingInternalArithmeticError n c (2 ^ n * (r₀ + m + 4 * n + 4))
          (Real.exp (A * m)) U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨C, hC, hcost⟩ := movingPattern_pointwise_cost_budget ψ n r₀ k A Wwin B D hA hWwin
  let H : ℝ := (2 ^ n : ℕ) * ((r₀ + 4 * n + 4 : ℕ) + (k : ℝ) ^ 4)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hAk : 0 ≤ A * (k : ℝ) ^ 4 := by positivity
  filter_upwards [moving_internal_error_with_cost n (4 * n * 2 ^ n)
    (A * (k : ℝ) ^ 4) H E 1 C hAk hH hE (by norm_num) (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L herr hL
  dsimp only
  intro p c U α β amp lo hi hc hU hUlog hα0 hα hβ0 hβ hamp0 hamp hhi hwidth hp
  let m := spectatorBulkCount k L
  let d := 2 ^ n * (r₀ + m + 4 * n + 4)
  let F := Real.exp (A * m)
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hF : 1 ≤ F := Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))
  have hFreq : Real.log F ≤ A * (k : ℝ) ^ 4 * L := by
    rw [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_left hm hA]
  have hdeg : (d : ℝ) ≤ H * L := by
    dsimp only [d, H]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (2 : ℝ) ^ n by positivity)
    have hbase := mul_le_mul_of_nonneg_left hL (show 0 ≤ (2 : ℝ) ^ n * (r₀ + 4 * n + 4) by positivity)
    nlinarith
  have hs := herr d F U α β hF hU hα0 hα hβ0 hFreq hdeg hUlog hβ
  have hmono := movingInternalArithmeticError_mono_card n c (4 * n * 2 ^ n) d F U α β
    (Real.exp ((1 / 100 : ℝ) * L)) hc hF hU hα0 hβ0 (Real.exp_nonneg _)
  have he0 := movingInternalArithmeticError_nonneg n (4 * n * 2 ^ n) d F U α β
    (Real.exp ((1 / 100 : ℝ) * L)) hF hU hα0 hβ0 (Real.exp_nonneg _)
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ F lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hprod : (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 = ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, pow_succ]
  have hcb : cost ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply le_trans _ (hcost L hL p F lo hi (Real.exp_nonneg _) le_rfl hhi hwidth hp)
    rw [hprod]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hamp (Finset.prod_nonneg fun _ _ => by positivity))
      (sq_nonneg _)
  have hbudget : (1 : ℝ) ≤ (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 2 (Real.exp ((1 : ℝ) * L))) ^ (4 * n * 2 ^ n) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (le_trans (by norm_num) (le_max_left _ _)))
  have hcb' := hcb.trans (le_mul_of_one_le_left (Real.exp_nonneg _) hbudget)
  exact ((mul_le_mul_of_nonneg_left hmono hcost0).trans
    (mul_le_mul_of_nonneg_right hcb' he0)).trans hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalNumericalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical simplification of the original diagonal comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem diagonalOuterMajorant_eventually (B D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ diagonal : Bool,
      2 * Real.exp 1 * diagonalOuterMajorant B D diagonal ≤
        Real.exp ((49 / 1000 : ℝ) * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((49 / 1000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually_ge_atTop
    (max (2 * Real.exp 1 * diagonalOuterMajorant B D false)
      (2 * Real.exp 1 * diagonalOuterMajorant B D true))] with L hL diagonal
  cases diagonal
  · exact (le_max_left _ _).trans hL
  · exact (le_max_right _ _).trans hL

/-- The actual denominator and coefficient mass absorb all comparison costs.
The remaining main term `K` is the nonnegative leaf/split contribution. -/
theorem movingPattern_diagonal_pointwise_rate (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D Cprior Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hCprior : 1 ≤ Cprior) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (c : ℕ) (E U α β amp lo hi rG K z : ℝ) (diagonal : Bool),
      let κE := (2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)
      let κ := (2 : ℝ) ^ c * (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - c)
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      c ≤ 4 * n * 2 ^ n → 0 ≤ E → E ≤ Real.exp (Cprior * L) →
      1 ≤ U → Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 ≤ α → α ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      0 ≤ β → β ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      0 ≤ amp → amp ≤ 4 → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG → 0 ≤ K →
      z ≤ (κE * U ^ c) * (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        diagonalOuterMajorant B D diagonal * ((2 * Real.exp 1 *
          (κE * (cost * movingInternalArithmeticError n c (2 ^ n * (r₀ + m + 4 * n + 4))
            (Real.exp (A * m)) U α β (Real.exp ((1 / 100 : ℝ) * L)) + K +
            (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
              2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) →
      z ≤ κ * (K + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [movingPattern_internal_arithmetic_error_rate ψ n r₀ k A Wwin B D Cmass
      hA hWwin hCmass, movingPattern_giant_error_rate n Cprior hCprior,
    diagonalOuterMajorant_eventually B D, eventually_ge_atTop (0 : ℝ)]
    with L hinternal hgiant houter hL
  dsimp only
  intro p c E U α β amp lo hi rG K z diagonal hc hE hEup hU hUlog
    hα hαup hβ hβup hamp hampup hhi hwidth hp hrG hK hz
  let κE := (2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)
  let κ := (2 : ℝ) ^ c * (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - c)
  let e₁ := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L))
  let e₂ := Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
  let err := ((amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * spectatorBulkCount k L)) lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2) *
    movingInternalArithmeticError n c (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
      (Real.exp (A * spectatorBulkCount k L)) U α β (Real.exp ((1 / 100 : ℝ) * L))
  have hint : err ≤ e₂ := hinternal p c U α β amp lo hi hc hU hUlog hα hαup hβ hβup
    hamp hampup hhi hwidth hp
  have hUup : U ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Real.exp_log (by linarith : 0 < U)]
    exact Real.exp_le_exp.mpr hUlog
  have hg := hgiant c hc E U hE hEup (by linarith) hUup
  have hκE : 0 ≤ κE := by dsimp only [κE]; positivity
  have hκmono : κE ≤ κ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE hEup _) (by positivity)
  have hκ : 1 ≤ κ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hL)))
  have hrG0 : 0 < rG := (Real.exp_pos _).trans_le hrG
  have hscale : diagonalOuterMajorant B D diagonal * (2 * Real.exp 1) / rG ≤ 1 := by
    apply (div_le_one hrG0).mpr
    nlinarith only [(houter diagonal).trans hrG]
  have herr0 : 0 ≤ err := by
    apply mul_nonneg (by positivity)
    exact movingInternalArithmeticError_nonneg n c _ _ U α β _
      (Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))) hU hα hβ (Real.exp_nonneg _)
  have hb0 : 0 ≤ err + K + (e₁ + 2 * e₂) := by dsimp only [e₁, e₂]; positivity
  have hstep :
      diagonalOuterMajorant B D diagonal *
        ((2 * Real.exp 1 * (κE * (err + K + (e₁ + 2 * e₂)))) / rG) ≤
      κ * (K + e₁ + 3 * e₂) := by
    calc
      _ = (diagonalOuterMajorant B D diagonal * (2 * Real.exp 1) / rG) *
          (κE * (err + K + (e₁ + 2 * e₂))) := by ring
      _ ≤ κE * (err + K + (e₁ + 2 * e₂)) :=
        mul_le_of_le_one_left (mul_nonneg hκE hb0) hscale
      _ ≤ κE * (K + e₁ + 3 * e₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hκE
      _ ≤ κ * (K + e₁ + 3 * e₂) :=
        mul_le_mul_of_nonneg_right hκmono (by dsimp only [e₁, e₂]; positivity)
  have hrest := add_le_add hg hstep
  have hh : z ≤ e₂ + κ * (K + e₁ + 3 * e₂) := hz.trans hrest
  have he₂ : e₂ ≤ κ * e₂ := le_mul_of_one_le_left (Real.exp_nonneg _) hκ
  change z ≤ κ * (K + e₁ + 4 * e₂)
  nlinarith only [hh, he₂]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLeafAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar leaf weights retain the actual frequency cutoff -/

namespace Ostmann
open scoped Classical

/-- Removing the explicit compensation multipliers leaves a scalar amplitude
of norm at most one whenever the actual leaf coefficients have that bound. -/
theorem movingDataWeight_unit_norm_le_one {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ 1)
    {n : ℕ} (T : MovingSlotData σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1) T‖ ≤ 1 := by
  induction T with
  | leaf s regular => exact hF s regular
  | node s CL CR U l r ihL ihR =>
    simp only [movingDataWeight, Complex.ofReal_one, one_mul, norm_mul, norm_star]
    exact (mul_le_mul ihL ihR (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternCoefficientMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
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

/-- Only the internal classes cost a factor of the upper prime cutoff. This
bound is used solely for the negligible giant-comparison errors. -/
theorem movingPattern_coefficient_norm_le {A B C : Type*} [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U : ℝ) (hE : 0 ≤ E) (_hU : 0 ≤ U)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (hsize : ∀ a, (prime a : ℝ) ≤ U) (x : Fin (N + 1) → A) :
    ‖movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
        productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let R := ∏ c : C, (prime (x (e.symm (.inr c))) : ℝ)
  let κ := (2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hprior : 0 ≤ productPrior law x := productPrior_nonneg law (by
    intro i a
    dsimp only [law]
    cases e i <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hν _ a
    · exact hμ _ a) x
  have hR : 0 < R := Finset.prod_pos (fun c _ => by exact_mod_cast (hprime _).pos)
  have hRupper : R ≤ U ^ Fintype.card C := by
    calc
      R ≤ ∏ _c : C, U := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun _ _ => hsize _)
      _ = _ := by simp
  have hb := movingPattern_fin_prior_bound e μ ν prime n pattern rep E hprime hμ hν hbound
    (movingPatternInjectionGuard e (fun _ => 1)) 1 zero_le_one
    (movingPatternInjectionGuard_norm e (fun _ => 1) 1 zero_le_one (fun _ => by simp)) x
  have hscalar : (∏ c : C, internalLineScalar true (prime (x (e.symm (.inr c))))) = R⁻¹ := by
    simp only [internalLineScalar, ite_true, if_true, R, Finset.prod_inv_distrib]
  change ‖w‖ * _ ≤ 1 * κ * productPrior law x at hb
  rw [hscalar, one_mul] at hb
  have hm := mul_le_mul_of_nonneg_right hb hR.le
  rw [mul_assoc, inv_mul_cancel₀ hR.ne', mul_one] at hm
  calc
    ‖w‖ ≤ (κ * productPrior law x) * R := hm
    _ ≤ (κ * productPrior law x) * U ^ Fintype.card C :=
      mul_le_mul_of_nonneg_left hRupper (mul_nonneg hκ hprior)
    _ = _ := by ring

theorem movingPattern_coefficient_mass_le {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U : ℝ) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hμmass : ∀ j, ∑ a, μ j a = 1) (hνmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E) (hsize : ∀ a, (prime a : ℝ) ≤ U) :
    (∑ x, ‖movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x‖) ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  have hlaw (i) : ∑ a, law i a = 1 := by
    dsimp only [law]
    cases e i with
    | inl b => exact hνmass b
    | inr c => exact hμmass _
  calc
    _ ≤ ∑ x, ((((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
      productPrior law x) := Finset.sum_le_sum (fun x _ =>
        movingPattern_coefficient_norm_le e μ ν prime n pattern rep E U hE hU hprime hμ hν hbound hsize x)
    _ = _ := by rw [← Finset.mul_sum, productPrior_mass law hlaw, mul_one]

/-- A uniform giant-comparison error is charged against the original
coefficient mass. The ideal signed mean stays inside its norm. -/
theorem movingPattern_comparison_norm {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (E U ε : ℝ) (hE : 0 ≤ E) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hμmass : ∀ j, ∑ a, μ j a = 1) (hνmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E) (hsize : ∀ a, (prime a : ℝ) ≤ U)
    (actual ideal : (Fin (N + 1) → A) → ℂ)
    (hcompare : ∀ x, movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      ‖actual x - ideal x‖ ≤ ε) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern actual x‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) * ε +
      ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern ideal x‖ := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1)
  have herror : ‖∑ x, w x * (actual x - ideal x)‖ ≤
      (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) * ε := by
    calc
      _ ≤ ∑ x, ‖w x‖ * ε := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => by
        rw [norm_mul]
        by_cases hw : w x = 0
        · simp only [hw, norm_zero, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hcompare x hw) (norm_nonneg _)))
      _ = (∑ x, ‖w x‖) * ε := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (movingPattern_coefficient_mass_le e μ ν prime n pattern rep E U hE hU
          hprime hμ hν hμmass hνmass hbound hsize) hε
  have heq : (∑ x, w x * actual x) =
      (∑ x, w x * (actual x - ideal x)) + ∑ x, w x * ideal x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have ha : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern actual x) =
      ∑ x, w x * actual x := Finset.sum_congr rfl (fun x _ =>
        movingOriginalPatternWeight_eq_coefficient_mul e μ ν prime n pattern actual x)
  have hi : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern ideal x) =
      ∑ x, w x * ideal x := Finset.sum_congr rfl (fun x _ =>
        movingOriginalPatternWeight_eq_coefficient_mul e μ ν prime n pattern ideal x)
  rw [ha, hi, heq]
  exact (norm_add_le _ _).trans (add_le_add herror (le_refl _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern denominator satisfies the frequency-model requirements -/

namespace Ostmann
open scoped Classical

theorem movingPattern_frequencyProduct_dvd {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (S : Finset ℤ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (b : Bool) :
    (movingPatternFinBulkData e n m
      (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection S n side t))
      small slot perm pattern b).frequencyProduct ∣ (frequencyModelBase S n t : ℤ) := by
  apply Int.natAbs_dvd.mp
  apply Int.natCast_dvd_natCast.mpr
  rw [movingPatternFinBulkData_build, buildMovingSlotData_frequencyProduct_abs]
  cases b
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem prime_coprime_frequencyModelBase (S : Finset ℤ) (N p n : ℕ)
    (hp : p.Prime) (hpN : N < p) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (t : FrequencyTree (S × S) n) : p.Coprime (frequencyModelBase S n t) := by
  have h (b : Bool) : p.Coprime (historyFrequencyProduct S n (frequencyPairProjection S n b t)) := by
    have hb := prime_coprime_historyFrequencyModulus S N p hp hpN hS n 0
      (frequencyPairProjection S n b t)
    exact Nat.Coprime.of_dvd_right (dvd_pow_self _ (by decide : (0 + 2 : ℕ) ≠ 0)) hb
  exact (h false).mul_right (h true)

theorem frequencyModelModulus_bound (S : Finset ℤ) (N n : ℕ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (t : FrequencyTree (S × S) n) :
    frequencyModelBase S n t ^ (n - 1 + 2) ≤
      N ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
  exact (Nat.pow_le_pow_left (frequencyModelBase_le S n N t hN) _).trans_eq (pow_mul _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prior support supplies the level and prime-separation hypotheses -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_internal_prior_nonzero {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    ∀ i, μ (movingSampleTier i.2) (x (e.symm (.inr (pattern i)))) ≠ 0 := by
  have hm : movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) ≠ 0 := by
    intro hz
    apply hx
    simp only [movingOriginalPatternWeight, hz, Complex.ofReal_zero, mul_zero, zero_mul]
  have hp := movingPairCompensatedMass_pattern μ prime n pattern
    (fun c => x (e.symm (.inr c)))
  change movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
    (fun i => x (e.symm (.inr (pattern i))))) = _ at hp
  rw [hp] at hm
  intro i
  exact (mul_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hm i (Finset.mem_univ _))).2

theorem movingPattern_prior_tiers {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ)
    (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hν : ∀ j a, ν j a ≠ 0 → tier a = tierB j)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, tier (x i) = (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  cases he : e i with
  | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
  | inr c => exact hμ _ (movingSampleTier_lt (rep c).val.2) (x i) (by simpa only [he, Sum.elim_inr] using hi)

theorem movingPattern_prior_prime_separation {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ) (prime : A → ℕ) (hinj : Function.Injective prime)
    (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hν : ∀ j a, ν j a ≠ 0 → tier a = tierB j)
    (hB : ∀ b, n ≤ tierB b) (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
        prime (x i) ≠ prime (x j)) ∧
    (∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c)))) := by
  have ht := movingPattern_prior_tiers e μ ν pattern rep tier tierB hμ hν x hx
  have hd (i j) (hij : (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j)) :
      prime (x i) ≠ prime (x j) := by
    intro hp
    apply hij
    rw [← ht i, ← ht j, hinj hp]
  refine ⟨hd, ?_⟩
  intro b c
  apply hd
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
  have hc := movingSampleTier_lt (rep c).val.2
  have hb := hB b
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete prime support of a nonzero original pattern coefficient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original coefficient can only be nonzero on its representative
product prior. This implication does not replace repeated samples by
independent ones. -/
theorem movingPattern_nonzero_prior {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 := by
  intro hz
  have h := movingPattern_coefficient_zero_of_prior e μ ν prime pattern rep E
    hprime hμ hν hbound x hz
  apply hx
  change _ * movingPatternInjectionGuard e G x = 0
  rw [h, zero_mul]

theorem movingPattern_nonzero_internal_injective {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    Function.Injective (fun c => prime (x (e.symm (.inr c)))) := by
  have hg : movingPatternInjectionGuard e G x ≠ 0 := (mul_ne_zero_iff.mp hx).2
  exact hinj.comp (movingPatternInjectionGuard_nonzero e G x hg).1

/-- All prime coprimality conditions against the actual history modulus
follow from the lower endpoint of the original product prior. -/
theorem movingPattern_prior_frequency_coprime {A B C : Type*}
    {N n : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V)
    (hμ : ∀ j a, μ j a ≠ 0 → V < prime a)
    (hν : ∀ j a, ν j a ≠ 0 → V < prime a)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, (prime (x i)).Coprime (frequencyModelBase S n t) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  apply prime_coprime_frequencyModelBase S V (prime (x i)) n (hprime _)
  · cases he : e i with
    | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
    | inr c => exact hμ _ (x i) (by simpa only [he, Sum.elim_inr] using hi)
  · exact hS

theorem movingPatternInternalPrimes_prime {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) :
    ∀ p ∈ movingPatternInternalPrimes e prime x, p.Prime := by
  intro p hp
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
  exact hprime _

/-- Distinct spectators and the prior's elementary prime coprimality give
pairwise coprimality of every actual giant CRT block. -/
theorem movingPattern_prime_moduli_coprime {A B C I : Type*} [Fintype C] [Fintype I] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (r : ℕ) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hr : ∀ i, r.Coprime (prime (x i))) (hrp : ∀ i, r.Coprime (p i))
    (hsep : ∀ i j, prime (x j) ≠ p i) :
    Pairwise (fun a b =>
      (movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ a).Coprime
      (movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ b)) := by
  apply movingArithmeticModuli_coprime r p (movingPatternInternalPrimes e prime x) Finset.univ
    (movingPatternInternalPrimes_prime e prime hprime x) (fun i _ => hp i)
    (fun _ _ _ _ h => hinj h)
  · intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact hr _
  · exact fun i _ => hrp i
  · intro q hq i _
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact hsep i _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Range separation and conductor deletion for the actual giant comparison -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_prior_lower {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (lo : ℕ)
    (hμ : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hν : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, lo < prime (x i) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  cases he : e i with
  | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
  | inr c => exact hμ _ (x i) (by simpa only [he, Sum.elim_inr] using hi)

/-- The original prior supplies all prime-range and frequency-unit conditions
for the giant comparison, including the protected bulk coordinates. -/
theorem movingPattern_prior_giant_support {A B C I : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ)
    (hμtier : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hνtier : ∀ j a, ν j a ≠ 0 → tier a = tierB j) (hB : ∀ b, n ≤ tierB b)
    (S : Finset ℤ) (V lo : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hVlo : V ≤ lo)
    (hμlo : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hνlo : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hplo : ∀ i, p i ≤ lo)
    (E : ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0) :
    let R := frequencyModelBase S n t
    (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
        prime (x i) ≠ prime (x j)) ∧
    (∀ i, V < prime (x i)) ∧
    (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
    (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
    (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) := by
  intro R
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  have hlargeV (i) : V < prime (x i) := hVlo.trans_lt (hlarge i)
  have hcop := movingPattern_prior_frequency_coprime e μ ν prime hprime pattern rep S V t hS
    (fun j a ha => hVlo.trans_lt (hμlo j a ha))
    (fun j a ha => hVlo.trans_lt (hνlo j a ha)) x hprior
  refine ⟨(movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hprior).1, hlargeV, ?_, ?_, ?_⟩
  · intro i
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop i
  · intro i
    exact ((hcop i).pow_right _).symm
  · intro i j hz
    have hd := (ZMod.natCast_eq_zero_iff (prime (x j)) (p i)).mp hz
    have heq := (Nat.prime_dvd_prime_iff_eq (hp i) (hprime _)).mp hd
    have hlt := (hplo i).trans_lt (hlarge j)
    omega

/-- Deleting the selected large conductor prime confines the actual Page
correction to the history-frequency modulus, including all its powers. -/
theorem frequencyModel_page_projection {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (z : Option PrimitiveRealZero)
    (hP : ∀ q ∈ P, q.Prime ∧ cutoff ≤ q) (hp : ∀ i, (p i).Prime ∧ cutoff ≤ p i)
    (hdeleteP : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → q ∉ P)
    (hdeletep : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) z = pageAtModulus (frequencyModelBase S n t ^ (n - 1 + 2)) z := by
  let R := frequencyModelBase S n t ^ (n - 1 + 2)
  let C := (∏ q ∈ P, q) ^ 2 * ∏ i, p i
  have heq : (∏ b, movingArithmeticModuli R p P Finset.univ b) = R * C :=
    movingArithmeticModuli_product R p P Finset.univ
  change pageAtModulus (∏ b, movingArithmeticModuli R p P Finset.univ b) z = _
  rw [heq]
  apply pageAtModulus_mul_eq z R C cutoff
  · intro q hq hd
    by_contra hh
    have hVq : V < q := hcut.trans_le (Nat.le_of_not_lt hh)
    have hc := (prime_coprime_frequencyModelBase S V q n hq hVq hS t).pow_right (n - 1 + 2)
    exact (hq.coprime_iff_not_dvd.mp hc) hd
  · intro q hq hd
    rcases hq.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hq.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hq.dvd_of_dvd_pow hleft)
      have he := (Nat.prime_dvd_prime_iff_eq hq (hP a ha).1).mp hqa
      simpa only [he] using (hP a ha).2
    · obtain ⟨i, _, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hright
      have he := (Nat.prime_dvd_prime_iff_eq hq (hp i).1).mp hqi
      simpa only [he] using (hp i).2
  · intro e he q hq hd
    have hprime := (deletedConductorPrime_spec hq).1
    rcases hprime.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hprime.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hprime.dvd_of_dvd_pow hleft)
      have heq := (Nat.prime_dvd_prime_iff_eq hprime (hP a ha).1).mp hqa
      exact hdeleteP e he q hq (heq.symm ▸ ha)
    · obtain ⟨i, _, hqi⟩ := (hprime.prime.dvd_finsetProd_iff p).mp hright
      exact hdeletep e he q hq i ((Nat.prime_dvd_prime_iff_eq hprime (hp i).1).mp hqi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPageDeletion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor deletion for the separated diagonal modulus -/

namespace Ostmann
open scoped Classical BigOperators

/-- Prime factors in a regular block are disjoint from the frequency,
internal and spectator factors of the separated modulus. -/
theorem movingArithmeticModuli_coprime_product {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) (p : I → ℕ) (P : Finset ℕ) (reg : J → ℕ)
    (hp : ∀ i, (p i).Prime) (hP : ∀ q ∈ P, q.Prime) (hreg : ∀ j, (reg j).Prime)
    (hr : ∀ j, (reg j).Coprime r)
    (hregP : ∀ j q, q ∈ P → reg j ≠ q) (hregp : ∀ j i, reg j ≠ p i) :
    (∏ j, reg j).Coprime (∏ b, movingArithmeticModuli r p P Finset.univ b) := by
  rw [movingArithmeticModuli_product]
  apply Nat.coprime_prod_left_iff.mpr
  intro j _
  apply (hr j).mul_right
  apply Nat.Coprime.mul_right
  · apply Nat.Coprime.pow_right
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact (hreg j).coprime_iff_not_dvd.mpr (fun h => hregP j q hq
      ((Nat.prime_dvd_prime_iff_eq (hreg j) (hP q hq)).mp h))
  · apply Nat.coprime_prod_right_iff.mpr
    intro i _
    exact (hreg j).coprime_iff_not_dvd.mpr (fun h => hregp j i
      ((Nat.prime_dvd_prime_iff_eq (hreg j) (hp i)).mp h))

/-- The prescribed deleted conductor prime is coprime to the full separated
arithmetic block. The frequency part is smaller than the deletion threshold. -/
theorem frequencyModel_deleted_prime_coprime {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (hP : ∀ q ∈ P, q.Prime) (hp : ∀ i, (p i).Prime)
    (q : ℕ) (hq : q.Prime) (hlarge : cutoff ≤ q)
    (hneqP : q ∉ P) (hneqp : ∀ i, q ≠ p i) :
    q.Coprime (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) := by
  rw [movingArithmeticModuli_product]
  apply ((prime_coprime_frequencyModelBase S V q n hq (hcut.trans_le hlarge) hS t).pow_right _).mul_right
  apply Nat.Coprime.mul_right
  · apply Nat.Coprime.pow_right
    apply Nat.coprime_prod_right_iff.mpr
    intro a ha
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    exact hneqP (((Nat.prime_dvd_prime_iff_eq hq (hP a ha)).mp hd).symm ▸ ha)
  · apply Nat.coprime_prod_right_iff.mpr
    intro i _
    exact hq.coprime_iff_not_dvd.mpr (fun hd => hneqp i
      ((Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hd))

/-- The regular block contributes no Page correction under exactly the
conductor-prime deletion used to construct the original priors. -/
theorem frequencyModel_regular_page_projection {I J : Type*} [Fintype I] [Fintype J]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (reg : J → ℕ) (z : Option PrimitiveRealZero)
    (hP : ∀ q ∈ P, q.Prime) (hp : ∀ i, (p i).Prime)
    (hreg : ∀ j, (reg j).Prime ∧ cutoff ≤ reg j)
    (hdeleteP : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → q ∉ P)
    (hdeletep : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i)
    (hdeletereg : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ j, q ≠ reg j) :
    pageAtModulus ((∏ j, reg j) *
      ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2)) p P Finset.univ b) z =
    pageAtModulus (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) z := by
  apply pageAtModulus_regular_factor z _ _ cutoff
  · intro q hq hd
    obtain ⟨j, _, hj⟩ := (hq.prime.dvd_finsetProd_iff reg).mp hd
    have he := (Nat.prime_dvd_prime_iff_eq hq (hreg j).1).mp hj
    exact he.symm ▸ (hreg j).2
  · intro e he q hq hd
    have hs := deletedConductorPrime_spec hq
    have harith := frequencyModel_deleted_prime_coprime S n V cutoff t hS hcut P p hP hp
      q hs.1 hs.2.2 (hdeleteP e he q hq) (hdeletep e he q hq)
    have hr : q.Coprime (∏ j, reg j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j _
      exact hs.1.coprime_iff_not_dvd.mpr (fun h => hdeletereg e he q hq j
        ((Nat.prime_dvd_prime_iff_eq hs.1 (hreg j).1).mp h))
    exact hs.1.coprime_iff_not_dvd.mp (hr.mul_right harith) hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternRegularSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and arithmetic of the original regular-prime list -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternRegularSlots_external {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (i : Fin (N + 1))
    (hi : i ∈ movingPatternRegularSlots e n m small slot) :
    ∃ b, e.symm (.inl b) = i := by
  rcases List.mem_append.mp hi with hi | hi
  · rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hi
    exact ⟨b, hb⟩
  · obtain ⟨j, hj⟩ := (mem_flatten_bulkSlotLeaves n m (movingPatternBulkEmbedding e slot) i).mp hi
    exact ⟨slot j, hj⟩

theorem naturalProduct_eq_finprod {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    MovingSlotReversal.naturalProduct value slots = ∏ i : Fin slots.length, value (slots.get i) := by
  have h : List.ofFn (value ∘ slots.get) = slots.map value := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [MovingSlotReversal.naturalProduct, ← h, List.prod_ofFn]
  rfl

/-- The two history roots contain precisely the fixed regular slots. -/
theorem movingPatternFinBulkData_regular_perm {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (b : Bool) :
    (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b).regularSlots.Perm
      (movingPatternRegularSlots e n m small slot) := by
  rw [movingPatternFinBulkData_build]
  have h := buildMovingSlotData_regular_perm n (t b)
    (movingPatternFiniteSmall e n small)
    (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
    (movingPatternFiniteSamples e n pattern b)
  cases b <;> exact h

/-- Distinctness of the canonical regular enumeration comes from the original
support guard, so repeated independent draws need no extra assumption. -/
theorem movingPattern_regular_pairwise {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (outside : List ℕ) (b : Bool)
    (h : movingRegularOutsidePairwise value outside
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b)) :
    Pairwise (fun i j : Fin (movingPatternRegularSlots e n m small slot).length =>
      (value ((movingPatternRegularSlots e n m small slot).get i)).Coprime
        (value ((movingPatternRegularSlots e n m small slot).get j))) := by
  let slots := movingPatternRegularSlots e n m small slot
  have hp := movingRegularOutsidePairwise_root value outside _ h
  have hperm := (movingPatternFinBulkData_regular_perm e t small slot pattern b).map value
  have hs : (slots.map value).Pairwise Nat.Coprime :=
    (hperm.pairwise_iff (R := Nat.Coprime) (fun h => h.symm)).mp hp
  have hlist : List.ofFn (value ∘ slots.get) = slots.map value := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← hlist, List.pairwise_ofFn] at hs
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hs hlt
  · exact (hs hgt).symm

/-- External regular primes are coprime to the separated internal/frequency
block on the original prior support. -/
theorem movingPattern_regular_arithmetic_coprime {A B C I : Type*}
    [Fintype C] [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (r : ℕ) (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hr : ∀ i, r.Coprime (prime (x i)))
    (hcross : ∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c))))
    (hspect : ∀ i j, prime (x j) ≠ p i) :
    (MovingSlotReversal.naturalProduct (fun i => prime (x i))
      (movingPatternRegularSlots e n m small slot)).Coprime
      (∏ b, movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ b) := by
  let slots := movingPatternRegularSlots e n m small slot
  rw [naturalProduct_eq_finprod]
  apply movingArithmeticModuli_coprime_product r p (movingPatternInternalPrimes e prime x)
    (fun j : Fin slots.length => prime (x (slots.get j))) hp
    (movingPatternInternalPrimes_prime e prime hprime x) (fun _ => hprime _)
    (fun j => (hr _).symm)
  · intro j q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb⟩ := movingPatternRegularSlots_external e small slot _ (List.get_mem slots j)
    exact hb ▸ hcross b c
  · exact fun j i => hspect i _

/-- The same one-prime conductor deletion used in the priors removes any
Page contribution from the original regular list. -/
theorem movingPattern_regular_page_projection {A B C I : Type*}
    [Fintype C] [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (S : Finset ℤ) (V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (hlarge : ∀ i, cutoff ≤ prime (x i)) (z : Option PrimitiveRealZero)
    (hdelete : ∀ a, z = some a → ∀ q,
      deletedConductorPrime a.modulus cutoff = some q → ∀ i, prime (x i) ≠ q)
    (hdeletep : ∀ a, z = some a → ∀ q,
      deletedConductorPrime a.modulus cutoff = some q → ∀ i, p i ≠ q) :
    let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p (movingPatternInternalPrimes e prime x) Finset.univ b
    pageAtModulus (MovingSlotReversal.naturalProduct (fun i => prime (x i))
      (movingPatternRegularSlots e n m small slot) * M) z = pageAtModulus M z := by
  dsimp only
  let slots := movingPatternRegularSlots e n m small slot
  rw [naturalProduct_eq_finprod]
  apply frequencyModel_regular_page_projection S n V cutoff t hS hcut
    (movingPatternInternalPrimes e prime x) p (fun j : Fin slots.length => prime (x (slots.get j))) z
    (movingPatternInternalPrimes_prime e prime hprime x) hp (fun j => ⟨hprime _, hlarge _⟩)
  · intro a ha q hq hmem
    obtain ⟨c, _, heq⟩ := Finset.mem_image.mp hmem
    exact hdelete a ha q hq _ heq
  · exact fun a ha q hq i => (hdeletep a ha q hq i).symm
  · exact fun a ha q hq j => (hdelete a ha q hq _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternRegularUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual regular Fourier denominators are units on the original support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_regular_other_unit {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ)
    (hprime : ∀ i, (value i).Prime) (outside : List ℕ) (b : Bool)
    (h : movingRegularOutsidePairwise value outside
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b))
    (j : Fin (movingPatternRegularSlots e n m small slot).length) :
    (movingRegularOther value outside (movingPatternRegularSlots e n m small slot) j :
      ZMod (value ((movingPatternRegularSlots e n m small slot).get j))) ≠ 0 := by
  let slots := movingPatternRegularSlots e n m small slot
  let : Fact (value (slots.get j)).Prime := ⟨hprime _⟩
  have hp : (((movingPatternFinBulkData e n m t (fun _ => small) slot
      (Equiv.refl _) pattern b).regularSlots.map value) ++ outside).Pairwise Nat.Coprime := by
    cases ht : movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b with
    | leaf => exact ht ▸ h
    | node => exact (ht ▸ h).1
  have hperm := ((movingPatternFinBulkData_regular_perm e t small slot pattern b).map value).append_right outside
  have hc : (slots.map value ++ outside).Pairwise Nat.Coprime :=
    (hperm.pairwise_iff (R := Nat.Coprime) (fun h => h.symm)).mp hp
  have ho : (value (slots.get j)).Coprime outside.prod := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro q hq
    exact (List.pairwise_append.mp hc).2.2 _
      (List.mem_map.mpr ⟨slots.get j, List.get_mem slots j, rfl⟩) q hq
  have hr := movingPattern_regular_pairwise e t small slot pattern value outside b h
  have hrest : (value (slots.get j)).Coprime
      (∏ i ∈ Finset.univ.erase j, value (slots.get i)) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    exact hr (Finset.ne_of_mem_erase hi).symm
  have hu := (ZMod.isUnit_iff_coprime _ (value (slots.get j))).mpr (ho.mul_right hrest).symm
  simpa only [movingRegularOther, Int.cast_natCast] using hu.ne_zero

/-- Every retained frequency is a unit at a regular prime above the common cutoff. -/
theorem movingPattern_regular_frequency_unit {σ : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) (slots : List σ)
    (V : ℕ) (hlarge : ∀ i, V < value i) (s : ℤ) (hs : s ≠ 0) (hV : s.natAbs ≤ V)
    (j : Fin slots.length) : (s : ZMod (value (slots.get j))) ≠ 0 := by
  let : Fact (value (slots.get j)).Prime := ⟨hprime _⟩
  have hc := small_prime_frequency_unit (value (slots.get j)) (hprime (slots.get j)) s hs
    (hV.trans_lt (hlarge (slots.get j)))
  have hu : IsUnit (s : ZMod (value (slots.get j))) := by
    apply isCoprime_zero_right.mp
    simpa only [Int.cast_natCast, ZMod.natCast_self] using
      hc.intCast (R := ZMod (value (slots.get j)))
  exact hu.ne_zero

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternModulusRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full pattern modulus and the separate giant progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingArithmeticModuli_exp_bound (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ)
    (F U V : ℝ) (hr : (r : ℝ) ≤ Real.exp (F * m))
    (hP : ∀ q ∈ P, (q : ℝ) ≤ Real.exp U)
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    ((∏ b, movingArithmeticModuli r p P Finset.univ b : ℕ) : ℝ) ≤
      Real.exp (F * m + 2 * P.card * U + (m : ℝ) * V) := by
  have hprod : ((∏ q ∈ P, q : ℕ) : ℝ) ≤ Real.exp ((P.card : ℝ) * U) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _q ∈ P, Real.exp U :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) hP
      _ = _ := by simp only [Finset.prod_const, ← Real.exp_nat_mul]
  have hspec : ((∏ i : Fin m, p i : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * V) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin m, Real.exp V :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hp i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  rw [movingArithmeticModuli_product]
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (F * m) * ((Real.exp ((P.card : ℝ) * U)) ^ 2 *
        Real.exp ((m : ℝ) * V)) :=
      mul_le_mul hr (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)
        hspec (Nat.cast_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The actual number of internal classes is fixed by the tree depth. Thus
internal squares fit the giant cutoff, uniformly in the pattern and its
sampled prime assignment. -/
theorem movingArithmeticModuli_giant_range (n : ℕ) (F K : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ),
      (m : ℝ) ≤ K * L → P.card ≤ 4 * n * 2 ^ n →
      (r : ℝ) ≤ Real.exp (F * m) →
      (∀ q ∈ P, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∏ b, movingArithmeticModuli r p P Finset.univ b) ≤ giantProgressionCutoff L := by
  let J : ℝ := 4 * n * 2 ^ n
  let C := F * K + 2 * J + K
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hFK : 0 ≤ F * K := mul_nonneg hF hK
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro m r p P hm hc hr hP hp
  apply Nat.le_floor
  have hbound := movingArithmeticModuli_exp_bound m r p P F
    (Real.exp ((11 / 1000 : ℝ) * L)) (Real.exp ((1 / 1000 : ℝ) * L)) hr hP hp
  apply hbound.trans
  change Real.exp _ ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * (10 * L)))
  rw [show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring]
  apply Real.exp_le_exp.mpr
  have hc' : (P.card : ℝ) ≤ J := by
    dsimp only [J]
    exact_mod_cast hc
  have he : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hKL : 0 ≤ K * L := mul_nonneg hK (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hm hF
  have hi := mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  have hiL : 2 * J * Real.exp ((11 / 1000 : ℝ) * L) ≤
      (2 * J * L) * Real.exp ((11 / 1000 : ℝ) * L) := by
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) hJ) hL) (Real.exp_nonneg _)
  have hs := mul_le_mul hm he (Real.exp_nonneg _) hKL
  have hC1 : F * K ≤ C := by dsimp only [C]; linarith
  have hC2 : 2 * J + K ≤ C := by dsimp only [C]; linarith
  have hC1L := mul_le_mul_of_nonneg_right hC1 (show 0 ≤ L by linarith)
  have hC2L := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ L by linarith)
  have hC2e := mul_le_mul_of_nonneg_right hC2L (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  nlinarith only [hmain, hi, hiL, hs, hC1L, hC2e, hrate]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete logarithmic bounds for the original giant comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem giantProgressionCutoff_log_le {M : ℕ} {L : ℝ}
    (hM : 0 < M) (hbound : M ≤ giantProgressionCutoff L) :
    Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  have hupper : (M : ℝ) ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    apply (Nat.cast_le.mpr hbound).trans
    have h := Nat.floor_le (Real.exp_nonneg (Real.exp ((12 / 10000 : ℝ) * (10 * L))))
    simpa only [giantProgressionCutoff, bulkProgressionCutoff,
      show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring] using h
  have hlog := Real.log_le_log (show (0 : ℝ) < M by exact_mod_cast hM) hupper
  simpa only [Real.log_exp] using hlog

theorem naturalProduct_exp_bound {σ : Type*} (value : σ → ℕ) (A : ℝ)
    (hvalue : ∀ i, (value i : ℝ) ≤ Real.exp A) (slots : List σ) :
    (MovingSlotReversal.naturalProduct value slots : ℝ) ≤ Real.exp (slots.length * A) := by
  induction slots with
  | nil => simp [MovingSlotReversal.naturalProduct]
  | cons i slots ih =>
    simp only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
    apply (mul_le_mul (hvalue i) ih (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, List.length_cons, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem naturalProduct_log_bound {σ : Type*} (value : σ → ℕ) (A : ℝ)
    (hpos : ∀ i, value i ≠ 0) (hvalue : ∀ i, (value i : ℝ) ≤ Real.exp A) (slots : List σ) :
    Real.log (MovingSlotReversal.naturalProduct value slots : ℝ) ≤ slots.length * A := by
  have hn : MovingSlotReversal.naturalProduct value slots ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hz
    exact hpos i hi
  have hp : (0 : ℝ) < MovingSlotReversal.naturalProduct value slots := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have h := Real.log_le_log hp (naturalProduct_exp_bound value A hvalue slots)
  simpa only [Real.log_exp] using h

/-- A list containing linearly many primes in the actual nongiant range
satisfies the logarithmic budget used by the giant progression theorem. -/
theorem naturalProduct_giant_log_range (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type) (value : σ → ℕ) (slots : List σ),
      (∀ i, value i ≠ 0) → (slots.length : ℝ) ≤ K * L →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      Real.log (MovingSlotReversal.naturalProduct value slots : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 K 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hL
  intro σ value slots hpos hlen hvalue
  have hlog := naturalProduct_log_bound value (Real.exp ((11 / 1000 : ℝ) * L)) hpos hvalue slots
  have hlen' := mul_le_mul_of_nonneg_right hlen (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero, one_mul] at hL
  exact (hlog.trans hlen').trans (by linarith)

/-- The common regular product of both histories uses only the original
small and bulk leaves. Its logarithmic budget follows from their lengths. -/
theorem movingPattern_regular_giant_log_range (n r₀ k : ℕ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ),
      MovingLeafLengthLE n small r₀ → (∀ i, value i ≠ 0) →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      Real.log (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  let K : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [naturalProduct_giant_log_range K hK, eventually_ge_atTop (1 : ℝ)]
    with L hL hlarge
  dsimp only
  intro B C N e small slot value hsmall hpos hvalue
  apply hL (Fin (N + 1)) value _ hpos _ hvalue
  have hsmall' := moving_flatten_length_le n (movingPatternFiniteSmall e n small) r₀
    (movingLeafLengthLE_map _ n small r₀ hsmall)
  have hbulk := moving_flatten_length_le n
    (bulkSlotLeaves n (spectatorBulkCount k L) (movingPatternBulkEmbedding e slot))
    (spectatorBulkCount k L) (bulkSlotLeaves_length n _ _)
  have hlen := Nat.cast_le (α := ℝ).mpr (Nat.add_le_add hsmall' hbulk)
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hr := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg r₀)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hr hm)
    (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  rw [List.length_append, Nat.cast_add]
  push_cast at hlen
  apply hlen.trans
  simpa only [K, mul_one, Nat.cast_pow, Nat.cast_ofNat, mul_add, add_mul, mul_assoc] using hh

/-- The frequency modulus used by the actual pair of histories has a fixed
polynomial degree in the frequency cutoff. -/
theorem frequencyModelModulus_exp_bound (S : Finset ℤ) (N n : ℕ)
    (t : FrequencyTree (S × S) n) (A : ℝ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (hA : (N : ℝ) ≤ Real.exp A) :
    ((frequencyModelBase S n t ^ (n - 1 + 2) : ℕ) : ℝ) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1) * (n - 1 + 2) : ℕ) * A) := by
  calc
    _ ≤ (N : ℝ) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
      exact_mod_cast frequencyModelModulus_bound S N n hN t
    _ ≤ (Real.exp A) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg N) hA _
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- The paired frequency modulus, the actual internal prime image, and the
selected spectators all fit the giant cutoff at the manuscript scales. -/
theorem movingPattern_actual_modulus_range (n k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (S : Finset ℤ) (N : ℕ) (t : FrequencyTree (S × S) n)
        (p : Fin m → ℕ) (P : Finset ℕ),
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) → (N : ℝ) ≤ Real.exp (Cfreq * m) →
      P.card ≤ 4 * n * 2 ^ n →
      (∀ q ∈ P, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
        p P Finset.univ b
      M ≤ giantProgressionCutoff L ∧ Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  let D : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  filter_upwards [movingArithmeticModuli_giant_range n ((D : ℝ) * Cfreq) ((k : ℝ) ^ 4)
      (by positivity) (by positivity), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  dsimp only
  intro S N t p P hS hN hcard hP hp
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : (r : ℝ) ≤ Real.exp (((D : ℝ) * Cfreq) * spectatorBulkCount k L) := by
    simpa only [mul_assoc, D, r] using frequencyModelModulus_exp_bound S N n t
      (Cfreq * spectatorBulkCount k L) (fun s hs => (hS s hs).2) hN
  have hbound := hL (spectatorBulkCount k L) r p P (spectatorBulkCount_upper k L hL0)
    hcard hr (fun q hq => (hP q hq).2) (fun i => (hp i).2)
  refine ⟨hbound, giantProgressionCutoff_log_le ?_ hbound⟩
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  exact movingArithmeticModuli_ne_zero r p P Finset.univ
    (pow_ne_zero _ (Nat.ne_of_gt (frequencyModelBase_pos S n t (fun s hs => (hS s hs).1))))
    (fun q hq => (hP q hq).1) (fun i _ => (hp i).1) b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supplying the giant arithmetic conditions from the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All assignment-dependent conditions of the giant comparison follow from
actual prime ranges, original-prior support, and the prescribed conductor
prime deletion. No arithmetic comparison is assumed in this statement. -/
theorem movingPattern_giant_conditions (input : PublishedProgressionInput)
    (n r₀ k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
        (tier : A → ℕ) (tierB : B → ℕ)
        (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
        (pattern : Bool × MovingSampleIndex n → C)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (p : Fin m → ℕ) (lo cutoff : ℕ) (E : ℝ),
      let R := frequencyModelBase S n t
      let Pi := fun x => movingPatternInternalPrimes e prime x
      let M := fun x => ∏ b, movingArithmeticModuli (R ^ (n - 1 + 2)) p (Pi x) Finset.univ b
      Function.Injective prime → (∀ a, (prime a).Prime) →
      (∀ j a, 0 ≤ μ j a) → (∀ j a, 0 ≤ ν j a) →
      (∀ j a, (prime a : ℝ) * μ j a ≤ E) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) → (∀ b, n ≤ tierB b) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) → (V : ℝ) ≤ Real.exp (Cfreq * m) →
      V ≤ lo → V < cutoff → cutoff ≤ lo →
      (∀ j a, μ j a ≠ 0 → lo < prime a) →
      (∀ j a, ν j a ≠ 0 → lo < prime a) →
      (∀ a, (prime a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ cutoff ≤ p i ∧ p i ≤ lo ∧
        (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → prime a ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      M x ≤ giantProgressionCutoff L ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Real.log (M x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) ∧
      Real.log (MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [movingPattern_actual_modulus_range n k Cfreq hCfreq,
    movingPattern_regular_giant_log_range n r₀ k] with L hmod hreg
  dsimp only
  intro A B C _ _ _ N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep x hx
  let m := spectatorBulkCount k L
  let R := frequencyModelBase S n t
  let Pi := movingPatternInternalPrimes e prime x
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  obtain ⟨hsep, hsize, hcop, hrcop, hres⟩ := movingPattern_prior_giant_support e μ ν prime hinj
    hprime pattern rep tier tierB hμtier hνtier hB S V lo t hS hVlo hμlo hνlo p
    (fun i => (hp i).1) (fun i => (hp i).2.2.1) E hμ hν hbound x hx
  have hPi : ∀ q ∈ Pi, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
    intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime _, hupper _⟩
  have hcard : Pi.card ≤ 4 * n * 2 ^ n := by
    calc
      Pi.card ≤ (Finset.univ : Finset C).card := Finset.card_image_le
      _ = Fintype.card C := Finset.card_univ
      _ ≤ 4 * n * 2 ^ n := movingPattern_class_card_le n pattern rep
  have hm := hmod S V t p Pi hS hV hcard hPi (fun i => ⟨(hp i).1, (hp i).2.2.2⟩)
  have hpage := frequencyModel_page_projection S n V cutoff t hS hVcut Pi p
    (selectedPageZero input (giantProgressionCutoff L))
    (by
      intro q hq
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨hprime _, hcutlo.trans (hlarge _).le⟩)
    (fun i => ⟨(hp i).1, (hp i).2.1⟩)
    (by
      intro z hz q hq hmem
      obtain ⟨c, _, hqc⟩ := Finset.mem_image.mp hmem
      have hpc := movingPattern_internal_prior_nonzero e μ ν prime pattern (fun _ => 1) x hx
        (rep c).val
      rw [(rep c).property] at hpc
      exact hdeleteμ z hz q hq _ _ hpc hqc)
    (fun z hz q hq i => (hdeletep z hz q hq i).symm)
  have hr := hreg B C N e small slot (fun i => prime (x i)) hsmall
    (fun i => (hprime _).ne_zero) (fun i => hupper _)
  exact ⟨hsep, hsize, hcop, hrcop, hres, hm.1, hpage, hm.2, hr⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedModulusRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular product and separated arithmetic modulus share one cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The regular primes are included before absorbing the logarithmic budget.
This retains the slack between the nongiant and giant progression scales. -/
theorem movingArithmeticModuli_with_regular_giant_range (n : ℕ) (F K H : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ) (reg : ℕ),
      (m : ℝ) ≤ K * L → P.card ≤ 4 * n * 2 ^ n →
      (r : ℝ) ≤ Real.exp (F * m) →
      (∀ q ∈ P, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (reg : ℝ) ≤ Real.exp (H * L * Real.exp ((11 / 1000 : ℝ) * L)) →
      reg * (∏ b, movingArithmeticModuli r p P Finset.univ b) ≤
        giantProgressionCutoff L := by
  let J : ℝ := 4 * n * 2 ^ n
  let C := F * K + 2 * J + K + H
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hFK : 0 ≤ F * K := mul_nonneg hF hK
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro m r p P reg hm hc hr hP hp hreg
  apply Nat.le_floor
  have hbound := movingArithmeticModuli_exp_bound m r p P F
    (Real.exp ((11 / 1000 : ℝ) * L)) (Real.exp ((1 / 1000 : ℝ) * L)) hr hP hp
  have htotal : ((reg * ∏ b, movingArithmeticModuli r p P Finset.univ b : ℕ) : ℝ) ≤
      Real.exp (F * m + 2 * P.card * Real.exp ((11 / 1000 : ℝ) * L) +
        (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L) + H * L * Real.exp ((11 / 1000 : ℝ) * L)) := by
    rw [Nat.cast_mul]
    apply (mul_le_mul hreg hbound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  apply htotal.trans
  change Real.exp _ ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * (10 * L)))
  rw [show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring]
  apply Real.exp_le_exp.mpr
  have hc' : (P.card : ℝ) ≤ J := by
    dsimp only [J]
    exact_mod_cast hc
  have he : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hKL : 0 ≤ K * L := mul_nonneg hK (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hm hF
  have hi := mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  have hiL : 2 * J * Real.exp ((11 / 1000 : ℝ) * L) ≤
      (2 * J * L) * Real.exp ((11 / 1000 : ℝ) * L) := by
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) hJ) hL) (Real.exp_nonneg _)
  have hs := mul_le_mul hm he (Real.exp_nonneg _) hKL
  have hC1 : F * K ≤ C := by dsimp only [C]; linarith
  have hC2 : 2 * J + K + H ≤ C := by dsimp only [C]; linarith
  have hC1L := mul_le_mul_of_nonneg_right hC1 (show 0 ≤ L by linarith)
  have hC2L := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ L by linarith)
  have hC2e := mul_le_mul_of_nonneg_right hC2L (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  nlinarith only [hmain, hi, hiL, hs, hC1L, hC2e, hrate]

theorem movingPattern_regular_exp_range (n r₀ k : ℕ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ),
      MovingLeafLengthLE n small r₀ →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp (((2 ^ n : ℕ) : ℝ) * ((r₀ : ℝ) + (k : ℝ) ^ 4) * L *
          Real.exp ((11 / 1000 : ℝ) * L)) := by
  let K : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hlarge
  dsimp only
  intro B C N e small slot value hsmall hvalue
  apply (naturalProduct_exp_bound value (Real.exp ((11 / 1000 : ℝ) * L)) hvalue _).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  have hsmall' := moving_flatten_length_le n (movingPatternFiniteSmall e n small) r₀
    (movingLeafLengthLE_map _ n small r₀ hsmall)
  have hbulk := moving_flatten_length_le n
    (bulkSlotLeaves n (spectatorBulkCount k L) (movingPatternBulkEmbedding e slot))
    (spectatorBulkCount k L) (bulkSlotLeaves_length n _ _)
  have hlen := Nat.cast_le (α := ℝ).mpr (Nat.add_le_add hsmall' hbulk)
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hr := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg r₀)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hr hm)
    (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  rw [List.length_append, Nat.cast_add]
  push_cast at hlen
  apply hlen.trans
  simpa only [K, mul_one, Nat.cast_pow, Nat.cast_ofNat, mul_add, add_mul, mul_assoc] using hh

/-- The actual frequency tree, internal image and regular product fit the
same giant cutoff, rather than two separately exhausted budgets. -/
theorem movingPattern_actual_separated_modulus_range (n r₀ k : ℕ)
    (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ)
        (S : Finset ℤ) (Nfreq : ℕ) (t : FrequencyTree (S × S) n)
        (p : Fin m → ℕ) (P : Finset ℕ),
      MovingLeafLengthLE n small r₀ →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ Nfreq) →
      (Nfreq : ℝ) ≤ Real.exp (Cfreq * m) → P.card ≤ 4 * n * 2 ^ n →
      (∀ q ∈ P, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
        p P Finset.univ b
      reg * M ≤ giantProgressionCutoff L := by
  let D : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  let H : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  filter_upwards [movingArithmeticModuli_with_regular_giant_range n
      ((D : ℝ) * Cfreq) ((k : ℝ) ^ 4) H
      (by positivity) (by positivity) (by dsimp only [H]; positivity),
    movingPattern_regular_exp_range n r₀ k, eventually_ge_atTop (0 : ℝ)]
    with L hL hregular hL0
  dsimp only at hregular ⊢
  intro B C N e small slot value S Nfreq t p P hsmall hvalue hS hN hcard hP hp
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : (r : ℝ) ≤ Real.exp (((D : ℝ) * Cfreq) * spectatorBulkCount k L) := by
    simpa only [mul_assoc, D, r] using frequencyModelModulus_exp_bound S Nfreq n t
      (Cfreq * spectatorBulkCount k L) (fun s hs => (hS s hs).2) hN
  exact hL (spectatorBulkCount k L) r p P _ (spectatorBulkCount_upper k L hL0)
    hcard hr (fun q hq => (hP q hq).2) (fun i => (hp i).2)
    (hregular B C N e small slot value hsmall hvalue)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSeparatedConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supplying the giant arithmetic conditions from the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All assignment-dependent conditions of the giant comparison follow from
actual prime ranges, original-prior support, and the prescribed conductor
prime deletion. No arithmetic comparison is assumed in this statement. -/
theorem movingPattern_separated_giant_conditions (input : PublishedProgressionInput)
    (n r₀ k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
        (tier : A → ℕ) (tierB : B → ℕ)
        (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
        (pattern : Bool × MovingSampleIndex n → C)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (p : Fin m → ℕ) (lo cutoff : ℕ) (E : ℝ),
      let R := frequencyModelBase S n t
      let Pi := fun x => movingPatternInternalPrimes e prime x
      let M := fun x => ∏ b, movingArithmeticModuli (R ^ (n - 1 + 2)) p (Pi x) Finset.univ b
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (movingPatternRegularSlots e n m small slot)
      Function.Injective prime → (∀ a, (prime a).Prime) →
      (∀ j a, 0 ≤ μ j a) → (∀ j a, 0 ≤ ν j a) →
      (∀ j a, (prime a : ℝ) * μ j a ≤ E) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) → (∀ b, n ≤ tierB b) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) → (V : ℝ) ≤ Real.exp (Cfreq * m) →
      V ≤ lo → V < cutoff → cutoff ≤ lo →
      (∀ j a, μ j a ≠ 0 → lo < prime a) →
      (∀ j a, ν j a ≠ 0 → lo < prime a) →
      (∀ a, (prime a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ cutoff ≤ p i ∧ p i ≤ lo ∧
        (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → prime a ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → prime a ≠ q) →
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      Reg x * M x ≤ giantProgressionCutoff L ∧
      (Reg x).Coprime (M x) ∧
      pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Real.log (M x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [movingPattern_giant_conditions input n r₀ k Cfreq hCfreq,
    movingPattern_actual_separated_modulus_range n r₀ k Cfreq hCfreq]
    with L hbase hmod
  dsimp only
  intro A B C _ _ _ N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν x hx
  have hb := hbase A B C N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep x hx
  dsimp only at hb
  rcases hb with ⟨hsep, hsize, hcop, hrcop, hres, _, hpage, hlog, _⟩
  let Pi := movingPatternInternalPrimes e prime x
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  have hcross := (movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hprior).2
  have hspec (i j) : prime (x j) ≠ p i := by
    intro he
    have hh := (hp i).2.2.1.trans_lt (hlarge j)
    omega
  have hregcop := movingPattern_regular_arithmetic_coprime e prime hprime x
    (frequencyModelBase S n t ^ (n - 1 + 2)) p (fun i => (hp i).1)
    small slot hrcop hcross hspec
  have hdelete (z : PrimitiveRealZero)
      (hz : selectedPageZero input (giantProgressionCutoff L) = some z)
      (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) :
      ∀ i, prime (x i) ≠ q := by
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hprior i (Finset.mem_univ i)
    cases he : e i with
    | inl b =>
      have hνi : ν b (x i) ≠ 0 := by simpa only [he, Sum.elim_inl] using hi
      exact hdeleteν z hz q hq b (x i) hνi
    | inr c =>
      have hμi : μ (movingSampleTier (rep c).val.2) (x i) ≠ 0 := by
        simpa only [he, Sum.elim_inr] using hi
      exact hdeleteμ z hz q hq _ _ hμi
  have hregpage := movingPattern_regular_page_projection e prime hprime x p
    (fun i => (hp i).1) small slot S V cutoff t hS hVcut
    (fun i => hcutlo.trans (hlarge i).le) (selectedPageZero input (giantProgressionCutoff L))
    hdelete hdeletep
  have hPi : ∀ q ∈ Pi, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
    intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime _, hupper _⟩
  have hcard : Pi.card ≤ 4 * n * 2 ^ n := by
    calc
      Pi.card ≤ (Finset.univ : Finset C).card := Finset.card_image_le
      _ = Fintype.card C := Finset.card_univ
      _ ≤ 4 * n * 2 ^ n := movingPattern_class_card_le n pattern rep
  have hfull := hmod B C N e small slot (fun i => prime (x i)) S V t p Pi hsmall
    (fun i => hupper _) hS hV hcard hPi (fun i => ⟨(hp i).1, (hp i).2.2.2⟩)
  exact ⟨hsep, hsize, hcop, hrcop, hres, hfull, hregcop, hregpage, hpage, hlog⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueFamily_eq (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] :
    normalizedResidueFamily sets q = normalizedResidueTransform (sets q) := by
  simp only [normalizedResidueFamily, dite_eq_right (NeZero.ne q)]

theorem normalizedResidueFamily_zero (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] : normalizedResidueFamily sets q 0 = 0 := by
  rw [normalizedResidueFamily_eq]
  exact normalizedResidueTransform_zero _

theorem normalizedResidueFamily_energy (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] (h : (sets q).Nonempty) (hcard : (sets q).card < q) :
    (∑ z : ZMod q, ‖normalizedResidueFamily sets q z‖ ^ 2) = q := by
  rw [normalizedResidueFamily_eq]
  exact normalizedResidueTransform_energy _ h hcard

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete diagonal arithmetic data under the original prime priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingPattern_diagonal_conditions (input : PublishedProgressionInput)
    (n r₀ k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
        (tier : A → ℕ) (tierB : B → ℕ)
        (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
        (pattern : Bool × MovingSampleIndex n → C)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (p : Fin m → ℕ) (lo cutoff : ℕ) (E : ℝ)
        (sreg : ℤ) (sets : ∀ q : ℕ, Finset (ZMod q)),
      let R := frequencyModelBase S n t
      let Pi := fun x => movingPatternInternalPrimes e prime x
      let M := fun x => ∏ b, movingArithmeticModuli (R ^ (n - 1 + 2)) p (Pi x) Finset.univ b
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => prime (x i))
        (movingPatternRegularSlots e n m small slot)
      Function.Injective prime →
      (∀ j a, 0 ≤ μ j a) → (∀ j a, 0 ≤ ν j a) →
      (∀ j a, (prime a : ℝ) * μ j a ≤ E) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) → (∀ b, n ≤ tierB b) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) → (V : ℝ) ≤ Real.exp (Cfreq * m) →
      V ≤ lo → V < cutoff → cutoff ≤ lo →
      (∀ j a, μ j a ≠ 0 → lo < prime a) →
      (∀ j a, ν j a ≠ 0 → lo < prime a) →
      (∀ a, (prime a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ cutoff ≤ p i ∧ p i ≤ lo ∧
        (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → prime a ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → prime a ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ V →
      (∀ q, q.Prime → (sets q).Nonempty ∧ (sets q).card < q) →
      ∀ x : Fin (N + 1) → A,
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0 →
      let t₀ := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
      let slots := movingPatternRegularSlots e n m small slot
      let T := movingPatternFinBulkData e n m t₀ (fun _ => small) slot (Equiv.refl _) pattern
      ∀ (outside : List ℕ),
      (∀ b, movingRegularOutsidePairwise (fun i => prime (x i)) outside (T b)) →
      let : ∀ j : Fin slots.length, Fact (prime (x (slots.get j))).Prime :=
        fun _ => ⟨hprime _⟩
      (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
        (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
          prime (x i) ≠ prime (x j)) ∧
      (∀ i, V < prime (x i)) ∧
      (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
      (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
      (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
      (Reg x).Coprime (M x) ∧ Reg x * M x ≤ giantProgressionCutoff L ∧
      pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
      pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus (R ^ (n - 1 + 2)) (selectedPageZero input (giantProgressionCutoff L)) ∧
      Pairwise (fun i j : Fin slots.length =>
        (prime (x (slots.get i))).Coprime (prime (x (slots.get j)))) ∧
      (∀ i : Fin slots.length, (sreg : ZMod (prime (x (slots.get i)))) ≠ 0) ∧
      (∀ i : Fin slots.length,
        (movingRegularOther (fun j => prime (x j)) outside slots i :
          ZMod (prime (x (slots.get i)))) ≠ 0) ∧
      (∀ i : Fin slots.length, normalizedResidueFamily sets (prime (x (slots.get i))) 0 = 0) ∧
      (∀ i : Fin slots.length,
        (∑ z : ZMod (prime (x (slots.get i))),
          ‖normalizedResidueFamily sets (prime (x (slots.get i))) z‖ ^ 2) =
          prime (x (slots.get i))) := by
  filter_upwards [movingPattern_separated_giant_conditions input n r₀ k Cfreq hCfreq]
    with L hbase
  dsimp only
  intro A B C _ _ _ N e prime hprime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    sreg sets hinj hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo
    hupper hp hsmall hdeleteμ hdeletep hdeleteν hsreg hsregV hsets x hx outside hgood
  have hb := hbase A B C N e prime tier tierB μ ν pattern rep S V t small slot p lo cutoff E
    hinj hprime hμ hν hbound hμtier hνtier hB hS hV hVlo hVcut hcutlo hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν x hx
  dsimp only at hb
  rcases hb with ⟨hsep, hlarge, hcop, hrcop, hres, hfull, hregcop, hpageReg, hpage, _⟩
  let t₀ := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
  let slots := movingPatternRegularSlots e n (spectatorBulkCount k L) small slot
  let : ∀ j : Fin slots.length, Fact (prime (x (slots.get j))).Prime := fun _ => ⟨hprime _⟩
  refine ⟨hsep, hlarge, hcop, hrcop, hres, hregcop, hfull, hpageReg, hpage, ?_, ?_, ?_, ?_, ?_⟩
  · exact movingPattern_regular_pairwise e t₀ small slot pattern (fun i => prime (x i))
      outside false (hgood false)
  · exact movingPattern_regular_frequency_unit (fun i => prime (x i)) (fun _ => hprime _)
      slots V hlarge sreg hsreg hsregV
  · exact movingPattern_regular_other_unit e t₀ small slot pattern (fun i => prime (x i))
      (fun _ => hprime _) outside false (hgood false)
  · intro i
    exact normalizedResidueFamily_zero sets _
  · intro i
    exact normalizedResidueFamily_energy sets _ (hsets _ (hprime _)).1 (hsets _ (hprime _)).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularCollisionSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invalid regular-prime configurations vanish before either average -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSupportedWeight_zero_of_not_regular {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hbad : ¬ movingRegularOutsidePairwise value outside T)
    (XL XR : ℕ) (z : ℂ) : movingSupportedWeight value outside T XL XR z = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (movingFullOutsidePairwise_regular value outside T XL XR h.1)

theorem movingOriginalSupportedOuterPair_zero_of_not_regular {σ I : Type*}
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (t : Bool → FrequencyTree ℤ n) (hbad : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b))
    (XL XR : ℕ) :
    movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi
      φ G Jleft Jright diagonal T t XL XR = 0 := by
  obtain ⟨b, hb⟩ := not_forall.mp hbad
  have hz := movingSupportedWeight_zero_of_not_regular value outside (T b) hb XL XR
  cases b <;> simp only [movingOriginalSupportedOuterPair, hz, map_zero, zero_mul, mul_zero]

theorem movingFrequencyPageAverage_zero_of_not_regular {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (hbad : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b)) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y = 0 := by
  rw [movingFrequencyPageAverage_core]
  have hn : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds) := fun h => hbad (fun b => (h b).1)
  rw [ite_eq_right hn, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternOriginalDiagonalNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original signed diagonal and its retained arithmetic integral -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_diagonal_norm
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C J : Type) [Fintype B] [Fintype C] [Fintype J] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (_hinjp : Function.Injective p)
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (reg : J → Fin (N + 1)) (active : J → Bool) (sreg : ℤ)
        (other : (Fin (N + 1) → primes) → J → ℤ) (greg : ∀ q : ℕ, ZMod q → ℂ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (V : ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
        (E U u v a b center : ℝ),
      let : ∀ q : primes, Fact (q : ℕ).Prime := fun q => ⟨hprimes _ q.property⟩
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let coeff := movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1)
      let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
      let M := fun x => ∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
        (movingPatternRegularSlots e n m small slot)
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ E → 0 ≤ U → (∀ j (q : primes), (q : ℝ) * μ j q ≤ E) →
      (∀ q : primes, (q : ℝ) ≤ U) →
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, r.Coprime (p i)) → (∀ i, V < p i) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      (∀ x, Reg x = ∏ j, (x (reg j) : ℕ)) →
      (∀ x, coeff x ≠ 0 →
        (∀ b, movingRegularOutsidePairwise (fun i => (x i : ℕ)) outside (T b)) →
        (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) ∧
        (∀ i, V < (x i : ℕ)) ∧
        (∀ i, IsCoprime ((x i : ℕ) : ℤ) R) ∧
        (∀ i, r.Coprime (x i : ℕ)) ∧
        (∀ i j, ((x j : ℕ) : ZMod (p i)) ≠ 0) ∧
        (Reg x).Coprime (M x) ∧ Reg x * M x ≤ giantProgressionCutoff L ∧
        pageAtModulus (Reg x * M x) (selectedPageZero input (giantProgressionCutoff L)) =
          pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) ∧
        pageAtModulus (M x) (selectedPageZero input (giantProgressionCutoff L)) =
          pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) ∧
        Pairwise (fun i j => (x (reg i) : ℕ).Coprime (x (reg j) : ℕ)) ∧
        (∀ i, (sreg : ZMod (x (reg i) : ℕ)) ≠ 0) ∧
        (∀ i, (other x i : ZMod (x (reg i) : ℕ)) ≠ 0) ∧
        (∀ i, greg (x (reg i) : ℕ) 0 = 0) ∧
        (∀ i, (∑ z : ZMod (x (reg i) : ℕ), ‖greg (x (reg i) : ℕ) z‖ ^ 2) = (x (reg i) : ℕ))) →
      let actual := movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
        p g Dq reg active sreg other greg f outside childBound pivotBound ψ X lo hi φ G
        Jleft Jright diagonal u v a b center
      let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) *
          movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
            primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
            (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
            (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern actual x‖ ≤
        (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ := by
  filter_upwards [input.moving_pattern_diagonal_haar_rate ψ n r₀ k Afreq Wwin Bφ Dφ
    hAfreq hWwin hBφ hDφ] with L hL
  dsimp only
  intro B C J _ _ _ N e tierB tierC t small slot pattern rep primes hprimes μ ν
    p _ hinjp g Dq reg active sreg other greg f outside childBound pivotBound R r _ V hfreq
    X lo hi hlo hhi φ G Jleft Jright diagonal E U u v a b center
    hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout hR
    hprecision hrp hspecLarge hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter
    ha hab hb hRegEq hdata
  let m := spectatorBulkCount k L
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
  let haar := movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
    n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern
  let actual := movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
    p g Dq reg active sreg other greg f outside childBound pivotBound ψ X lo hi φ G
    Jleft Jright diagonal u v a b center
  let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
      (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) *
      movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
        primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
        (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
        (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
        (Real.exp (z - center) : ℂ) / (y : ℂ)
  let ε := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
    Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))
  have hcompare (x : Fin (N + 1) → primes)
      (hx : movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1) x ≠ 0) :
      ‖actual x - integral x * haar x‖ ≤ ε := by
    by_cases hgood : ∀ b, movingRegularOutsidePairwise (fun i => (x i : ℕ)) outside (T b)
    ·
      obtain ⟨hdisjoint, hlarge, hsmallR, hrcop, hres, hcop, hfull, hpageReg, hpage,
        hreg, hsreg, hother, hgreg, henergy⟩ := hdata x hx hgood
      have hprime (i) : (x i : ℕ).Prime := hprimes _ (x i).property
      let : ∀ j, Fact (x (reg j) : ℕ).Prime := fun j => ⟨hprime _⟩
      have hPi := movingPatternInternalPrimes_prime e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) x
      let : ∀ q : Pi x, Fact q.val.Prime := fun q => ⟨hPi _ q.property⟩
      have hnz (z) : movingArithmeticModuli r p (Pi x) Finset.univ z ≠ 0 :=
        movingArithmeticModuli_ne_zero r p (Pi x) Finset.univ (NeZero.ne r) hPi
          (fun i _ => (Fact.out : (p i).Prime)) z
      let : ∀ z, NeZero (movingArithmeticModuli r p (Pi x) Finset.univ z) := fun z => ⟨hnz z⟩
      let : NeZero (∏ z, movingArithmeticModuli r p (Pi x) Finset.univ z) :=
        ⟨Finset.prod_ne_zero_iff.mpr (fun z _ => hnz z)⟩
      have hsep (i : Fin m) (j : Fin (N + 1)) : (x j : ℕ) ≠ p i := by
        intro heq
        apply hres i j
        rw [heq]
        exact ZMod.natCast_self (p i)
      have hc := movingPattern_prime_moduli_coprime e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) x r p (fun i => (Fact.out : (p i).Prime))
        hinjp hrcop hrp hsep
      have hinj := movingPattern_nonzero_internal_injective e μ ν (fun q : primes => (q : ℕ))
        Subtype.val_injective pattern (fun _ => 1) x hx
      have hqs (i : Fin m) : (∏ j, (x (reg j) : ℕ)).Coprime (p i) := by
        apply Nat.coprime_prod_left_iff.mpr
        intro j _
        exact (Nat.coprime_primes (hprime _) (Fact.out : (p i).Prime)).mpr (hsep i _)
      have hh := hL B C J N e tierB tierC t small slot pattern primes hprimes x p g Dq
        (fun j => (x (reg j) : ℕ)) active sreg (fun j => (other x j : ZMod (x (reg j) : ℕ)))
        (fun j => greg (x (reg j) : ℕ)) f outside childBound pivotBound R r (Pi x) hfreq V
        X lo hi hlo hhi φ G Jleft Jright diagonal hB htier hdisjoint hV hlarge hf hg hgnorm
        hout hR hprecision hsmallR hres hspecLarge rfl hinj hc (hRegEq x) hcop hfull hpageReg hpage
        hgood hreg hqs hsreg hother hgreg henergy hVA hwindow hpupper hφ hlip hφout
        u v a b center hcenter huv hv hvcenter ha hab hb
      exact hh
    · have ha0 (XL XR : ℕ) : movingOriginalSupportedOuterPair p (fun i => (x i : ℕ)) outside
          childBound pivotBound (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g
          (fun _ => Dq) Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t XL XR = 0 :=
        movingOriginalSupportedOuterPair_zero_of_not_regular p _ outside childBound pivotBound
          _ _ g _ Finset.univ ψ X lo hi φ G Jleft Jright diagonal T t hgood XL XR
      have hraw (z y : ℝ) : movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _)
          pattern primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
          (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
          (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x = 0 := by
        change _ * (movingFrequencyPageAverage (fun i => (x i : ℕ)) outside
          (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) T _ R r input
          (giantProgressionCutoff L) y * _) = 0
        rw [movingFrequencyPageAverage_zero_of_not_regular _ outside _ _ T _ R r input
          (giantProgressionCutoff L) y hgood, zero_mul, mul_zero]
      dsimp only [T, m] at ha0
      have hactual : actual x = 0 := by
        simp only [actual, movingOriginalPatternDiagonalObservable, ha0, zero_mul,
          complexIntegerInterval, complexPrimeInterval, ite_self, Finset.sum_const_zero]
      have hideal : integral x = 0 := by
        simp only [integral, hraw, mul_zero, zero_mul, zero_div, integral_zero]
      rw [hactual, hideal, zero_mul, sub_self, norm_zero]
      dsimp only [ε]
      positivity
  have hbnd := movingPattern_comparison_norm e μ ν (fun q : primes => (q : ℕ)) pattern rep
    E U ε hE hU (by dsimp only [ε]; positivity) (fun q => hprimes _ q.property)
    hμ hν hμmass hνmass hbound hsize actual (fun x => integral x * haar x) hcompare
  have he : (∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
      (fun x => integral x * haar x) x) =
      ∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x * haar x := by
    apply Finset.sum_congr rfl
    intro x _
    conv_lhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    conv_rhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    ring
  simpa only [he] using hbnd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalPrimeRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original signed diagonal bound from actual prime ranges and conductor deletion -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_diagonal_prime_ranges
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) [Fintype B] [Fintype C] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (_hinjp : Function.Injective p)
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (sets : ∀ q : ℕ, Finset (ZMod q))
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (S : Finset ℤ) (ft : FrequencyTree (S × S) n)
        [NeZero (frequencyModelBase S n ft ^ (n - 1 + 2))] (V : ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
        (E U u v a b center : ℝ),
      let reg := (movingPatternRegularSlots e n m small slot).get
      let other := fun (x : Fin (N + 1) → primes) =>
        movingRegularOther (fun i => (x i : ℕ)) outside (movingPatternRegularSlots e n m small slot)
      let greg := normalizedResidueFamily sets
      let R : ℤ := frequencyModelBase S n ft
      let r := frequencyModelBase S n ft ^ (n - 1 + 2)
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ E → 0 ≤ U → (∀ j (q : primes), (q : ℝ) * μ j q ≤ E) →
      (∀ q : primes, (q : ℝ) ≤ U) →
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b ft)) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) →
      ∀ (tier : primes → ℕ) (lower cutoff : ℕ),
      V ≤ lower → V < cutoff → cutoff ≤ lower →
      (∀ j, j < n → ∀ q, μ j q ≠ 0 → tier q = j) →
      (∀ j q, ν j q ≠ 0 → tier q = tierB j) →
      (∀ j q, μ j q ≠ 0 → lower < (q : ℕ)) →
      (∀ j q, ν j q ≠ 0 → lower < (q : ℕ)) →
      (∀ q : primes, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ lower) →
      MovingLeafLengthLE n small r₀ →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero input (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ V →
      (∀ q, q.Prime → (sets q).Nonempty ∧ (sets q).card < q) →
      let actual := movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
        p g Dq reg active sreg other greg f outside childBound pivotBound ψ X lo hi φ G
        Jleft Jright diagonal u v a b center
      let integral := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) *
          movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
            primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
            (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
            (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern actual x‖ ≤
        (((2 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * U ^ Fintype.card C) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern integral x *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ := by
  filter_upwards [input.movingPattern_original_diagonal_norm ψ n r₀ k Afreq Wwin Bφ Dφ
    hAfreq hWwin hBφ hDφ, movingPattern_diagonal_conditions input n r₀ k Afreq hAfreq]
    with L hnorm hconditions
  dsimp only
  intro B C _ _ N e tierB tierC t small slot pattern rep primes hprimes μ ν p _ hinjp
    g Dq active sreg sets f outside childBound pivotBound S ft _ V hfreq
    X lo hi hlo hhi φ G Jleft Jright diagonal E U u v a b center
    hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout
    hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter ha hab hb
    ht hS tier lower cutoff hVlo hVcut hcutlo hμtier hνtier hμlo hνlo hupper
    hp hsmall hdeleteμ hdeletep hdeleteν hsreg hsregV hsets
  let m := spectatorBulkCount k L
  let R := frequencyModelBase S n ft
  let r := R ^ (n - 1 + 2)
  let slots := movingPatternRegularSlots e n m small slot
  let reg := slots.get
  let other := fun (x : Fin (N + 1) → primes) => movingRegularOther (fun i => (x i : ℕ)) outside slots
  have hR (b : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b).frequencyProduct ∣
        (R : ℤ) := by
    simpa only [ht, R] using
      movingPattern_frequencyProduct_dvd e S ft (fun _ => small) slot (Equiv.refl _) pattern b
  have hrp (i) : r.Coprime (p i) := by
    exact ((prime_coprime_frequencyModelBase S V (p i) n Fact.out
      (hVcut.trans_le (hp i).1) hS ft).pow_right _).symm
  apply hnorm B C (Fin slots.length) N e tierB tierC t small slot pattern rep primes hprimes μ ν
    p hinjp g Dq reg active sreg other (normalizedResidueFamily sets) f outside
    childBound pivotBound (R : ℤ) r V hfreq X lo hi hlo hhi φ G Jleft Jright diagonal
    E U u v a b center hμ hν hμmass hνmass hE hU hbound hsize hB htier hV hf hg hgnorm hout
    hR (frequencyModelModulus_precision R n) hrp (fun i => hVcut.trans_le (hp i).1)
    hVA hwindow hpupper hφ hlip hφout hcenter huv hv hvcenter ha hab hb
  · intro x
    exact naturalProduct_eq_finprod (fun i => (x i : ℕ)) slots
  · intro x hx hgood
    have hh := hconditions primes B C N e (fun q : primes => (q : ℕ))
      (fun q => hprimes _ q.property) tier tierB μ ν pattern rep S V ft small slot p lower cutoff E
      sreg sets Subtype.val_injective hμ hν hbound hμtier hνtier hB hS hVA hVlo hVcut hcutlo
      hμlo hνlo hupper (fun i => ⟨Fact.out, (hp i).1, (hp i).2, hpupper i⟩) hsmall
      hdeleteμ hdeletep hdeleteν hsreg hsregV hsets x hx outside
    have hteq : tierC = fun c => movingSampleTier (rep c).val.2 := by
      funext c
      have hh := htier (rep c).val
      simpa only [(rep c).property] using hh
    simpa only [← ht, ← hteq] using hh (by simpa only [← ht] using hgood)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic support under the unchanged representative prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- The literal list of frequencies still lies in the finite source set. -/
theorem allFrequencyList_subtype_mem (S : Finset ℤ) (n : ℕ)
    (t : FrequencyTree S n) (s : ℤ)
    (hs : s ∈ allFrequencyList n (frequencyTreeMap Subtype.val n t)) : s ∈ S := by
  induction n with
  | zero =>
    have heq : s = Subtype.val t := by simpa only [frequencyTreeMap, allFrequencyList, List.mem_singleton] using hs
    simpa only [heq] using (Subtype.property t)
  | succ n ih =>
    simp only [frequencyTreeMap, allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with heq | hs | hs
    · simpa only [heq] using (Subtype.property t.1)
    · exact ih t.2.1 hs
    · exact ih t.2.2 hs

/-- Range separation supplies the arithmetic support used when averaging
internal primes. The conclusion holds on the actual product prior, before
restricting to a nonzero observable. -/
theorem movingPattern_prior_arithmetic_support {A B C I : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ) (tierC : C → ℕ)
    (hμtier : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hνtier : ∀ j a, ν j a ≠ 0 → tier a = tierB j) (hB : ∀ b, n ≤ tierB b)
    (htierC : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (S : Finset ℤ) (V lo : ℕ) (ft : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hVlo : V ≤ lo)
    (hμlo : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hνlo : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hplo : ∀ i, p i ≤ lo)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    (∀ i, IsCoprime (prime (x i) : ℤ) (frequencyModelBase S n ft : ℤ)) ∧
    (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
    (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
      prime (x i) ≠ prime (x j)) ∧
    (∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c)))) ∧
    (∀ c b, (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies
      (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) := by
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hx
  have hlargeV (i) : V < prime (x i) := hVlo.trans_lt (hlarge i)
  have hcop := movingPattern_prior_frequency_coprime e μ ν prime hprime pattern rep S V ft hS
    (fun j a ha => hVlo.trans_lt (hμlo j a ha))
    (fun j a ha => hVlo.trans_lt (hνlo j a ha)) x hx
  have hsep := movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hx
  have htierEq : tierC = fun c => movingSampleTier (rep c).val.2 := by
    funext c
    have h := htierC (rep c).val
    simpa only [(rep c).property] using h
  refine ⟨?_, ?_, ?_, hsep.2, ?_⟩
  · intro i
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop i
  · intro i j hz
    have hd := (ZMod.natCast_eq_zero_iff (prime (x j)) (p i)).mp hz
    have heq := (Nat.prime_dvd_prime_iff_eq (hp i) (hprime _)).mp hd
    have hlt := (hplo i).trans_lt (hlarge j)
    omega
  · simpa only [htierEq] using hsep.1
  · intro c b
    let T := movingPatternFinBulkData e n m t small slot perm pattern b
    exact T.small_frequency_residues (fun i => prime (x i)) (fun i => hprime _)
      V hlargeV (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hf b)
      (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hfreq b) (e.symm (.inr c))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full per-pattern diagonal bound under its original signed prime priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_diagonal_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (_hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG center : ℝ),
      let reg := (movingPatternRegularSlots e n m small slot).get
      let data := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (fun {_} _ => f) ((fun _ _ _ _ _ => 1) false) (data false)‖ *
        ‖movingDataWeight (fun {_} _ => f) ((fun _ _ _ _ _ => 1) true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      MovingLeafLengthLE n small r₀ →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
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
      Function.Injective p →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      ∀ (tier : primes → ℕ) (lower cutoff : ℕ),
      Nfreq ≤ lower → Nfreq < cutoff → cutoff ≤ lower →
      (∀ j, j < n → ∀ q, μ j q ≠ 0 → tier q = j) →
      (∀ j q, ν j q ≠ 0 → tier q = tierB j) →
      (∀ j q, μ j q ≠ 0 → lower < (q : ℕ)) →
      (∀ j q, ν j q ≠ 0 → lower < (q : ℕ)) →
      (∀ q : primes, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ lower) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq reg active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          Uall ^ Fintype.card Cidx) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
      diagonalOuterMajorant Bφ Dφ diagonal * ((2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) := by
  filter_upwards [P.movingPattern_diagonal_ideal_integral_rate ψ n r₀ k A Wwin Bφ Dφ Cmass
    hA hWwin hCmass hBφ hDφ,
    P.movingPattern_original_diagonal_prime_ranges ψ n r₀ k A Wwin Bφ Dφ hA hWwin hBφ hDφ]
    with L hideal hcompare
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes _ childBound pivotBound hfreq f outside _ p _ hc _
    Dq sets X j₀ φ G u v deleted initial μ ν active sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed
    hinjp houtp hNupper hcenterlow hrGlow tier lower cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hprange hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  let m := spectatorBulkCount k L
  let slots := movingPatternRegularSlots e n m small slot
  let reg := slots.get
  have hsmall' : ∀ b : Bool, ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot :=
    fun _ => hsmall
  have hsmallLen' : ∀ b : Bool, MovingLeafLengthLE n small r₀ := fun _ => hsmallLen
  have hfreqN (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s.natAbs ≤ Nfreq := by
    rw [ht] at hs
    exact hN s (allFrequencyList_subtype_mem Sfreq n _ s hs)
  have hsupport (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :=
    movingPattern_prior_arithmetic_support e μ ν (fun q : primes => (q : ℕ))
      Subtype.val_injective (fun q => hprimes _ q.property) pattern rep tier tierB tierC
      hμtier hνtier hB htier Sfreq Nfreq lower ft (fun s hs => ⟨hS s hs, hN s hs⟩)
      hNlo hμlo hνlo p (fun i => Fact.out) (fun i => (hprange i).2) t
      (fun _ => small) slot (Equiv.refl _) hfreq hfreqN x hx
  have hfreqp (i : Fin m) (b : Bool) : movingGiantFrequencyUnits (p i) n (t b) :=
    movingGiantFrequencyUnits_of_bounds (t b) (fun s hs =>
      ⟨hfreq b s hs, (hfreqN b s hs).trans_lt (hNcut.trans_le (hprange i).1)⟩)
  have hIdeal := hideal lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq Vleaf D
    (fun _ => small) slot pattern rep primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
    outside p hc (fun i _ => Dq i) sets (giantProgressionCutoff L) X j₀ φ G u v deleted initial μ ν
    (Fin slots.length) reg active Jleft Jright diagonal Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter hsmall' hB htier hsmallLen' ht hS hN (fun _ s _ => hleaf s) hD hdiv hm
    hp hfreqp
    (fun x hx i _ => (hsupport x hx).1 i)
    (fun x hx i _ j _ => (hsupport x hx).2.1 i (e.symm (.inl j)))
    (fun x hx i c => (hsupport x hx).2.1 i (e.symm (.inr c))) hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.1)
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.2.1)
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.2.2)
  have hf (s : ℤ) : ‖f s‖ ≤ 1 := (hleaf s).trans (by split_ifs <;> norm_num)
  have hspect (i : Fin m) (z : ZMod (p i)) : ‖normalizedResidueTransform (sets i) z‖ ≤ (p i : ℝ) :=
    normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z
  have hc := hcompare Bidx Cidx N e tierB tierC t small slot pattern rep primes hprimes μ ν p
    hinjp (fun i => normalizedResidueTransform (sets i)) Dq active sreg setsReg f outside
    childBound pivotBound Sfreq ft Nfreq hfreq X lo hi hlo hhi φ G Jleft Jright diagonal
    Eprior Uall uG vG rG sG center hμ0 hν0 hμmass hνmass hEprior (by linarith)
    hμbound hvalues hB htier hfreqN hf (fun i => normalizedResidueTransform_zero (sets i))
    hspect houtp hNupper hwindow hpupper hφ hlip hφout hcenterlow huvG hvG hcenter
    hrGlow hrsG hsG ht (fun s hs => ⟨hS s hs, hN s hs⟩) tier lower cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hprange hsmallLen hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  exact hc.trans (add_le_add (le_refl _) hIdeal)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalSharp
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp original-prior diagonal estimate after absorbing the comparison errors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_diagonal_sharp
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass Cprior : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) (hCprior : 1 ≤ Cprior) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (_hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG center : ℝ),
      let reg := (movingPatternRegularSlots e n m small slot).get
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      MovingLeafLengthLE n small r₀ →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
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
      Function.Injective p →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      ∀ (tier : primes → ℕ) (lower cutoff : ℕ),
      Nfreq ≤ lower → Nfreq < cutoff → cutoff ≤ lower →
      (∀ j, j < n → ∀ q, μ j q ≠ 0 → tier q = j) →
      (∀ j q, ν j q ≠ 0 → tier q = tierB j) →
      (∀ j q, μ j q ≠ 0 → lower < (q : ℕ)) →
      (∀ j q, ν j q ≠ 0 → lower < (q : ℕ)) →
      (∀ q : primes, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ lower) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      Eprior ≤ Real.exp (Cprior * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq reg active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx *
        (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
      ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
        Bφ ^ (2 ^ n - 1)) ^ 2) * A₀ * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [P.movingPattern_original_diagonal_arithmetic_rate ψ n r₀ k A Wwin Bφ Dφ Cmass
    hA hWwin hCmass hBφ hDφ,
    movingPattern_diagonal_pointwise_rate ψ n r₀ k A Wwin Bφ Dφ Cprior Cmass
      hA hWwin hBφ hDφ hCprior (by linarith)] with L hmain hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes _ childBound pivotBound hfreq f outside _ p _ hc _
    Dq sets X j₀ φ G u v deleted initial μ ν active sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed
    hinjp houtp hNupper hcenterlow hrGlow tier lower cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hprange hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg hEup hUlog hαup hβup hVeq
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let amp := 2 * (‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data false)‖ *
    ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data true)‖)
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  let K := (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
    Bφ ^ (2 ^ n - 1)) ^ 2) * A₀ * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)
  have hh := hmain lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes childBound pivotBound hfreq f outside p hc Dq sets X j₀ φ G
    u v deleted initial μ ν active sreg setsReg Jleft Jright diagonal Eprior αall βint Vint Uall
    uG vG rG sG center huG hrG huvG hrsG hvG hsG hcenter hsmall hB htier hsmallLen ht hS hN hleaf
    hD hdiv hm hp hV hsets hsetsp hpupper hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell
    hSS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall
    hβint hVint hUall hμbound hμall hνall hμmax hμmin hvalues hfixed hinjp houtp hNupper hcenterlow
    hrGlow tier lower cutoff hNlo hNcut hcutlo hμtier hνtier hμlo hνlo hupper hprange
    hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  have hone (b : Bool) : ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data b)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f)
      (fun s _ => (hleaf s).trans (by split_ifs <;> norm_num)) (data b)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hamp : amp ≤ 4 := by
    have h := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp only [amp]
    linarith
  have hK : 0 ≤ K := by
    have hf := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hs : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact pairFrequencySupportBound_nonneg D b
    dsimp only [K, A₀]
    positivity
  apply hrate p (Fintype.card Cidx) Eprior Uall αall βint amp lo hi rG K _ diagonal
    (movingPattern_class_card_le n pattern rep) hEprior hEup hUall hUlog hαall hαup hβint hβup
    hamp0 hamp hhi hwindow hpupper hrGlow hK
  simpa only [hVeq, add_assoc] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholePrimeGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact short-cell partitions of the original whole prime shells -/

namespace Ostmann
open Filter
open scoped Classical

theorem wholePrimeGridCount_pos (b : ℝ) : 0 < wholePrimeGridCount b := by
  unfold wholePrimeGridCount
  omega

theorem wholePrimeGridCount_upper (b : ℝ) :
    (wholePrimeGridCount b : ℝ) ≤ Real.exp (b + 1) + 2 := by
  have h := Nat.ceil_lt_add_one (Real.exp_nonneg (b + 1))
  unfold wholePrimeGridCount
  push_cast
  linarith

theorem interval_grid_width {N : ℕ} (hN : 0 < N) {u v : ℝ}
    (huv : u ≤ v) (hwidth : v - u ≤ (N : ℝ)) :
    0 ≤ (v - u) / (N : ℝ) ∧ (v - u) / (N : ℝ) ≤ 1 ∧
      u + (N : ℝ) * ((v - u) / (N : ℝ)) = v := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨div_nonneg (sub_nonneg.mpr huv) hp.le, ?_, ?_⟩
  · exact (div_le_one hp).mpr hwidth
  · rw [mul_div_cancel₀ _ hp.ne']
    ring

/-- A whole shell of arbitrary log-log width has the same exact finite grid.
The mesh size depends on the upper endpoint, not on a unit-width restriction. -/
theorem whole_interval_prime_grid_support (q : ℕ) [NeZero q] (a b : ℝ)
    (hab : a ≤ b) (hq : (q : ℝ) ≤ Real.exp (Real.exp a)) :
    let N := wholePrimeGridCount b
    let h := (Real.exp b - Real.exp a) / (N : ℝ)
    primeCellSupport q (gridResidue (N := N) (q := q))
      (gridLower (Real.exp a) h) (gridUpper (Real.exp a) h) =
        primeLogCellSet 1 0 (Real.exp a) (Real.exp b) := by
  intro N h
  have hwidth : Real.exp b - Real.exp a ≤ (wholePrimeGridCount b : ℝ) := by
    have hc := Nat.le_ceil (Real.exp (b + 1))
    have he : Real.exp b ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr (by linarith)
    unfold wholePrimeGridCount
    push_cast
    linarith [Real.exp_pos a]
  have hp := interval_grid_width (wholePrimeGridCount_pos b)
    (Real.exp_le_exp.mpr hab) hwidth
  ext p
  rw [mem_gridPrimeSupport_iff_prime N q (Real.exp a) h hp.1 hq,
    mem_primeLogCellSet_iff]
  rw [show Real.exp a + N * h = Real.exp b from hp.2.2]
  simp only [Nat.modEq_one, true_and]

/-- The coarse partition is enough because the sharp real kernel is
integrated exactly on each cell. Its count is far below the cell budget. -/
theorem wholePrimeGridCount_eventual (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℝ, b ≤ K * L →
      (wholePrimeGridCount b : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_exponent_absorption 0 (14 / 10000) 0 (K + 3) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro b hb
  have hL0 : 0 ≤ L := by linarith
  have hCL0 : 0 ≤ K * L := mul_nonneg hK hL0
  have hscale : K * L + 3 ≤ Real.exp ((14 / 10000 : ℝ) * L) := by
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
    nlinarith
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hunit : 1 ≤ Real.exp (K * L + 1) := Real.one_le_exp_iff.mpr (by linarith)
  calc
    _ ≤ Real.exp (b + 1) + 2 := wholePrimeGridCount_upper b
    _ ≤ Real.exp (K * L + 1) + 2 := by
      have he : Real.exp (b + 1) ≤ Real.exp (K * L + 1) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ 3 * Real.exp (K * L + 1) := by linarith
    _ ≤ Real.exp 2 * Real.exp (K * L + 1) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = Real.exp (K * L + 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hscale

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WholeShellGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact interval geometry for the full original bulk prime shell -/

namespace Ostmann
open scoped Classical

theorem whole_shell_geometry (a b : ℝ) (hab : a ≤ b) :
    (∀ c, Real.exp a ≤ wholeShellLower a b c) ∧
    (∀ c, wholeShellLower a b c ≤ wholeShellUpper a b c) ∧
    (∀ c, wholeShellUpper a b c ≤ wholeShellLower a b c + 1) ∧
    (∀ c d, c ≠ d → wholeShellUpper a b c ≤ wholeShellLower a b d ∨
      wholeShellUpper a b d ≤ wholeShellLower a b c) := by
  have hwidth : Real.exp b - Real.exp a ≤ (wholePrimeGridCount b : ℝ) := by
    have hc := Nat.le_ceil (Real.exp (b + 1))
    have he : Real.exp b ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr (by linarith)
    unfold wholePrimeGridCount
    push_cast
    linarith [Real.exp_pos a]
  have hh := interval_grid_width (wholePrimeGridCount_pos b)
    (Real.exp_le_exp.mpr hab) hwidth
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only [wholeShellLower]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hh.1)
  · intro c
    dsimp only [wholeShellLower, wholeShellUpper]
    nlinarith [hh.1]
  · intro c
    dsimp only [wholeShellLower, wholeShellUpper]
    nlinarith [hh.2.1]
  · intro c d hcd
    rcases lt_or_gt_of_ne hcd with hlt | hgt
    · left
      have h : (c : ℝ) + 1 ≤ d := by
        exact_mod_cast (show c.val + 1 ≤ d.val from hlt)
      dsimp only [wholeShellLower, wholeShellUpper]
      nlinarith [hh.1]
    · right
      have h : (d : ℝ) + 1 ≤ c := by
        exact_mod_cast (show d.val + 1 ≤ c.val from hgt)
      dsimp only [wholeShellLower, wholeShellUpper]
      nlinarith [hh.1]

theorem whole_shell_support (q : ℕ) [NeZero q] (a b : ℝ) (hab : a ≤ b)
    (hq : (q : ℝ) ≤ Real.exp (Real.exp a)) :
    primeCellSupport q (fun c : Fin (wholePrimeGridCount b) × (ZMod q)ˣ => c.2.val.val)
      (fun c => wholeShellLower a b c.1) (fun c => wholeShellUpper a b c.1) =
      primeLogCellSet 1 0 (Real.exp a) (Real.exp b) := by
  exact whole_interval_prime_grid_support q a b hab hq

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WholeShellMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed positive mass in the original whole bulk shell

This uses only the stated bounded-error Mertens estimate. A single ordinary
logarithmic band inside the shell suffices for the bulk normalization.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem whole_shell_mass_lower {C : ℝ} (hM : MertensEstimate C)
    (u v : ℝ) (hu : 1 ≤ u) (herror : 2 * (Real.log 2 + 2 * C) ≤ u)
    (huv : 2 * u ≤ v) :
    (1 / 4 : ℝ) ≤ ∑ p ∈ primeLogCellSet 1 0 u v, (p : ℝ)⁻¹ := by
  have hband := (logPrimeBand_weight_bounds u C hu hM).1
  have hsub : logPrimeBand u ⊆ primeLogCellSet 1 0 u v := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := logPrimeBand_mem hp
    exact mem_primeLogCellSet_iff.mpr ⟨hprime, by simp only [Nat.modEq_one],
      hlo, hhi.trans huv⟩
  have hweight : (∑ p ∈ logPrimeBand u, Real.log (p : ℝ) / p) ≤
      (2 * u) * ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hhi := (logPrimeBand_mem hp).2.2
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hhi (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hmass : (1 / 4 : ℝ) ≤ ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    nlinarith
  exact hmass.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WholeShellArithmeticCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical and measure data of the full bulk-shell partition -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem whole_shell_arithmetic_cells (C Cmass : ℝ) (hM : MertensEstimate C)
    (hCmass : 1 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) [NeZero M], M ≤ bulkProgressionCutoff L →
      let a := (4 / 1000 : ℝ) * L
      let b := (6 / 1000 : ℝ) * L
      (Fintype.card (Fin (wholePrimeGridCount b)) : ℝ) ≤
        Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) ∧
      (∀ c, 1 ≤ wholeShellLower a b c) ∧
      (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ wholeShellLower a b c) ∧
      (∀ c, wholeShellLower a b c ≤ wholeShellUpper a b c) ∧
      (∀ c, wholeShellUpper a b c ≤ wholeShellLower a b c + 1) ∧
      (∀ c d, c ≠ d → wholeShellUpper a b c ≤ wholeShellLower a b d ∨
        wholeShellUpper a b d ≤ wholeShellLower a b c) ∧
      (∀ c, (M : ℝ) ≤ Real.exp (wholeShellLower a b c)) ∧
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => wholeShellLower a b c.1) (fun c => wholeShellUpper a b c.1) =
        primeLogCellSet 1 0 (Real.exp a) (Real.exp b) ∧
      Real.exp (-Cmass * L) ≤ ∑ q ∈ primeLogCellSet 1 0 (Real.exp a) (Real.exp b), (q : ℝ)⁻¹ := by
  have hlarge := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [wholePrimeGridCount_eventual (6 / 1000) (by norm_num), hlarge,
    eventually_ge_atTop (max 0 (max (Real.log 4) (500 * Real.log 2)))]
    with L hgrid hlarge hL
  intro M _ hMQ
  dsimp only
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hL4 : Real.log 4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 500 * Real.log 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hab : a ≤ b := by dsimp only [a, b]; linarith only [hL0]
  have hgeometry := whole_shell_geometry a b hab
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) hL0
  have hMbase : (M : ℝ) ≤ Real.exp (Real.exp a) :=
    modulus_le_exp_bulk_endpoint hMQ hL0
      (Real.exp_le_exp.mpr (by dsimp only [a]; linarith only [hL0]))
  refine ⟨?_, ?_, ?_, hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2, ?_,
    whole_shell_support M a b hab hMbase, ?_⟩
  · simpa only [Fintype.card_fin] using hgrid b (le_refl _)
  · intro c
    exact (Real.one_le_exp_iff.mpr ha0).trans (hgeometry.1 c)
  · intro c
    exact (Real.exp_le_exp.mpr (by dsimp only [a]; linarith only [hL0])).trans (hgeometry.1 c)
  · intro c
    exact hMbase.trans (Real.exp_le_exp.mpr (hgeometry.1 c))
  · have htwo : 2 * Real.exp a ≤ Real.exp b := by
      have he : Real.log 2 + a ≤ b := by dsimp only [a, b]; linarith only [hL2]
      have hh := Real.exp_le_exp.mpr he
      simpa only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
    have he : Real.exp (-Cmass * L) ≤ (1 / 4 : ℝ) := by
      have hprod := mul_le_mul_of_nonneg_right hCmass hL0
      calc
        _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by nlinarith only [hprod, hL4])
        _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
    exact he.trans (whole_shell_mass_lower hM (Real.exp a) (Real.exp b)
      (Real.one_le_exp_iff.mpr ha0) hlarge htwo)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenPrimeDeletions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite primes excluded after freezing the nonbulk coordinates -/

namespace Ostmann
open scoped Classical

theorem mem_frozenPrimeDeletions_base {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) (i : σ) (hi : i ∉ Set.range slot) :
    base i ∈ frozenPrimeDeletions base slot outside := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

theorem mem_frozenPrimeDeletions_outside {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) (q : ℕ) (hq : q ∈ outside) :
    q ∈ frozenPrimeDeletions base slot outside :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr hq)

theorem frozenPrimeDeletions_card_le {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) :
    (frozenPrimeDeletions base slot outside).card ≤ Fintype.card σ + outside.length := by
  have h₁ := Finset.card_image_le (s := Finset.univ)
    (f := fun i : {i : σ // i ∉ Set.range slot} => base i)
  have h₂ := Fintype.card_subtype_le (fun i : σ => i ∉ Set.range slot)
  have h₃ := List.toFinset_card_le outside
  have h₄ := Finset.card_union_le
    (Finset.univ.image (fun i : {i : σ // i ∉ Set.range slot} => base i)) outside.toFinset
  simp only [Finset.card_univ] at h₁
  exact h₄.trans (Nat.add_le_add (h₁.trans h₂) h₃)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalMaskedShell
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed diagonal bound with the restored compensation mask -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate_oai
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (Eprior αall βint Vint Uall : ℝ)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e n m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Eprior ≤ Real.exp (Cmass * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e n m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          (Real.exp (Cmass * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
              Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
                2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [P.movingPattern_original_diagonal_sharp ψ n r₀ k
    A Wwin Bφ Dφ Cmass Cmass hA hWwin hCmass hBφ hDφ hCmass,
    whole_shell_arithmetic_cells C Cmass hM hCmass] with L hrate hcells
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound f outside _ p _ hc _ Dq sets
    primeLo cutoff tier X j₀ φ G global μ ν active Eprior αall βint Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp
    hsets hsetsp hpupper hMQ hφ hlip hφout hShell hdel hout hν
    hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hactive houtcover hinjp huBig hrBig
    hNfreq hEup hαup hβup hVeq hUlog _hUup hμtier hνtier hNlo hNcut hcutlo hμlo hνlo
    hupper hpband hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  let m := spectatorBulkCount k L
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  let u := fun (_ : TreeLeafIndex n × Fin m) => wholeShellLower a b
  let v := fun (_ : TreeLeafIndex n × Fin m) => wholeShellUpper a b
  let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
  let S := primeLogCellSet 1 0 (Real.exp a) (Real.exp b)
  let deleted := fun x : Fin (N + 1) → primes => global ∪
    frozenPrimeDeletions (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside
  obtain ⟨hcard, hunit, hlow, huv, hshort, hsep, hMcell, hsupport, hmass⟩ :=
    hcells M hMQ
  have hDcard (x) : ((deleted x).card : ℝ) ≤ Real.exp (Cmass * L) := by
    have hh : (deleted x).card ≤ global.card + (N + 1) + outside.length := by
      have ht := (Finset.card_union_le global _).trans
        (Nat.add_le_add_left (frozenPrimeDeletions_card_le
          (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside) global.card)
      simpa only [Fintype.card_fin, Nat.add_assoc] using ht
    exact (Nat.cast_le.mpr hh).trans hdel
  have hsub (j) : S \ global ⊆ primeCellSupport M
      (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) := by
    rw [hsupport]; exact Finset.sdiff_subset
  have hretain (x) (j) :
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) \ deleted x ⊆ S \ global := by
    rw [hsupport]
    intro q hq
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1,
      fun hg => (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_left _ hg)⟩
  have hmem (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ∈ Sfreq := by
    rw [ht] at hs
    exact allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n b ft) s hs
  have hfreq (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ≠ 0 :=
    hS s (hmem b s hs)
  have hV (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) :
      |(s : ℝ)| ≤ Real.exp (A * m) := by
    have hn : (s.natAbs : ℝ) ≤ Nfreq := by exact_mod_cast hN s (hmem b s hs)
    exact (show |(s : ℝ)| ≤ Nfreq by simpa only [Nat.cast_natAbs, Int.cast_abs] using hn).trans hNfreq
  exact hrate lo hi hlo hhi hwindow Bidx Cidx (Fin (wholePrimeGridCount b)) N e tierB tierC
    t Sfreq ft Nfreq Vleaf D small slot pattern rep primes hprimes childBound pivotBound hfreq f
    outside p hc Dq sets X j₀ φ G u v (fun x _ => deleted x) (fun _ => S \ global)
    μ ν active sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (hsmall false) hB htier (hsmallLen false)
    ht hS hN (fun s => hleaf false s []) hD hdiv hm hp hV
    hsets hsetsp hpupper hMQ hφ hlip hφout hcard (fun _ => hunit) (fun _ => hlow)
    (fun _ => huv) (fun _ => hshort) (fun _ => hsep) (fun _ => hMcell)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hShell) (fun x _ _ => hDcard x)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hmass)
    (fun x _ _ i hi => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_base (fun i => (x i : ℕ)) _ outside i hi)) hout
    (fun x _ _ q hq => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_outside (fun i => (x i : ℕ)) _ outside q hq))
    (⟨0, wholePrimeGridCount_pos b⟩, 1) hsub (fun x _ => hretain x) hν
    hμ0 hν0 hμmass hνmass (le_trans (by norm_num) hEprior) hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hactive
    hinjp houtcover hNfreq huBig hrBig tier primeLo cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hpband hdeleteμ hdeletep hdeleteν
    hsreg hsregN hsetsReg hEup hUlog hαup hβup hVeq

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate_oai := @OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate_oai
