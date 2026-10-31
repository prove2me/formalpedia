-- Prove2me | solution 1 for OAI.Ostmann.eventual_large_kernel_prime_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:38.562049+00:00
-- url     : https://prove2.me/submissions/b17aff05-14a0-41fc-83c3-5383204264ff

import Mathlib
import Definitions.Def_OAIQ095D007

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
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RealQuadraticPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem realAdditivePhase_add (x y : ℝ) :
    realAdditivePhase (x + y) = realAdditivePhase x * realAdditivePhase y := by
  unfold realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realAdditivePhase_sub (x y : ℝ) :
    realAdditivePhase (x - y) = realAdditivePhase x * conj (realAdditivePhase y) := by
  rw [sub_eq_add_neg, realAdditivePhase_add, conj_realAdditivePhase]

end Ostmann

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
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PhaseDistance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance to the nearest integer controls a linear phase sum -/

namespace Ostmann

open scoped BigOperators

theorem realAdditivePhase_sub_int (x : ℝ) (k : ℤ) :
    realAdditivePhase (x - k) = realAdditivePhase x := by
  rw [realAdditivePhase_sub, realAdditivePhase_intCast]
  simp

theorem norm_realAdditivePhase_sub_one (x : ℝ) :
    ‖realAdditivePhase x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  unfold realAdditivePhase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem round_distance_le_phase_norm (x : ℝ) :
    4 * |x - (round x : ℤ)| ≤ ‖realAdditivePhase x - 1‖ := by
  rw [← realAdditivePhase_sub_int x (round x), norm_realAdditivePhase_sub_one]
  have hx := abs_sub_round x
  have hpi := Real.pi_pos
  have harg : |Real.pi * (x - (round x : ℤ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos hpi] at hsin
  have heq : 2 / Real.pi * (Real.pi * |x - (round x : ℤ)|) =
      2 * |x - (round x : ℤ)| := by field_simp
  rw [heq] at hsin
  linarith

/-- The multiplicative form remains valid at integral phases, so no division
by zero or exceptional phase needs to enter the packing argument. -/
theorem linear_phase_sum_distance_bound (x : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ N ∧
      2 * |x - (round x : ℤ)| *
        ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ 1 := by
  have hz := norm_realAdditivePhase x
  constructor
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ‖realAdditivePhase x ^ j‖ := norm_sum_le _ _
      _ = N := by simp [hz]
  · have hgeom := geom_sum_mul (realAdditivePhase x) N
    have heq : ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ *
        ‖realAdditivePhase x - 1‖ = ‖realAdditivePhase x ^ N - 1‖ := by
      rw [← Complex.norm_mul, hgeom]
    have hb : ‖realAdditivePhase x ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖realAdditivePhase x ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [hz]
    have hm := mul_le_mul_of_nonneg_right (round_distance_le_phase_norm x)
      (norm_nonneg (∑ j ∈ Finset.range N, realAdditivePhase x ^ j))
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedPhasePacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite reciprocal-distance bound for separated centered phases -/

namespace Ostmann

open scoped BigOperators Classical

private theorem same_sign_abs_difference (x y : ℝ)
    (hs : decide (x < 0) = decide (y < 0)) :
    |(|x| - |y|)| = |x - y| := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · rw [abs_of_neg hx, abs_of_neg hy]
    have heq : -x - -y = -(x - y) := by ring
    rw [heq, abs_neg]
  · simp [hx, hy] at hs
  · simp [hx, hy] at hs
  · rw [abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]

theorem centeredPhaseBin_injective {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (r : ℕ) (hr : 0 < r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|) :
    Set.InjOn (fun i => centeredPhaseBin r (f i)) S := by
  intro i hi j hj heq
  by_contra hij
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs := congrArg Prod.fst heq
  have hb := congrArg Prod.snd heq
  have hfi : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
    Nat.floor_le (by positivity)
  have hfj : (⌊2 * (r : ℝ) * |f j|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f j| :=
    Nat.floor_le (by positivity)
  have hfi' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f i|)
  have hfj' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f j|)
  change ⌊2 * (r : ℝ) * |f i|⌋₊ = ⌊2 * (r : ℝ) * |f j|⌋₊ at hb
  rw [hb] at hfi hfi'
  have hclose : |(2 * (r : ℝ) * |f i|) - (2 * (r : ℝ) * |f j|)| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_pos (show 0 < 2 * (r : ℝ) by positivity),
    same_sign_abs_difference (f i) (f j) hs] at hclose
  have hfar := (div_le_iff₀ (show 0 < 2 * (r : ℝ) by positivity)).mp (hsep i hi j hj hij)
  nlinarith

/-- Each signed distance bin contains at most one point. The zero bin costs
N; all other bins cost r/k. This is the finite harmonic estimate needed for
one rational-approximation block. -/
theorem separated_phase_weight_sum {ι : Type*} (S : Finset ι) (f w : ι → ℝ)
    (r : ℕ) (N : ℝ) (hr : 0 < r) (hN : 0 ≤ N)
    (hsize : ∀ i ∈ S, |f i| ≤ 1 / 2)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hupper : ∀ i ∈ S, w i ≤ N)
    (hdist : ∀ i ∈ S, 2 * |f i| * w i ≤ 1) :
    ∑ i ∈ S, w i ≤
      2 * ∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k := by
  let bin := fun i => centeredPhaseBin r (f i)
  let B := fun k : ℕ => if k = 0 then N else (r : ℝ) / k
  have hB : ∀ k, 0 ≤ B k := by
    intro k
    dsimp [B]
    split_ifs <;> positivity
  have hinj : Set.InjOn bin S := centeredPhaseBin_injective S f r hr hsep
  have hmem : ∀ i ∈ S, bin i ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)) := by
    intro i hi
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
    have hfloor : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
      Nat.floor_le (by positivity)
    have hb : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ r := by
      have hh := hsize i hi
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    have hk : ⌊2 * (r : ℝ) * |f i|⌋₊ ≤ r := by exact_mod_cast hb
    exact Nat.lt_succ_of_le hk
  have hpoint : ∀ i ∈ S, w i ≤ B (bin i).2 := by
    intro i hi
    let k := (bin i).2
    change w i ≤ if k = 0 then N else (r : ℝ) / k
    by_cases hk : k = 0
    · simpa only [hk, ite_true, if_true] using hupper i hi
    · rw [ite_eq_right hk]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      apply (le_div_iff₀ hkpos).mpr
      have hfloor : (k : ℝ) ≤ 2 * (r : ℝ) * |f i| := Nat.floor_le (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hfloor (hw i hi)
      have hbound := mul_le_mul_of_nonneg_left (hdist i hi) (Nat.cast_nonneg r)
      nlinarith
  calc
    _ ≤ ∑ i ∈ S, B (bin i).2 := Finset.sum_le_sum hpoint
    _ = ∑ b ∈ S.image bin, B b.2 := (Finset.sum_image (f := fun b : Bool × ℕ => B b.2) hinj).symm
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)), B b.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact hmem i hi
      · intro b _ _
        exact hB b.2
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]; simp [B, two_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalPhaseBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic bound for one short rational phase block -/

namespace Ostmann

open scoped BigOperators Classical

theorem phase_bin_sum_eq (r : ℕ) (N : ℝ) :
    (∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k) =
      N + r * (harmonic r : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, if_false, ite_true, if_true,
    Nat.cast_add, Nat.cast_one]
  rw [harmonic, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  simp only [div_eq_mul_inv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformPhaseGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform harmonic control of an arbitrarily translated frequency grid -/

namespace Ostmann

open scoped BigOperators

private theorem centered_grid_separation (q : ℕ) [NeZero q] (α : ℝ)
    (i j : Fin q) (hij : i ≠ j) :
    1 / (2 * (q : ℝ)) ≤
      |(α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)) -
        (α + (j.val : ℝ) / q - (round (α + (j.val : ℝ) / q) : ℤ))| := by
  let z : ℤ := (i.val : ℤ) - j.val -
    (q : ℤ) * (round (α + (i.val : ℝ) / q) - round (α + (j.val : ℝ) / q))
  have hz : z ≠ 0 := by
    intro hz
    have he := congrArg (fun t : ℤ => (t : ZMod q)) hz
    simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, sub_zero, Int.cast_zero] at he
    have he' := congrArg ZMod.val (sub_eq_zero.mp he)
    apply hij
    apply Fin.ext
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using he'
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq : (z : ℝ) = (q : ℝ) *
      ((α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)) -
        (α + (j.val : ℝ) / q - (round (α + (j.val : ℝ) / q) : ℤ))) := by
    dsimp [z]
    push_cast
    field_simp [hq.ne']
    ring
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hp : (0 : ℤ) < |z| := abs_pos.mpr hz
    have hh : (1 : ℤ) ≤ |z| := by omega
    exact_mod_cast hh
  rw [heq, abs_mul, abs_of_pos hq] at habs
  apply (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mpr
  nlinarith

/-- No Diophantine approximation of the offset `α` is required. A closest
frequency costs `N`; all remaining frequencies cost the harmonic sum. -/
theorem uniform_phase_grid_bound (q : ℕ) [NeZero q] (α : ℝ) (N : ℕ) :
    (∑ i : Fin q, ‖∑ n ∈ Finset.range N,
      realAdditivePhase (α + (i.val : ℝ) / q) ^ n‖) ≤
      2 * ((N : ℝ) + q * (1 + Real.log q)) := by
  classical
  let f : Fin q → ℝ := fun i => α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)
  let w : Fin q → ℝ := fun i => ‖∑ n ∈ Finset.range N,
    realAdditivePhase (α + (i.val : ℝ) / q) ^ n‖
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb := separated_phase_weight_sum Finset.univ f w q N hq (Nat.cast_nonneg N)
    (fun i _ => abs_sub_round _) (fun i _ j _ hij => centered_grid_separation q α i j hij)
    (fun i _ => norm_nonneg _)
    (fun i _ => (linear_phase_sum_distance_bound (α + (i.val : ℝ) / q) N).1)
    (fun i _ => (linear_phase_sum_distance_bound (α + (i.val : ℝ) / q) N).2)
  rw [phase_bin_sum_eq] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Nat.cast_nonneg q)
    dsimp [w] at hb ⊢
    linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PeriodicLinearPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform linear-phase sums of a periodic function from Fourier coefficient bounds -/

namespace Ostmann

open scoped BigOperators

theorem stdAddChar_eq_realPhase {q : ℕ} [NeZero q] (u : ZMod q) :
    ZMod.stdAddChar u = realAdditivePhase ((u.val : ℝ) / q) := by
  calc
    _ = ZMod.stdAddChar ((u.val : ℕ) : ZMod q) := by rw [ZMod.natCast_zmod_val]
    _ = Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / q) := by
      rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
      push_cast
      rfl
    _ = _ := by
      unfold realAdditivePhase
      congr 1
      push_cast
      ring

theorem stdAddChar_mul_natCast {q : ℕ} [NeZero q] (u : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (u * (n : ZMod q)) = ZMod.stdAddChar u ^ n := by
  induction n with
  | zero => simp [AddChar.map_zero_eq_one]
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one,
      AddChar.map_add_eq_mul, ih, pow_succ]

theorem periodic_linear_phase_expansion (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (α : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q) * realAdditivePhase α ^ n) =
      ∑ u : ZMod q, additiveFourier f u *
        ∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n := by
  simp_rw [additiveFourier_inversion f, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [stdAddChar_mul_natCast, stdAddChar_eq_realPhase, realAdditivePhase_add, mul_pow]
  ring

theorem periodic_linear_phase_sum_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f (n : ZMod q) * realAdditivePhase α ^ n‖ ≤
      2 * A * ((N : ℝ) + q * (1 + Real.log q)) := by
  rw [periodic_linear_phase_expansion]
  have hgrid : (∑ u : ZMod q, ‖∑ n ∈ Finset.range N,
      realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖) ≤
        2 * ((N : ℝ) + q * (1 + Real.log q)) := by
    have he := (ZMod.finEquiv q).toEquiv.sum_comp (fun u =>
      ‖∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖)
    have heq (i : Fin q) : ((ZMod.finEquiv q).toEquiv i).val = i.val := by
      cases q with
      | zero => exact Fin.elim0 i
      | succ q => rfl
    simp_rw [heq] at he
    exact he.symm.trans_le (uniform_phase_grid_bound q α N)
  calc
    _ ≤ ∑ u : ZMod q, ‖additiveFourier f u *
        ∑ n ∈ Finset.range N, realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ u : ZMod q, A * ‖∑ n ∈ Finset.range N,
        realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf u) (norm_nonneg _)
    _ = A * (∑ u : ZMod q, ‖∑ n ∈ Finset.range N,
        realAdditivePhase (α + (u.val : ℝ) / q) ^ n‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 * ((N : ℝ) + q * (1 + Real.log q))) :=
      mul_le_mul_of_nonneg_left hgrid hA
    _ = _ := by ring

theorem weighted_periodic_linear_phase_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n * (f (n : ZMod q) * realAdditivePhase α ^ n)‖ ≤
      discreteVariation w N * (2 * A * ((N : ℝ) + q * (1 + Real.log q))) := by
  apply weighted_sum_le_variation
  intro n hn
  apply (periodic_linear_phase_sum_bound q f A α hA hf n).trans
  have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
  exact mul_le_mul_of_nonneg_left (add_le_add_left hnn _) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Autocorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive autocorrelation

The probability-normalized Fourier transform of an autocorrelation is
the squared modulus of the original transform. This is the positivity
identity used for the bottom-pair coefficients in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_translation_sum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (a y : ZMod p) :
    (∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a))) =
      ZMod.stdAddChar (-(y * a)) * ∑ z : ZMod p, g z * ZMod.stdAddChar (-(z * a)) := by
  calc
    _ = ∑ z : ZMod p, g ((z + y) - y) * ZMod.stdAddChar (-((z + y) * a)) :=
      ((Equiv.addRight y).bijective.sum_comp
        (fun x : ZMod p => g (x - y) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by
      simp only [add_sub_cancel_right, add_mul, neg_add, AddChar.map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

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

theorem additiveFourier_add_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (b a : ZMod p) :
    additiveFourier (fun x => f (x + b)) a =
      ZMod.stdAddChar (b * a) * additiveFourier f a := by
  have h := additiveFourier_translation_sum f a (-b)
  simp only [sub_neg_eq_add, neg_mul, neg_neg] at h
  simp only [additiveFourier_apply]
  rw [h]
  ring

theorem additiveFourier_unit_mul {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (a : ZMod p) :
    additiveFourier (fun x => f ((u : ZMod p) * x)) a =
      additiveFourier f (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a) := by
  exact congrArg (fun z : ℂ => (p : ℂ)⁻¹ * z) (ZMod.dft_comp_unitMul f u a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalDistribution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interval distribution for the external integer giant -/

namespace Ostmann

open scoped Classical
open MeasureTheory

theorem integer_interval_residue_error (lo hi q a : ℕ) (hlo : lo ≤ hi) (hq : 0 < q) :
    |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ((hi : ℝ) - lo) / q| ≤ 1 := by
  let A : ℚ := ((lo : ℚ) - a) / q
  let B : ℚ := ((hi : ℚ) - a) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (by exact_mod_cast hlo : (lo : ℚ) ≤ hi) a) hq'.le
  have hf := Int.floor_mono hAB
  have hcard := Nat.Ioc_filter_modEq_card lo hi hq a
  have hcast : (((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) =
      ((⌊B⌋ : ℤ) : ℚ) - ((⌊A⌋ : ℤ) : ℚ) := by
    rw [max_eq_left (sub_nonneg.mpr hf)] at hcard
    exact_mod_cast hcard
  have hA := Int.floor_le A
  have hA' := Int.lt_floor_add_one A
  have hB := Int.floor_le B
  have hB' := Int.lt_floor_add_one B
  have hrat : |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| ≤ 1 := by
    rw [hcast]
    have hid : ((hi : ℚ) - lo) / q = B - A := by dsimp [A, B]; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hr : ((|(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem densityFourier_energy_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) ≤ q := by
  rw [densityFourier_energy]
  calc
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

theorem densityCRTList_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (densityCRTList ps hp hc S).value (n : ZMod ps.prod) =
      (ps.map fun p => (centeredDensity (S p) (n : ZMod p) : ℂ)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : Fact p.Prime := ⟨hp p List.mem_cons_self⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change (centeredDensity (S p)
      ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).1 : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change (centeredDensity (S p) (n : ZMod p) : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

/-- The hypotheses of the small-kernel bound hold for the original finite
product of centered density functions. -/
theorem densityCRTList_energy (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ a : ZMod ps.prod, ‖densityFourier (densityCRTList ps hp hc S).value a‖ ^ 2) ≤ ps.prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  exact densityFourier_energy_le _ (densityCRTList ps hp hc S).norm_le_one

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

/-- A prime occurring in exactly one of the divisors costs `q^(-1/2)`. -/
theorem densityFourier_coefficient_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (a : ZMod q) :
    ‖additiveFourier (densityFourier f) a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  change ‖additiveFourier (fun x => (Real.sqrt (q : ℝ) : ℂ) * additiveFourier f x) a‖ ≤ _
  rw [additiveFourier_const_mul, additiveFourier_twice, norm_mul, norm_mul, norm_inv,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc
    _ ≤ Real.sqrt (q : ℝ) * ((q : ℝ)⁻¹ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf (-a)) (by positivity)) hs.le
    _ = _ := by field_simp; nlinarith

/-- Unit dilations preserve the local coefficient bound. -/
theorem densityFourier_unit_coefficient_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (a : (ZMod q)ˣ) (u : ZMod q) :
    ‖additiveFourier (fun x => densityFourier f ((a : ZMod q) * x)) u‖ ≤ (Real.sqrt (q : ℝ))⁻¹ := by
  rw [additiveFourier_unit_mul]
  exact densityFourier_coefficient_le f hf _

/-- At a common prime, the product costs only one, by Cauchy--Schwarz. -/
theorem additiveFourier_cross_le_one {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : (∑ x, ‖f x‖ ^ 2) ≤ q)
    (hg : (∑ x, ‖g x‖ ^ 2) ≤ q) (u : ZMod q) :
    ‖additiveFourier (fun x => f x * conj (g x)) u‖ ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hS : 0 ≤ ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun x => ‖g x‖)
  have he : (∑ x : ZMod q, ‖f x‖ * ‖g x‖) ≤ q := by
    have hb := mul_le_mul hf hg (by positivity : 0 ≤ ∑ x : ZMod q, ‖g x‖ ^ 2) hq.le
    nlinarith
  rw [additiveFourier_apply, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro x hx
      simp only [norm_mul, Complex.norm_conj]
      have hn : ‖ZMod.stdAddChar (-(x * u))‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
      rw [hn, mul_one]
    _ ≤ (q : ℝ)⁻¹ * q := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hq.le)
    _ = 1 := inv_mul_cancel₀ hq.ne'

/-- Conjugation reverses the Fourier frequency. -/
theorem additiveFourier_conj_density {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_sum, map_inv₀, map_natCast,
    stdAddChar_conj, mul_neg, neg_neg]

/-- Unit dilations preserve the counting-measure energy. -/
theorem unit_dilation_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖f ((a : ZMod q) * x)‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 :=
  (Units.mulLeft a).bijective.sum_comp (fun x : ZMod q => ‖f x‖ ^ 2)

/-- The common-prime factor of the original density correlation. -/
theorem densityFourier_unit_cross_le_one {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (a b : (ZMod q)ˣ) (u : ZMod q) :
    ‖additiveFourier (fun x => densityFourier f ((a : ZMod q) * x) *
      conj (densityFourier g ((b : ZMod q) * x))) u‖ ≤ 1 := by
  apply additiveFourier_cross_le_one
  · rw [unit_dilation_energy]
    exact densityFourier_energy_le f hf
  · rw [unit_dilation_energy]
    exact densityFourier_energy_le g hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeCRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the local correlation bounds over the prime factors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primeCRTFunction_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) (n : ℤ) :
    primeCRTFunction ps hp hc F (n : ZMod ps.prod) = (ps.map fun p => F p (n : ZMod p)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    change F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
      (n : ZMod (p * ps.prod))).1 * primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
          (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change F p (n : ZMod p) * primeCRTFunction ps hp' hcp.2 F (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

/-- Probability-normalized Fourier coefficients multiply under CRT. -/
theorem primeCRTFunction_coefficient_le (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) (A : ℕ → ℝ)
    (hA : ∀ p ∈ ps, 0 ≤ A p)
    (hF : ∀ p (h : p ∈ ps), ∀ u : ZMod p, ‖@additiveFourier p ⟨(hp p h).ne_zero⟩ (F p) u‖ ≤ A p) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∀ u, ‖additiveFourier (primeCRTFunction ps hp hc F) u‖ ≤ (ps.map A).prod := by
  induction ps with
  | nil =>
    intro _ u
    change ZMod 1 at u
    change ‖additiveFourier (fun _ : ZMod 1 => (1 : ℂ)) u‖ ≤ 1
    simp [additiveFourier_apply]
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    intro _ u
    change ZMod (p * ps.prod) at u
    change ‖additiveFourier (fun x : ZMod (p * ps.prod) =>
      F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2) u‖ ≤ _
    rw [additiveFourier_crt (m := p) (n := ps.prod), norm_mul]
    exact mul_le_mul (hF p List.mem_cons_self _)
      (ih hp' hcp.2 (fun q hq => hA q (List.mem_cons_of_mem p hq))
        (fun q hq => hF q (List.mem_cons_of_mem p hq)) _)
      (norm_nonneg _) (hA p List.mem_cons_self)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-by-prime correlation bound for centered densities -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primeDensityFourier_eq {p : ℕ} [NeZero p] (f : ∀ p : ℕ, ZMod p → ℂ) :
    primeDensityFourier f p = densityFourier (f p) := by
  simp only [primeDensityFourier, dite_eq_left (Nat.pos_of_ne_zero (NeZero.ne p))]

theorem correlationPrimeBound_nonneg (side : ℕ → CorrelationSide) (p : ℕ) :
    0 ≤ correlationPrimeBound side p := by
  unfold correlationPrimeBound
  split <;> positivity

theorem correlationPrimeFactor_coefficient_le {p : ℕ} [NeZero p]
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) (u : ZMod p) :
    ‖additiveFourier (correlationPrimeFactor f side a b p) u‖ ≤
      correlationPrimeBound side p := by
  unfold correlationPrimeFactor correlationPrimeBound
  cases side p with
  | left =>
    simp only [primeDensityFourier_eq]
    exact densityFourier_unit_coefficient_le (f p) hf (a p) u
  | right =>
    simp only [primeDensityFourier_eq, additiveFourier_conj_density, Complex.norm_conj]
    exact densityFourier_unit_coefficient_le (f p) hf (b p) (-u)
  | both =>
    simp only [primeDensityFourier_eq]
    exact densityFourier_unit_cross_le_one (f p) (f p) hf hf (a p) (b p) u

/-- This proves the local-product form of the manuscript's `A_{d,d'}`,
with no analytic hypothesis on the density beyond its pointwise bound. -/
theorem density_correlation_coefficient_bound (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ ps, ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∀ u, ‖additiveFourier (primeCRTFunction ps hp hc (correlationPrimeFactor f side a b)) u‖ ≤
      (ps.map (correlationPrimeBound side)).prod := by
  apply primeCRTFunction_coefficient_le
  · intro p _
    exact correlationPrimeBound_nonneg side p
  · intro p h u
    let : NeZero p := ⟨(hp p h).ne_zero⟩
    exact correlationPrimeFactor_coefficient_le f (hf p h) side a b u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the original density transform with its local prime factors -/

namespace Ostmann

open scoped BigOperators

private theorem intCast_isUnit_of_dvd {d q : ℕ} (hd : d ∣ q) (j : ℤ)
    (hj : IsUnit (j : ZMod q)) : IsUnit (j : ZMod d) := by
  simpa only [map_intCast] using hj.map (ZMod.castHom hd (ZMod d))

/-- The multipliers produced by CRT are genuine units; they may be absorbed
in the local arguments without imposing a new hypothesis on the density. -/
theorem densityFourier_primeCRTFunction (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (primeCRTFunction ps hp hc f) (n : ZMod ps.prod) =
        (ps.map fun p => primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))).prod := by
  classical
  induction ps with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    intro n
    change densityFourier (fun _ : ZMod 1 => (1 : ℂ)) (n : ZMod 1) = 1
    simp only [densityFourier, additiveFourier_apply, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, inv_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
    exact (congrArg ZMod.stdAddChar (Subsingleton.elim _ (0 : ZMod 1))).trans
      (AddChar.map_zero_eq_one _)
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    obtain ⟨b, hb⟩ := ih hp' hcp.2
    have hv : IsUnit (ps.prod : ZMod p) :=
      (ZMod.isUnit_iff_coprime ps.prod p).mpr
        (Nat.coprime_list_prod_right_iff.mpr hcp.1).symm
    let v : (ZMod p)ˣ := hv.unit⁻¹
    have hvval : (v : ZMod p) = (ps.prod : ZMod p)⁻¹ := by
      change (hv.unit⁻¹ : (ZMod p)ˣ).val = _
      rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]
    have hu : IsUnit (p : ZMod ps.prod) :=
      (ZMod.isUnit_iff_coprime p ps.prod).mpr (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    let u : (ZMod ps.prod)ˣ := hu.unit⁻¹
    have huval : (u : ZMod ps.prod) = (p : ZMod ps.prod)⁻¹ := by
      change (hu.unit⁻¹ : (ZMod ps.prod)ˣ).val = _
      rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (u : ZMod ps.prod)
    have hjunit : IsUnit (j : ZMod ps.prod) := hj ▸ u.isUnit
    let c : ∀ q : ℕ, (ZMod q)ˣ := fun q =>
      if hq : q ∈ ps then (intCast_isUnit_of_dvd (List.dvd_prod hq) j hjunit).unit else 1
    have hcval (q : ℕ) (hq : q ∈ ps) : (c q : ZMod q) = (j : ZMod q) := by
      simp only [c, dite_eq_left hq, IsUnit.unit_spec]
    have hne (q : ℕ) (hq : q ∈ ps) : q ≠ p := by
      intro he
      subst q
      have hh := hcp.1 p hq
      have hh1 : p = 1 := by simpa [Nat.Coprime] using hh
      exact (hp p List.mem_cons_self).ne_one hh1
    let a : ∀ q : ℕ, (ZMod q)ˣ := Function.update (fun q => b q * c q) p v
    refine ⟨a, ?_⟩
    intro n
    change densityFourier (fun x : ZMod (p * ps.prod) =>
      f p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 f
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2)
      (n : ZMod (p * ps.prod)) = _
    rw [densityFourier_crt (m := p) (n := ps.prod), map_intCast]
    change densityFourier (f p) ((ps.prod : ZMod p)⁻¹ * (n : ZMod p)) *
      densityFourier (primeCRTFunction ps hp' hcp.2 f)
        ((p : ZMod ps.prod)⁻¹ * (n : ZMod ps.prod)) = _
    rw [← huval, ← hj, ← Int.cast_mul, hb (j * n)]
    simp only [List.map_cons, List.prod_cons]
    congr 1
    · rw [primeDensityFourier_eq]
      simp only [a, Function.update_self, hvval]
    · apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have haq : a q = b q * c q := Function.update_of_ne (hne q hq) _ _
      rw [haq, Units.val_mul, hcval q hq, Int.cast_mul, mul_assoc]

/-- The recursively formed CRT density is exactly the product of the
centered functions in the manuscript. -/
theorem densityCRTList_value_eq_primeCRTFunction (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (densityCRTList ps hp hc S).value =
      primeCRTFunction ps hp hc (fun p x => (centeredDensity (S p) x : ℂ)) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  funext x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [densityCRTList_intCast, primeCRTFunction_intCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierUnitProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local factorization after the scalar multipliers in the quadratic sum -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_primeCRTFunction_unit (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) (v : (ZMod ps.prod)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (primeCRTFunction ps hp hc f) ((v : ZMod ps.prod) * (n : ZMod ps.prod)) =
        (ps.map fun p => primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))).prod := by
  classical
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  obtain ⟨b, hb⟩ := densityFourier_primeCRTFunction ps hp hc f
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (v : ZMod ps.prod)
  let c : ∀ p : ℕ, (ZMod p)ˣ := fun p => if h : p ∈ ps then
    Units.map (ZMod.castHom (List.dvd_prod h) (ZMod p)).toMonoidHom v else 1
  have hcv (p : ℕ) (h : p ∈ ps) : (c p : ZMod p) = (j : ZMod p) := by
    simp only [c, dite_eq_left h, Units.coe_map]
    change (ZMod.castHom (List.dvd_prod h) (ZMod p)) (v : ZMod ps.prod) = _
    rw [← hj, map_intCast]
  refine ⟨fun p => b p * c p, ?_⟩
  intro n
  rw [← hj, ← Int.cast_mul, hb]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p h
  rw [Units.val_mul, hcv p h, Int.cast_mul, mul_assoc]

theorem densityFourier_centered_unit_product (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (v : (ZMod ps.prod)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (densityCRTList ps hp hc S).value ((v : ZMod ps.prod) * (n : ZMod ps.prod)) =
        (ps.map fun p => primeDensityFourier (fun p x => (centeredDensity (S p) x : ℂ)) p
          ((a p : ZMod p) * (n : ZMod p))).prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  rw [densityCRTList_value_eq_primeCRTFunction]
  exact densityFourier_primeCRTFunction_unit ps hp hc _ v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OriginalDensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correlation estimates for the original two divisor transforms -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem prime_list_nodup (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) : ps.Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
    refine List.nodup_cons.mpr ⟨?_, ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) htail⟩
    intro hmem
    have he : p = 1 := by simpa [Nat.Coprime] using hhead p hmem
    exact (hp p List.mem_cons_self).ne_one he

private theorem prod_mask_subset {ι : Type*} [DecidableEq ι] (U P : Finset ι)
    (hUP : U ⊆ P) (F : ι → ℂ) :
    (∏ p ∈ P, if p ∈ U then F p else 1) = ∏ p ∈ U, F p := by
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hUP]

theorem local_correlation_product (U V P : Finset ℕ) (hP : P = U ∪ V)
    (f : ∀ p : ℕ, ZMod p → ℂ) (a b : ∀ p : ℕ, (ZMod p)ˣ) (n : ℤ) :
    (∏ p ∈ P, correlationPrimeFactor f (supportCorrelationSide U V) a b p (n : ZMod p)) =
      (∏ p ∈ U, primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))) *
        conj (∏ p ∈ V, primeDensityFourier f p ((b p : ZMod p) * (n : ZMod p))) := by
  classical
  have hf (p : ℕ) (hp : p ∈ P) :
      correlationPrimeFactor f (supportCorrelationSide U V) a b p (n : ZMod p) =
      (if p ∈ U then primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p)) else 1) *
      (if p ∈ V then conj (primeDensityFourier f p ((b p : ZMod p) * (n : ZMod p))) else 1) := by
    have hm : p ∈ U ∨ p ∈ V := by simpa only [hP, Finset.mem_union] using hp
    unfold correlationPrimeFactor supportCorrelationSide
    rcases hm with hu | hv
    · by_cases hv : p ∈ V <;> simp [hu, hv]
    · by_cases hu : p ∈ U <;> simp [hu, hv]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib,
    prod_mask_subset U P (by rw [hP]; exact Finset.subset_union_left),
    prod_mask_subset V P (by rw [hP]; exact Finset.subset_union_right), map_prod]

/-- Both original transforms have one common periodic model. Its coefficient
bound is derived from the local density functions, including their CRT twists. -/
theorem original_density_correlation_model (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (vp : (ZMod ps.prod)ˣ) (vq : (ZMod qs.prod)ˣ)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
    ∃ F : ZMod rs.prod → ℂ,
      (∀ n : ℤ, densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n : ZMod ps.prod)) *
        conj (densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n : ZMod qs.prod))) = F (n : ZMod rs.prod)) ∧
      (∀ u, ‖additiveFourier F u‖ ≤
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
  obtain ⟨a, ha⟩ := densityFourier_primeCRTFunction_unit ps hp hcp f vp
  obtain ⟨b, hb⟩ := densityFourier_primeCRTFunction_unit qs hq hcq f vq
  refine ⟨primeCRTFunction rs hr hcr
    (correlationPrimeFactor f (supportCorrelationSide ps.toFinset qs.toFinset) a b), ?_, ?_⟩
  · intro n
    rw [ha, hb, primeCRTFunction_intCast,
      ← List.prod_toFinset _ (prime_list_nodup ps hp hcp),
      ← List.prod_toFinset _ (prime_list_nodup qs hq hcq),
      ← List.prod_toFinset _ (prime_list_nodup rs hr hcr)]
    exact (local_correlation_product ps.toFinset qs.toFinset rs.toFinset hrs f a b n).symm
  · exact density_correlation_coefficient_bound rs hr hcr f hf _ a b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrelationNormalization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the quadratic-sum normalization on a dyadic segment -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem quadratic_normalization_product (R d e s v : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (hv : 0 < v) :
    Real.sqrt (R * d / (s * v)) * Real.sqrt (R * e / (s * v)) * s =
      R * Real.sqrt (d * e) / v := by
  have hx : 0 ≤ R / (s * v) := by positivity
  calc
    _ = Real.sqrt ((R * d / (s * v)) * (R * e / (s * v))) * s := by
      rw [Real.sqrt_mul (show 0 ≤ R * d / (s * v) by positivity)]
    _ = Real.sqrt ((R / (s * v)) ^ 2 * (d * e)) * s := by
      congr 2
      ring
    _ = (R / (s * v)) * Real.sqrt (d * e) * s := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx]
    _ = _ := by field_simp

theorem quadratic_normalization_cancel (R d e s v : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (hv : 0 < v)
    (A B : ℂ) :
    (((Real.sqrt (R * d / (s * v)) : ℝ) : ℂ)⁻¹ * A) *
      conj (((Real.sqrt (R * e / (s * v)) : ℝ) : ℂ)⁻¹ * B) / (s : ℂ) =
        ((v / (R * Real.sqrt (d * e)) : ℝ) : ℂ) * (A * conj B) := by
  have hp := quadratic_normalization_product R d e s v hR hd he hs hv
  have hde : 0 < Real.sqrt (d * e) := Real.sqrt_pos.mpr (mul_pos hd he)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hdeC : (Real.sqrt (d * e) : ℂ) ≠ 0 := by exact_mod_cast hde.ne'
  have hprod : (Real.sqrt (R * d / (s * v)) : ℂ) *
      (Real.sqrt (R * e / (s * v)) : ℂ) * (s : ℂ) =
        (R : ℂ) * (Real.sqrt (d * e) : ℂ) / (v : ℂ) := by exact_mod_cast hp
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (R * d / (s * v)) : ℂ) *
        (Real.sqrt (R * e / (s * v)) : ℂ) * (s : ℂ))⁻¹ * (A * conj B) := by
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [hprod]
      push_cast
      field_simp

/-- After cancellation the remaining finite sum has a constant positive
normalization, independent of the kernel index. -/
theorem quadratic_normalized_correlation_bound {ι : Type*}
    (S : Finset ι) (σ : ι → ℝ) (A B : ι → ℂ) (R d e v C : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hcor : ‖∑ s ∈ S, A s * conj (B s)‖ ≤ C) :
    ‖∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * A s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * B s) / (σ s : ℂ)‖ ≤
      v / (R * Real.sqrt (d * e)) * C := by
  have hn : 0 ≤ v / (R * Real.sqrt (d * e)) := by positivity
  have heq : (∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * A s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * B s) / (σ s : ℂ)) =
      ((v / (R * Real.sqrt (d * e)) : ℝ) : ℂ) * ∑ s ∈ S, A s * conj (B s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact quadratic_normalization_cancel R d e (σ s) v hR hd he (hσ s hs) hv (A s) (B s)
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left hcor hn

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

theorem finite_correlation_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (F : κ → ι → ℂ) (G : υ → ι → ℂ)
    (B : ℝ) (hB : ∀ w ∈ W, ∀ v ∈ V, ‖∑ s ∈ S, F w s * conj (G v s)‖ ≤ B) :
    ‖∑ s ∈ S, (∑ w ∈ W, F w s) * conj (∑ v ∈ V, G v s)‖ ≤
      (W.card : ℝ) * V.card * B := by
  rw [finite_correlation_expansion]
  calc
    _ ≤ ∑ w ∈ W, ‖∑ v ∈ V, ∑ s ∈ S, F w s * conj (G v s)‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ W, ∑ v ∈ V, B := by
      apply Finset.sum_le_sum
      intro w hw
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => hB w hw v hv))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The exact normalized pair count is all that remains after bounding each
expanded pair by the translated periodic estimate. -/
theorem normalized_quadratic_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (σ : ι → ℝ)
    (F : κ → ι → ℂ) (G : υ → ι → ℂ) (R d e v B : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hB : ∀ w ∈ W, ∀ v ∈ V, ‖∑ s ∈ S, F w s * conj (G v s)‖ ≤ B) :
    ‖∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ w ∈ W, F w s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ v ∈ V, G v s) / (σ s : ℂ)‖ ≤
      v / (R * Real.sqrt (d * e)) * ((W.card : ℝ) * V.card * B) := by
  exact quadratic_normalized_correlation_bound S σ _ _ R d e v _ hR hd he hv hσ
    (finite_correlation_pair_bound S W V F G B hB)

/-- The support pair count cancels the normalization and the interval length. -/
theorem quadratic_pair_count_cancellation (R d e v N C A H : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v) (hN : 0 < N)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (J J' : ℕ)
    (hJ : (J : ℝ) * J' ≤ H * R * Real.sqrt (d * e) / (N * v)) :
    v / (R * Real.sqrt (d * e)) * ((J : ℝ) * J' * (C * A * N)) ≤ H * C * A := by
  have hs : 0 < Real.sqrt (d * e) := Real.sqrt_pos.mpr (mul_pos hd he)
  calc
    _ ≤ v / (R * Real.sqrt (d * e)) *
        ((H * R * Real.sqrt (d * e) / (N * v)) * (C * A * N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedQuadraticCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A scalar weight commutes with the exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_normalized_quadratic_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (σ : ι → ℝ) (ρ : ι → ℂ)
    (F : κ → ι → ℂ) (G : υ → ι → ℂ) (R d e v B : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hB : ∀ w ∈ W, ∀ z ∈ V, ‖∑ s ∈ S, ρ s * (F w s * conj (G z s))‖ ≤ B) :
    ‖∑ s ∈ S, ρ s *
      ((((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ w ∈ W, F w s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ z ∈ V, G z s) / (σ s : ℂ))‖ ≤
      v / (R * Real.sqrt (d * e)) * ((W.card : ℝ) * V.card * B) := by
  have hb := normalized_quadratic_pair_bound S W V σ (fun w s => ρ s * F w s) G
    R d e v B hR hd he hv hσ (by
      intro w hw z hz
      convert hB w hw z hz using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      ring)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiMonomialFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-cube inequality for a concrete family of distinct monomials -/

namespace Ostmann

open scoped BigOperators

private theorem monomialCoefficients_apply {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (i : ι) : monomialCoefficients σ a (σ i) = a i := by
  classical
  unfold monomialCoefficients
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp only [ite_eq_right_iff]
    exact fun h => (hji (hσ h)).elim
  · simp

private theorem monomialCoefficients_sum {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, monomialCoefficients σ a Q * F Q) = ∑ i, a i * F (σ i) := by
  classical
  simp only [monomialCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private theorem monomialCoefficients_energy {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, F Q * (monomialCoefficients σ a Q) ^ 2) =
      ∑ i, F (σ i) * (a i) ^ 2 := by
  classical
  have he (Q : Finset P) : (monomialCoefficients σ a Q) ^ 2 =
      monomialCoefficients σ (fun i => (a i) ^ 2) Q := by
    by_cases hQ : ∃ i, σ i = Q
    · obtain ⟨i, rfl⟩ := hQ
      rw [monomialCoefficients_apply σ hσ, monomialCoefficients_apply σ hσ]
    · have hne (i : ι) : σ i ≠ Q := fun hi => hQ ⟨i, hi⟩
      simp [monomialCoefficients, hne]
  simp_rw [he, mul_comm (F _)]
  rw [monomialCoefficients_sum]

/-- Apply the published cube bound after inserting the coefficient array
by zero outside the actual monomial family. -/
theorem bonami_monomial_family (hB : PublishedBonamiBound)
    {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (hσ : Function.Injective σ) (a : ι → ℝ)
    (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) ≤
      (∑ i, ((2 * l - 1 : ℕ) : ℝ) ^ (σ i).card * (a i) ^ 2) ^ l := by
  have hb := hB P l hl (monomialCoefficients σ a)
  simp_rw [monomialCoefficients_sum] at hb
  rw [monomialCoefficients_energy σ hσ] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarefreeBonami
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bonami's inequality for the actual squarefree coefficient indices -/

namespace Ostmann

open scoped BigOperators

theorem mem_primeFactorSubset (P : Finset ℕ) (s : ℕ) (p : P) :
    p ∈ primeFactorSubset P s ↔ p.val ∈ s.primeFactors := by
  simp [primeFactorSubset]

theorem primeFactorSubset_map (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).map (Function.Embedding.subtype (· ∈ P)) = s.primeFactors := by
  ext p
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_primeFactorSubset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hp
    exact ⟨⟨p, hs hp⟩, hp, rfl⟩

theorem primeFactorSubset_card (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).card = s.primeFactors.card := by
  rw [← primeFactorSubset_map P s hs, Finset.card_map]

theorem primeFactorSubset_injective (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P) :
    Function.Injective (fun s : S => primeFactorSubset P s.val) := by
  intro s t hst
  apply Subtype.ext
  have hp := congrArg (fun Q : Finset P => Q.map (Function.Embedding.subtype (· ∈ P))) hst
  rw [primeFactorSubset_map P s.val (hP s s.property),
    primeFactorSubset_map P t.val (hP t t.property)] at hp
  have hh := congrArg (fun Q : Finset ℕ => ∏ p ∈ Q, p) hp
  rwa [Nat.prod_primeFactors_of_squarefree (hS s s.property),
    Nat.prod_primeFactors_of_squarefree (hS t t.property)] at hh

/-- This is the even moment bound in the manuscript, indexed by
the squarefree integers themselves. -/
theorem bonami_squarefree_family (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool,
        |∑ s : S, a s * rademacherMonomial (primeFactorSubset P s.val) ε| ^ (2 * l) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have h := bonami_monomial_family hB P (fun s : S => primeFactorSubset P s.val)
    (primeFactorSubset_injective P S hS hP) a l hl
  simpa only [primeFactorSubset_card P _ (hP _ (Subtype.property _))] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SquarefreeEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted reciprocal squarefree sum in the coefficient estimate -/

namespace Ostmann

open scoped BigOperators

theorem squarefree_weighted_reciprocal_le_product (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      ∏ p ∈ P, (1 + u / (p : ℝ)) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors (↑S : Set ℕ) := by
    intro a ha b hb he
    calc
      a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hS a ha)).symm
      _ = ∏ p ∈ b.primeFactors, p := by rw [he]
      _ = b := Nat.prod_primeFactors_of_squarefree (hS b hb)
  have hterm (s : ℕ) (hs : s ∈ S) :
      u ^ s.primeFactors.card / (s : ℝ) = ∏ p ∈ s.primeFactors, u / (p : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hS s hs)]
  calc
    _ = ∑ s ∈ S, ∏ p ∈ s.primeFactors, u / (p : ℝ) :=
      Finset.sum_congr rfl hterm
    _ = ∑ Q ∈ S.image Nat.primeFactors, ∏ p ∈ Q, u / (p : ℝ) :=
      (Finset.sum_image (f := fun Q : Finset ℕ => ∏ p ∈ Q, u / (p : ℝ)) hinj).symm
    _ ≤ ∑ Q ∈ P.powerset, ∏ p ∈ Q, u / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Q hQ
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
        exact Finset.mem_powerset.mpr (hP s hs)
      · intro Q hQ hnot
        exact Finset.prod_nonneg (fun p hp => div_nonneg hu (Nat.cast_nonneg _))
    _ = _ := (Finset.prod_one_add P).symm

theorem squarefree_weighted_reciprocal_le_exp (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      Real.exp (u * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  apply (squarefree_weighted_reciprocal_le_product S P hS hP u hu).trans
  calc
    _ ≤ ∏ p ∈ P, Real.exp (u / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (u / (p : ℝ))
    _ = Real.exp (∑ p ∈ P, u / (p : ℝ)) := (Real.exp_sum P _).symm
    _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum]

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
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeReciprocalBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary logarithmic bound for the reciprocal-prime sum -/

namespace Ostmann

open scoped BigOperators

private theorem prime_dyadic_reciprocal_bound (S : Finset ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hS : ∀ p ∈ S, p.Prime ∧ 2 ^ j ≤ p ∧ p ≤ 2 ^ (j + 1)) :
    (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 4 / (j : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hd : 0 < (2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) := by positivity
  have hlogsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log 4 * (2 ^ (j + 1) : ℕ) := by
    apply le_trans _ (prime_log_weight_le (2 ^ (j + 1)))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨(hS p hp).2.2, (hS p hp).1⟩
    · intro p hp hn
      exact Real.log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hS p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlow : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hlo
      have hlog : (j : ℝ) * Real.log 2 ≤ Real.log p := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hlow
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hp0 hd).mpr
      simp only [one_mul]
      calc
        _ ≤ (p : ℝ) * Real.log p := mul_le_mul hlow hlog (by positivity) hp0.le
        _ = _ := mul_comm _ _
    _ = (∑ p ∈ S, Real.log (p : ℝ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (Real.log 4 * (2 ^ (j + 1) : ℕ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      div_le_div_of_nonneg_right hlogsum hd.le
    _ = 4 / (j : ℝ) := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      ring

theorem prime_reciprocal_sum_le_harmonic (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (harmonic (Nat.log 2 N) : ℝ) := by
  classical
  let P := Nat.primesLE N
  let K := Nat.log 2 N
  have hmaps (p : ℕ) (hp : p ∈ P) : Nat.log 2 p ∈ Finset.Icc 1 K := by
    have hprime := Nat.prime_of_mem_primesLE hp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.log_pos (by decide) hprime.two_le
    · exact Nat.log_mono_right (Nat.le_of_mem_primesLE hp)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 K, 4 / (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply prime_dyadic_reciprocal_bound _ j (Finset.mem_Icc.mp hj).1
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      refine ⟨Nat.prime_of_mem_primesLE hp, ?_, ?_⟩
      · rw [← he]
        exact Nat.pow_log_le_self 2 (Nat.prime_of_mem_primesLE hp).ne_zero
      · rw [← he]
        exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le
    _ = 4 * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, Finset.mul_sum]

theorem prime_reciprocal_sum_le_log (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (1 + Real.log (Nat.log 2 N)) := by
  exact (prime_reciprocal_sum_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by norm_num))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarefreeCoefficientBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential weighted squarefree coefficient budget at the paper's scales -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem prime_reciprocal_exponential_cutoff (C T : ℝ)
    (hT : 1 ≤ T) (N : ℕ) (hN : (N : ℝ) ≤ Real.exp (C * T)) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤
      4 * (1 + Real.log (max 1 (C / Real.log 2)) + Real.log T) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := max 1 (C / Real.log 2)
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  apply (prime_reciprocal_sum_le_log N).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  by_cases hj : Nat.log 2 N = 0
  · simp only [hj, Nat.cast_zero, Real.log_zero]
    linarith
  · have hNp : 0 < N := by
      by_contra hh
      have : N = 0 := Nat.eq_zero_of_not_pos hh
      simp [this] at hj
    have hjp : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 hNp.ne'
    have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ C * T := by
      calc
        _ = Real.log ((2 : ℝ) ^ (Nat.log 2 N)) := (Real.log_pow _ _).symm
        _ ≤ Real.log N := Real.log_le_log (by positivity) hpow
        _ ≤ C * T := (Real.log_le_iff_le_exp (by exact_mod_cast hNp)).mpr hN
    have hjbound : (Nat.log 2 N : ℝ) ≤ D * T := by
      have hh : C ≤ D * Real.log 2 := (div_le_iff₀ hl2).mp (le_max_right _ _)
      nlinarith
    have hlog : Real.log (Nat.log 2 N) ≤ Real.log D + Real.log T := by
      calc
        _ ≤ Real.log (D * T) := Real.log_le_log hjp hjbound
        _ = _ := Real.log_mul hD0.ne' (by linarith)
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_DivisibleResidueCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform counts of multiples in a prescribed coprime residue class -/

namespace Ostmann

theorem divisible_residue_class_count (lo hi L r a : ℕ)
    (hlo : lo ≤ hi) (hL : 0 < L) (hr : 0 < r) (hcop : L.Coprime r) :
    (((Finset.Ioc lo hi).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)).card : ℝ) ≤
      ((hi : ℝ) - lo) / (L * r) + 1 := by
  classical
  let T := (Finset.Ioc lo hi).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)
  change (T.card : ℝ) ≤ _
  by_cases hT : T.Nonempty
  · obtain ⟨x, hx⟩ := hT
    have hx' := (Finset.mem_filter.mp hx).2
    have hsub : T ⊆ (Finset.Ioc lo hi).filter (fun n => Nat.ModEq (L * r) n x) := by
      intro n hn
      obtain ⟨hnI, hnL, hnr⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      exact ⟨hnL.trans hx'.1.symm,
        (Nat.modEq_zero_iff_dvd.mpr hnr).trans (Nat.modEq_zero_iff_dvd.mpr hx'.2).symm⟩
    have hcard : (T.card : ℝ) ≤
        (((Finset.Ioc lo hi).filter (fun n => Nat.ModEq (L * r) n x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hh := (abs_le.mp (integer_interval_residue_error lo hi (L * r) x hlo (Nat.mul_pos hL hr))).2
    push_cast at hh
    linarith
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [he, Finset.card_empty, Nat.cast_zero]
    have hwidth : (0 : ℝ) ≤ (hi : ℝ) - lo := sub_nonneg.mpr (Nat.cast_le.mpr hlo)
    positivity

theorem dyadic_divisible_residue_class_count (N L r a : ℕ)
    (hL : 0 < L) (hr : 0 < r) (hcop : L.Coprime r) (hsize : L * r ≤ N) :
    (((Finset.Ioc N (2 * N)).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)).card : ℝ) ≤
      2 * (N : ℝ) / (L * r) := by
  have hb := divisible_residue_class_count N (2 * N) L r a (by omega) hL hr hcop
  have hden : (0 : ℝ) < L * r := by positivity
  have hs : (L : ℝ) * r ≤ N := by exact_mod_cast hsize
  have hone : (1 : ℝ) ≤ (N : ℝ) / (L * r) := (one_le_div hden).mpr hs
  push_cast at hb
  ring_nf at hb hone ⊢
  linarith

/-- The dyadic range absorbs the additive residue-count error for every
half kernel of size at most the square root of its upper endpoint. -/
theorem half_kernel_modulus_le (L N r : ℕ) (hN : 2 * L ^ 2 ≤ N) (hr : r ^ 2 ≤ 2 * N) :
    L * r ≤ N := by
  have hs : (L * r) ^ 2 ≤ N ^ 2 := by
    calc
      _ = L ^ 2 * r ^ 2 := mul_pow _ _ _
      _ ≤ L ^ 2 * (2 * N) := Nat.mul_le_mul_left _ hr
      _ = (2 * L ^ 2) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right _ hN
      _ = _ := (pow_two N).symm
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le N) hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetProducts_mem_range (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) : primeSubsetProducts P k ⊆ oddSquarefreeRange (Z ^ k) := by
  intro s hs
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hsf := primeSubset_product_squarefree Q hprime
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsf.ne_zero, ?_⟩, ?_, hsf⟩
  · simpa only [hcard] using Finset.prod_le_pow_card Q (fun p => p) Z (fun p hp => hZ p (hQP hp))
  · have ho : ∀ p ∈ Q, Odd p := fun p hp => hodd p (hQP hp)
    clear hprime hsf hcard hQP hQ hs
    induction Q using Finset.induction_on with
    | empty => simp
    | @insert p Q hp ih =>
      rw [Finset.prod_insert hp]
      exact (ho p (Finset.mem_insert_self _ _)).mul
        (ih (fun q hq => ho q (Finset.mem_insert_of_mem hq)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HalfKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small divisor carrying half the prime factors of a squarefree kernel -/

namespace Ostmann

open scoped BigOperators

theorem half_kernel_weight (s r : ℕ) (hcard : r.primeFactors.card = s.primeFactors.card / 2)
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ s.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
  have hc : s.primeFactors.card ≤ 2 * r.primeFactors.card + 1 := by omega
  calc
    _ ≤ u ^ (2 * r.primeFactors.card + 1) := pow_le_pow_right₀ hu hc
    _ = _ := by rw [pow_add, pow_mul]; ring

theorem smallHalfKernel_spec (s : ℕ) (hs : Squarefree s) :
    Squarefree (smallHalfKernel s) ∧ smallHalfKernel s ∣ s ∧ (smallHalfKernel s) ^ 2 ≤ s ∧
      (smallHalfKernel s).primeFactors.card = s.primeFactors.card / 2 := by
  classical
  simpa only [smallHalfKernel, dite_eq_left hs] using Classical.choose_spec (squarefree_half_kernel s hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HalfKernelRankin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rankin's bound for the reciprocal mass of high-weight half kernels -/

namespace Ostmann

open scoped BigOperators

theorem high_weight_squarefree_reciprocal (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u t : ℝ) (hu : 0 ≤ u) (ht : 1 ≤ t) (b : ℕ)
    (hb : ∀ s ∈ S, b ≤ s.primeFactors.card) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      (t ^ b)⁻¹ * Real.exp (u * t * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  have htb : 0 < t ^ b := pow_pos (lt_of_lt_of_le zero_lt_one ht) _
  calc
    _ ≤ (t ^ b)⁻¹ * ∑ s ∈ S, (u * t) ^ s.primeFactors.card / (s : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ htb).mpr
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (hb s hs))
        (show 0 ≤ u ^ s.primeFactors.card / (s : ℝ) by positivity)
      calc
        _ = t ^ b * (u ^ s.primeFactors.card / (s : ℝ)) := by ring
        _ ≤ t ^ s.primeFactors.card * (u ^ s.primeFactors.card / (s : ℝ)) := hp
        _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (squarefree_weighted_reciprocal_le_exp S P hS hP (u * t) (by positivity)) (by positivity)

/-- The exponential high-weight condition forces many factors in the small
half kernel. -/
theorem high_weight_half_kernel_card (s r : ℕ)
    (hcard : r.primeFactors.card = s.primeFactors.card / 2)
    (u K τ : ℝ) (hu : 1 < u) (hhigh : Real.exp (τ * K) < u ^ s.primeFactors.card) :
    τ * K / (2 * Real.log u) - 1 ≤ r.primeFactors.card := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hh := Real.log_lt_log (Real.exp_pos _) hhigh
  rw [Real.log_exp, Real.log_pow] at hh
  have hc : s.primeFactors.card ≤ 2 * r.primeFactors.card + 1 := by omega
  have hcR : (s.primeFactors.card : ℝ) ≤ 2 * r.primeFactors.card + 1 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcR hlog.le
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log u)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightResidueMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue-uniform high-weight mass via the small half kernels -/

namespace Ostmann

open scoped BigOperators

/-- The half-kernel construction converts the mass in one residue class into
a reciprocal squarefree sum. Its fibers are controlled uniformly in the residue. -/
theorem half_kernel_residue_mass (S : Finset ℕ) (N L a : ℕ)
    (hL : 0 < L) (hsize : 2 * L ^ 2 ≤ N)
    (hS : ∀ s ∈ S, Squarefree s)
    (hrange : ∀ s ∈ S, s ∈ Finset.Ioc N (2 * N))
    (hres : ∀ s ∈ S, Nat.ModEq L s a)
    (hcop : ∀ s ∈ S, L.Coprime s) (u : ℝ) (hu : 1 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card) ≤
      (2 * u * N / L) * ∑ r ∈ S.image smallHalfKernel, (u ^ 2) ^ r.primeFactors.card / (r : ℝ) := by
  classical
  have hmaps (s : ℕ) (hs : s ∈ S) : smallHalfKernel s ∈ S.image smallHalfKernel :=
    Finset.mem_image_of_mem smallHalfKernel hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  obtain ⟨s₀, hs₀, heq₀⟩ := Finset.mem_image.mp hr
  have hspec₀ := smallHalfKernel_spec s₀ (hS s₀ hs₀)
  rw [heq₀] at hspec₀
  have hr0 : 0 < r := Nat.pos_of_ne_zero hspec₀.1.ne_zero
  have hcopr : L.Coprime r := (hcop s₀ hs₀).of_dvd_right hspec₀.2.1
  have hrN : r ^ 2 ≤ 2 * N := hspec₀.2.2.1.trans (Finset.mem_Ioc.mp (hrange s₀ hs₀)).2
  have hLr := half_kernel_modulus_le L N r hsize hrN
  let T := S.filter (fun s => smallHalfKernel s = r)
  have hsub : T ⊆ (Finset.Ioc N (2 * N)).filter (fun s => Nat.ModEq L s a ∧ r ∣ s) := by
    intro s hs
    obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
    have hsp := smallHalfKernel_spec s (hS s hs)
    rw [heq] at hsp
    exact Finset.mem_filter.mpr ⟨hrange s hs, hres s hs, hsp.2.1⟩
  have hcard : (T.card : ℝ) ≤ 2 * (N : ℝ) / (L * r) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (dyadic_divisible_residue_class_count N L r a hL hr0 hcopr hLr)
  have hweight (s : ℕ) (hs : s ∈ T) :
      u ^ s.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
    obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
    have hsp := smallHalfKernel_spec s (hS s hs)
    rw [heq] at hsp
    exact half_kernel_weight s r hsp.2.2.2 u hu
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  change (∑ s ∈ T, u ^ s.primeFactors.card) ≤ _
  calc
    _ ≤ ∑ _s ∈ T, u * (u ^ 2) ^ r.primeFactors.card := Finset.sum_le_sum hweight
    _ = (T.card : ℝ) * (u * (u ^ 2) ^ r.primeFactors.card) := by simp
    _ ≤ (2 * (N : ℝ) / (L * r)) * (u * (u ^ 2) ^ r.primeFactors.card) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

/-- Rankin's parameter bounds the residue mass with its half-kernel,
congruence and multiplicity conditions. -/
theorem high_weight_residue_mass (S P : Finset ℕ) (N L a b : ℕ)
    (hL : 0 < L) (hsize : 2 * L ^ 2 ≤ N)
    (hS : ∀ s ∈ S, Squarefree s)
    (hrange : ∀ s ∈ S, s ∈ Finset.Ioc N (2 * N))
    (hres : ∀ s ∈ S, Nat.ModEq L s a) (hcop : ∀ s ∈ S, L.Coprime s)
    (hP : ∀ s ∈ S, (smallHalfKernel s).primeFactors ⊆ P)
    (hb : ∀ s ∈ S, b ≤ (smallHalfKernel s).primeFactors.card)
    (u t : ℝ) (hu : 1 ≤ u) (ht : 1 ≤ t) :
    (∑ s ∈ S, u ^ s.primeFactors.card) ≤
      (2 * u * N / L) * (t ^ b)⁻¹ *
        Real.exp (u ^ 2 * t * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  apply (half_kernel_residue_mass S N L a hL hsize hS hrange hres hcop u hu).trans
  have hrank := high_weight_squarefree_reciprocal (S.image smallHalfKernel) P
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact (smallHalfKernel_spec s (hS s hs)).1)
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact hP s hs)
    (u ^ 2) t (sq_nonneg _) ht b
    (by intro r hr; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr; exact hb s hs)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrank (by positivity : 0 ≤ 2 * u * N / L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RankinExponentialBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit numerical margin in the high-weight Rankin parameter -/

namespace Ostmann

/-- The large negative Rankin exponent dominates with ample margin once the
stated logarithmic and positive-error bounds hold. -/
theorem rankin_exponential_bound (T u K E : ℝ) (b : ℕ)
    (hT : 1 < T) (hu : 1 < u) (hK : 0 ≤ K)
    (hlog : Real.log u ≤ Real.log T / 100000)
    (hb : K / (400 * Real.log u) - 1 ≤ b)
    (hE : Real.log u + Real.log T / 4 + E ≤ K) :
    u * ((T ^ (1 / 4 : ℝ)) ^ b)⁻¹ * Real.exp E ≤ Real.exp (-20 * K) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hlt : 0 < Real.log T := Real.log_pos hT
  have hb' : K ≤ ((b : ℝ) + 1) * (400 * Real.log u) := by
    apply (div_le_iff₀ (by positivity : 0 < 400 * Real.log u)).mp
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (b : ℝ) + 1 by positivity)
  have hexp : Real.log u - (b : ℝ) * (Real.log T / 4) + E ≤ -20 * K := by
    nlinarith
  have hp : (T ^ (1 / 4 : ℝ)) ^ b = Real.exp ((b : ℝ) * (Real.log T / 4)) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp, ← Real.exp_neg]
  calc
    _ = Real.exp (Real.log u - (b : ℝ) * (Real.log T / 4) + E) := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hu0, div_eq_mul_inv, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RankinParameterBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specializing the high-weight Rankin parameter at the manuscript's exponents -/

namespace Ostmann

open Filter Asymptotics

theorem rankin_parameter_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      Real.log u ≤ Real.log T / 100000 ∧
      Real.log u + Real.log T / 4 + C * u ^ 2 * T ^ (1 / 4 : ℝ) * (1 + Real.log T) ≤
        T ^ (9999999 / 10000000 : ℝ) := by
  let μ : ℝ := 1 / 1000000
  let a : ℝ := 1 / 4 + 2 * μ
  let κ : ℝ := 9999999 / 10000000
  let D : ℝ := 1 + 16 * C
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < κ - a := by norm_num [κ, a, μ]
  have hlog := (isLittleO_log_rpow_atTop hδ).bound (show 0 < 1 / (2 * D) by positivity)
  have hpow := (tendsto_rpow_atTop hδ).eventually_ge_atTop (2 * D)
  have hloglarge := Real.tendsto_log_atTop.eventually_ge_atTop (1000000 : ℝ)
  filter_upwards [hlog, hpow, hloglarge, eventually_ge_atTop (1 : ℝ)] with T hl hp hlbig hT u hu huU
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hulog : Real.log u ≤ 3 + μ * Real.log T := by
    calc
      _ ≤ Real.log (4 * T ^ μ) := Real.log_le_log hu0 huU
      _ = Real.log 4 + μ * Real.log T := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT0 μ).ne', Real.log_rpow hT0]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlu : Real.log u ≤ Real.log T / 100000 := by
    dsimp [μ] at hulog
    linarith
  refine ⟨hlu, ?_⟩
  have hTa : 1 ≤ T ^ a := Real.one_le_rpow hT (by dsimp [a, μ]; positivity)
  have hsquare : u ^ 2 * T ^ (1 / 4 : ℝ) ≤ 16 * T ^ a := by
    calc
      _ ≤ (4 * T ^ μ) ^ 2 * T ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0.le huU 2) (by positivity)
      _ = 16 * (T ^ μ * T ^ μ * T ^ (1 / 4 : ℝ)) := by ring
      _ = 16 * T ^ a := by
        rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
        congr 2
        dsimp [a]
        ring
  have hupper : Real.log u + Real.log T / 4 + C * u ^ 2 * T ^ (1 / 4 : ℝ) * (1 + Real.log T) ≤
      D * T ^ a * (1 + Real.log T) := by
    have hlogu : Real.log u + Real.log T / 4 ≤ 1 + Real.log T := by
      dsimp [μ] at hulog
      nlinarith
    have hlin : 1 + Real.log T ≤ T ^ a * (1 + Real.log T) := by
      exact le_mul_of_one_le_left (by positivity) hTa
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hC)
      (show 0 ≤ 1 + Real.log T by positivity)
    calc
      _ ≤ (1 + Real.log T) + C * (16 * T ^ a) * (1 + Real.log T) := by
        convert add_le_add hlogu he using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ ≤ T ^ a * (1 + Real.log T) + C * (16 * T ^ a) * (1 + Real.log T) :=
        add_le_add_left hlin _
      _ = D * T ^ a * (1 + Real.log T) := by dsimp [D]; ring
  have hl' : Real.log T ≤ 1 / (2 * D) * T ^ (κ - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)] using hl
  have hc' : (1 : ℝ) ≤ 1 / (2 * D) * T ^ (κ - a) := by
    rw [one_div_mul_eq_div]
    exact (one_le_div (by positivity : 0 < 2 * D)).mpr hp
  apply hupper.trans
  calc
    _ ≤ D * T ^ a * (1 / D * T ^ (κ - a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he : 1 / D * T ^ (κ - a) =
          1 / (2 * D) * T ^ (κ - a) + 1 / (2 * D) * T ^ (κ - a) := by
        field_simp
        ring
      have hh : 1 + Real.log T ≤ 1 / D * T ^ (κ - a) := by linarith
      exact hh
    _ = T ^ κ := by
      have hprod : T ^ a * T ^ (κ - a) = T ^ κ := by
        rw [← Real.rpow_add hT0]
        congr 1
        ring
      calc
        _ = T ^ a * T ^ (κ - a) := by field_simp
        _ = _ := hprod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay of the actual high-weight residue mass -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- The high-weight estimate at the manuscript's moment and kernel scales.
The set consists of actual squarefree integers in a dyadic residue class;
neither a reciprocal-mass estimate nor a half-kernel count is assumed. -/
theorem eventual_high_weight_residue_mass (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (N L a : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < L → 2 * L ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, Nat.ModEq L s a) → (∀ s ∈ S, L.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      (∑ s ∈ S, u ^ s.primeFactors.card) ≤
        ((N : ℝ) / L) * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  let B : ℝ := 1 + Real.log (max 1 (C / Real.log 2))
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Real.log_nonneg (le_max_left (1 : ℝ) (C / Real.log 2))]
  have hbudget := rankin_parameter_budget (4 * B) (by positivity)
  filter_upwards [hbudget, eventually_ge_atTop (2 : ℝ)] with T hbudget hT N L a S u
    hL hsize hcut hS hrange hres hcop hu huU hhigh
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hu1 : 1 < u := by linarith
  let K : ℝ := T ^ (9999999 / 10000000 : ℝ)
  let b : ℕ := ⌈K / (400 * Real.log u) - 1⌉₊
  have hK : 1 ≤ K := Real.one_le_rpow hT1 (by norm_num)
  have hb (s : ℕ) (hs : s ∈ S) : b ≤ (smallHalfKernel s).primeFactors.card := by
    apply Nat.ceil_le.mpr
    have hh := high_weight_half_kernel_card s (smallHalfKernel s)
      (smallHalfKernel_spec s (hS s hs)).2.2.2 u K (1 / 200) hu1 (by
        simpa only [one_div_mul_eq_div] using hhigh s hs)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hP (s : ℕ) (hs : s ∈ S) :
      (smallHalfKernel s).primeFactors ⊆ Nat.primesLE (2 * N) := by
    intro p hp
    obtain ⟨hpp, hpr, _⟩ := Nat.mem_primeFactors.mp hp
    have hs0 := Nat.pos_of_ne_zero (hS s hs).ne_zero
    have hps : p ∣ s := dvd_trans hpr (smallHalfKernel_spec s (hS s hs)).2.1
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd hs0 hps).trans (Finset.mem_Ioc.mp (hrange s hs)).2, hpp⟩
  have hprime := prime_reciprocal_exponential_cutoff C T hT1 (2 * N) (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcut)
  have hprime' : (∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹) ≤
      (4 * B) * (1 + Real.log T) := by
    apply hprime.trans
    change 4 * (B + Real.log T) ≤ _
    have hh := mul_le_mul_of_nonneg_right hB (Real.log_nonneg hT1)
    nlinarith
  have hE : Real.log u + Real.log T / 4 +
      u ^ 2 * T ^ (1 / 4 : ℝ) * (∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹) ≤ K := by
    apply le_trans _ (hbudget u hu huU).2
    have hh := mul_le_mul_of_nonneg_left hprime'
      (show 0 ≤ u ^ 2 * T ^ (1 / 4 : ℝ) by positivity)
    nlinarith only [hh]
  have hdecay := rankin_exponential_bound T u K
    (u ^ 2 * T ^ (1 / 4 : ℝ) * ∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹)
    b (by linarith) hu1 (by positivity) (hbudget u hu huU).1 (Nat.le_ceil _) hE
  have hmass := high_weight_residue_mass S (Nat.primesLE (2 * N)) N L a b
    hL hsize hS hrange hres hcop hP hb u (T ^ (1 / 4 : ℝ)) (by linarith)
    (Real.one_le_rpow hT1 (by norm_num))
  have hNL : 0 ≤ (N : ℝ) / L := by positivity
  have htwo : 2 * Real.exp (-20 * K) ≤ Real.exp (-10 * K) := by
    calc
      _ = Real.exp (Real.log 2 - 20 * K) := by
        have he : Real.log 2 - 20 * K = Real.log 2 + (-20 * K) := by ring
        rw [he, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith)
  calc
    _ ≤ _ := hmass
    _ = ((N : ℝ) / L) * (2 * (u * ((T ^ (1 / 4 : ℝ)) ^ b)⁻¹ *
        Real.exp (u ^ 2 * T ^ (1 / 4 : ℝ) * ∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹))) := by ring
    _ ≤ ((N : ℝ) / L) * (2 * Real.exp (-20 * K)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo hNL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorCorrelationEuler
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Euler factor after summing the two divisor weights -/

namespace Ostmann

open scoped BigOperators

private theorem sum_powerset_prod_ite (P : Finset ℕ) (A B : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∏ p ∈ P, if p ∈ U then A p else B p) =
      ∏ p ∈ P, (A p + B p) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro U hU
  have hUP := Finset.mem_powerset.mp hU
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hUP)
  · congr 1
    ext p
    simp

private theorem divisor_pair_local_factor (lam : ℝ) (r : ℕ → ℝ)
    (P U V : Finset ℕ) (hU : U ⊆ P) (hV : V ⊆ P) :
    lam ^ (U.card + V.card) * (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else r p) =
      ∏ p ∈ P, if p ∈ U then (if p ∈ V then lam ^ 2 else lam * r p)
        else (if p ∈ V then lam * r p else 1) := by
  classical
  have hlam (U : Finset ℕ) (hU : U ⊆ P) :
      (∏ p ∈ P, if p ∈ U then lam else 1) = lam ^ U.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hU, Finset.prod_const]
  rw [pow_add, ← hlam U hU, ← hlam V hV, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hu : p ∈ U <;> by_cases hv : p ∈ V <;> simp [hu, hv, pow_two]

theorem divisor_correlation_euler_product (P : Finset ℕ) (lam : ℝ) (r : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
      lam ^ (U.card + V.card) * (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else r p)) =
        ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * r p) := by
  classical
  calc
    _ = ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        ∏ p ∈ P, if p ∈ U then (if p ∈ V then lam ^ 2 else lam * r p)
          else (if p ∈ V then lam * r p else 1) := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      exact divisor_pair_local_factor lam r P U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
    _ = ∑ U ∈ P.powerset, ∏ p ∈ P,
        ((if p ∈ U then lam ^ 2 else lam * r p) + (if p ∈ U then lam * r p else 1)) := by
      apply Finset.sum_congr rfl
      intro U hU
      convert sum_powerset_prod_ite P (fun p => if p ∈ U then lam ^ 2 else lam * r p)
        (fun p => if p ∈ U then lam * r p else 1) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro V hV
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hu : p ∈ U <;> by_cases hv : p ∈ V <;> simp [hu, hv]
    _ = ∑ U ∈ P.powerset, ∏ p ∈ P,
        if p ∈ U then lam ^ 2 + lam * r p else lam * r p + 1 := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.prod_congr rfl
      intro p hp
      split <;> simp_all
    _ = ∏ p ∈ P, ((lam ^ 2 + lam * r p) + (lam * r p + 1)) := sum_powerset_prod_ite P _ _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LowWeightEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Euler-product constants for the large-kernel coefficient energy -/

namespace Ostmann

open scoped BigOperators

/-- A fixed lower cutoff for the small primes suffices for the manuscript's
`.006 K` low-weight norm estimate. No asymptotic prime estimate is assumed. -/
theorem low_weight_euler_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 10000 ≤ p) :
    Real.exp ((P.card : ℝ) / 200) *
      (∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) ≤
        Real.exp (3 * (P.card : ℝ) / 250) := by
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹) ≤
        Real.exp (7 / 1000 : ℝ) := by
    have hpR : (10000 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hs : (100 : ℝ) ≤ Real.sqrt (p : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ)]
    have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ (100 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hs
    have hb : (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ≤ 7 / 1000 := by
      norm_num at hi ⊢
      linarith
    have hex := Real.add_one_le_exp (7 / 1000 : ℝ)
    linarith
  calc
    _ ≤ Real.exp ((P.card : ℝ) / 200) * ∏ _p ∈ P, Real.exp (7 / 1000 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Finset.prod_le_prod (fun p hp => by positivity) hlocal
    _ = Real.exp (3 * (P.card : ℝ) / 250) := by
      rw [← Real.exp_sum, Finset.sum_const, nsmul_eq_mul, ← Real.exp_add]
      congr 1
      ring

theorem low_weight_euler_bound_scale (P : Finset ℕ) (hP : ∀ p ∈ P, 10000 ≤ p)
    (K : ℝ) (hK : (P.card : ℝ) ≤ K) :
    Real.exp (K / 200) *
      (∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) ≤
        Real.exp (3 * K / 250) := by
  calc
    _ = Real.exp ((K - P.card) / 200) * (Real.exp ((P.card : ℝ) / 200) *
        ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp ((K - P.card) / 200) * Real.exp (3 * (P.card : ℝ) / 250) :=
      mul_le_mul_of_nonneg_left (low_weight_euler_bound P hP) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

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

theorem divisor_combination_energy_bound {ι : Type*}
    (S : Finset ι) (P : Finset ℕ) (μ : ι → ℝ)
    (c : Finset ℕ → ℂ) (G : Finset ℕ → ι → ℂ) (lam C : ℝ)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card)
    (hpair : ∀ U ∈ P.powerset, ∀ V ∈ P.powerset,
      ‖∑ s ∈ S, (μ s : ℂ) * (G U s * conj (G V s))‖ ≤
        C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) :
    (∑ s ∈ S, μ s * ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
      C * ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * (Real.sqrt (p : ℝ))⁻¹) := by
  classical
  apply (weighted_sum_energy_le_correlations S P.powerset μ c G).trans
  calc
    _ ≤ ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        C * (lam ^ (U.card + V.card) *
          ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro V hV
      have hprod : 0 ≤ C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
        positivity
      calc
        _ ≤ (lam ^ U.card * lam ^ V.card) *
            (C * ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹) :=
          mul_le_mul (mul_le_mul (hc U hU) (hc V hV) (norm_nonneg _) (by positivity))
            (hpair U hU V hV) (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [divisor_correlation_euler_product]

/-- A uniform pair bound costs exactly the square of the divisor-weight sum. -/
theorem uniform_divisor_combination_energy_bound {ι : Type*}
    (S : Finset ι) (P : Finset ℕ) (μ : ι → ℝ)
    (c : Finset ℕ → ℂ) (G : Finset ℕ → ι → ℂ) (lam C : ℝ)
    (hlam : 0 ≤ lam) (_hC : 0 ≤ C)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card)
    (hpair : ∀ U ∈ P.powerset, ∀ V ∈ P.powerset,
      ‖∑ s ∈ S, (μ s : ℂ) * (G U s * conj (G V s))‖ ≤ C) :
    (∑ s ∈ S, μ s * ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
      C * (1 + lam) ^ (2 * P.card) := by
  apply (weighted_sum_energy_le_correlations S P.powerset μ c G).trans
  calc
    _ ≤ ∑ U ∈ P.powerset, ∑ V ∈ P.powerset, C * lam ^ (U.card + V.card) := by
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro V hV
      have hh := mul_le_mul
        (mul_le_mul (hc U hU) (hc V hV) (norm_nonneg _) (by positivity))
        (hpair U hU V hV) (norm_nonneg _) (by positivity)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [pow_add]
      ring
    _ = C * (∑ U ∈ P.powerset, ∑ V ∈ P.powerset, lam ^ (U.card + V.card)) := by
      simp_rw [← Finset.mul_sum]
    _ = C * ∏ _p ∈ P, (1 + lam ^ 2 + 2 * lam) := by
      congr 1
      simpa using divisor_correlation_euler_product P lam (fun _ => 1)
    _ = C * (1 + lam) ^ (2 * P.card) := by
      have he : 1 + lam ^ 2 + 2 * lam = (1 + lam) ^ 2 := by ring
      rw [he, Finset.prod_const, pow_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PeriodicIntervalPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The periodic phase estimate on a translated integer interval -/

namespace Ostmann

open scoped BigOperators

theorem weighted_periodic_linear_shift_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (M N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))‖ ≤
      discreteVariation w N * (2 * A * ((N : ℝ) + q * (1 + Real.log q))) := by
  have ht (u : ZMod q) : ‖additiveFourier (fun x => f (x + (M : ZMod q))) u‖ ≤ A := by
    rw [additiveFourier_add_right, norm_mul]
    have hc : ‖ZMod.stdAddChar ((M : ZMod q) * u)‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
    rw [hc, one_mul]
    exact hf u
  have heq : (∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))) =
      realAdditivePhase α ^ M * ∑ n ∈ Finset.range N, w n *
        ((fun x : ZMod q => f (x + (M : ZMod q))) (n : ZMod q) * realAdditivePhase α ^ n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_add, Nat.cast_add]
    ring
  rw [heq, norm_mul, norm_pow, norm_realAdditivePhase, one_pow, one_mul]
  exact weighted_periodic_linear_phase_bound q _ A α hA ht w N

theorem periodic_grid_cost_le_square (q : ℕ) [NeZero q] :
    (q : ℝ) * (1 + Real.log q) ≤ (q : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hl := Real.log_le_sub_one_of_pos hq
  nlinarith

theorem weighted_periodic_linear_shift_long_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (M N : ℕ)
    (hN : q ^ 2 ≤ N) :
    ‖∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))‖ ≤
      discreteVariation w N * (4 * A * N) := by
  apply (weighted_periodic_linear_shift_bound q f A α hA hf w M N).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold discreteVariation; positivity)
  have hN' : (q : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hg := periodic_grid_cost_le_square q
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RescaledWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the rescaled smooth weight -/

namespace Ostmann

open scoped BigOperators

theorem rescaledPhaseWeight_variation (Φ : ℝ → ℂ) (ξ Y B D : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * N / Y := by
  have hstep : ∀ j : ℕ, ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖ ≤ D / Y := by
    intro j
    have h := hlip ((((j + 1 : ℕ) : ℝ) + ξ) / Y) (((j : ℝ) + ξ) / Y)
    have heq : ((((j + 1 : ℕ) : ℝ) + ξ) / Y - ((j : ℝ) + ξ) / Y) = 1 / Y := by
      push_cast
      ring
    rw [heq, abs_of_pos (one_div_pos.mpr hY)] at h
    simpa only [rescaledPhaseWeight, mul_one_div] using h
  have hsum : (∑ j ∈ Finset.range (N - 1), ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖) ≤ (N - 1 : ℕ) * (D / Y) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard (div_nonneg hD hY.le))
  have hend := hbound (((N - 1 : ℕ) + ξ) / Y)
  unfold discreteVariation
  change ‖Φ (((N - 1 : ℕ) + ξ) / Y)‖ + _ ≤ _
  calc
    _ ≤ B + (N : ℝ) * (D / Y) := add_le_add hend hsum'
    _ = _ := by ring

theorem rescaledPhaseWeight_variation_uniform (Φ : ℝ → ℂ) (ξ Y B D C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D) (hN : (N : ℝ) ≤ C * Y)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * C := by
  apply (rescaledPhaseWeight_variation Φ ξ Y B D N hY hD hbound hlip).trans
  have hn' := (div_le_iff₀ hY).mpr hN
  have hh := mul_le_mul_of_nonneg_left hn' hD
  rw [mul_div_assoc]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SchwartzWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete variation bounds for the quadratic Schwartz weight -/

namespace Ostmann

open scoped SchwartzMap

theorem schwartz_norm_sub_le (Φ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ‖Φ x - Φ y‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ * |x - y| := by
  have hd (z : ℝ) : ‖fderiv ℝ Φ z‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by
    simpa only [norm_iteratedFDeriv_one] using Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := Set.univ) (fun _ _ => Φ.differentiableAt)
    (fun z _ => hd z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

theorem schwartz_rescaled_variation (Φ : 𝓢(ℝ, ℂ)) (ξ Y C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hN : (N : ℝ) ≤ C * Y) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤
      SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C := by
  have hD : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ :=
    (norm_nonneg _).trans (Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
  exact rescaledPhaseWeight_variation_uniform Φ ξ Y _ _ C N hY hD hN
    (Φ.norm_le_seminorm ℝ) (schwartz_norm_sub_le Φ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CorrelationWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the two transform factors in a correlation -/

namespace Ostmann

open scoped BigOperators SchwartzMap ComplexConjugate

theorem discreteVariation_conj (w : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun n => conj (w n)) N = discreteVariation w N := by
  simp only [discreteVariation, ← map_sub, Complex.norm_conj]

theorem discreteVariation_mul_le (w z : ℕ → ℂ) (N : ℕ) (B C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ n, ‖w n‖ ≤ B) (hz : ∀ n, ‖z n‖ ≤ C) :
    discreteVariation (fun n => w n * z n) N ≤
      B * discreteVariation z N + C * discreteVariation w N := by
  have hstep (j : ℕ) : ‖w (j + 1) * z (j + 1) - w j * z j‖ ≤
      B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖ := by
    calc
      _ = ‖w (j + 1) * (z (j + 1) - z j) + (w (j + 1) - w j) * z j‖ := by
        congr 1
        ring
      _ ≤ ‖w (j + 1) * (z (j + 1) - z j)‖ + ‖(w (j + 1) - w j) * z j‖ := norm_add_le _ _
      _ ≤ B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖ := by
        simp only [norm_mul]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)
        · rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (hz _) (norm_nonneg _)
  have hend : ‖w (N - 1) * z (N - 1)‖ ≤
      B * ‖z (N - 1)‖ + C * ‖w (N - 1)‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)).trans
      (le_add_of_nonneg_right (by positivity))
  unfold discreteVariation
  calc
    _ ≤ (B * ‖z (N - 1)‖ + C * ‖w (N - 1)‖) +
        ∑ j ∈ Finset.range (N - 1), (B * ‖z (j + 1) - z j‖ + C * ‖w (j + 1) - w j‖) :=
      add_le_add hend (Finset.sum_le_sum (fun j _ => hstep j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The two smooth Fourier-transform weights have uniform variation on any
interval whose length is bounded by both scaling lengths. -/
theorem schwartz_correlation_variation (Φ Ψ : 𝓢(ℝ, ℂ))
    (ξ η Y Z C D : ℝ) (N : ℕ) (hY : 0 < Y) (hZ : 0 < Z)
    (hNY : (N : ℝ) ≤ C * Y) (hNZ : (N : ℝ) ≤ D * Z) :
    discreteVariation (fun n => Φ (((n : ℝ) + ξ) / Y) *
      conj (Ψ (((n : ℝ) + η) / Z))) N ≤
      SchwartzMap.seminorm ℝ 0 0 Φ *
        (SchwartzMap.seminorm ℝ 0 0 Ψ + SchwartzMap.seminorm ℝ 0 1 Ψ * D) +
      SchwartzMap.seminorm ℝ 0 0 Ψ *
        (SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C) := by
  have hB : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ :=
    (norm_nonneg _).trans (Φ.norm_le_seminorm ℝ 0)
  have hB' : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Ψ :=
    (norm_nonneg _).trans (Ψ.norm_le_seminorm ℝ 0)
  apply (discreteVariation_mul_le _ _ N _ _ hB'
    (fun n => Φ.norm_le_seminorm ℝ _) (fun n => by
      rw [Complex.norm_conj]
      exact Ψ.norm_le_seminorm ℝ _)).trans
  rw [discreteVariation_conj]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (schwartz_rescaled_variation Ψ η Z D N hZ hNZ) hB)
    (mul_le_mul_of_nonneg_left (schwartz_rescaled_variation Φ ξ Y C N hY hNY) hB')

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SchwartzDensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single expanded pair in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

/-- Each expanded pair is bounded by its exact exclusive-prime factor times
the interval length and a fixed Schwartz seminorm budget. -/
theorem schwartz_density_correlation_bound (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (vp : (ZMod ps.prod)ˣ) (vq : (ZMod qs.prod)ˣ)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z C D : ℝ) (M N : ℕ)
    (hY : 0 < Y) (hZ : 0 < Z) (hNY : (N : ℝ) ≤ C * Y) (hNZ : (N : ℝ) ≤ D * Z)
    (hN : rs.prod ^ 2 ≤ N) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      (Φ (((n + M : ℕ) : ℝ) / Y) *
        densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
          realAdditivePhase α ^ (n + M)) *
      conj (Ψ (((n + M : ℕ) : ℝ) / Z) *
        densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)) *
          realAdditivePhase β ^ (n + M))‖ ≤
      correlationWeightBudget Φ Ψ C D *
        (4 * (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod * N) := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
  obtain ⟨F, hF, hbound⟩ := original_density_correlation_model ps qs rs hp hq hr hcp hcq hcr hrs vp vq f hf
  let w : ℕ → ℂ := fun n => Φ (((n + M : ℕ) : ℝ) / Y) * conj (Ψ (((n + M : ℕ) : ℝ) / Z))
  have he (n : ℕ) : densityFourier (primeCRTFunction ps hp hcp f)
      ((vp : ZMod ps.prod) * (n + M : ℕ)) *
      conj (densityFourier (primeCRTFunction qs hq hcq f)
        ((vq : ZMod qs.prod) * (n + M : ℕ))) = F (n + M : ℕ) := by
    simpa only [Int.cast_natCast] using hF ((n + M : ℕ) : ℤ)
  have hphase (n : ℕ) : realAdditivePhase α ^ n * conj (realAdditivePhase β ^ n) =
      realAdditivePhase (α - β) ^ n := by
    rw [realAdditivePhase_sub, mul_pow, map_pow]
  have hsum : (∑ n ∈ Finset.range N,
      (Φ (((n + M : ℕ) : ℝ) / Y) *
        densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
          realAdditivePhase α ^ (n + M)) *
      conj (Ψ (((n + M : ℕ) : ℝ) / Z) *
        densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)) *
          realAdditivePhase β ^ (n + M))) =
      ∑ n ∈ Finset.range N, w n * (F (n + M : ℕ) * realAdditivePhase (α - β) ^ (n + M)) := by
    apply Finset.sum_congr rfl
    intro n hn
    calc
      _ = w n * (densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
        conj (densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)))) *
        (realAdditivePhase α ^ (n + M) * conj (realAdditivePhase β ^ (n + M))) := by
          simp only [w, map_mul]
          ring
      _ = _ := by rw [he, hphase]; ring
  have hA : 0 ≤ (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact correlationPrimeBound_nonneg _ p
  have hvar : discreteVariation w N ≤ correlationWeightBudget Φ Ψ C D := by
    simpa only [w, correlationWeightBudget, Nat.cast_add] using
      schwartz_correlation_variation Φ Ψ M M Y Z C D N hY hZ hNY hNZ
  rw [hsum]
  exact (weighted_periodic_linear_shift_long_bound rs.prod F _ (α - β) hA hbound w M N hN).trans
    (mul_le_mul_of_nonneg_right hvar (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_TruncatedQuadraticCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete finite correlation bound after quadratic normalization -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

/-- The normalized large-kernel correlation estimate, with the finite support
pair count and the two smooth scaling bounds made explicit. -/
theorem truncated_quadratic_correlation_bound {ι κ : Type*}
    (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1)
    (W : Finset ι) (V : Finset κ) (u : ι → (ZMod ps.prod)ˣ) (v' : κ → (ZMod qs.prod)ˣ)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α Y : ι → ℝ) (β Z : κ → ℝ)
    (R v C D H : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 < M) (hN : 0 < N)
    (hperiod : rs.prod ^ 2 ≤ N)
    (hY : ∀ w ∈ W, 0 < Y w) (hZ : ∀ z ∈ V, 0 < Z z)
    (hNY : ∀ w ∈ W, (N : ℝ) ≤ C * Y w) (hNZ : ∀ z ∈ V, (N : ℝ) ≤ D * Z z)
    (hcount : (W.card : ℝ) * V.card ≤
      H * R * Real.sqrt ((ps.prod : ℝ) * qs.prod) / ((N : ℝ) * v)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      normalizedDensityWaveSum (densityFourier (primeCRTFunction ps hp hcp f)) W u Φ α Y R v (n + M) *
      conj (normalizedDensityWaveSum (densityFourier (primeCRTFunction qs hq hcq f)) V v' Ψ β Z R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      H * (4 * correlationWeightBudget Φ Ψ C D) *
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let A := (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod
  let B := correlationWeightBudget Φ Ψ C D
  have hA : 0 ≤ A := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact correlationPrimeBound_nonneg _ p
  have hB : 0 ≤ B := by
    have hΦ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := (norm_nonneg _).trans (Φ.norm_le_seminorm ℝ 0)
    have hΨ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Ψ := (norm_nonneg _).trans (Ψ.norm_le_seminorm ℝ 0)
    have hΦ1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ :=
      (norm_nonneg _).trans (Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
    have hΨ1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Ψ :=
      (norm_nonneg _).trans (Ψ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
    dsimp [B, correlationWeightBudget]
    positivity
  have hpR : (0 : ℝ) < ps.prod := by exact_mod_cast prime_list_prod_pos ps hp
  have hqR : (0 : ℝ) < qs.prod := by exact_mod_cast prime_list_prod_pos qs hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpair (w : ι) (hw : w ∈ W) (z : κ) (hz : z ∈ V) :
      ‖∑ n ∈ Finset.range N,
        densityWave (densityFourier (primeCRTFunction ps hp hcp f)) (u w) Φ (α w) (Y w) (n + M) *
        conj (densityWave (densityFourier (primeCRTFunction qs hq hcq f)) (v' z) Ψ (β z) (Z z) (n + M))‖ ≤
          B * (4 * A * N) := by
    exact schwartz_density_correlation_bound ps qs rs hp hq hr hcp hcq hcr hrs (u w) (v' z) f hf
      Φ Ψ (α w) (β z) (Y w) (Z z) C D M N (hY w hw) (hZ z hz) (hNY w hw) (hNZ z hz) hperiod
  have hnorm := normalized_quadratic_pair_bound (Finset.range N) W V
    (fun n => ((n + M : ℕ) : ℝ))
    (fun w n => densityWave (densityFourier (primeCRTFunction ps hp hcp f)) (u w) Φ (α w) (Y w) (n + M))
    (fun z n => densityWave (densityFourier (primeCRTFunction qs hq hcq f)) (v' z) Ψ (β z) (Z z) (n + M))
    R (ps.prod : ℝ) (qs.prod : ℝ) v (B * (4 * A * N)) hR hpR hqR hv
    (fun n _ => by exact_mod_cast (show 0 < n + M by omega)) hpair
  change _ ≤ H * (4 * B) * A
  apply hnorm.trans
  have hc := quadratic_pair_count_cancellation R (ps.prod : ℝ) (qs.prod : ℝ) v N (4 * B) A H
    hR hpR hqR hv hNR (by positivity) hA W.card V.card hcount
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDensitySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's finite quadratic sums and their zero nonunit terms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem unitQuadraticSupport_subset {q : ℕ} (W : Finset ℕ) (a : ZMod q) :
    unitQuadraticSupport W a ⊆ W := by
  intro w hw
  exact (mem_unitQuadraticSupport W a w).mp hw |>.1

theorem quadraticDensityTerm_nonunit {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (hg : ∀ x, ¬IsUnit x → g x = 0) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v : ℝ) (s w : ℕ) (hw : ¬IsUnit (a * (w : ZMod q) ^ 2)) :
    quadraticDensityTerm g a θ Φ R v s w = 0 := by
  have hn : ¬IsUnit (a * (w : ZMod q) ^ 2 * (s : ZMod q)) :=
    fun h => hw (isUnit_of_mul_isUnit_left h)
  simp only [quadraticDensityTerm, hg _ hn, zero_mul]

theorem quadraticDensityTerm_eq_wave {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s w : ℕ)
    (hw : IsUnit (a * (w : ZMod q) ^ 2)) (hw0 : 0 < w) (hR : 0 < R) (hv : 0 < v) :
    quadraticDensityTerm g a θ Φ R v s w =
      densityWave g (quadraticUnitScalar a w) Φ
        (θ * v * (w : ℝ) ^ 2 / q) (R * q / (v * (w : ℝ) ^ 2)) s := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hy : (s : ℝ) / (R * q / (v * (w : ℝ) ^ 2)) =
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by field_simp
  simp only [quadraticDensityTerm, densityWave, quadraticUnitScalar, dite_eq_left hw,
    IsUnit.unit_spec, hy]
  ring

/-- Removing the zero nonunit terms leaves precisely the unit-wave sum to
which the original-density correlation estimate applies. -/
theorem quadraticDensitySum_eq_unit_waves {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (hg : ∀ x, ¬IsUnit x → g x = 0) (W : Finset ℕ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hR : 0 < R) (hv : 0 < v) :
    quadraticDensitySum g W a θ Φ R v s =
      normalizedDensityWaveSum g (unitQuadraticSupport W a) (quadraticUnitScalar a) Φ
        (fun w => θ * v * (w : ℝ) ^ 2 / q) (fun w => R * q / (v * (w : ℝ) ^ 2)) R v s := by
  classical
  unfold quadraticDensitySum normalizedDensityWaveSum
  congr 1
  calc
    _ = ∑ w ∈ unitQuadraticSupport W a, quadraticDensityTerm g a θ Φ R v s w := by
      symm
      apply Finset.sum_subset (unitQuadraticSupport_subset W a)
      intro w hw hn
      have hnu : ¬IsUnit (a * (w : ZMod q) ^ 2) := by
        intro hu
        exact hn ((mem_unitQuadraticSupport W a w).mpr ⟨hw, hu⟩)
      exact quadraticDensityTerm_nonunit g hg a θ Φ R v s w hnu
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hw, hu⟩ := (mem_unitQuadraticSupport W a w).mp hw
      exact quadraticDensityTerm_eq_wave g a θ Φ R v s w hu (hW w hw) hR hv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSupportCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The support-size and scaling bounds for the expanded quadratic sums -/

namespace Ostmann

open scoped BigOperators

theorem quadratic_support_count_le (W : Finset ℕ) (Q : ℝ)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ Q) : (W.card : ℝ) ≤ Real.sqrt Q := by
  have hsub : W ⊆ Finset.Ioc 0 ⌊Real.sqrt Q⌋₊ := by
    intro w hw
    obtain ⟨hw0, hwQ⟩ := hW w hw
    exact Finset.mem_Ioc.mpr ⟨hw0, Nat.le_floor (Real.le_sqrt_of_sq_le hwQ)⟩
  have hc : W.card ≤ ⌊Real.sqrt Q⌋₊ := by
    simpa using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.sqrt_nonneg Q))

theorem quadratic_support_pair_count (W V : Finset ℕ) (R d e v N C : ℝ)
    (hR : 0 < R) (hd : 0 < d) (hv : 0 < v) (hN : 0 < N) (hC : 0 ≤ C)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * d / (N * v))
    (hV : ∀ w ∈ V, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * e / (N * v)) :
    (W.card : ℝ) * V.card ≤ C * R * Real.sqrt (d * e) / (N * v) := by
  have hK : 0 ≤ C * R / (N * v) := by positivity
  calc
    _ ≤ Real.sqrt (C * R * d / (N * v)) * Real.sqrt (C * R * e / (N * v)) :=
      mul_le_mul (quadratic_support_count_le W _ hW) (quadratic_support_count_le V _ hV)
        (by positivity) (Real.sqrt_nonneg _)
    _ = Real.sqrt (((C * R / (N * v)) ^ 2) * (d * e)) := by
      rw [← Real.sqrt_mul (show 0 ≤ C * R * d / (N * v) by positivity)]
      congr 1
      ring
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
      ring

theorem quadratic_support_scale (R d v N C : ℝ) (w : ℕ)
    (hR : 0 < R) (hd : 0 < d) (hv : 0 < v) (hN : 0 < N)
    (hw : 0 < w) (hW : (w : ℝ) ^ 2 ≤ C * R * d / (N * v)) :
    0 < R * d / (v * (w : ℝ) ^ 2) ∧ N ≤ C * (R * d / (v * (w : ℝ) ^ 2)) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  constructor
  · positivity
  · have hh := (le_div_iff₀ (mul_pos hN hv)).mp hW
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < v * (w : ℝ) ^ 2 by positivity)).mpr
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-kernel correlation of the original centered-density quadratic sums -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

/-- This is the finite, explicit form of the manuscript's correlation (src12).
The cutoff hypotheses give both the support pair count and smooth scaling;
all Fourier and nonunit conditions are supplied by the centered densities. -/
theorem quadratic_density_correlation_bound (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W V : Finset ℕ)
    (a : ZMod ps.prod) (b : ZMod qs.prod) (Φ Ψ : 𝓢(ℝ, ℂ))
    (θ η R v C : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C)
    (hM : 0 < M) (hN : 0 < N) (hperiod : rs.prod ^ 2 ≤ N)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * ps.prod / ((N : ℝ) * v))
    (hV : ∀ w ∈ V, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * qs.prod / ((N : ℝ) * v)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      quadraticDensitySum (densityFourier (densityCRTList ps hp hcp S).value) W a θ Φ R v (n + M) *
      conj (quadraticDensitySum (densityFourier (densityCRTList qs hq hcq S).value) V b η Ψ R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      C * (4 * correlationWeightBudget Φ Ψ C C) *
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let f : ∀ p : ℕ, ZMod p → ℂ := fun p x => (centeredDensity (S p) x : ℂ)
  have hfnorm (p : ℕ) (hp' : p ∈ rs) (x : ZMod p) : ‖f p x‖ ≤ 1 := by
    let : NeZero p := ⟨(hr p hp').ne_zero⟩
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le (S p) x
  have hep := densityCRTList_value_eq_primeCRTFunction ps hp hcp S
  have heq := densityCRTList_value_eq_primeCRTFunction qs hq hcq S
  have hgp : ∀ x, ¬IsUnit x → densityFourier (primeCRTFunction ps hp hcp f) x = 0 := by
    rw [← hep]
    exact (densityCRTList ps hp hcp S).fourier_nonunit
  have hgq : ∀ x, ¬IsUnit x → densityFourier (primeCRTFunction qs hq hcq f) x = 0 := by
    rw [← heq]
    exact (densityCRTList qs hq hcq S).fourier_nonunit
  have hpR : (0 : ℝ) < ps.prod := by exact_mod_cast prime_list_prod_pos ps hp
  have hqR : (0 : ℝ) < qs.prod := by exact_mod_cast prime_list_prod_pos qs hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let W' := unitQuadraticSupport W a
  let V' := unitQuadraticSupport V b
  have hW' (w : ℕ) (hw : w ∈ W') :
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * ps.prod / ((N : ℝ) * v) :=
    hW w (((mem_unitQuadraticSupport W a w).mp hw).1)
  have hV' (w : ℕ) (hw : w ∈ V') :
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * qs.prod / ((N : ℝ) * v) :=
    hV w (((mem_unitQuadraticSupport V b w).mp hw).1)
  have hwp (s : ℕ) := quadraticDensitySum_eq_unit_waves
    (densityFourier (primeCRTFunction ps hp hcp f)) hgp W a θ Φ R v s
      (fun w hw => (hW w hw).1) hR hv
  have hwq (s : ℕ) := quadraticDensitySum_eq_unit_waves
    (densityFourier (primeCRTFunction qs hq hcq f)) hgq V b η Ψ R v s
      (fun w hw => (hV w hw).1) hR hv
  rw [hep, heq]
  change ‖∑ n ∈ Finset.range N,
    quadraticDensitySum (densityFourier (primeCRTFunction ps hp hcp f)) W a θ Φ R v (n + M) *
    conj (quadraticDensitySum (densityFourier (primeCRTFunction qs hq hcq f)) V b η Ψ R v (n + M)) /
      ((n + M : ℕ) : ℂ)‖ ≤ _
  simp_rw [hwp, hwq]
  apply truncated_quadratic_correlation_bound ps qs rs hp hq hr hcp hcq hcr hrs f hfnorm
    W' V' (quadraticUnitScalar a) (quadraticUnitScalar b) Φ Ψ
    (fun w => θ * v * (w : ℝ) ^ 2 / ps.prod) (fun w => R * ps.prod / (v * (w : ℝ) ^ 2))
    (fun w => η * v * (w : ℝ) ^ 2 / qs.prod) (fun w => R * qs.prod / (v * (w : ℝ) ^ 2))
    R v C C C M N hR hv hC hC hM hN hperiod
  · intro w hw
    exact (quadratic_support_scale R ps.prod v N C w hR hpR hv hNR (hW' w hw).1 (hW' w hw).2).1
  · intro w hw
    exact (quadratic_support_scale R qs.prod v N C w hR hqR hv hNR (hV' w hw).1 (hV' w hw).2).1
  · intro w hw
    exact (quadratic_support_scale R ps.prod v N C w hR hpR hv hNR (hW' w hw).1 (hW' w hw).2).2
  · intro w hw
    exact (quadratic_support_scale R qs.prod v N C w hR hqR hv hNR (hV' w hw).1 (hV' w hw).2).2
  · exact quadratic_support_pair_count W' V' R ps.prod qs.prod v N C hR hpR hv hNR hC hW' hV'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem support_correlation_product (P U V : Finset ℕ) (hU : U ⊆ P) (hV : V ⊆ P) :
    ((U ∪ V).toList.map (correlationPrimeBound (supportCorrelationSide U V))).prod =
      ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹ := by
  classical
  rw [← List.prod_toFinset _ (U ∪ V).nodup_toList, Finset.toList_toFinset]
  have hsub : U ∪ V ⊆ P := Finset.union_subset hU hV
  have heq : (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹) =
      ∏ p ∈ U ∪ V, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹ := by
    apply (Finset.prod_subset hsub _).symm
    intro p hp hnot
    have hu : p ∉ U := fun hh => hnot (Finset.mem_union_left V hh)
    have hv : p ∉ V := fun hh => hnot (Finset.mem_union_right U hh)
    simp [hu, hv]
  rw [heq]
  apply Finset.prod_congr rfl
  intro p hp
  have hm := Finset.mem_union.mp hp
  unfold supportCorrelationSide correlationPrimeBound
  rcases hm with hu | hv
  · by_cases hv : p ∈ V <;> simp [hu, hv]
  · by_cases hu : p ∈ U <;> simp [hu, hv]

theorem primeSet_prod_le_of_subset (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) : U.toList.prod ≤ P.toList.prod := by
  have he (Q : Finset ℕ) : Q.toList.prod = ∏ p ∈ Q, p := by
    simp
  rw [he, he]
  exact Finset.prod_le_prod_of_subset_of_one_le hU (fun _ _ => Nat.zero_le _)
    (fun p hp _ => (hP p hp).one_lt.le)

theorem primeSet_prod_dvd_of_subset (P U : Finset ℕ) (hU : U ⊆ P) :
    U.toList.prod ∣ P.toList.prod := by
  simpa using Finset.prod_dvd_prod_of_subset U P (fun p : ℕ => p) hU

theorem primeSetQuadraticSum_eq_unit_waves (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ)
    (a : ZMod U.toList.prod) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hR : 0 < R) (hv : 0 < v) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hU)).ne'⟩
    primeSetQuadraticSum U hU S W a θ Φ R v s =
      normalizedDensityWaveSum
        (densityFourier (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) S).value)
        (unitQuadraticSupport W a) (quadraticUnitScalar a) Φ
        (fun w => θ * v * (w : ℝ) ^ 2 / U.toList.prod)
        (fun w => R * U.toList.prod / (v * (w : ℝ) ^ 2)) R v s := by
  intro _
  exact quadraticDensitySum_eq_unit_waves _
    (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) S).fourier_nonunit
    W a θ Φ R v s hW hR hv

/-- The pair bound for actual prime-divisor sums, with the common modulus
and exclusive-prime factor obtained from their prime sets. -/
theorem primeSet_quadratic_correlation (P U V : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) (hV : V ⊆ P)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W Vw : Finset ℕ)
    (a : ZMod U.toList.prod) (b : ZMod V.toList.prod) (Φ Ψ : 𝓢(ℝ, ℂ))
    (θ η R v C : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C)
    (hM : 0 < M) (hN : 0 < N) (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * U.toList.prod / ((N : ℝ) * v))
    (hVw : ∀ w ∈ Vw, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * V.toList.prod / ((N : ℝ) * v)) :
    ‖∑ n ∈ Finset.range N,
      primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S W a θ Φ R v (n + M) *
      conj (primeSetQuadraticSum V (fun p hp => hP p (hV hp)) S Vw b η Ψ R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      C * (4 * correlationWeightBudget Φ Ψ C C) *
        ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
  have hUV : U ∪ V ⊆ P := Finset.union_subset hU hV
  have hpU : ∀ p ∈ U, p.Prime := fun p hp => hP p (hU hp)
  have hpV : ∀ p ∈ V, p.Prime := fun p hp => hP p (hV hp)
  have hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp => hP p (hUV hp)
  have hb := quadratic_density_correlation_bound U.toList V.toList (U ∪ V).toList
    (primeSet_list_prime U hpU) (primeSet_list_prime V hpV) (primeSet_list_prime _ hpUV)
    (primeSet_list_coprime U hpU) (primeSet_list_coprime V hpV) (primeSet_list_coprime _ hpUV)
    (by simp) S W Vw a b Φ Ψ θ η R v C M N hR hv hC hM hN
    ((Nat.pow_le_pow_left (primeSet_prod_le_of_subset P (U ∪ V) hP hUV) 2).trans hperiod) hW hVw
  simpa only [primeSetQuadraticSum, Finset.toList_toFinset,
    support_correlation_product P U V hU hV] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCorrelationMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute residue mass of the actual density correlations -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_sum_le_of_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : (∑ x : ZMod q, ‖f x‖ ^ 2) ≤ q) :
    (∑ x : ZMod q, ‖f x‖) ≤ q := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at hc
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hh := mul_le_mul_of_nonneg_right hf hq
  have hs : 0 ≤ ∑ x : ZMod q, ‖f x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem norm_product_sum_le_of_energy {q : ℕ} [NeZero q] (f g : ZMod q → ℂ)
    (hf : (∑ x : ZMod q, ‖f x‖ ^ 2) ≤ q)
    (hg : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q) :
    (∑ x : ZMod q, ‖f x * conj (g x)‖) ≤ q := by
  simp only [norm_mul, Complex.norm_conj]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun x => ‖g x‖)
  have hh := mul_le_mul hf hg (by positivity) (Nat.cast_nonneg q)
  have hs : 0 ≤ ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith

theorem correlationPrimeFactor_mass (p : ℕ) [NeZero p]
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) :
    (∑ x : ZMod p, ‖correlationPrimeFactor f side a b p x‖) ≤ p := by
  have ha : (∑ x : ZMod p, ‖densityFourier (f p) ((a p : ZMod p) * x)‖ ^ 2) ≤ p := by
    rw [unit_dilation_energy]
    exact densityFourier_energy_le _ hf
  have hb : (∑ x : ZMod p, ‖densityFourier (f p) ((b p : ZMod p) * x)‖ ^ 2) ≤ p := by
    rw [unit_dilation_energy]
    exact densityFourier_energy_le _ hf
  simp only [correlationPrimeFactor, primeDensityFourier_eq]
  cases side p with
  | left => exact norm_sum_le_of_energy _ ha
  | right => simpa only [Complex.norm_conj] using norm_sum_le_of_energy _ hb
  | both => exact norm_product_sum_le_of_energy _ _ ha hb

theorem primeCRTFunction_mass (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ)
    (hF : ∀ p (h : p ∈ ps), let : NeZero p := ⟨(hp p h).ne_zero⟩;
      (∑ x : ZMod p, ‖F p x‖) ≤ p) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ x : ZMod ps.prod, ‖primeCRTFunction ps hp hc F x‖) ≤ ps.prod := by
  induction ps with
  | nil =>
    intro _
    simp only [primeCRTFunction, norm_one, Finset.sum_const, nsmul_eq_mul,
      mul_one, List.prod_nil, Nat.cast_one]
    have hcard : (Finset.univ : Finset (ZMod ([] : List ℕ).prod)).card = 1 := by
      rw [Finset.card_univ, ZMod.card, List.prod_nil]
    exact_mod_cast hcard.le
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    intro _
    let e := ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    change (∑ x : ZMod (p * ps.prod), ‖F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2‖) ≤ _
    rw [← e.symm.bijective.sum_comp (fun x =>
      ‖F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2‖)]
    simp only [e.apply_symm_apply]
    simp only [Fintype.sum_prod_type, norm_mul]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have ht := ih hp' hcp.2 (fun q hq => hF q (List.mem_cons_of_mem p hq))
    simpa only [List.prod_cons, Nat.cast_mul] using
      mul_le_mul (hF p List.mem_cons_self) ht (by positivity) (Nat.cast_nonneg p)

/-- The original two density transforms have a common periodic model whose
absolute mass is at most one after probability normalization. -/
theorem primeSet_density_correlation_mass_model (U V : Finset ℕ)
    (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p))
    (vp : (ZMod U.toList.prod)ˣ) (vq : (ZMod V.toList.prod)ˣ) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
    let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
    ∃ F : ZMod (U ∪ V).toList.prod → ℂ,
      (∀ n : ℤ,
        densityFourier (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) S).value
          ((vp : ZMod U.toList.prod) * (n : ZMod U.toList.prod)) *
        conj (densityFourier (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) S).value
          ((vq : ZMod V.toList.prod) * (n : ZMod V.toList.prod))) = F (n : ZMod (U ∪ V).toList.prod)) ∧
      (let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _
        (primeSet_list_prime (U ∪ V) (fun p hp => (Finset.mem_union.mp hp).elim (hpU p) (hpV p)))).ne'⟩
       (∑ x : ZMod (U ∪ V).toList.prod, ‖F x‖) ≤ (U ∪ V).toList.prod) := by
  intro _ _
  let hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp =>
    (Finset.mem_union.mp hp).elim (hpU p) (hpV p)
  let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime _ hpUV)).ne'⟩
  let f : ∀ p : ℕ, ZMod p → ℂ := fun p x => (centeredDensity (S p) x : ℂ)
  obtain ⟨a, ha⟩ := densityFourier_centered_unit_product U.toList
    (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) S vp
  obtain ⟨b, hb⟩ := densityFourier_centered_unit_product V.toList
    (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) S vq
  refine ⟨primeCRTFunction (U ∪ V).toList (primeSet_list_prime _ hpUV)
    (primeSet_list_coprime _ hpUV) (correlationPrimeFactor f (supportCorrelationSide U V) a b), ?_, ?_⟩
  · intro n
    rw [ha, hb, primeCRTFunction_intCast,
      ← List.prod_toFinset _ U.nodup_toList,
      ← List.prod_toFinset _ V.nodup_toList,
      ← List.prod_toFinset _ (U ∪ V).nodup_toList]
    simp only [Finset.toList_toFinset]
    exact (local_correlation_product U V (U ∪ V) rfl f a b n).symm
  · apply primeCRTFunction_mass
    intro p hp
    let : NeZero p := ⟨(primeSet_list_prime _ hpUV p hp).ne_zero⟩
    apply correlationPrimeFactor_mass
    intro x
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le (S p) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightPeriodicMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the high-weight bound against the actual periodic residue mass -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_high_weight_periodic_mass (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (N L : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < L → 2 * L ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, L.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ [NeZero L] (F : ZMod L → ℂ), (∑ x : ZMod L, ‖F x‖) ≤ L →
        (∑ s ∈ S, u ^ s.primeFactors.card * ‖F (s : ZMod L)‖) ≤
          N * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  classical
  filter_upwards [eventual_high_weight_residue_mass C] with T hT N L S u hL hsize hcut
    hS hrange hcop hu huU hhigh inst F hF
  have hmaps (s : ℕ) (_hs : s ∈ S) : (s : ZMod L) ∈ (Finset.univ : Finset (ZMod L)) :=
    Finset.mem_univ _
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let E := Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))
  calc
    _ = ∑ x : ZMod L, (∑ s ∈ S.filter (fun s : ℕ => (s : ZMod L) = x), u ^ s.primeFactors.card) * ‖F x‖ := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ ≤ ∑ x : ZMod L, (((N : ℝ) / L) * E) * ‖F x‖ := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply hT N L x.val (S.filter (fun s => (s : ZMod L) = x)) u hL hsize hcut
      · intro s hs; exact hS s (Finset.mem_filter.mp hs).1
      · intro s hs; exact hrange s (Finset.mem_filter.mp hs).1
      · intro s hs
        apply (ZMod.natCast_eq_natCast_iff s x.val L).mp
        exact (Finset.mem_filter.mp hs).2.trans (ZMod.natCast_zmod_val x).symm
      · intro s hs; exact hcop s (Finset.mem_filter.mp hs).1
      · exact hu
      · exact huU
      · intro s hs; exact hhigh s (Finset.mem_filter.mp hs).1
    _ = (((N : ℝ) / L) * E) * ∑ x : ZMod L, ‖F x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (((N : ℝ) / L) * E) * L := mul_le_mul_of_nonneg_left hF (by positivity)
    _ = (N : ℝ) * E := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_HighWeightDensityWave
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-weight decay for the original smoothed density waves -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem densityWave_pair_norm_le {p q : ℕ} [NeZero p] [NeZero q]
    (g : ZMod p → ℂ) (h : ZMod q → ℂ) (a : (ZMod p)ˣ) (b : (ZMod q)ˣ)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z : ℝ) (n : ℕ) :
    ‖densityWave g a Φ α Y n * conj (densityWave h b Ψ β Z n)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
        ‖g ((a : ZMod p) * n) * conj (h ((b : ZMod q) * n))‖ := by
  simp only [densityWave, norm_mul, Complex.norm_conj, norm_pow,
    norm_realAdditivePhase, one_pow, mul_one]
  calc
    _ = (‖Φ ((n : ℝ) / Y)‖ * ‖Ψ ((n : ℝ) / Z)‖) *
        (‖g ((a : ZMod p) * n)‖ * ‖h ((b : ZMod q) * n)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (Φ.norm_le_seminorm ℝ _) (Ψ.norm_le_seminorm ℝ _)
        (norm_nonneg _) (by positivity)) (by positivity)

theorem eventual_high_weight_density_wave (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (a : (ZMod U.toList.prod)ˣ) (b : (ZMod V.toList.prod)ˣ)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z : ℝ),
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
      let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (densityWave (densityFourier
          (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value)
          a Φ α Y s *
        conj (densityWave (densityFourier
          (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value)
          b Ψ β Z s))‖ ≤
        (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          (N * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))) := by
  filter_upwards [eventual_high_weight_periodic_mass C] with T hT
  intro U V hpU hpV N S u hsize hcut hS hrange hcop hu huU hhigh D a b Φ Ψ α β Y Z _ _
  let hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp =>
    (Finset.mem_union.mp hp).elim (hpU p) (hpV p)
  let : NeZero (U ∪ V).toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime _ hpUV)).ne'⟩
  let g := densityFourier
    (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value
  let h := densityFourier
    (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value
  obtain ⟨F, hF, hmass⟩ := primeSet_density_correlation_mass_model U V hpU hpV D a b
  have he (s : ℕ) : g ((a : ZMod U.toList.prod) * s) *
      conj (h ((b : ZMod V.toList.prod) * s)) = F (s : ZMod (U ∪ V).toList.prod) := by
    simpa only [Int.cast_natCast] using hF (s : ℤ)
  have hdecay := hT N (U ∪ V).toList.prod S u (prime_list_prod_pos _ (primeSet_list_prime _ hpUV))
    hsize hcut hS hrange hcop hu huU hhigh F hmass
  have hu0 : 0 ≤ u := by linarith
  let B := SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ
  change ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
    (densityWave g a Φ α Y s * conj (densityWave h b Ψ β Z s))‖ ≤ _
  calc
    _ ≤ ∑ s ∈ S, ‖(u ^ s.primeFactors.card : ℂ) *
        (densityWave g a Φ α Y s * conj (densityWave h b Ψ β Z s))‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ S, u ^ s.primeFactors.card * (B * ‖F (s : ZMod (U ∪ V).toList.prod)‖) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [he, B] using densityWave_pair_norm_le g h a b Φ Ψ α β Y Z s
    _ = B * ∑ s ∈ S, u ^ s.primeFactors.card * ‖F (s : ZMod (U ∪ V).toList.prod)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by dsimp [B]; positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightQuadraticWaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-weight correlations after the quadratic normalization and pair count -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_quadratic_waves (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ {ι κ : Type*} (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ι) (W' : Finset κ)
        (a : ι → (ZMod U.toList.prod)ˣ) (b : κ → (ZMod V.toList.prod)ˣ)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (α Y : ι → ℝ) (β Z : κ → ℝ) (R v H : ℝ),
      0 < R → 0 < v →
      (W.card : ℝ) * W'.card ≤ H * R * Real.sqrt ((U.toList.prod : ℝ) * V.toList.prod) / ((N : ℝ) * v) →
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
      let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (normalizedDensityWaveSum (densityFourier
          (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value)
          W a Φ α Y R v s *
        conj (normalizedDensityWaveSum (densityFourier
          (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value)
          W' b Ψ β Z R v s) / (s : ℂ))‖ ≤
        H * (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_density_wave C] with T hT
  intro U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh ι κ D W W' a b
    Φ Ψ α Y β Z R v H hR hv hcount _ _
  let g := densityFourier
    (densityCRTList U.toList (primeSet_list_prime U hpU) (primeSet_list_coprime U hpU) D).value
  let h := densityFourier
    (densityCRTList V.toList (primeSet_list_prime V hpV) (primeSet_list_coprime V hpV) D).value
  let B := SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ
  let E := Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))
  have hpair (w : ι) (_hw : w ∈ W) (z : κ) (_hz : z ∈ W') :
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (densityWave g (a w) Φ (α w) (Y w) s *
          conj (densityWave h (b z) Ψ (β z) (Z z) s))‖ ≤ B * ((N : ℝ) * E) :=
    hT U V hpU hpV N S u hsize hcut hS hrange hcop hu huU hhigh D (a w) (b z)
      Φ Ψ (α w) (β z) (Y w) (Z z)
  have hd : (0 : ℝ) < U.toList.prod := by
    exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime U hpU)
  have he : (0 : ℝ) < V.toList.prod := by
    exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime V hpV)
  have hn := weighted_normalized_quadratic_pair_bound S W W' (fun s => (s : ℝ))
    (fun s => (u ^ s.primeFactors.card : ℂ))
    (fun w s => densityWave g (a w) Φ (α w) (Y w) s)
    (fun z s => densityWave h (b z) Ψ (β z) (Z z) s)
    R U.toList.prod V.toList.prod v (B * ((N : ℝ) * E)) hR hd he hv
    (by intro s hs; exact_mod_cast lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp (hrange s hs)).1) hpair
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  change _ ≤ H * B * E
  apply hn.trans
  have hc := quadratic_pair_count_cancellation R U.toList.prod V.toList.prod v N B E H
    hR hd he hv hNR (by dsimp [B]; positivity) (by dsimp [E]; positivity) W.card W'.card hcount
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightPrimeSet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # High-weight correlation of the original prime-divisor quadratic sums -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_primeSet_correlation (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W W' : Finset ℕ)
        (a : ZMod U.toList.prod) (b : ZMod V.toList.prod)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (θ η R v H : ℝ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ w ∈ W', 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * V.toList.prod / ((N : ℝ) * v)) →
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (primeSetQuadraticSum U hpU D W a θ Φ R v s *
          conj (primeSetQuadraticSum V hpV D W' b η Ψ R v s) / (s : ℂ))‖ ≤
        H * (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_quadratic_waves C₀] with T hT
  intro U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh D W W' a b
    Φ Ψ θ η R v H hR hv hH hW hW'
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
  let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
  have heU (s : ℕ) := primeSetQuadraticSum_eq_unit_waves U hpU D W a θ Φ R v s
    (fun w hw => (hW w hw).1) hR hv
  have heV (s : ℕ) := primeSetQuadraticSum_eq_unit_waves V hpV D W' b η Ψ R v s
    (fun w hw => (hW' w hw).1) hR hv
  simp_rw [heU, heV]
  apply hT U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh D
    (unitQuadraticSupport W a) (unitQuadraticSupport W' b)
    (quadraticUnitScalar a) (quadraticUnitScalar b) Φ Ψ
    (fun w => θ * v * (w : ℝ) ^ 2 / U.toList.prod)
    (fun w => R * U.toList.prod / (v * (w : ℝ) ^ 2))
    (fun w => η * v * (w : ℝ) ^ 2 / V.toList.prod)
    (fun w => R * V.toList.prod / (v * (w : ℝ) ^ 2)) R v H hR hv
  exact quadratic_support_pair_count _ _ R U.toList.prod V.toList.prod v N H hR
    (by exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime U hpU)) hv
    (by exact_mod_cast hN) hH
    (fun w hw => hW w (unitQuadraticSupport_subset W a hw))
    (fun w hw => hW' w (unitQuadraticSupport_subset W' b hw))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The low-weight coefficient energy of the actual divisor sums -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeDivisorQuadratic_pair (P U V : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) (hV : V ⊆ P)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v C : ℝ) (M N : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ Q ⊆ P, ∀ w ∈ W Q,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * Q.toList.prod / ((N : ℝ) * v)) :
    ‖∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ) : ℂ) *
      (primeDivisorQuadratic P hP S W a θ Φ R v U (n + M) *
        conj (primeDivisorQuadratic P hP S W a θ Φ R v V (n + M)))‖ ≤
      C * (4 * correlationWeightBudget Φ Φ C C) *
        ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
  have hb := primeSet_quadratic_correlation P U V hP hU hV S (W U) (W V)
    (a U) (a V) Φ Φ (θ U) (θ V) R v C M N hR hv hC hM hN hperiod (hW U hU) (hW V hV)
  have heq : (∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ) : ℂ) *
      (primeDivisorQuadratic P hP S W a θ Φ R v U (n + M) *
        conj (primeDivisorQuadratic P hP S W a θ Φ R v V (n + M)))) =
      ∑ n ∈ Finset.range N,
        primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S (W U) (a U) (θ U) Φ R v (n + M) *
        conj (primeSetQuadraticSum V (fun p hp => hP p (hV hp)) S (W V) (a V) (θ V) Φ R v (n + M)) /
          ((n + M : ℕ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [primeDivisorQuadratic, dite_eq_left hU, dite_eq_left hV,
      Complex.ofReal_natCast]
    ring
  rw [heq]
  exact hb

/-- The unweighted coefficient-energy bound obtained from double-divisor
correlations for the quadratic family. -/
theorem primeDivisor_quadratic_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v C lam : ℝ) (M N : ℕ) (c : Finset ℕ → ℂ)
    (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hM : 0 < M) (hN : 0 < N) (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ Q ⊆ P, ∀ w ∈ W Q,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * Q.toList.prod / ((N : ℝ) * v))
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card) :
    (∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP S W a θ Φ R v U (n + M)‖ ^ 2) ≤
      (C * (4 * correlationWeightBudget Φ Φ C C)) *
        ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * (Real.sqrt (p : ℝ))⁻¹) := by
  refine divisor_combination_energy_bound (Finset.range N) P
    (fun n => 1 / ((n + M : ℕ) : ℝ)) c
    (fun U n => primeDivisorQuadratic P hP S W a θ Φ R v U (n + M))
    lam (C * (4 * correlationWeightBudget Φ Φ C C)) hlam ?_ hc ?_
  · unfold correlationWeightBudget
    positivity
  · intro U hU V hV
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using
      primeDivisorQuadratic_pair P U V hP (Finset.mem_powerset.mp hU)
      (Finset.mem_powerset.mp hV) S W a θ Φ R v C M N hR hv hC hM hN hperiod hW

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HighWeightDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentially small high-weight energy of the actual divisor expansion -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_divisor_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * P.toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C₀ * T) →
      (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ U ⊆ P, ∀ w ∈ W U, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s‖ ^ 2) ≤
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) *
          Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_primeSet_correlation C₀,
    eventually_ge_atTop (1 : ℝ)] with T hT hT1
  intro P hP N S u hN hsize hcut hcard hS hrange hcop hu huU hhigh D W a θ Φ R v H c
    hR hv hH hW hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let B := H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpair (U : Finset ℕ) (hU : U ∈ P.powerset) (V : Finset ℕ) (hV : V ∈ P.powerset) :
      ‖∑ s ∈ S, ((u ^ s.primeFactors.card / (s : ℝ) : ℝ) : ℂ) *
        (primeDivisorQuadratic P hP D W a θ Φ R v U s *
          conj (primeDivisorQuadratic P hP D W a θ Φ R v V s))‖ ≤ B * Real.exp (-10 * K) := by
    have hUP := Finset.mem_powerset.mp hU
    have hVP := Finset.mem_powerset.mp hV
    have hUV : U ∪ V ⊆ P := Finset.union_subset hUP hVP
    have hbound := hT U V (fun p hp => hP p (hUP hp)) (fun p hp => hP p (hVP hp))
      N S u hN
      ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (primeSet_prod_le_of_subset P (U ∪ V) hP hUV) 2)).trans hsize)
      hcut hS hrange (fun s hs => (hcop s hs).of_dvd_left (primeSet_prod_dvd_of_subset P (U ∪ V) hUV))
      hu huU hhigh D (W U) (W V) (a U) (a V) Φ Φ (θ U) (θ V) R v H hR hv hH
      (hW U hUP) (hW V hVP)
    have heq : (∑ s ∈ S, ((u ^ s.primeFactors.card / (s : ℝ) : ℝ) : ℂ) *
        (primeDivisorQuadratic P hP D W a θ Φ R v U s *
          conj (primeDivisorQuadratic P hP D W a θ Φ R v V s))) =
        ∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
          (primeSetQuadraticSum U (fun p hp => hP p (hUP hp)) D (W U) (a U) (θ U) Φ R v s *
          conj (primeSetQuadraticSum V (fun p hp => hP p (hVP hp)) D (W V) (a V) (θ V) Φ R v s) / (s : ℂ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [primeDivisorQuadratic, dite_eq_left hUP, dite_eq_left hVP,
        Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
      ring
    rw [heq]
    simpa only [B, K, pow_two] using hbound
  have he := uniform_divisor_combination_energy_bound S P
    (fun s => u ^ s.primeFactors.card / (s : ℝ)) c (primeDivisorQuadratic P hP D W a θ Φ R v)
    (1 / 16) (B * Real.exp (-10 * K)) (by norm_num) (by positivity) hc hpair
  have hpow : (1 + (1 / 16 : ℝ)) ^ (2 * P.card) ≤ Real.exp K := by
    calc
      _ ≤ (Real.exp (1 / 16 : ℝ)) ^ (2 * P.card) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 / 16 : ℝ)]) _
      _ = Real.exp ((P.card : ℝ) / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hK : 0 ≤ K := by dsimp [K]; positivity
        dsimp [K] at hK ⊢
        linarith)
  calc
    _ ≤ _ := he
    _ ≤ (B * Real.exp (-10 * K)) * Real.exp K := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = B * Real.exp (-9 * K) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DyadicDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the low and high weights on an actual dyadic kernel segment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sum_Ioc_dyadic (N : ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ Finset.Ioc N (2 * N), f s) = ∑ n ∈ Finset.range N, f (n + (N + 1)) := by
  rw [← Finset.Ico_succ_succ_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  change (∑ k ∈ Finset.range ((2 * N + 1) - (N + 1)), f ((N + 1) + k)) = _
  have he : (2 * N + 1) - (N + 1) = N := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  omega

theorem eventual_dyadic_divisor_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ U ⊆ P, ∀ w ∈ W U, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s‖ ^ 2) ≤
        (H * (4 * correlationWeightBudget Φ Φ H H)) * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  classical
  filter_upwards [eventual_high_weight_divisor_energy C₀] with T hT
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D W a θ Φ R v H c hR hv hH hW hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let G := fun s => ∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s
  let E := fun s : ℕ => (u ^ s.primeFactors.card / (s : ℝ)) * ‖G s‖ ^ 2
  let low := fun s : ℕ => u ^ s.primeFactors.card ≤ Real.exp (K / 200)
  let B := H * (4 * correlationWeightBudget Φ Φ H H)
  have hB : 0 ≤ B := by dsimp [B, correlationWeightBudget]; positivity
  have hlo : (∑ s ∈ S.filter low, E s) ≤ B * Real.exp (3 * K / 250) := by
    have hbase := primeDivisor_quadratic_energy P hP D W a θ Φ R v H (1 / 16) (N + 1) N c
      hR hv hH (by norm_num) (by omega) hN (by omega) hW hc
    have hfull : (∑ s ∈ Finset.Ioc N (2 * N), (1 / (s : ℝ)) * ‖G s‖ ^ 2) ≤
        B * ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹) := by
      rw [sum_Ioc_dyadic]
      exact hbase
    calc
      _ ≤ ∑ s ∈ S.filter low, Real.exp (K / 200) * ((1 / (s : ℝ)) * ‖G s‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro s hs
        have hh := mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hs).2
          (show 0 ≤ (1 / (s : ℝ)) * ‖G s‖ ^ 2 by positivity)
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [E]
        ring
      _ ≤ Real.exp (K / 200) * ∑ s ∈ Finset.Ioc N (2 * N), (1 / (s : ℝ)) * ‖G s‖ ^ 2 := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun s hs => hrange s (Finset.mem_filter.mp hs).1) (fun _ _ _ => by positivity)
      _ ≤ Real.exp (K / 200) * (B * ∏ p ∈ P,
          (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hfull (Real.exp_nonneg _)
      _ = B * (Real.exp (K / 200) * ∏ p ∈ P,
          (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (low_weight_euler_bound_scale P hlarge K hcard) hB
  have hhi : (∑ s ∈ S.filter (fun s => ¬low s), E s) ≤
      (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * K) := by
    exact hT P hP N (S.filter (fun s => ¬low s)) u hN hsize hcut hcard
      (fun s hs => hS s (Finset.mem_filter.mp hs).1)
      (fun s hs => hrange s (Finset.mem_filter.mp hs).1)
      (fun s hs => hcop s (Finset.mem_filter.mp hs).1) hu huU
      (fun s hs => lt_of_not_ge (Finset.mem_filter.mp hs).2) D W a θ Φ R v H c hR hv hH hW hc
  change (∑ s ∈ S, E s) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S low E]
  exact add_le_add hlo hhi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCompactCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite cutoffs for compactly supported quadratic transforms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticCompactCutoff_spec (q : ℕ) (R v C : ℝ) (N : ℕ)
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hC : 0 ≤ C) :
    ∀ w ∈ quadraticCompactCutoff q R v C N,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
  intro w hw
  obtain ⟨hw0, hw⟩ := Finset.mem_Ioc.mp hw
  refine ⟨hw0, ?_⟩
  have hQ : 0 ≤ C * R * q / ((N : ℝ) * v) := by positivity
  have hle : (w : ℝ) ≤ Real.sqrt (C * R * q / ((N : ℝ) * v)) :=
    (Nat.cast_le.mpr hw).trans (Nat.floor_le (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg (C * R * q / ((N : ℝ) * v)), (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]

theorem quadraticDensityTerm_mem_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s w : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hw : 0 < w) (hΦ : ∀ x : ℝ, C < x → Φ x = 0)
    (hne : quadraticDensityTerm g a θ Φ R v s w ≠ 0) :
    w ∈ quadraticCompactCutoff q R v C N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (N : ℝ) ≤ s := Nat.cast_le.mpr hs
  have hsupport : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) ≤ C := by
    by_contra hh
    have hz := hΦ _ (lt_of_not_ge hh)
    exact hne (by simp only [quadraticDensityTerm, hz, mul_zero])
  have hb : (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
    apply (le_div_iff₀ (mul_pos hNR hv)).mpr
    have hh := (div_le_iff₀ (mul_pos hR hq)).mp hsupport
    have hm := mul_le_mul_of_nonneg_right hsR (show 0 ≤ v * (w : ℝ) ^ 2 by positivity)
    nlinarith only [hh, hm]
  exact Finset.mem_Ioc.mpr ⟨hw, Nat.le_floor (Real.le_sqrt_of_sq_le hb)⟩

/-- Compact support makes the positive quadratic series exactly finite,
with one common cutoff for every index in the dyadic segment. -/
theorem positiveQuadraticSum_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hΦ : ∀ x : ℝ, C < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q R v C N) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q R v C N,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticDensityTerm_mem_cutoff g a θ Φ R v C N s w hR hv hN hs hw0 hΦ hn)
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy of the original positive quadratic series on a dyadic segment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem primeDivisorPositive_eq_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (N s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hN : 0 < N) (hs : N ≤ s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (U : Finset ℕ) :
    primeDivisorPositive P hP D a θ Φ R v U s =
      primeDivisorQuadratic P hP D (fun U => quadraticCompactCutoff U.toList.prod R v H N)
        a θ Φ R v U s := by
  classical
  by_cases hU : U ⊆ P
  · let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))).ne'⟩
    simp only [primeDivisorPositive, primeDivisorQuadratic, dite_eq_left hU, primeSetQuadraticSum]
    exact positiveQuadraticSum_eq_cutoff _ _ _ _ _ _ _ _ _ hR hv hN hs hΦ
  · simp only [primeDivisorPositive, primeDivisorQuadratic, dite_eq_right hU]

theorem eventual_dyadic_positive_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H → (∀ x : ℝ, H < x → Φ x = 0) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        (H * (4 * correlationWeightBudget Φ Φ H H)) * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_dyadic_divisor_energy C₀] with T hT
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D a θ Φ R v H c
    hR hv hH hΦ hc
  have he (s : ℕ) (hs : s ∈ S) (U : Finset ℕ) :
      primeDivisorPositive P hP D a θ Φ R v U s =
      primeDivisorQuadratic P hP D (fun U => quadraticCompactCutoff U.toList.prod R v H N)
        a θ Φ R v U s :=
    primeDivisorPositive_eq_cutoff P hP D a θ Φ R v H N s hR hv hN
      (Finset.mem_Ioc.mp (hrange s hs)).1.le hΦ U
  have heSum : (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) =
      ∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D
        (fun U => quadraticCompactCutoff U.toList.prod R v H N) a θ Φ R v U s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [he s hs]
  rw [heSum]
  apply hT P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D
    (fun U => quadraticCompactCutoff U.toList.prod R v H N) a θ Φ R v H c hR hv hH _ hc
  intro U _
  exact quadraticCompactCutoff_spec U.toList.prod R v H N hR.le hv.le hH

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEnergyExponent
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical .006 exponent after the low/high energy split -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_quadratic_energy_exponent (A B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      Real.sqrt (A * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        B * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ))) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hk := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9999999 / 10000000)).eventually_ge_atTop
    ((A + B) / (2 * ε))
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with T hbound hT
  let K := T ^ (9999999 / 10000000 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc : A + B ≤ Real.exp (2 * ε * K) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp hbound
    have he := Real.add_one_le_exp (2 * ε * K)
    dsimp [K]
    nlinarith
  have hd : Real.exp (-9 * K) ≤ Real.exp (3 * K / 250) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum : A * Real.exp (3 * K / 250) + B * Real.exp (-9 * K) ≤
      Real.exp (2 * (3 / 500 + ε) * K) := by
    calc
      _ ≤ (A + B) * Real.exp (3 * K / 250) := by
        have hh := mul_le_mul_of_nonneg_left hd hB
        nlinarith only [hh]
      _ ≤ Real.exp (2 * ε * K) * Real.exp (3 * K / 250) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.sqrt_le_sqrt hsum).trans_eq
  rw [← Real.exp_half]
  congr 1
  ring

theorem eventual_dyadic_positive_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hnum := eventual_quadratic_energy_exponent
    (H * (4 * correlationWeightBudget Φ Φ H H))
    (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) ε (by positivity) hε
  filter_upwards [eventual_dyadic_positive_energy C₀, hnum] with T hT hn
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D a θ R v c hR hv hc
  exact (Real.sqrt_le_sqrt (hT P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU
    D a θ Φ R v H c hR hv hH hΦ hc)).trans hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DyadicKernelShells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite dyadic decomposition of the large squarefree kernels -/

namespace Ostmann

open scoped BigOperators

theorem dyadicKernelShell_mem (s : ℕ) (hs : 2 ≤ s) :
    s ∈ Finset.Ioc (2 ^ dyadicKernelShell s) (2 * 2 ^ dyadicKernelShell s) := by
  have hlo := Nat.pow_log_le_self 2 (show s - 1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (s - 1)
  rw [pow_succ] at hhi
  exact Finset.mem_Ioc.mpr ⟨by dsimp [dyadicKernelShell]; omega,
    by dsimp [dyadicKernelShell]; omega⟩

theorem dyadicKernelShell_le (s M : ℕ) (hs : s ≤ M) :
    dyadicKernelShell s ≤ Nat.log 2 M :=
  Nat.log_mono_right ((Nat.sub_le s 1).trans hs)

theorem dyadicKernelShell_modulus (L s : ℕ) (hs : 4 * L ^ 2 ≤ s) (hs2 : 2 ≤ s) :
    2 * L ^ 2 ≤ 2 ^ dyadicKernelShell s := by
  have hh := (Finset.mem_Ioc.mp (dyadicKernelShell_mem s hs2)).2
  omega

theorem sum_dyadicKernelShells (S : Finset ℕ) (M : ℕ) (hS : ∀ s ∈ S, s ≤ M)
    (f : ℕ → ℝ) :
    (∑ s ∈ S, f s) = ∑ j ∈ Finset.range (Nat.log 2 M + 1),
      ∑ s ∈ S.filter (fun s => dyadicKernelShell s = j), f s := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadicKernelShell_le s M (hS s hs)))) f).symm

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

theorem eventual_dyadic_shell_budget (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ M : ℕ, (M : ℝ) ≤ Real.exp (C * T) →
      (Nat.log 2 M + 1 : ℝ) ≤ Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) := by
  let D := 2 + C / Real.log 2
  have hD : 1 ≤ D := by
    have : 0 ≤ C / Real.log 2 := div_nonneg hC (Real.log_pos (by norm_num)).le
    dsimp [D]
    linarith
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hκ : (0 : ℝ) < 9999999 / 10000000 := by norm_num
  have hl := (isLittleO_log_rpow_atTop hκ).bound (show 0 < ε / 2 by positivity)
  have hp := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * Real.log D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT M hM
  apply (dyadic_shell_count_bound C T hC hT M hM).trans
  apply (Real.log_le_iff_le_exp (mul_pos hD0 (by linarith))).mp
  rw [Real.log_mul hD0.ne' (by linarith : T ≠ 0)]
  have hh : Real.log T ≤ ε / 2 * T ^ (9999999 / 10000000 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) _)] using hlog
  have hc := (div_le_iff₀ hε).mp hpow
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LargeKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-kernel norm of the original positive quadratic series -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

/-- The `.006 + o(1)` bound over the full large-kernel range. The coefficient
family is the original compactly supported quadratic series, and the dyadic
decomposition and all residue estimates are supplied by proved lemmas. -/
theorem eventual_large_kernel_positive_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, 4 * P.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hdy := eventual_dyadic_positive_norm (C₀ + 1) H (ε / 2) Φ hH (by positivity) hΦ
  have hcount := eventual_dyadic_shell_budget C₀ ε hC₀ hε
  filter_upwards [hdy, hcount, eventually_ge_atTop (1 : ℝ)] with T hdy hcount hT
  intro P hP M S u hlarge hM hcard hS hrange hcop hu huU D a θ R v c hR hv hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let f := fun s : ℕ => (u ^ s.primeFactors.card / (s : ℝ)) *
    ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2
  have hu0 : 0 ≤ u := by linarith
  have hf : ∀ s, 0 ≤ f s := by intro s; dsimp [f]; positivity
  have hL : 0 < P.toList.prod := prime_list_prod_pos _ (primeSet_list_prime P hP)
  have hs2 (s : ℕ) (hs : s ∈ S) : 2 ≤ s := by
    have hh := (hrange s hs).1
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hsegment (j : ℕ) :
      (∑ s ∈ S.filter (fun s => dyadicKernelShell s = j), f s) ≤
        Real.exp (2 * (3 / 500 + ε / 2) * K) := by
    let Sj := S.filter (fun s => dyadicKernelShell s = j)
    by_cases hne : Sj.Nonempty
    · obtain ⟨s₀, hs₀⟩ := hne
      obtain ⟨hs₀S, hj⟩ := Finset.mem_filter.mp hs₀
      have hjL : 2 * P.toList.prod ^ 2 ≤ 2 ^ j := by
        simpa only [hj] using dyadicKernelShell_modulus P.toList.prod s₀ (hrange s₀ hs₀S).1 (hs2 s₀ hs₀S)
      have hNM : 2 ^ j ≤ M := by
        have hh := (Finset.mem_Ioc.mp (dyadicKernelShell_mem s₀ (hs2 s₀ hs₀S))).1.le
        rw [hj] at hh
        exact hh.trans (hrange s₀ hs₀S).2
      have hcut : (2 * (2 ^ j) : ℝ) ≤ Real.exp ((C₀ + 1) * T) := by
        calc
          _ ≤ 2 * (M : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hNM
          _ ≤ 2 * Real.exp (C₀ * T) := mul_le_mul_of_nonneg_left hM (by norm_num)
          _ ≤ Real.exp T * Real.exp (C₀ * T) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have hSj (s : ℕ) (hs : s ∈ Sj) : s ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
        obtain ⟨hs, he⟩ := Finset.mem_filter.mp hs
        simpa only [he] using dyadicKernelShell_mem s (hs2 s hs)
      have hn := hdy P hP (2 ^ j) Sj u hlarge (by positivity) hjL (by
          simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using hcut)
        hcard (fun s hs => hS s (Finset.mem_filter.mp hs).1) hSj
        (fun s hs => hcop s (Finset.mem_filter.mp hs).1) hu huU D a θ R v c hR hv hc
      have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun s _ => hf s)), ← Real.exp_nat_mul] at hh
      simpa only [Nat.cast_ofNat, mul_assoc, K, Sj] using hh
    · have he : Sj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑ s ∈ Sj, f s) ≤ _
      rw [he, Finset.sum_empty]
      positivity
  have htotal : (∑ s ∈ S, f s) ≤ Real.exp (2 * (3 / 500 + ε) * K) := by
    rw [sum_dyadicKernelShells S M (fun s hs => (hrange s hs).2) f]
    calc
      _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M + 1), Real.exp (2 * (3 / 500 + ε / 2) * K) :=
        Finset.sum_le_sum (fun j _ => hsegment j)
      _ = (Nat.log 2 M + 1 : ℝ) * Real.exp (2 * (3 / 500 + ε / 2) * K) := by simp
      _ ≤ Real.exp (ε * K) * Real.exp (2 * (3 / 500 + ε / 2) * K) :=
        mul_le_mul_of_nonneg_right (hcount M hM) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.sqrt_le_sqrt htotal).trans_eq
  rw [← Real.exp_half]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_IntegerKernelScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the real analytic scale to the manuscript's integer K -/

namespace Ostmann

open Filter

theorem integerKernelScale_power (K : ℝ) (hK : 0 ≤ K) :
    integerKernelScale K ^ (9999999 / 10000000 : ℝ) = K := by
  rw [integerKernelScale, ← Real.rpow_mul hK]
  rw [show (10000000 / 9999999 : ℝ) * (9999999 / 10000000) = 1 by norm_num,
    Real.rpow_one]

theorem integerKernelScale_lower (T K : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K) :
    T / 1000000 ≤ integerKernelScale K := by
  have hT0 : 0 ≤ T := by linarith
  have hd : (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) ≤ 1000000 := by
    calc
      _ ≤ (1000 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_two]; norm_num
  calc
    _ ≤ T / (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) :=
      div_le_div_of_nonneg_left hT0 (Real.rpow_pos_of_pos (by norm_num) _) hd
    _ = (T ^ (9999999 / 10000000 : ℝ) / 1000) ^ (10000000 / 9999999 : ℝ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hT0 _) (by norm_num), ← Real.rpow_mul hT0]
      rw [show (9999999 / 10000000 : ℝ) * (10000000 / 9999999) = 1 by norm_num,
        Real.rpow_one]
    _ ≤ integerKernelScale K := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hT0 _) (by norm_num)) hK (by norm_num)

theorem integerKernelScale_moment (T K u : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hu : u ≤ 2 * T ^ (1 / 1000000 : ℝ)) :
    u ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hS : 0 < integerKernelScale K := Real.rpow_pos_of_pos hK0 _
  have hlo := integerKernelScale_lower T K hT hK
  have hTS : T ≤ 1000000 * integerKernelScale K := by linarith
  have hc : (1000000 : ℝ) ^ (1 / 1000000 : ℝ) ≤ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ (20 : ℕ)) ^ (1 / 1000000 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = (2 : ℝ) ^ ((20 : ℝ) * (1 / 1000000 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        simp only [Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  apply hu.trans
  calc
    _ ≤ 2 * (1000000 * integerKernelScale K) ^ (1 / 1000000 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT0 hTS (by norm_num)) (by norm_num)
    _ = 2 * ((1000000 : ℝ) ^ (1 / 1000000 : ℝ) *
        integerKernelScale K ^ (1 / 1000000 : ℝ)) := by rw [Real.mul_rpow (by norm_num) hS.le]
    _ ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 by norm_num))
        (Real.rpow_nonneg hS.le (1 / 1000000 : ℝ))
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num, mul_assoc] using hh

theorem eventually_at_integerKernelScale (Q : ℝ → Prop) (hQ : ∀ᶠ x : ℝ in atTop, Q x) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → Q (integerKernelScale K) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp hQ
  filter_upwards [eventually_ge_atTop (1000000 * max 1 B), eventually_ge_atTop (1 : ℝ)] with T ht hT K hK
  apply hB
  have hh := integerKernelScale_lower T K hT hK
  have hBB := le_max_right (1 : ℝ) B
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel divisor sum and its weighted square norm -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sum_powerset_power_card (P : Finset ℕ) (x : ℝ) :
    (∑ U ∈ P.powerset, x ^ U.card) = (1 + x) ^ P.card := by
  simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : ℕ => x) P).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CardinalKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient norms at the actual cardinality of the selected primes -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

private theorem kernelScale_range (C₀ T K : ℝ) (M : ℕ)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hM : (M : ℝ) ≤ Real.exp (C₀ * T)) :
    (M : ℝ) ≤ Real.exp ((1000000 * C₀) * integerKernelScale K) := by
  apply hM.trans
  apply Real.exp_le_exp.mpr
  have hlo := integerKernelScale_lower T K hT hK
  nlinarith

/-- The large-kernel norm has exponent `.006 K`, with `K` the actual
number of selected primes, including when `K` is a small fixed multiple
of the original analytic scale. -/
theorem eventual_large_kernel_norm_card (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (P.card : ℝ) →
      (∀ p ∈ P, 10000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * P.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, P.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * P.card) := by
  have hevent := eventual_large_kernel_positive_norm (1000000 * C₀) H ε Φ
    (by positivity) hH hε hΦ
  filter_upwards [eventually_at_integerKernelScale _ hevent,
    eventually_ge_atTop (1 : ℝ)] with T hnorm hT
  intro P hP M S u hK hlarge hM hS hrange hcop hu huU D a θ R v c hR hv hc
  have hscale := integerKernelScale_power (P.card : ℝ) (by positivity)
  have hn := hnorm (P.card : ℝ) hK P hP M S u hlarge
    (kernelScale_range C₀ T P.card M hC₀ hT hK hM) hscale.ge hS hrange hcop hu
    (integerKernelScale_moment T P.card u hT hK huU) D a θ R v c hR hv hc
  simpa only [hscale] using hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_DivisorReciprocalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal square-root mass of the selected divisors -/

namespace Ostmann

open scoped BigOperators

theorem sum_reciprocal_sqrt_divisors (Q : Finset ℕ) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) =
      ∏ p ∈ Q, (1 + (Real.sqrt (p : ℝ))⁻¹) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro V _
  have he : (V.toList.prod : ℝ) = ∏ p ∈ V, (p : ℝ) := by simp
  rw [he, Real.sqrt_prod V (fun p _ => Nat.cast_nonneg p), Finset.prod_inv_distrib]

theorem reciprocal_sqrt_divisor_mass_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤
      Real.exp ((Q.card : ℝ) / 1000) := by
  rw [sum_reciprocal_sqrt_divisors]
  calc
    _ ≤ ∏ _p ∈ Q, Real.exp (1 / 1000 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p _; positivity
      · intro p hp
        have hs : (1000 : ℝ) ≤ Real.sqrt (p : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          exact_mod_cast hQ p hp
        have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ (1 / 1000 : ℝ) := by
          simpa only [one_div] using (inv_anti₀ (by norm_num : (0 : ℝ) < 1000) hs)
        have he := Real.add_one_le_exp (1 / 1000 : ℝ)
        linarith
    _ = _ := by rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring

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

theorem sqrt_weighted_sum_energy_le {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ)
    (G : κ → ι → ℂ) (B : ℝ) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hG : ∀ d ∈ D, Real.sqrt (∑ s ∈ S, μ s * ‖G d s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      B * ∑ d ∈ D, ‖c d‖ := by
  have hp (d : κ) (hd : d ∈ D) (e : κ) (he : e ∈ D) :
      ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ ≤ B ^ 2 := by
    apply (weighted_correlation_le_sqrt_energy S μ (G d) (G e) hμ).trans
    simpa only [pow_two] using mul_le_mul (hG d hd) (hG e he) (Real.sqrt_nonneg _) hB
  have hb : (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      (B * ∑ d ∈ D, ‖c d‖) ^ 2 := by
    apply (weighted_sum_energy_le_correlations S D μ c G).trans
    calc
      _ ≤ ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hp d hd e he) (by positivity)
      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorWeightedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the squarefree divisors v in the original coefficients -/

namespace Ostmann

open scoped BigOperators

theorem divisor_weight_norm_sum_le (Q : Finset ℕ) (ξ : Finset ℕ → ℂ)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    (∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖) ≤
      ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply Finset.sum_le_sum
  intro V hV
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (hξ V hV)

theorem divisorWeightedCoefficient_norm_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ) (s : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, ‖F V s‖ ≤ B) :
    ‖divisorWeightedCoefficient Q ξ F s‖ ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  unfold divisorWeightedCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖ * B := by
      apply Finset.sum_le_sum
      intro V hV
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF V hV) (norm_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply (sqrt_weighted_sum_energy_le S Q.powerset μ
    (fun V => ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) F B hμ hB hF).trans
  exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_exp_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * Real.exp ((Q.card : ℝ) / 1000) :=
  (divisorWeightedCoefficient_energy_le Q ξ F S μ B hμ hB hξ hF).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sqrt_divisor_mass_le Q hQ) hB)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveQuadraticUniformBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the positive quadratic series at every kernel -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem positiveQuadraticSum_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hΦ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by positivity
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ]
  change ‖(Q : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤
      (W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, B * SchwartzMap.seminorm ℝ 0 0 Φ := by
        apply Finset.sum_le_sum
        intro w _
        simp only [quadraticDensityTerm, norm_mul, norm_pow, norm_realAdditivePhase,
          one_pow, mul_one]
        exact mul_le_mul (hg _) (Φ.norm_le_seminorm ℝ _) (norm_nonneg _) hB
      _ = _ := by simp
  calc
    _ ≤ Q⁻¹ * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQ.le)
    _ ≤ Q⁻¹ * ((Real.sqrt H * Q) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) := by gcongr
    _ = _ := by field_simp

theorem positiveQuadraticSum_energy_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      Real.sqrt q * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  apply positiveQuadraticSum_uniform_bound g (Real.sqrt q) _ a θ Φ R v H s hR hv hH hs hΦ
  intro x
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖g y‖) (Finset.mem_univ x)).trans hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootNormalizedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact coefficient energy of the normalized squarefree array -/

namespace Ostmann

open scoped BigOperators

theorem rootNormalizedCoefficient_norm_sq (F : ℕ → ℂ) (s : ℕ) :
    ‖rootNormalizedCoefficient F s‖ ^ 2 = (s : ℝ)⁻¹ * ‖F s‖ ^ 2 := by
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg s)]

theorem rootNormalizedCoefficient_energy (S : Finset ℕ) (u : ℝ) (F : ℕ → ℂ) :
    (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
      ∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) * ‖F s‖ ^ 2 := by
  rw [show (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
    ∑ s ∈ S, u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2 from
      Finset.sum_coe_sort S (fun s : ℕ => u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro s _
  rw [rootNormalizedCoefficient_norm_sq]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticArrayMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform absolute-mass bound for the original coefficient arrays -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorPositive_uniform_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (U : Finset ℕ) (hU : U ∈ P.powerset) :
    ‖primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  classical
  have hUP := Finset.mem_powerset.mp hU
  have hp : ∀ p ∈ U, p.Prime := fun p hp => hP p (hUP hp)
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hp)).ne'⟩
  rw [primeDivisorPositive, dite_eq_left hUP]
  apply (positiveQuadraticSum_energy_uniform_bound _ (densityCRTList_energy _ _ _ _)
    (a U) (θ U) Φ R v H s hR hv hH hs hΦ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact_mod_cast primeSet_prod_le_of_subset P U hP hUP

theorem primeDivisorPositive_combination_uniform_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      (Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ P.card := by
  let B := Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ U ∈ P.powerset, ‖c U * primeDivisorPositive P hP D a θ Φ R v U s‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ P.powerset, (1 / 16 : ℝ) ^ U.card * B := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul (hc U hU)
        (primeDivisorPositive_uniform_bound P hP D a θ Φ R v H s hR hv hH hs hΦ U hU)
        (norm_nonneg _) (by positivity)
    _ = B * (1 + 1 / 16 : ℝ) ^ P.card := by
      rw [← Finset.sum_mul, sum_powerset_power_card, mul_comm]

theorem rootNormalizedCoefficient_norm_le (F : ℕ → ℂ) (s : ℕ) (hs : 0 < s) :
    ‖rootNormalizedCoefficient F s‖ ≤ ‖F s‖ := by
  have hsq : (1 : ℝ) ≤ Real.sqrt s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hs
  have hi : (Real.sqrt (s : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hi

theorem rootNormalizedCoefficient_mass_le (S : Finset ℕ) (F : ℕ → ℂ) (B : ℝ)
    (hS : ∀ s ∈ S, 0 < s) (hF : ∀ s ∈ S, ‖F s‖ ≤ B) :
    (∑ s : S, ‖rootNormalizedCoefficient F s‖) ≤ (S.card : ℝ) * B := by
  calc
    _ = ∑ s ∈ S, ‖rootNormalizedCoefficient F s‖ :=
      Finset.sum_coe_sort S (fun s : ℕ => ‖rootNormalizedCoefficient F s‖)
    _ ≤ ∑ _s ∈ S, B := Finset.sum_le_sum (fun s hs =>
      (rootNormalizedCoefficient_norm_le F s (hS s hs)).trans (hF s hs))
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OuterDivisorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The outer divisor gives the full reciprocal-divisor norm gain -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorMultiples_combination_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s P : ℕ)
    (hP : 0 < P) (hs : 0 < s) (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s‖ ≤
      (Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P := by
  have he : (∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s) =
      (P : ℂ)⁻¹ * ∑ U ∈ Q.powerset, c U * primeDivisorPositive Q hQ D a θ Φ R v U (s * P ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    unfold primeDivisorMultiples
    ring
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  have hp := primeDivisorPositive_combination_uniform_bound Q hQ D a θ Φ R v H (s * P ^ 2)
    hR hv hH (Nat.mul_pos hs (pow_pos hP _)) hΦ c hc
  apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg P))).trans_eq
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both divisor sums in the original quadratic coefficient -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem fullQuadraticCoefficient_one (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (c ξ : Finset ℕ → ℂ) (s : ℕ) :
    fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s =
      divisorWeightedCoefficient Q ξ (fun V s => ∑ U ∈ Q.powerset, c U *
        primeDivisorPositive Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod U s) s := by
  simp only [fullQuadraticCoefficient, primeDivisorMultiples, one_pow, mul_one,
    Nat.cast_one, inv_one, one_mul]

theorem eventual_full_large_kernel_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, Q.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R : ℝ) (c ξ : Finset ℕ → ℂ),
      0 < R → (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s‖ ^ 2) ≤
        Real.exp ((7 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_large_kernel_norm_card C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hrange hcop hu huU D a θ R c ξ hR hc hξ
  simp_rw [fullQuadraticCoefficient_one]
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp ((3 / 500 + ε) * Q.card)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans_eq ?_
  · intro V hV
    have hVQ := Finset.mem_powerset.mp hV
    have hv : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    exact hn Q hQ M S u hK (fun p hp => by have := hlarge p hp; omega)
      hM hS hrange hcop hu huU D (divisorQuadraticScalar a V) θ R V.toList.prod c hR (by exact_mod_cast hv) hc
  · rw [← Real.exp_add]
    congr 1
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RademacherMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moments of the Boolean monomials -/

namespace Ostmann

open scoped BigOperators

theorem rademacherMonomial_univ {P : Finset ℕ} (Q : Finset P) (ε : P → Bool) :
    rademacherMonomial Q ε = ∏ p : P, if p ∈ Q then (if ε p then 1 else -1 : ℝ) else 1 := by
  classical
  exact (Finset.prod_ite_mem_eq Q (fun p => if ε p then (1 : ℝ) else -1)).symm

theorem rademacherMonomial_product {ι : Type*} [Fintype ι] {P : Finset ℕ}
    (σ : ι → Finset P) (ε : P → Bool) :
    (∏ i, rademacherMonomial (σ i) ε) =
      ∏ p : P, (if ε p then (1 : ℝ) else -1) ^ monomialOccurrence σ p := by
  classical
  simp_rw [rademacherMonomial_univ]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, monomialOccurrence]

private theorem bool_sign_power_sum (n : ℕ) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ n) = if Even n then 2 else 0 := by
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, one_pow, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

theorem rademacher_product_average {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, ∏ i, rademacherMonomial (σ i) ε =
        if ∀ p : P, Even (monomialOccurrence σ p) then 1 else 0 := by
  classical
  simp_rw [rademacherMonomial_product]
  rw [← Fintype.prod_sum (fun (p : P) (b : Bool) =>
    (if b then (1 : ℝ) else -1) ^ monomialOccurrence σ p)]
  simp_rw [bool_sign_power_sum]
  by_cases h : ∀ p : P, Even (monomialOccurrence σ p)
  · simp only [h, ite_true, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hcard : Fintype.card (P → Bool) = 2 ^ P.card := by simp
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ (by positivity)]
    simp
  · obtain ⟨p, hp⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp]), mul_zero, ite_eq_right h]

theorem rademacher_even_moment {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (a : ι → ℝ) (l : ℕ) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) =
      ∑ t : Fin (2 * l) → ι,
        (∏ j, a (t j)) * (if ∀ p : P, Even (monomialOccurrence (fun j => σ (t j)) p) then 1 else 0) := by
  classical
  simp only [Even.pow_abs (even_two_mul l)]
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum, mul_left_comm, rademacher_product_average]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying Boolean moments with square products of the actual indices -/

namespace Ostmann

open scoped BigOperators

private theorem squarefree_factorization_indicator {s : ℕ} (hs : Squarefree s) (p : ℕ) :
    s.factorization p = if p ∈ s.primeFactors then 1 else 0 := by
  classical
  by_cases hp : p ∈ s.primeFactors
  · rw [ite_eq_left hp]
    exact Nat.factorization_eq_one_of_squarefree hs (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · rw [ite_eq_right hp]
    by_cases hprime : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hd, hs.ne_zero⟩)
    · exact Nat.factorization_eq_zero_of_not_prime _ hprime

theorem isSquare_iff_even_factorization_aux {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p : ℕ, p.Prime → Even (n.factorization p) := by
  constructor
  · rintro ⟨m, rfl⟩ p _
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hm hm, Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    let f : ℕ →₀ ℕ := n.factorization.mapRange (· / 2) (by simp)
    have hf : ∀ p ∈ f.support, p.Prime := by
      intro p hp
      have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
      exact Nat.prime_of_mem_primeFactors (by simpa using this)
    refine ⟨f.prod (· ^ ·), ?_⟩
    have hm := Nat.prod_pow_factorization_eq_self hf
    have hm0 : f.prod (· ^ ·) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hf p hp).ne_zero)
    apply Nat.eq_of_factorization_eq hn (mul_ne_zero hm0 hm0)
    intro p
    rw [Nat.factorization_mul hm0 hm0, Finsupp.add_apply, hm]
    by_cases hp : p.Prime
    · obtain ⟨r, hr⟩ := h p hp
      simp only [f, Finsupp.mapRange_apply]
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp, f]

theorem squarefree_product_isSquare_iff {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (s : ι → ℕ) (hs : ∀ i, Squarefree (s i))
    (hP : ∀ i, (s i).primeFactors ⊆ P) :
    IsSquare (∏ i, s i) ↔ ∀ p : P,
      Even (monomialOccurrence (fun i => primeFactorSubset P (s i)) p) := by
  classical
  have he (p : ℕ) : (∏ i, s i).factorization p =
      ∑ i, if p ∈ (s i).primeFactors then 1 else 0 := by
    rw [Nat.factorization_prod (fun i _ => (hs i).ne_zero), Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact squarefree_factorization_indicator (hs i) p
  have hoc (p : P) : monomialOccurrence (fun i => primeFactorSubset P (s i)) p =
      (∏ i, s i).factorization p.val := by
    rw [he]
    simp only [monomialOccurrence, Finset.card_filter, mem_primeFactorSubset]
  rw [isSquare_iff_even_factorization_aux (Finset.prod_ne_zero_iff.mpr fun i _ => (hs i).ne_zero)]
  constructor
  · intro h p
    rw [hoc]
    by_cases hp : p.val.Prime
    · exact h p.val hp
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, Even.zero]
  · intro h p hp
    by_cases hpP : p ∈ P
    · simpa only [hoc] using h ⟨p, hpP⟩
    · rw [he]
      have hnot (i : ι) : p ∉ (s i).primeFactors := fun hh => hpP (hP i hh)
      simp only [hnot, ite_false, if_false, Finset.sum_const_zero, Even.zero]

theorem squarefree_diagonal_bonami (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (∑ t : Fin (2 * l) → S, (∏ j, a (t j)) *
      (if IsSquare (∏ j, (t j).val) then (1 : ℝ) else 0)) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have he := rademacher_even_moment P (fun s : S => primeFactorSubset P s.val) a l
  have hi (t : Fin (2 * l) → S) :
      IsSquare (∏ j, (t j).val) ↔
        ∀ p : P, Even (monomialOccurrence (fun j => primeFactorSubset P (t j).val) p) :=
    squarefree_product_isSquare_iff P (fun j => (t j).val)
      (fun j => hS _ (t j).property) (fun j => hP _ (t j).property)
  simp_rw [← hi] at he
  rw [← he]
  exact bonami_squarefree_family hB P S hS hP a l hl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_WeightedJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring square-product moments to weighted Jacobi sums

The nonsquare error is an explicit numerical bound to be supplied by the
periodic-character calculation; it is not a published or global assumption.
-/

namespace Ostmann

open scoped BigOperators

theorem realJacobi_abs_le (n m : ℕ) : |realJacobi n m| ≤ 1 := by
  rcases jacobiSym.trichotomy (n : ℤ) m with h | h | h <;> simp [realJacobi, h]

theorem realJacobi_prod {ι : Type*} (S : Finset ι) (s : ι → ℕ) (m : ℕ) :
    realJacobi (∏ i ∈ S, s i) m = ∏ i ∈ S, realJacobi (s i) m := by
  let J : ℕ →* ℝ :=
    { toFun := fun n => realJacobi n m
      map_one' := by simp [realJacobi, jacobiSym.one_left]
      map_mul' := fun a b => by simp [realJacobi, jacobiSym.mul_left] }
  exact map_prod J s S

theorem weighted_jacobi_abs_le_mass (T : Finset ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (n : ℕ) :
    |∑ m ∈ T, μ m * realJacobi n m| ≤ ∑ m ∈ T, μ m := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [abs_mul, abs_of_nonneg (hμ m hm)]
  exact (mul_le_mul_of_nonneg_left (realJacobi_abs_le n m) (hμ m hm)).trans_eq (mul_one _)

theorem weighted_jacobi_moment_expansion {ι : Type*} [Fintype ι]
    (T : Finset ℕ) (μ : ℕ → ℝ) (s : ι → ℕ) (a : ι → ℝ) (q : ℕ) :
    (∑ m ∈ T, μ m * (∑ i, a i * realJacobi (s i) m) ^ q) =
      ∑ t : Fin q → ι, (∏ j, a (t j)) *
        ∑ m ∈ T, μ m * realJacobi (∏ j, s (t j)) m := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, ← realJacobi_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Bonami controls the square products. Every remaining product pays only
the supplied finite nonsquare-character error `E`. -/
theorem weighted_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S T : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (a : S → ℝ) (l : ℕ) (hl : 0 < l)
    (E : ℝ) (hE : 0 ≤ E)
    (hns : ∀ t : Fin (2 * l) → S, ¬IsSquare (∏ j, (t j).val) →
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤ E) :
    (∑ m ∈ T, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) ≤
      (∑ m ∈ T, μ m) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      E * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let W := ∑ m ∈ T, μ m
  have hW : 0 ≤ W := Finset.sum_nonneg hμ
  have hJ (t : Fin (2 * l) → S) :
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤
        W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E := by
    split_ifs with ht
    · have hh := weighted_jacobi_abs_le_mass T μ hμ (∏ j, (t j).val)
      dsimp [W]
      linarith
    · simpa only [mul_zero, zero_add] using hns t ht
  simp only [Even.pow_abs (even_two_mul l)]
  rw [weighted_jacobi_moment_expansion]
  calc
    _ ≤ ∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ |(∏ j, a (t j)) * ∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := le_abs_self _
        _ = (∏ j, |a (t j)|) * |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := by
          rw [abs_mul, Finset.abs_prod]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hJ t) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = W * (∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (if IsSquare (∏ j, (t j).val) then 1 else 0)) + E * (∑ s : S, |a s|) ^ (2 * l) := by
      rw [Fintype.sum_pow, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left
      (squarefree_diagonal_bonami hB P S hS hP (fun s => |a s|) l hl) hW) _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependence of the original coefficient on finite arithmetic residues -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticSymbolCoefficient_norm_le (M : ℕ) (U : Finset ℕ) :
    ‖quadraticSymbolCoefficient M U‖ ≤ (1 / 16 : ℝ) ^ U.card := by
  have hn : ‖((1 / 16 : ℝ) : ℂ)‖ = (1 / 16 : ℝ) := by norm_num
  rw [quadraticSymbolCoefficient, norm_mul, norm_pow, hn,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (by positivity) (realJacobi_abs_le _ _)

theorem quadraticDivisorSymbol_norm_le (M : ℕ) (V : Finset ℕ) :
    ‖quadraticDivisorSymbol M V‖ ≤ 1 := by
  simpa only [quadraticDivisorSymbol, Complex.norm_real, Real.norm_eq_abs] using
    realJacobi_abs_le V.toList.prod M

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
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SquarefreeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor of the Jacobi character at odd squarefree level -/

namespace Ostmann

private theorem jacobi_crt_negative (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 0 < M) (hcop : p.Coprime M) :
    ∃ n : ℕ, n.Coprime (p * M) ∧ n ≡ 1 [MOD M] ∧ jacobiSym (n : ℤ) (p * M) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  let n := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnp : (n : ℕ) ≡ (a : ZMod p).val [MOD p] := n.property.1
  have hnM : (n : ℕ) ≡ 1 [MOD M] := n.property.2
  have hpa : ((n : ℕ) : ZMod p) = (a : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (n : ℕ) (a : ZMod p).val p).mpr hnp
    simpa only [ZMod.natCast_zmod_val] using h
  have hMa : ((n : ℕ) : ZMod M) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (n : ℕ) 1 M).mpr hnM
  have hcp : (n : ℕ).Coprime p := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) p).mp
    rw [hpa]
    exact a.isUnit
  have hcM : (n : ℕ).Coprime M := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) M).mp
    rw [hMa]
    exact isUnit_one
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiCharacterInt_intCast p, Int.cast_natCast, jacobiCharacterInt_prime, hpa, ha]
  have hJM : jacobiSym (n : ℤ) M = 1 := by
    have h := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' (n : ℤ) 1 M).mp
      (by simpa only [Int.cast_natCast, Int.cast_one] using hMa))
    simpa only [jacobiSym.one_left] using h
  exact ⟨n, hcp.mul_right hcM, hnM, by rw [jacobiSym.mul_right, hJp, hJM, mul_one]⟩

/-- An odd prime factor missing from the conductor is contradicted by a
CRT unit whose Jacobi value is -1 and whose conductor residue is 1. -/
theorem jacobiCharacter_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiCharacter N).IsPrimitive := by
  let χ := jacobiCharacter N
  have hcN := χ.conductor_dvd_level
  have hcp (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : p ∣ χ.conductor := by
    by_contra hpc
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hodd.not_two_dvd_nat hpN
    have hprod : p * (N / p) = N := Nat.mul_div_cancel' hpN
    have hM : 0 < N / p := by
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hN)
    obtain ⟨n, hn, hnM, hJn⟩ := jacobi_crt_negative p (N / p) hp hp2 hM hcop
    have hnc : n.Coprime N := hprod ▸ hn
    have hcd : χ.conductor ∣ N / p := by
      apply ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_left
      rwa [hprod]
    have hncon : (n : ZMod χ.conductor) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff n 1 χ.conductor).mpr (hnM.of_dvd hcd)
      simpa only [Nat.cast_one] using h
    have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hnc)
    have hv : χ.primitiveCharacter (n : ℤ) = 1 := by
      rw [Int.cast_natCast, hncon, map_one]
    have hv' : χ (n : ℤ) = -1 := by
      change jacobiCharacter N (n : ℤ) = -1
      rw [jacobiCharacter_intCast, ← hprod, hJn]
      norm_num
    rw [hv, hv'] at he
    norm_num at he
  have hNc : (∏ p ∈ N.primeFactors, p) ∣ χ.conductor := by
    apply (Nat.prod_primeFactors_dvd_iff χ.conductor_ne_zero).mpr
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, hcp p hp'.1 hp'.2.1, χ.conductor_ne_zero⟩
  have hNc' : N ∣ χ.conductor := by
    simpa only [Nat.prod_primeFactors_of_squarefree hN] using hNc
  exact Nat.dvd_antisymm hcN hNc'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticReciprocityCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity formulas for the sign and two-part of a kernel -/

namespace Ostmann

theorem jacobi_odd_numerator_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (N : ℤ) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) := by
  have h := jacobiSym.quadratic_reciprocity' hN ha
  rw [qrSign.symm ha hN, qrSign.neg_one_pow hN ha] at h
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ha), ← pow_mul]
  rw [Nat.mul_comm (a / 2) (N / 2)]
  exact h.trans (mul_comm _ _)

theorem jacobi_negative_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(N : ℤ)) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) := by
  rw [jacobiSym.neg _ ha, jacobi_odd_numerator_formula N a hN ha, pow_succ]
  ring

theorem jacobi_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (2 * (N : ℤ)) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) * ZMod.χ₈ a := by
  rw [jacobiSym.mul_left, jacobiSym.at_two ha, jacobi_odd_numerator_formula N a hN ha]
  ring

theorem jacobi_negative_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(2 * (N : ℤ))) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) * ZMod.χ₈ a := by
  rw [jacobiSym.neg _ ha, jacobi_twice_odd_formula N a hN ha, pow_succ]
  ring

theorem signedOddKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 4)) (haodd : Odd a) :
    signedOddKernelCharacter N negative (a : ZMod (Nat.lcm N 4)) =
      (jacobiSym (if negative then -(N : ℤ) else (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 4) := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (Nat.dvd_lcm_right N 4))
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 4))]
  rw [signedOddKernelCharacter, DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    jacobiCharacter_intCast]
  have hpow (k : ℕ) : (realFourCharacter ^ k) ((a : ℤ) : ZMod 4) = (ZMod.χ₄ a : ℝ) ^ k := by
    rw [Int.cast_natCast, ← hunit.unit_spec, MulChar.pow_apply_coe]
    rfl
  rw [hpow]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_odd_numerator_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_odd_formula N a hN haodd).symm

theorem evenKernelTwist_value (k a : ℕ) (ha : a.Coprime 8) :
    evenKernelTwist k (a : ZMod 8) = (ZMod.χ₄ a : ℝ) ^ k * (ZMod.χ₈ a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) 8 := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (by decide : 4 ∣ 8))
  rw [evenKernelTwist, MulChar.mul_apply, ← Int.cast_natCast (R := ZMod 8),
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, Int.cast_natCast,
    ← hunit.unit_spec, MulChar.pow_apply_coe, hunit.unit_spec]
  rfl

theorem signedEvenKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 8)) (haodd : Odd a) :
    signedEvenKernelCharacter N negative (a : ZMod (Nat.lcm N 8)) =
      (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 8) := Nat.isCoprime_iff_coprime.mpr ha
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 8)), signedEvenKernelCharacter,
    DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, jacobiCharacter_intCast,
    Int.cast_natCast, evenKernelTwist_value _ _ (ha.of_dvd_right (Nat.dvd_lcm_right N 8))]
  rw [← mul_assoc]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_twice_odd_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_twice_odd_formula N a hN haodd).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelConductor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor bounds for the signed kernel characters -/

namespace Ostmann

/-- A twist whose conductor is coprime to that of a character cannot remove
any of the latter's conductor. -/
theorem conductor_dvd_conductor_mul {n : ℕ} [NeZero n]
    (χ ψ : DirichletCharacter ℝ n) (hcop : χ.conductor.Coprime ψ.conductor) :
    χ.conductor ∣ (χ * ψ).conductor := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
  exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))

/-- Only the two-part can change when the odd squarefree Jacobi character is
multiplied by a character of level coprime to that odd part. -/
theorem odd_part_dvd_twisted_conductor (N t : ℕ) [NeZero N] [NeZero t]
    (hN : Squarefree N) (hodd : Odd N) (hcop : N.Coprime t)
    (ψ : DirichletCharacter ℝ t) :
    N ∣ (DirichletCharacter.mul (jacobiCharacter N) ψ).conductor := by
  let : NeZero (Nat.lcm N t) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  let χ' := (jacobiCharacter N).changeLevel (Nat.dvd_lcm_left N t)
  let ψ' := ψ.changeLevel (Nat.dvd_lcm_right N t)
  have hχ : χ'.conductor = N := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact jacobiCharacter_squarefree_primitive N hN hodd
  have hψ : ψ'.conductor ∣ t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact ψ.conductor_dvd_level
  have hc : χ'.conductor.Coprime ψ'.conductor := by
    rw [hχ]
    exact hcop.of_dvd_right hψ
  change N ∣ (χ' * ψ').conductor
  simpa only [hχ] using conductor_dvd_conductor_mul χ' ψ' hc

theorem signedOddKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedOddKernelCharacter N negative).conductor ∧
    (signedOddKernelCharacter N negative).conductor ≤ 4 * N := by
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 4 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 2
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 4)))
      (signedOddKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 4)).trans_eq (Nat.mul_comm N 4))

theorem signedEvenKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedEvenKernelCharacter N negative).conductor ∧
    (signedEvenKernelCharacter N negative).conductor ≤ 8 * N := by
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 8 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 3
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 8)))
      (signedEvenKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 8)).trans_eq (Nat.mul_comm N 8))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimitiveKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive real characters representing the four signed kernel shapes -/

namespace Ostmann

theorem character_ne_one_of_conductor_dvd {n N : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hN : 1 < N) (hdiv : N ∣ χ.conductor) : χ ≠ 1 := by
  intro h
  rw [h, DirichletCharacter.conductor_one] at hdiv
  have := Nat.dvd_one.mp hdiv
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_NonsquareJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete character behind nonsquare Jacobi cancellation -/

namespace Ostmann

private theorem exists_squarefree_jacobi_level (s : ℕ) (hs : Squarefree s)
    (hs1 : 1 < s) :
    ∃ q : ℕ, 0 < q ∧ q ∣ 8 * s ∧ ∃ χ : DirichletCharacter ℝ q,
      χ ≠ 1 ∧ ∀ a : ℕ, Odd a → a.Coprime s →
        χ (a : ZMod q) = realJacobi s a := by
  rcases Nat.even_or_odd s with he | ho
  · obtain ⟨N, hN⟩ := he
    have hsN : s = 2 * N := by omega
    have hNp : 0 < N := by omega
    have hsf : Squarefree (2 * N) := hsN ▸ hs
    have hNo : Odd N := (Nat.coprime_of_squarefree_mul hsf).odd_of_left
    have hNs : Squarefree N := hsf.of_mul_right
    let : NeZero N := ⟨hNp.ne'⟩
    let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero hNp.ne' (by decide)⟩
    let χ := signedEvenKernelCharacter N false
    have hχ : χ ≠ 1 := by
      by_cases hN1 : N = 1
      · subst N
        intro hc
        have hv := signedEvenKernelCharacter_value 1 false (by decide) 5 (by decide) (by decide)
        change χ (5 : ZMod (Nat.lcm 1 8)) = _ at hv
        have hu : IsUnit (5 : ZMod (Nat.lcm 1 8)) := (ZMod.isUnit_iff_coprime 5 _).mpr (by decide)
        rw [hc, MulChar.one_apply hu] at hv
        have hJ : jacobiSym 2 5 = -1 := by
          rw [jacobiSym.at_two (by decide)]
          norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
        norm_num [hJ] at hv
      · exact character_ne_one_of_conductor_dvd χ (by omega)
          (signedEvenKernelCharacter_conductor_bounds N false hNs hNo).1
    refine ⟨Nat.lcm N 8, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, hχ, ?_⟩
    · apply Nat.lcm_dvd
      · rw [hsN]
        exact dvd_mul_of_dvd_right (dvd_mul_left N 2) 8
      · exact dvd_mul_right 8 s
    · intro a hao hac
      have hacN := hac.of_dvd_right (hsN ▸ dvd_mul_left N 2)
      have hac8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
      have hacq := (hacN.mul_right hac8).of_dvd_right (Nat.lcm_dvd_mul N 8)
      have hv := signedEvenKernelCharacter_value N false hNo a hacq hao
      simpa [χ, realJacobi, hsN, Nat.cast_mul] using hv
  · let : NeZero s := ⟨by omega⟩
    let : NeZero (Nat.lcm s 4) := ⟨Nat.lcm_ne_zero (NeZero.ne s) (by decide)⟩
    let χ := signedOddKernelCharacter s false
    refine ⟨Nat.lcm s 4, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, ?_, ?_⟩
    · exact Nat.lcm_dvd (dvd_mul_left s 8) (dvd_mul_of_dvd_left (by decide : 4 ∣ 8) s)
    · exact character_ne_one_of_conductor_dvd χ hs1
        (signedOddKernelCharacter_conductor_bounds s false hs ho).1
    · intro a hao hac
      have hac4 : a.Coprime 4 := by simpa using hao.coprime_two_right.pow_right 2
      have hacq := (hac.mul_right hac4).of_dvd_right (Nat.lcm_dvd_mul s 4)
      simpa [χ, realJacobi] using signedOddKernelCharacter_value s false ho a hacq hao

/-- At level `8*n` the extra nonunit zeroes are exactly the even arguments
and the common factors with `n`. Induction from the nontrivial squarefree
kernel preserves nonprincipality. -/
theorem exists_nonsquare_jacobi_character (n : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    ∃ χ : DirichletCharacter ℝ (8 * n), χ ≠ 1 ∧
      ∀ a : ℕ, χ (a : ZMod (8 * n)) = if Odd a then realJacobi n a else 0 := by
  obtain ⟨s, w, hsp, hwp, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hs1 : 1 < s := by
    by_contra h
    have hs : s = 1 := by omega
    apply hns
    refine ⟨w, ?_⟩
    simpa [hs, pow_two] using he.symm
  obtain ⟨q, hqp, hqd, ψ, hψ, hvalue⟩ := exists_squarefree_jacobi_level s hsf hs1
  have hsn : s ∣ n := ⟨w ^ 2, by nlinarith [he]⟩
  have hqn : q ∣ 8 * n := hqd.trans (Nat.mul_dvd_mul_left 8 hsn)
  let : NeZero (8 * n) := ⟨by omega⟩
  let χ := ψ.changeLevel hqn
  refine ⟨χ, ?_, ?_⟩
  · exact fun hc => hψ ((DirichletCharacter.changeLevel_eq_one_iff hqn).mp hc)
  · intro a
    by_cases hao : Odd a
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hao))]
      by_cases hac : a.Coprime (8 * n)
      · have hasn : a.Coprime n := hac.of_dvd_right (dvd_mul_left n 8)
        have has : a.Coprime s := hasn.of_dvd_right hsn
        have hwan : w ∣ n := ⟨w * s, by nlinarith [he]⟩
        have hwc : w.Coprime a := (hasn.of_dvd_right hwan).symm
        have hcast : χ (a : ZMod (8 * n)) = ψ (a : ZMod q) := by
          rw [← Int.cast_natCast (R := ZMod (8 * n)),
            DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _
              (Nat.isCoprime_iff_coprime.mpr hac), Int.cast_natCast]
        rw [hcast, hvalue a hao has]
        unfold realJacobi
        congr 1
        rw [← he, Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left,
          jacobiSym.pow_left, jacobiSym.sq_one (by simpa using hwc), one_mul]
      · have hnotu : ¬IsUnit (a : ZMod (8 * n)) := by
          simpa only [ZMod.isUnit_iff_coprime] using hac
        rw [MulChar.map_nonunit χ hnotu]
        have hasn : ¬a.Coprime n := by
          intro han
          have ha8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
          exact hac (ha8.mul_right han)
        have ha0 : a ≠ 0 := by intro h; subst a; norm_num at hao
        let : NeZero a := ⟨ha0⟩
        have hj : jacobiSym (n : ℤ) a = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Nat.coprime_comm] using hasn)
        simp [realJacobi, hj]
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hao h))]
      apply MulChar.map_nonunit
      intro hu
      have hc := (ZMod.isUnit_iff_coprime a (8 * n)).mp hu
      have hc2 : a.Coprime 2 := hc.of_dvd_right (dvd_mul_of_dvd_left (by decide : 2 ∣ 8) n)
      exact hao hc2.odd_of_right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PeriodicCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial sums of nonprincipal periodic characters -/

namespace Ostmann

open scoped BigOperators

private theorem sum_range_periodic_blocks (f : ℕ → ℝ) (q : ℕ)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (k r : ℕ) : ∑ a ∈ Finset.range (k * q + r), f a = ∑ a ∈ Finset.range r, f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q + r = q + (k * q + r) by ring, Finset.sum_range_add, hz, zero_add]
    have hp' (a : ℕ) : f (q + a) = f a := by simpa only [Nat.add_comm] using hp a
    simpa only [hp'] using ih

theorem periodic_zero_sum_range_bound (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (hb : ∀ a, |f a| ≤ 1) (N : ℕ) : |∑ a ∈ Finset.range N, f a| ≤ q := by
  have he : N / q * q + N % q = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  rw [← he, sum_range_periodic_blocks f q hp hz]
  calc
    _ ≤ ∑ a ∈ Finset.range (N % q), |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
    _ = (N % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le

theorem nonprincipal_character_sum_range_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (N : ℕ) :
    |∑ a ∈ Finset.range N, χ (a : ZMod q)| ≤ q := by
  apply periodic_zero_sum_range_bound (fun a => χ (a : ZMod q)) q
    (Nat.pos_of_ne_zero (NeZero.ne q))
  · intro a
    simp
  · have hsum : ∑ a : Fin q, χ ((a.val : ℕ) : ZMod q) = 0 := by
      have he := (ZMod.finEquiv q).toEquiv.sum_comp (fun a => χ a)
      have heq (a : Fin q) : (ZMod.finEquiv q).toEquiv a = (a.val : ZMod q) := by
        cases q with
        | zero => exact Fin.elim0 a
        | succ q =>
          apply Fin.ext
          exact (Nat.mod_eq_of_lt a.isLt).symm
      simp_rw [heq] at he
      exact he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    exact (Fin.sum_univ_eq_sum_range (fun a => χ (a : ZMod q)) q).symm.trans hsum
  · intro a
    simpa only [Real.norm_eq_abs] using χ.norm_le_one (a : ZMod q)

/-- The nonsquare term in the original odd-modulus Jacobi moment has a
uniform initial-sum bound, with no analytic hypothesis. -/
theorem nonsquare_jacobi_sum_range_bound (n N : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    |∑ a ∈ Finset.range N, if Odd a then realJacobi n a else 0| ≤ 8 * n := by
  obtain ⟨χ, hχ, hv⟩ := exists_nonsquare_jacobi_character n hn hns
  let : NeZero (8 * n) := ⟨by omega⟩
  simpa only [hv, Nat.cast_mul, Nat.cast_ofNat] using
    nonprincipal_character_sum_range_bound (8 * n) χ hχ N

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FallingFactorialError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary collision loss for sampling distinct indices -/

namespace Ostmann

/-- A convenient collision bound with no restriction that k be smaller than J. -/
theorem pow_le_descFactorial_add (J : ℕ) (hJ : 1 ≤ J) (k : ℕ) :
    J ^ k ≤ J.descFactorial k + k ^ 2 * J ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    by_cases hkJ : k ≤ J
    · have hmul := Nat.mul_le_mul_left J ih
      have hprev : J * J ^ (k - 1) = J ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      have hdesc : J * J.descFactorial k =
          J.descFactorial (k + 1) + k * J.descFactorial k := by
        rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel hkJ]
      have hsmall := Nat.mul_le_mul_left k (Nat.descFactorial_le_pow J k)
      have herr : J * (k ^ 2 * J ^ (k - 1)) = k ^ 2 * J ^ k := by
        calc
          _ = k ^ 2 * (J * J ^ (k - 1)) := by ring
          _ = _ := by rw [hprev]
      rw [Nat.mul_add, hdesc, herr, ← pow_succ' J k] at hmul
      have hpoly : k ^ 2 + k ≤ (k + 1) ^ 2 := by nlinarith
      have hfinal := Nat.mul_le_mul_right (J ^ k) hpoly
      simp only [Nat.add_sub_cancel]
      nlinarith
    · have hJK : J ≤ (k + 1) ^ 2 := by
        have : J ≤ k := by omega
        nlinarith
      have h := Nat.mul_le_mul_right (J ^ k) hJK
      rw [pow_succ' J k]
      simpa only [Nat.add_sub_cancel] using h.trans (Nat.le_add_left _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_OddJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit Bonami moment bound over all odd moduli -/

namespace Ostmann

open scoped BigOperators

/-- The nonsquare contribution is bounded by `8*U^(2*l)` independently of
how many moduli are summed. Only the classical Bonami input remains. -/
theorem odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (a : S → ℝ) :
    (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤
      (M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let μ : ℕ → ℝ := fun m => if Odd m then 1 else 0
  have hμ : ∀ m ∈ Finset.range M, 0 ≤ μ m := by
    intro m hm
    dsimp [μ]
    split <;> norm_num
  have hE : 0 ≤ 8 * (U : ℝ) ^ (2 * l) := by positivity
  have hns (t : Fin (2 * l) → S) (ht : ¬IsSquare (∏ j, (t j).val)) :
      |∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m| ≤
        8 * (U : ℝ) ^ (2 * l) := by
    have hn : 0 < ∏ j, (t j).val := Finset.prod_pos (fun j _ =>
      Nat.pos_of_ne_zero (hS _ (t j).property).ne_zero)
    have hnU : ∏ j, (t j).val ≤ U ^ (2 * l) := by
      calc
        _ ≤ ∏ _j : Fin (2 * l), U := Finset.prod_le_prod' (fun j _ => hU _ (t j).property)
        _ = _ := by simp
    have hh := nonsquare_jacobi_sum_range_bound (∏ j, (t j).val) M hn ht
    have heq : (∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m) =
        ∑ m ∈ Finset.range M, if Odd m then realJacobi (∏ j, (t j).val) m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [μ]
      split <;> simp_all
    rw [heq]
    exact hh.trans (by exact_mod_cast Nat.mul_le_mul_left 8 hnU)
  have h := weighted_jacobi_even_moment_bound hB P S (Finset.range M) hS hP μ hμ a l hl
    (8 * (U : ℝ) ^ (2 * l)) hE hns
  have hmass : (∑ m ∈ Finset.range M, μ m) ≤ M := by
    calc
      _ ≤ ∑ _m ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        dsimp [μ]
        split <;> norm_num
      _ = M := by simp
  have hleft : (∑ m ∈ Finset.range M, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) =
      ∑ m ∈ Finset.range M, if Odd m then |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [μ]
    split <;> simp_all
  rw [hleft] at h
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hmass (by positivity)) _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_ComplexJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The odd-modulus moment estimate for complex coefficient arrays -/

namespace Ostmann

open scoped BigOperators

theorem complex_odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (b : S → ℂ) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)) := by
  classical
  let B := (M : ℝ) *
    (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
    (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)
  have hcomponent (a : S → ℝ) (ha : ∀ s, |a s| ≤ ‖b s‖) :
      (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤ B := by
    apply (odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl a).trans
    have he : (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ≤
        ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (ha s) 2) (by positivity)
    have he0 : 0 ≤ ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2 := by
      positivity
    have hsum : (∑ s : S, |a s|) ≤ ∑ s : S, ‖b s‖ := Finset.sum_le_sum (fun s _ => ha s)
    dsimp [B]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 he l) (by positivity))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum (2 * l)) (by positivity))
  have hre := hcomponent (fun s => (b s).re) (fun s => Complex.abs_re_le_norm (b s))
  have him := hcomponent (fun s => (b s).im) (fun s => Complex.abs_im_le_norm (b s))
  have hpoint (m : ℕ) :
      ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) ≤
        (2 : ℝ) ^ (2 * l - 1) *
          (|∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) +
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l)) := by
    let z := ∑ s : S, b s * (realJacobi s.val m : ℂ)
    have hz := (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) (2 * l)).trans
      (add_pow_le (abs_nonneg z.re) (abs_nonneg z.im) (2 * l))
    simpa [z, Complex.mul_re, Complex.mul_im] using hz
  calc
    _ ≤ (2 : ℝ) ^ (2 * l - 1) *
        ((∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) else 0) +
          ∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l) else 0) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with h
      · exact hpoint m
      · simp
    _ ≤ (2 : ℝ) ^ (2 * l - 1) * (B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add hre him) (by positivity)
    _ = (2 : ℝ) ^ (2 * l) * B := by
      calc
        _ = ((2 : ℝ) ^ (2 * l - 1) * 2) * B := by ring
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * l)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiFamilyMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A moment bound uniform over a finite family of coefficient arrays -/

namespace Ostmann

open scoped BigOperators

/-- The array may be chosen separately at each modulus. Thus this estimate
also bounds the pointwise maximum over the family. -/
theorem complex_odd_jacobi_chosen_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (U M l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
  classical
  have heach (i : I) :
      (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
    apply (complex_odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl (b i)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (henergy i) l
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (hmass i) (2 * l)
  calc
    _ ≤ ∑ i : I, ∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with ho
      · exact Finset.single_le_sum
          (f := fun i : I => ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
          (fun i _ => by positivity) (Finset.mem_univ (pick m))
      · simp
    _ ≤ ∑ _i : I, (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring the finite-family moment to products of distinct primes -/

namespace Ostmann

open scoped BigOperators

theorem inverse_choose_le (J k : ℕ) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ J) :
    ((J.choose k : ℝ))⁻¹ ≤ 2 * (k.factorial : ℝ) / (J : ℝ) ^ k := by
  have hJ : 0 < J := by nlinarith
  have hkJ : k ≤ J := by nlinarith
  have hp : J ^ k = J * J ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hb := pow_le_descFactorial_add J hJ k
  have hloss := Nat.mul_le_mul_right (J ^ (k - 1)) hsize
  have hbound : J ^ k ≤ 2 * J.descFactorial k := by nlinarith
  have hchoose : (0 : ℝ) < J.choose k := by exact_mod_cast Nat.choose_pos hkJ
  have hJpow : (0 : ℝ) < (J : ℝ) ^ k := by positivity
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hchoose hJpow).mpr
  have hh : (J : ℝ) ^ k ≤ 2 * ((k.factorial : ℝ) * (J.choose k : ℝ)) := by
    exact_mod_cast (show J ^ k ≤ 2 * (k.factorial * J.choose k) by
      rwa [Nat.descFactorial_eq_factorial_mul_choose] at hbound)
  nlinarith

/-- Positivity transfers any statistic of the prime product to all odd
moduli in its range; unique factorization gives the exact uniform weight. -/
theorem prime_product_mean_le_odd_sum (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k, F m) ≤
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ Finset.range (Z ^ k + 1), if Odd m then F m else 0) := by
  classical
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hmem := primeSubsetProducts_mem_range P k Z hP hodd hZ
  have hs : primeSubsetProducts P k ⊆ Finset.range (Z ^ k + 1) := by
    intro m hm
    have hh := (Finset.mem_filter.mp (hmem hm)).1
    have hh' := (Finset.mem_Icc.mp hh).2
    exact Finset.mem_range.mpr (by omega)
  have heq : (∑ m ∈ primeSubsetProducts P k, F m) =
      ∑ m ∈ primeSubsetProducts P k, if Odd m then F m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have ho := (Finset.mem_filter.mp (hmem hm)).2.1
    simp only [ho, ite_true, if_true]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hs
  intro m hm hnot
  split <;> simp_all

/-- This is the finite, explicit version of the manuscript's uniform
Jacobi-family moment estimate, before its final numerical specialization. -/
theorem prime_product_family_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
          (((Z ^ k + 1 : ℕ) : ℝ) * E ^ l +
            (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by
  classical
  have hdom := prime_product_mean_le_odd_sum P k Z hP hodd hZ
    (fun m => ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
    (fun _ => by positivity)
  have hm := complex_odd_jacobi_chosen_moment_bound hB R S hS hR U (Z ^ k + 1) l
    hU hl b pick E A henergy hmass
  have hoddnonneg : 0 ≤ ∑ m ∈ Finset.range (Z ^ k + 1),
      if Odd m then ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
    apply Finset.sum_nonneg
    intro m hm
    split <;> positivity
  exact hdom.trans ((mul_le_mul_of_nonneg_right (inverse_choose_le P.card k hk hsize)
    hoddnonneg).trans (mul_le_mul_of_nonneg_left hm (by positivity)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductNormTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Taking the even root of the finite prime-product moment bound -/

namespace Ostmann

open scoped BigOperators

/-- This finite inequality keeps the square and nonsquare contributions
separate, so their numerical estimates can be supplied independently. -/
theorem prime_product_family_norm_transfer (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A B δ : ℝ)
    (hE : 0 ≤ E) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A)
    (hsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤ B ^ (2 * l))
    (hnonsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤ δ ^ (2 * l)) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (B * Real.sqrt E + δ) ^ (2 * l) := by
  have hm := prime_product_family_moment_bound hB P S R hS hR hP hodd U Z k l hU hZ
    hl hk hsize b pick E A henergy hmass
  have hpow : (Real.sqrt E) ^ (2 * l) = E ^ l := by
    rw [pow_mul, Real.sq_sqrt hE]
  apply hm.trans
  calc
    _ = ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ)) * E ^ l +
        ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
          ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by ring
    _ ≤ B ^ (2 * l) * E ^ l + δ ^ (2 * l) :=
      add_le_add (mul_le_mul_of_nonneg_right hsquare (pow_nonneg hE _)) hnonsquare
    _ = (B * Real.sqrt E) ^ (2 * l) + δ ^ (2 * l) := by rw [mul_pow, hpow]
    _ ≤ _ := pow_add_pow_le (mul_nonneg hB0 (Real.sqrt_nonneg E)) hδ (by omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductParameterBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical overhead in the fixed-family prime-product moment estimate -/

namespace Ostmann

open Filter Asymptotics

/-- The transfer-factor logarithm is negligible after division by the
moment order. The small positive gap `mu + kappa - 1` is used explicitly. -/
theorem eventual_prime_product_parameter_budget (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (1 / 1000000 : ℝ) / 2 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + k * (C + 3 * Real.log T) + C * l ≤
        ε * l * T ^ (9999999 / 10000000 : ℝ) := by
  let μ : ℝ := 1 / 1000000
  let κ : ℝ := 9999999 / 10000000
  let A := 4 * C + 6
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).bound zero_lt_one
  have hpower := (tendsto_rpow_atTop (show 0 < κ + μ - 1 by norm_num [κ, μ])).eventually_ge_atTop
    (2 * A / ε)
  filter_upwards [hlog, hpower, eventually_ge_atTop (1 : ℝ)] with T hl hp hT k l hk hkU hlL hlU
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl' : Real.log T ≤ T ^ (2 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _), one_mul] using hl
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hμ : T ^ μ ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show μ ≤ 1 by norm_num [μ])
  have hklog : k * Real.log T ≤ 2 * T := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (2 / 5 : ℝ) :=
        mul_le_mul hkU hl' hlogT (by positivity)
      _ = 2 * T := by
        rw [mul_assoc, ← Real.rpow_add hT0]
        norm_num
  have hrough : C * T + k * (C + 3 * Real.log T) + C * l ≤ A * T := by
    have hkT : k ≤ 2 * T := hkU.trans (mul_le_mul_of_nonneg_left hρ (by norm_num))
    have hlT : l ≤ T := hlU.trans hμ
    have hkC := mul_le_mul_of_nonneg_left hkT hC
    have hlC := mul_le_mul_of_nonneg_left hlT hC
    dsimp [A]
    nlinarith
  apply hrough.trans
  have hp' : A ≤ ε / 2 * T ^ (κ + μ - 1) := by
    have hh := (div_le_iff₀ hε).mp hp
    calc
      A = (2 * A) / 2 := by ring
      _ ≤ (T ^ (κ + μ - 1) * ε) / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  have hcombined : T ^ (κ + μ - 1) * T = T ^ μ * T ^ κ := by
    calc
      _ = T ^ (κ + μ - 1) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((κ + μ - 1) + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (μ + κ) := by congr 1; ring
      _ = _ := Real.rpow_add hT0 _ _
  calc
    A * T ≤ (ε / 2 * T ^ (κ + μ - 1)) * T :=
      mul_le_mul_of_nonneg_right hp' hT0.le
    _ = ε * (T ^ μ / 2) * T ^ κ := by
      calc
        _ = ε / 2 * (T ^ (κ + μ - 1) * T) := by ring
        _ = _ := by rw [hcombined]; ring
    _ ≤ ε * l * T ^ κ := by gcongr

/-- The nonsquare character-sum error is exponentially small because
the number of sampled primes grows faster than the moment order. -/
theorem eventual_prime_product_error_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      T ^ (3 / 5 : ℝ) / 2 ≤ k →
      1 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + C * l + 2 * C * l * T + k * (C + 3 * Real.log T - T) ≤
        -20 * l * T := by
  let μ : ℝ := 1 / 1000000
  let D := 4 * C + 20
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  have hpower := (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 5 - μ by norm_num [μ])).eventually_ge_atTop
    (4 * D)
  filter_upwards [hlog, hpower, eventually_ge_atTop (4 * C),
    eventually_ge_atTop (1 : ℝ)] with T hl hp hCT hT k l hk hl1 hlU
  have hT0 : 0 < T := by linarith
  have hk0 : 0 ≤ k := le_trans (by positivity) hk
  have hl0 : 0 ≤ l := by linarith
  have hlog' : Real.log T ≤ T / 12 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hT), abs_of_nonneg hT0.le, one_div_mul_eq_div] using hl
  have hnegative : C + 3 * Real.log T - T ≤ -T / 2 := by linarith
  have hkl : D * l ≤ k / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hT0.le μ)
    have hpowers : T ^ (3 / 5 - μ) * T ^ μ = T ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    rw [hpowers] at hmul
    have hDl := mul_le_mul_of_nonneg_left hlU hD
    nlinarith only [hmul, hDl, hk]
  have hCT' : C * T ≤ C * l * T :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hl1) hT0.le
  have hCl : C * l ≤ C * l * T := by
    exact le_mul_of_one_le_right (mul_nonneg hC hl0) hT
  have hkn := mul_le_mul_of_nonneg_left hnegative hk0
  have hklT := mul_le_mul_of_nonneg_right hkl hT0.le
  dsimp [D] at hklT
  nlinarith only [hCT', hCl, hkn, hklT]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeMomentFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary transfer factors for sampling distinct prime products -/

namespace Ostmann

theorem prime_moment_factorial_bound (J k : ℕ) (a : ℝ) (hJ : 0 < J)
    (hk : (k : ℝ) ≤ Real.exp a * J) :
    2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤ 2 * Real.exp ((k : ℝ) * a) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hk k
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  apply (div_le_iff₀ (pow_pos hJ0 _)).mpr
  nlinarith only [hfac, hp]

theorem prime_moment_square_factor_bound (J Z k l I : ℕ) (a t C : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hZ : (Z : ℝ) ≤ Real.exp t) (hZ1 : 1 ≤ Z)
    (hI : (I : ℝ) ≤ Real.exp C) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
      Real.exp (2 + C + 2 * l + (k : ℝ) * a) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hZpow : ((Z ^ k + 1 : ℕ) : ℝ) ≤ 2 * Real.exp ((k : ℝ) * t) := by
    have h1 : (1 : ℝ) ≤ (Z : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hZ1)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z) hZ k
    rw [← Real.exp_nat_mul] at hp
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    linarith
  calc
    _ ≤ (2 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (2 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (Real.exp 1 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem prime_moment_nonsquare_factor_bound (J k l I U : ℕ) (a t C A B : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hI : (I : ℝ) ≤ Real.exp C) (hU : (U : ℝ) ≤ Real.exp B)
    (hA : 0 ≤ A) (hmass : A ≤ Real.exp B) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
      Real.exp (4 + C + 2 * l + 4 * l * B + (k : ℝ) * (a - t)) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one,
      show (2 : ℝ) ^ 3 = 8 by norm_num] using hh
  have hfac' : 2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤
      Real.exp 1 * Real.exp ((k : ℝ) * (a - t)) :=
    hfac.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _))
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hUp := pow_le_pow_left₀ (Nat.cast_nonneg U : (0 : ℝ) ≤ U) hU (2 * l)
  have hAp := pow_le_pow_left₀ hA hmass (2 * l)
  rw [← Real.exp_nat_mul] at hUp hAp
  calc
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) *
        ((Real.exp 3 * Real.exp ((2 * l : ℕ) * B)) * Real.exp ((2 * l : ℕ) * B)) := by
      gcongr
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem prime_moment_sampling_ratio (C T : ℝ) (J k : ℕ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hJ : Real.exp T ≤ C * T * J)
    (hk : (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ)) :
    (k : ℝ) ≤ Real.exp (2 * C + 3 * Real.log T - T) * J := by
  have hT0 : 0 < T := by linarith
  have hkT : (k : ℝ) ≤ 2 * T := by
    apply hk.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hconst : 2 * C ≤ Real.exp (2 * C) := by linarith [Real.add_one_le_exp (2 * C)]
  have hpower : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by omega)
  have hbound : 2 * C * T ^ 2 ≤ Real.exp (2 * C + 3 * Real.log T) := by
    calc
      _ ≤ Real.exp (2 * C) * T ^ 3 := mul_le_mul hconst hpower (by positivity) (Real.exp_nonneg _)
      _ = _ := by
        have hx : Real.exp (3 * Real.log T) = T ^ 3 := by
          calc
            _ = Real.exp ((3 : ℕ) * Real.log T) := by norm_num
            _ = (Real.exp (Real.log T)) ^ 3 := Real.exp_nat_mul _ _
            _ = _ := by rw [Real.exp_log hT0]
        rw [Real.exp_add, hx]
  have hscaled : (k : ℝ) * Real.exp T ≤ Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ ≤ (k : ℝ) * (C * T * J) := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)
      _ ≤ (2 * T) * (C * T * J) := mul_le_mul_of_nonneg_right hkT (by positivity)
      _ = (2 * C * T ^ 2) * J := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)
  have heq : (Real.exp (2 * C + 3 * Real.log T - T) * J) * Real.exp T =
      Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ = (Real.exp (2 * C + 3 * Real.log T - T) * Real.exp T) * J := by ring
      _ = _ := by rw [← Real.exp_add, sub_add_cancel]
  exact (mul_le_mul_iff_left₀ (Real.exp_pos T)).mp (hscaled.trans_eq heq.symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeMomentAsymptotics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square and nonsquare transfer factors at manuscript scales -/

namespace Ostmann

open Filter

theorem eventual_prime_moment_factors (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ J Z k l I U : ℕ, ∀ A : ℝ,
      0 < J → 1 ≤ Z → Real.exp T ≤ C * T * J →
      (Z : ℝ) ≤ Real.exp (T + 1) →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      0 ≤ A → A ≤ Real.exp (C * T) →
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ))) ^ (2 * l)) ∧
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
        ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
        (Real.exp (-10 * T)) ^ (2 * l)) := by
  let D := 4 * C + 10
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventual_prime_product_parameter_budget D (2 * ε) hD (by positivity),
    eventual_prime_product_error_budget D hD, eventually_ge_atTop (1 : ℝ)] with T hs he hT
  intro J Z k l I U A hJ hZ1 hpop hZ hkL hkU hl1 hlL hlU hI hU hA hmass
  have hT0 : 0 ≤ T := by linarith
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  have hratio := prime_moment_sampling_ratio C T J k hC0 hT hpop hkU
  have hratio' : (k : ℝ) ≤ Real.exp ((2 * C + 1 + 3 * Real.log T) - (T + 1)) * J := by
    have heq : (2 * C + 1 + 3 * Real.log T) - (T + 1) = 2 * C + 3 * Real.log T - T := by ring
    simpa only [heq] using hratio
  constructor
  · apply (prime_moment_square_factor_bound J Z k l I (2 * C + 1 + 3 * Real.log T)
      (T + 1) (C * T) hJ hratio' hZ hZ1 hI).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := hs k l hk0 hkU hlL hlU
    have hconst : 2 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hkconst : (k : ℝ) * (2 * C + 1 + 3 * Real.log T) ≤
        k * (D + 3 * Real.log T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hkconst]
  · apply (prime_moment_nonsquare_factor_bound J k l I U (2 * C + 3 * Real.log T)
      T (C * T) A (C * T) hJ hratio hI hU hA hmass).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := he k l hkL hl1' hlU
    have hconst : 4 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hlT : 4 * (l : ℝ) * (C * T) ≤ 2 * D * l * T := by
      have hh : 4 * C ≤ 2 * D := by dsimp [D]; linarith
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hl0) hT0
      nlinarith only [hmul]
    have hkconst : (k : ℝ) * (2 * C + 3 * Real.log T - T) ≤
        k * (D + 3 * Real.log T - T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hlT, hkconst]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorCoefficientError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform errors survive both finite divisor sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem sixteenth_divisor_weight_bound (K : ℕ) :
    (1 + 1 / 16 : ℝ) ^ K ≤ Real.exp ((K : ℝ) / 16) := by
  have hb : (1 + 1 / 16 : ℝ) ≤ Real.exp (1 / 16) := by
    linarith [Real.add_one_le_exp (1 / 16 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 1 / 16) hb K
  simpa only [← Real.exp_nat_mul, div_eq_mul_inv, one_mul] using hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticParameterGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite phase and scale grids for the quadratic coefficient arrays -/

namespace Ostmann

theorem quadraticParameterGrid_card_le (Rmax δ : ℝ) (hRmax : 0 ≤ Rmax) (hδ : 0 < δ) :
    ((quadraticParameterGrid Rmax δ).card : ℝ) ≤ (1 / δ + 1) * (Rmax / δ + 1) := by
  have ha : (⌊1 / δ⌋₊ : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hb : (⌊Rmax / δ⌋₊ : ℝ) ≤ Rmax / δ := Nat.floor_le (div_nonneg hRmax hδ.le)
  simp only [quadraticParameterGrid, Finset.card_product, Finset.card_range, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGridRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed polynomial-size grid with negligible approximation error -/

namespace Ostmann

open Filter
open scoped SchwartzMap

theorem quadraticParameterGrid_exponential_card (T : ℝ) (hT : 1 ≤ T) :
    ((quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card : ℝ) ≤
      Real.exp (416 * T) := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (1 : ℝ) ≤ Real.exp (200 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have h2 : (1 : ℝ) ≤ Real.exp (214 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfour : (4 : ℝ) ≤ Real.exp (2 * T) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  apply (quadraticParameterGrid_card_le _ _ (Real.exp_nonneg _) (Real.exp_pos _)).trans
  have hinv : 1 / Real.exp (-200 * T) = Real.exp (200 * T) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hratio : Real.exp (14 * T) / Real.exp (-200 * T) = Real.exp (214 * T) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hinv, hratio]
  calc
    _ ≤ (2 * Real.exp (200 * T)) * (2 * Real.exp (214 * T)) := by gcongr <;> linarith
    _ = 4 * Real.exp (414 * T) := by
      rw [mul_mul_mul_comm, ← Real.exp_add,
        show 200 * T + 214 * T = 414 * T by ring]
      norm_num
    _ ≤ Real.exp (2 * T) * Real.exp (414 * T) := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedQuadraticFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem mem_quadraticFamilyParameters (T : ℝ) (L : ℕ) (i : QuadraticFamilyIndex) :
    i ∈ quadraticFamilyParameters T L ↔
      i.1 < 4 * L ∧ i.2.1 < L ∧
      (1 ≤ i.2.2.1 ∧ i.2.2.1 ≤ ⌊Real.exp (7 * T)⌋₊) ∧
      i.2.2.2 ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_range, Finset.mem_Icc]

theorem quadraticFamilyParameters_card (T : ℝ) (L : ℕ) :
    (quadraticFamilyParameters T L).card =
      (4 * L) * (L * (⌊Real.exp (7 * T)⌋₊ *
        (quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Nat.card_Icc, Nat.add_sub_cancel]

theorem eventual_quadraticFamilyParameters_card :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ, (L : ℝ) ≤ Real.exp (T / 25) →
      ((quadraticFamilyParameters T L).card : ℝ) ≤ Real.exp (425 * T) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
  have hg := quadraticParameterGrid_exponential_card T (by linarith)
  intro L hL
  have hfour : (4 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  rw [quadraticFamilyParameters_card]
  push_cast
  calc
    _ ≤ (Real.exp T * Real.exp (T / 25)) * (Real.exp (T / 25) *
        (Real.exp (7 * T) * Real.exp (416 * T))) := by
      gcongr
      · exact Nat.floor_le (Real.exp_nonneg _)
    _ = Real.exp (T + T / 25 + T / 25 + 7 * T + 416 * T) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullCoefficientMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial absolute mass for the full coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem fullQuadraticCoefficient_norm_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R H : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ)
    (hR : 0 < R) (hH : 0 ≤ H) (hP : 0 < P) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s‖ ≤
      ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P) *
          ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply divisorWeightedCoefficient_norm_le Q ξ _ s _ (by positivity) hξ
  intro V hV
  have hv : 0 < V.toList.prod := prime_list_prod_pos _
    (primeSet_list_prime V (fun p hp => hQ p (Finset.mem_powerset.mp hV hp)))
  exact primeDivisorMultiples_combination_bound Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod H s P
    hP hs hR (by exact_mod_cast hv) hH hΦ c hc

theorem eventual_full_coefficient_point_bound (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ s : ℕ) (θ : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → 0 < s →
      ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s‖ ≤ Real.exp (2 * T) := by
  let C := SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  filter_upwards [eventually_ge_atTop C, eventually_ge_atTop (0 : ℝ)] with T hTC hT
  intro Q hQ D R P M h₀ s θ hcard hlarge hL hR hP hs
  have hC : C ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hLs : Real.sqrt Q.toList.prod ≤ Real.exp (T / 50) := by
    apply (Real.sqrt_le_sqrt hL).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  have he : (1 + 1 / 16 : ℝ) ^ Q.card ≤ Real.exp (T / 16) :=
    (sixteenth_divisor_weight_bound Q.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hm : (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤ Real.exp (T / 1000) :=
    (reciprocal_sqrt_divisor_mass_le Q hlarge).trans (Real.exp_le_exp.mpr (by linarith))
  have hb := fullQuadraticCoefficient_norm_le Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ) Φ R H P (quadraticSymbolCoefficient M)
    (quadraticDivisorSymbol M) s hR hH hP hs hΦ
    (fun U _ => quadraticSymbolCoefficient_norm_le M U)
    (fun V _ => quadraticDivisorSymbol_norm_le M V)
  apply hb.trans
  change ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
    (1 + 1 / 16 : ℝ) ^ Q.card / P) * _ ≤ _
  rw [mul_assoc (Real.sqrt (Q.toList.prod : ℝ))]
  calc
    _ ≤ (Real.exp (T / 50) * Real.exp T * Real.exp (T / 16) / 1) * Real.exp (T / 1000) := by
      gcongr
      exact_mod_cast hP
    _ = Real.exp (T / 50 + T + T / 16 + T / 1000) := by
      rw [div_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventual_arithmetic_coefficient_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      (∑ s : S, ‖rootNormalizedCoefficient
        (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) s‖) ≤ Real.exp (16 * T) := by
  filter_upwards [eventual_full_coefficient_point_bound H Φ hH hΦ] with T hp
  intro Q hQ D R P M h₀ θ S hcard hlarge hL hR hP hS hScard
  apply (rootNormalizedCoefficient_mass_le S _ (Real.exp (2 * T)) hS
    (fun s hs => hp Q hQ D R P M h₀ s θ hcard hlarge hL hR hP (hS s hs))).trans
  calc
    _ ≤ Real.exp (14 * T) * Real.exp (2 * T) :=
      mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_fixed_quadratic_family_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      ∀ i ∈ quadraticFamilyParameters T Q.toList.prod,
      (∑ s : S, ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤
        Real.exp (16 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_mass H Φ hH hΦ] with T hm
  intro Q hQ D S hcard hlarge hL hS hScard i hi
  have hmem := (mem_quadraticFamilyParameters T Q.toList.prod i).mp hi
  have hR : 0 < quadraticGridScale (Real.exp (-200 * T)) i.2.2.2 := by
    unfold quadraticGridScale
    positivity
  exact hm Q hQ D _ _ _ _ _ S hcard hlarge hL hR hmem.2.2.1.1 hS hScard

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformPrimeProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite-family moment bound under the original prime-product law -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- The manuscript's fixed-family estimate. All sampling and numerical
transfer factors are discharged; only Bonami's precisely stated published
inequality is an analytic input to this moment calculation. -/
theorem eventual_uniform_prime_product_moment (hB : PublishedBonamiBound)
    (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (P S R : Finset ℕ) (U Z k l : ℕ),
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ C * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (Fintype.card I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      ∀ (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ),
      0 ≤ E → 0 ≤ A → A ≤ Real.exp (C * T) →
      (∀ i, (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E) →
      (∀ i, (∑ s : S, ‖b i s‖) ≤ A) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) * Real.sqrt E +
          Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_prime_moment_factors C ε hC hε] with T hfactor
  intro I _ P S R U Z k l hS hR hP hodd hU hZ hZ1 hpop hZU hk hsize hkL hkU
    hl hlL hlU hI hUU b pick E A hE hA hAA henergy hmass
  have hJ : 0 < P.card := by nlinarith
  obtain ⟨hsquare, hnonsquare⟩ := hfactor P.card Z k l (Fintype.card I) U A
    hJ hZ1 hpop hZU hkL hkU hl hlL hlU hI hUU hA hAA
  have henergy' (i : I) :
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E := by
    apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) (henergy i)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le (2 * l) 1)) _)
      (sq_nonneg _)
  exact prime_product_family_norm_transfer hB P S R hS hR hP hodd U Z k l hU hZ
    (by omega) hk hsize b pick E A _ _ hE (Real.exp_nonneg _) (Real.exp_nonneg _)
    henergy' hmass hsquare hnonsquare

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedCoefficientMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the published Bonami input to the actual fixed coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_fixed_coefficient_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H η : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H) (hη : 0 < η)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (J : Finset QuadraticFamilyIndex)
      (P S R : Finset ℕ) (U Z k l : ℕ) (α : ℝ),
      J ⊆ quadraticFamilyParameters T Q.toList.prod →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (500 * T) →
      (∀ i ∈ J, Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp (α * Q.card)) →
      ∀ pick : ℕ → J,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((α + η) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_uniform_prime_product_moment hB Cpop (η / 1000)
      (by linarith) (by positivity),
    eventual_quadraticFamilyParameters_card,
    eventual_fixed_quadratic_family_mass H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hcard hmass hT
  intro Q hQ D J P S R U Z k l α hJ hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU hnorm pick
  have hJcard : (Fintype.card J : ℝ) ≤ Real.exp (Cpop * T) := by
    have hc : (J.card : ℝ) ≤ ((quadraticFamilyParameters T Q.toList.prod).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hJ)
    rw [Fintype.card_coe]
    exact (hc.trans (hcard Q.toList.prod hL)).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT]))
  have hSpos : ∀ s ∈ S, 0 < s := fun s hs => Nat.pos_of_ne_zero (hS s hs).ne_zero
  have hmass' (i : J) : (∑ s : S,
      ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤ Real.exp (16 * T) :=
    hmass Q hQ D S hQT hlarge hL hSpos hScard i (hJ i.property)
  have he (i : J) :
      (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card *
        ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖ ^ 2) ≤
        Real.exp (2 * (α * Q.card)) := by
    rw [rootNormalizedCoefficient_energy]
    have hh := (Real.sqrt_le_iff.mp (hnorm i i.property)).2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hh
  have hh := hm P S R U Z k l hS hSR hP hodd hSU hPZ hZ hpop hZU hk hsize hkL hkU hl
    hlL hlU hJcard (hU.trans (Real.exp_le_exp.mpr (by nlinarith))) (fun i s => rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s)
    pick (Real.exp (2 * (α * Q.card))) (Real.exp (16 * T)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT])) he hmass'
  apply hh.trans
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_left
  rw [← Real.exp_half, show 2 * (α * Q.card) / 2 = α * Q.card by ring, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hkη := mul_le_mul_of_nonneg_left hK hη.le
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LargeKernelFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed principal family on the large squarefree kernels -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem principalQuadraticParameters_subset (T : ℝ) (L : ℕ) :
    principalQuadraticParameters T L ⊆ quadraticFamilyParameters T L := Finset.filter_subset _ _

theorem eventual_large_kernel_family_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, Q.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (i : QuadraticFamilyIndex),
      i ∈ principalQuadraticParameters T Q.toList.prod →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤
        Real.exp ((7 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_full_large_kernel_norm C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hrange hcop hu huU D i hi
  have hp := (Finset.mem_filter.mp hi).2
  have hgrid : 0 < quadraticGridScale (Real.exp (-200 * T)) i.2.2.2 := by
    unfold quadraticGridScale
    positivity
  simp only [fixedQuadraticCoefficient, arithmeticQuadraticCoefficient, hp]
  exact hn Q hQ M S u hK hlarge hM hS hrange hcop hu huU D _ _ _ _ _
    hgrid
    (fun U _ => quadraticSymbolCoefficient_norm_le _ U)
    (fun V _ => quadraticDivisorSymbol_norm_le _ V)

theorem eventual_large_kernel_prime_moment_oai (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ Q.toList.prod.Coprime s) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → principalQuadraticParameters T Q.toList.prod,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_fixed_coefficient_moment hB Cpop hCpop H (1 / 1000) Φ hH (by norm_num) hΦ,
    eventual_large_kernel_family_norm 14 H (1 / 1000) Φ (by norm_num) hH (by norm_num) hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hn hT
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hrange hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hU500 : (U : ℝ) ≤ Real.exp (500 * T) :=
    hU.trans (Real.exp_le_exp.mpr (by linarith))
  have huU : ((2 * l : ℕ) : ℝ) ≤ 2 * T ^ (1 / 1000000 : ℝ) := by push_cast; linarith
  have he (i : QuadraticFamilyIndex) (hi : i ∈ principalQuadraticParameters T Q.toList.prod) :
      Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp ((8 / 1000 : ℝ) * Q.card) := by
    have hh := hn Q hQ U S ((2 * l : ℕ) : ℝ) hK hlarge hU hS
      (fun s hs => ⟨(hrange s hs).1, hSU s hs⟩) (fun s hs => (hrange s hs).2)
      (by exact_mod_cast (show 2 ≤ 2 * l by omega)) huU D i hi
    norm_num only at hh ⊢
    exact hh
  have hh := hm Q hQ D (principalQuadraticParameters T Q.toList.prod) P S R U Z k l (8 / 1000)
    (principalQuadraticParameters_subset _ _) hK hQT hlarge hL hS hSR hP hodd hSU hPZ
    hScard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU500 he pick
  norm_num only at hh ⊢
  exact hh

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_large_kernel_prime_moment_oai := @OAI.Ostmann.eventual_large_kernel_prime_moment_oai
