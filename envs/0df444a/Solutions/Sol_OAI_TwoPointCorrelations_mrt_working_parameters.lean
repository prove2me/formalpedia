-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_working_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:39:33.380249+00:00
-- url     : https://prove2.me/submissions/bba3c247-d115-4163-8f64-45a3f743d6d7

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingLength
namespace OAI

/-! Cap the original short length before choosing its prime bands. The
uncapped branch is kept exactly; on the capped branch the omitted final
block is negligible compared with W^(-1/4). -/

namespace TwoPointCorrelations

open _root_.Filter



lemma mrt_working_cap_upper (W : ℝ) :
    (mrtWorkingCap W : ℝ) ≤ Real.exp (Real.sqrt W / 2) :=
  Nat.floor_le (Real.exp_pos _).le

/-- The fixed cap eventually exceeds every prescribed power of W. -/
theorem mrt_working_cap_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, W ^ a ≤ (mrtWorkingCap W : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually
    (eventually_ge_atTop (8 * ((a : ℝ) + 1)))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have ht0 : 0 ≤ W ^ (1 / 4 : ℝ) := Real.rpow_nonneg hW0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg ht0, one_mul] at hs
  have ht2 : (W ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.sqrt_eq_rpow]
    norm_num
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have ham := mul_le_mul_of_nonneg_left hs ha
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hmul := mul_nonneg ht0 (sub_nonneg.mpr ht)
  have he : Real.log 2 + (a : ℝ) * Real.log W ≤ Real.sqrt W / 2 := by
    nlinarith
  have hpow : 2 * W ^ a ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2 + (a : ℝ) * Real.log W) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_nat_mul, Real.exp_log hW0]
      _ ≤ _ := Real.exp_le_exp.mpr he
  have hp : 1 ≤ W ^ a := one_le_pow₀ hW
  have hf := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hf
  linarith


lemma mrt_working_length_exp_upper (H : ℕ) (W : ℝ) :
    (mrtWorkingLength H W : ℝ) ≤ Real.exp (Real.sqrt W) := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact h
  · exact (mrt_working_cap_upper W).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W]))




lemma mrt_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1 : ℝ) < mrtWorkingLength H W) :
    Real.log (Real.log (mrtWorkingLength H W : ℝ)) ≤ (1 / 2 : ℝ) * Real.log W := by
  have hpos : (0 : ℝ) < mrtWorkingLength H W := by linarith
  have hlpos := Real.log_pos hH
  have hlog := Real.log_le_log hpos (mrt_working_length_exp_upper H W)
  rw [Real.log_exp] at hlog
  have hh := Real.log_le_log hlpos hlog
  rw [Real.log_sqrt hW.le] at hh
  linarith


/-- The bound W ≤ log(H)^5 forces H above any fixed power of W. -/
theorem mrt_working_original_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℝ, 0 < H → 1 ≤ Real.log H →
      W ≤ (Real.log H) ^ (5 : ℕ) → W ^ a ≤ H := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop (a : ℝ))
  filter_upwards [hs, ht, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hW), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hW0.le _), one_mul] at hs
  intro H hH0 hlog hWH
  have hp : W ^ (1 / 5 : ℝ) ≤ Real.log H := by
    calc
      _ ≤ ((Real.log H) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = Real.log H := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log H)]
        norm_num
  have ha : (a : ℝ) * Real.log W ≤ W ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ W ^ (1 / 10 : ℝ) * W ^ (1 / 10 : ℝ) :=
        mul_le_mul ht hs (Real.log_nonneg hW) (Real.rpow_nonneg hW0.le _)
      _ = _ := by rw [← Real.rpow_add hW0]; norm_num
  calc
    W ^ a = Real.exp ((a : ℝ) * Real.log W) := by
      rw [Real.exp_nat_mul, Real.exp_log hW0]
    _ ≤ Real.exp (Real.log H) := Real.exp_le_exp.mpr (ha.trans hp)
    _ = H := Real.exp_log hH0

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingLength
namespace OAI

/-! A fifth-root logarithmic cap, obtained from the general square-root
cap by substitution. Its size suits the common Diophantine parameter. -/
namespace TwoPointCorrelations

open _root_.Filter


lemma major_arc_working_root {W : ℝ} (hW : 0 ≤ W) :
    Real.sqrt (W^(2/5:ℝ))=W^(1/5:ℝ) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hW]
  norm_num


lemma major_arc_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1:ℝ) < majorArcWorkingLength H W) :
    Real.log (Real.log (majorArcWorkingLength H W:ℝ)) ≤ (1/5:ℝ)*Real.log W := by
  have hh := mrt_working_length_loglog (Real.rpow_pos_of_pos hW (2/5)) hH
  rw [Real.log_rpow hW] at hh
  dsimp only [majorArcWorkingLength]
  linarith

lemma major_arc_working_length_exp_upper (H : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (majorArcWorkingLength H W:ℝ) ≤ Real.exp (W^(1/5:ℝ)) := by
  simpa only [majorArcWorkingLength,major_arc_working_root hW] using
    mrt_working_length_exp_upper H (W^(2/5:ℝ))

theorem major_arc_working_length_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 → W^a ≤ (majorArcWorkingLength H W:ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually (mrt_working_cap_power (5*a)),
    mrt_working_original_power a,eventually_ge_atTop (1:ℝ)] with W hcap horiginal hW
  intro H hH hlog hWH
  have hW0 : 0 < W := by linarith
  have hc : W^a ≤ (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
    apply le_trans _ hcap
    rw [← Real.rpow_mul_natCast hW0.le (2/5:ℝ) (5*a)]
    rw [show (2/5:ℝ)*(5*a:ℕ)=(2:ℝ)*a by push_cast; ring]
    rw [Real.rpow_mul_natCast hW0.le,Real.rpow_two]
    exact pow_le_pow_left₀ hW0.le (by nlinarith) a
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · exact horiginal H (by exact_mod_cast hH) hlog hWH
  · exact hc



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingOuterScale
namespace OAI

/-! The capped working length fits below the common square-root origin
cutoff. Its boundary remains negligible after the correction division. -/

namespace TwoPointCorrelations

open _root_.Filter

theorem mrt_working_length_add_two_below_sqrt :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ H : ℕ, majorArcWorkingLength H W+2 ≤ ⌈Real.sqrt (X:ℝ)⌉₊ := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<624/625 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hlog.eventually hp,hlog.eventually (eventually_ge_atTop (4:ℝ)),
    eventually_ge_atTop (2:ℕ)] with X hp hL hX
  change 4 ≤ (Real.log (X:ℝ))^(624/625:ℝ) at hp
  intro W hW hWX H
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hpow : (Real.log (X:ℝ))^(1/625:ℝ) ≤ Real.log (X:ℝ)/4 := by
    have he : (Real.log (X:ℝ))^(1/625:ℝ)*
        (Real.log (X:ℝ))^(624/625:ℝ)=Real.log (X:ℝ) := by
      rw [← Real.rpow_add hL0]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg hL0.le (1/625))
    rw [he] at hh
    linarith
  have hroot : W^(1/5:ℝ) ≤ Real.log (X:ℝ)/4 := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^(1/5:ℝ) :=
        Real.rpow_le_rpow (by linarith) hWX (by norm_num)
      _ = (Real.log (X:ℝ))^(1/625:ℝ) := by
        rw [← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := hpow
  have hsize : (majorArcWorkingLength H W:ℝ) ≤ Real.exp (Real.log (X:ℝ)/4) :=
    (major_arc_working_length_exp_upper H (by linarith)).trans (Real.exp_le_exp.mpr hroot)
  have he : (Real.exp (Real.log (X:ℝ)/4))^2=Real.sqrt (X:ℝ) := by
    rw [pow_two,← Real.exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX0]
    congr 1
    ring
  have htwo : 2 ≤ Real.exp (Real.log (X:ℝ)/4) := by
    linarith [Real.add_one_le_exp (Real.log (X:ℝ)/4)]
  have hsum : (majorArcWorkingLength H W:ℝ)+2 ≤ Real.sqrt (X:ℝ) := by
    nlinarith
  have hh := hsum.trans (Nat.le_ceil (Real.sqrt (X:ℝ)))
  exact_mod_cast hh



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical







lemma mrt_band_index_le_log_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hlogQ : 1 ≤ Real.log Q) : (j : ℝ) ≤ Real.log (mrtBandUpper Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  simp only [mrtBandUpper, Real.log_exp]
  calc
    (j : ℝ) ≤ (j : ℝ) ^ (4 * j + 2) := by
      simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 4 * j + 2 by omega)
    _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by
      have hh := one_le_pow₀ (n := j) hlogQ
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ j) (4 * j + 2)]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMaximalBand
namespace OAI

/-! A maximal actual MRT band below a prescribed logarithmic cutoff.
The cubic next-band comparison supplies a large final lower endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_band_upper_log_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q j) := by
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hi.trans hij
  have hbase : (i:ℝ)^(4*i+2) ≤ (j:ℝ)^(4*j+2) :=
    (pow_le_pow_left₀ hi0 (Nat.cast_le.mpr hij) _).trans
      (pow_le_pow_right₀ hj1 (by omega))
  simp only [mrtBandUpper,Real.log_exp]
  exact mul_le_mul hbase (pow_le_pow_right₀ hQ hij)
    (by positivity) (by positivity)

theorem mrt_maximal_band_exists {Q B : ℝ} (hQ : 1 ≤ Real.log Q)
    (hB : Real.log Q ≤ B) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.log (mrtBandUpper Q J) ≤ B ∧
      B < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ B := by
  have hB0 : 0 ≤ B := by linarith
  let S := (Icc 1 ⌊B⌋₊).filter (fun j => Real.log (mrtBandUpper Q j) ≤ B)
  have h1 : 1 ∈ S := by
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨le_rfl,?_⟩,?_⟩
    · exact Nat.le_floor (by simpa using (show (1:ℝ) ≤ B by linarith))
    · simpa [mrtBandUpper] using hB
  let J := S.max' ⟨1,h1⟩
  have hJmem : J ∈ S := max'_mem S ⟨1,h1⟩
  have hJ : 1 ≤ J := (mem_Icc.mp (mem_filter.mp hJmem).1).1
  have hJB : Real.log (mrtBandUpper Q J) ≤ B := (mem_filter.mp hJmem).2
  refine ⟨J,hJ,hJB,?_,fun j hj =>
    (mrt_band_upper_log_mono hQ (mem_Icc.mp hj).1 (mem_Icc.mp hj).2).trans hJB⟩
  by_contra hh
  have hnext : Real.log (mrtBandUpper Q (J+1)) ≤ B := le_of_not_gt hh
  have hnextB : J+1 ≤ ⌊B⌋₊ := Nat.le_floor
    ((mrt_band_index_le_log_upper Q (J+1) (by omega) hQ).trans hnext)
  have hnextmem : J+1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hnextB⟩,hnext⟩
  have hh' : J+1 ≤ J := le_max' S (J+1) hnextmem
  omega

/-- Cubing the last lower endpoint dominates the next upper endpoint;
the small exceptional index is handled by direct integer arithmetic. -/
lemma mrt_next_band_log_le_lower_cube {P Q : ℝ}
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) {j : ℕ} (hj : 2 ≤ j) :
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.log (mrtBandLower P Q j)^3 := by
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hindex : ((j+1:ℕ):ℝ)^(4*(j+1)+2) ≤ (j:ℝ)^(12*j) := by
    by_cases htwo : j=2
    · subst j
      norm_num
    have hj3 : 3 ≤ j := by omega
    have hj3R : (3:ℝ) ≤ j := by exact_mod_cast hj3
    have hsq : ((j+1:ℕ):ℝ) ≤ (j:ℝ)^2 := by push_cast; nlinarith
    calc
      _ ≤ ((j:ℝ)^2)^(4*(j+1)+2) := pow_le_pow_left₀ (by positivity) hsq _
      _ = (j:ℝ)^(2*(4*(j+1)+2)) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_right₀ hj1 (by omega)
  have hq : Real.log Q^(j+1) ≤ Real.log Q^(3*(j-1)) :=
    pow_le_pow_right₀ hQ (by omega)
  have hp : (1:ℝ) ≤ Real.log P^3 := one_le_pow₀ hP
  have he1 : 4*j*3=12*j := by omega
  have he2 : (j-1)*3=3*(j-1) := by omega
  simp only [mrtBandUpper,mrtBandLower,Real.log_exp,mul_pow,← pow_mul,he1,he2]
  exact (mul_le_mul hindex hq (by positivity) (by positivity)).trans
    (le_mul_of_one_le_right (by positivity) hp)

/-- The first-band alternative covers J=1. Otherwise maximality and the
cubic comparison force the final lower endpoint above the desired target. -/
theorem mrt_maximal_band_lower {P Q B K : ℝ}
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hB : Real.log Q ≤ B) (hK : K^3 ≤ B)
    (hfirst : K ≤ Real.log P ∨ Real.log (mrtBandUpper Q 2) ≤ B) :
    ∃ J : ℕ, 1 ≤ J ∧ K ≤ Real.log (mrtBandLower P Q J) ∧
      B < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ B := by
  obtain ⟨J,hJ,_,hnext,hall⟩ := mrt_maximal_band_exists hQ hB
  refine ⟨J,hJ,?_,hnext,hall⟩
  by_cases hJ1 : J=1
  · subst J
    rcases hfirst with hp | hu
    · simpa [mrtBandLower] using hp
    · norm_num only at hnext
      linarith
  · have hJ2 : 2 ≤ J := by omega
    apply le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0)
      (show 0 ≤ Real.log (mrtBandLower P Q J) by
        simp only [mrtBandLower,Real.log_exp]
        positivity)
    exact hK.trans (hnext.le.trans (mrt_next_band_log_le_lower_cube hP hQ hJ2))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuotientFinalBand
namespace OAI

/-! A single final band for every quotient dyadic above the square-root
cutoff. The band is chosen before the quotient and the dyadic origin. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

lemma mrt_quotient_band_target :
    ∀ᶠ L : ℝ in atTop, (400*Real.log L+1)^3 ≤ Real.sqrt L/2 := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).bound
    (show (0:ℝ)<1/1600 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ)] with L hb hp hL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hh : 400*Real.log L+1 ≤ L^(1/6:ℝ)/2 := by linarith
  calc
    _ ≤ (L^(1/6:ℝ)/2)^3 := pow_le_pow_left₀ (by positivity) hh 3
    _ = Real.sqrt L/8 := by
      rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hL0.le,Real.sqrt_eq_rpow]
      norm_num
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg L]

lemma mrt_quotient_band_alternative :
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      400*Real.log L+1 ≤ Real.log P ∨
        Real.log (mrtBandUpper Q 2) ≤ Real.sqrt L/2 := by
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<249/500 by norm_num)).eventually
    (eventually_ge_atTop (2048:ℝ))
  filter_upwards [hp,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hp hL hlogL
  have hL0 : 0 < L := by linarith
  intro P Q hQ hbudget
  by_cases hfirst : 400*Real.log L+1 ≤ Real.log P
  · exact Or.inl hfirst
  right
  have hnot : Real.log P < 400*Real.log L+1 := lt_of_not_ge hfirst
  have hsmall : Real.log (Real.log Q) ≤ Real.log L/1000 := by linarith
  have hQ0 : 0 < Real.log Q := by linarith
  have hq : Real.log Q ≤ L^(1/1000:ℝ) := by
    calc
      _ = Real.exp (Real.log (Real.log Q)) := (Real.exp_log hQ0).symm
      _ ≤ Real.exp (Real.log L/1000) := Real.exp_le_exp.mpr hsmall
      _ = _ := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring
  have hu : Real.log (mrtBandUpper Q 2) ≤ 1024*L^(1/500:ℝ) := by
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log Q) hq 2
    have he : (L^(1/1000:ℝ))^2=L^(1/500:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [he] at hs
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤1024)
    have heq : Real.log (mrtBandUpper Q 2)=1024*(Real.log Q)^2 := by
      norm_num [mrtBandUpper]
    rw [heq]
    exact hm
  apply hu.trans
  calc
    1024*L^(1/500:ℝ) ≤ (L^(249/500:ℝ)/2)*L^(1/500:ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.sqrt L/2 := by
      rw [div_mul_eq_mul_div,← Real.rpow_add hL0,Real.sqrt_eq_rpow]
      norm_num

lemma mrt_quotient_dyadic_log {X n : ℕ} (hX : 2 ≤ X)
    (hn : ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n) :
    Real.log (X:ℝ)/2 ≤ Real.log (n:ℝ) ∧
      Real.sqrt (Real.log (X:ℝ))/2 ≤ Real.sqrt (Real.log (n:ℝ)) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hnr : Real.sqrt (X:ℝ) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : 0 < (n:ℝ) := (Real.sqrt_pos.2 hX0).trans_le hnr
  have hsq : (X:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [Real.sq_sqrt hX0.le,Real.sqrt_nonneg (X:ℝ)]
  have hl := Real.log_le_log hX0 hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤ X by omega))
  have hln : 0 ≤ Real.log (n:ℝ) := by linarith
  refine ⟨by linarith,?_⟩
  nlinarith [Real.sq_sqrt hLX,Real.sq_sqrt hln,
    Real.sqrt_nonneg (Real.log (X:ℝ)),Real.sqrt_nonneg (Real.log (n:ℝ))]

theorem mrt_quotient_common_final_band :
    ∀ᶠ X : ℕ in atTop, ∀ P Q : ℝ,
      1 ≤ Real.log P → 1 ≤ Real.log Q →
      Real.log Q ≤ Real.sqrt (Real.log X)/2 →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      ∃ J : ℕ, 1 ≤ J ∧
        200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) ∧
        Real.sqrt (Real.log X)/2 < Real.log (mrtBandUpper Q (J+1)) ∧
        (∀ i ∈ Icc 1 J, Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log X)/2) ∧
        ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 4*X →
          200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log n)) := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually mrt_quotient_band_target,
    hlog.eventually mrt_quotient_band_alternative,
    hlog.eventually (eventually_ge_atTop (2:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (4:ℕ)] with X htarget halt hL hLL hX
  change 1 ≤ Real.log (Real.log (X:ℝ)) at hLL
  intro P Q hP hQ hQU hbudget
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hLX : 0 < Real.log (X:ℝ) := by linarith
  have hlog4 : Real.log 4 ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hdouble : Real.log (4*(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hX0.ne']
    linarith
  have hll4 : Real.log (Real.log (4*(X:ℝ))) ≤ 2*Real.log (Real.log (X:ℝ)) := by
    have hpositive : 0 < Real.log (4*(X:ℝ)) := by
      rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hX0.ne']
      linarith [Real.log_nonneg (show (1:ℝ)≤4 by norm_num)]
    have hh := Real.log_le_log hpositive hdouble
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hLX.ne'] at hh
    linarith
  obtain ⟨J,hJ,hlo,hnext,hup⟩ := mrt_maximal_band_lower hP hQ hQU htarget
    (halt P Q hQ hbudget)
  have hlow : 200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) := by
    linarith
  refine ⟨J,hJ,hlow,hnext,hup,?_⟩
  intro n hn hnX
  obtain ⟨hln,hroot⟩ := mrt_quotient_dyadic_log (by omega : 2≤ X) hn
  have hn0 : 0 < Real.log (n:ℝ) := by linarith
  have hnpos : 0 < (n:ℝ) :=
    (Real.sqrt_pos.2 hX0).trans_le ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  have hl4 : Real.log (n:ℝ) ≤ Real.log (4*(X:ℝ)) :=
    Real.log_le_log hnpos (by exact_mod_cast hnX)
  refine ⟨(by linarith [Real.log_le_log hn0 hl4]),?_⟩
  intro i hi
  have he := Real.exp_le_exp.mpr ((hup i hi).trans hroot)
  rwa [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _)] at he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingBand
namespace OAI

/-! Prime-band costs for the fifth-root working length. Both density
and the minor-arc fourth root have the same elementary rate. -/
namespace TwoPointCorrelations

open _root_.Filter





lemma major_arc_working_band_budget (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 10 ≤ Real.log W) (hW0 : 0 < W)
    (hQ : 1 < Q) (hQH : Q ≤ majorArcWorkingLength H W) :
    8192 * (Real.log (Real.log Q) + 1) ≤ (1 / 100 : ℝ) * Real.log (W ^ A) := by
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (show 0 ≤ Real.log W by linarith)
  rw [Real.log_pow]
  nlinarith

lemma major_arc_working_band_resolution (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 1 ≤ W) (hQ : 1 < Q)
    (hQH : Q ≤ majorArcWorkingLength H W) :
    W ^ (100 : ℕ) ≤ mrtBaseResolution (W ^ A) Q (1 / 100) := by
  have hW0 : 0 < W := by linarith
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (Real.log_nonneg hW)
  rw [show W ^ (100 : ℕ) = Real.exp ((100 : ℝ) * Real.log W) by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hW0]
    congr 1
    ring, mrtBaseResolution, Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_nonneg hW]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingParameters
namespace OAI

/-! The literal first prime band, working length and common final band.
The W and X thresholds are independent of the original short length. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem mrt_working_prime_parameters :
    ∀ᶠ W : ℝ in atTop, 2 ≤ W ∧ ∀ H : ℕ, 0 < H →
      1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧
        2 ≤ mrtBaseResolution P Q (1/100) := by
  filter_upwards [major_arc_working_length_power 500003,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10:ℝ))]
    with W hpower hW hlog
  refine ⟨hW,?_⟩
  intro H hH hLH hWH
  let P := W^(500000:ℕ)
  let Q := (majorArcWorkingLength H W:ℝ)/W^3
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hlarge := hpower H hH hLH hWH
  have hP : 2 ≤ P := hW.trans (le_self_pow₀ hW1 (by decide))
  have hPQ : P ≤ Q := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    change W^500000*W^3 ≤ (majorArcWorkingLength H W:ℝ)
    simpa only [← pow_add] using hlarge
  have hLP : 2 ≤ Real.log P := by
    change 2 ≤ Real.log (W^(500000:ℕ))
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hLQ : 1 ≤ Real.log Q :=
    (show (1:ℝ)≤2 by norm_num).trans (hLP.trans
      (Real.log_le_log (by linarith : 0< P) hPQ))
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (hP.trans hPQ)
  have hQH : Q ≤ (majorArcWorkingLength H W:ℝ) :=
    div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hW1)
  have hbudget := major_arc_working_band_budget 500000 le_rfl hlog hW0 hQ hQH
  have hres := major_arc_working_band_resolution 500000 le_rfl hW1 hQ hQH
  exact ⟨hP,hPQ,hLP,hLQ,hbudget,hres,
    (hW.trans (le_self_pow₀ hW1 (by decide))).trans hres⟩

theorem mrt_working_outer_parameters :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 2 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) → ∀ H : ℕ,
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      0 < Q → Real.log Q ≤ Real.sqrt (Real.log X)/2 ∧
        2*Q ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<623/1250 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hlog.eventually hp,hlog.eventually (eventually_ge_atTop (1:ℝ)),
    mrt_working_length_add_two_below_sqrt] with X hp hL hlength
  change 2 ≤ (Real.log (X:ℝ))^(623/1250:ℝ) at hp
  intro W hW hWX H
  dsimp only
  intro hQ
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hroot : W^(1/5:ℝ) ≤ Real.sqrt (Real.log X)/2 := by
    have he : (Real.log (X:ℝ))^(1/625:ℝ)*
        (Real.log (X:ℝ))^(623/1250:ℝ)=Real.sqrt (Real.log X) := by
      rw [← Real.rpow_add hL0,Real.sqrt_eq_rpow]
      norm_num
    have hm := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg hL0.le (1/625))
    rw [he] at hm
    have hw : W^(1/5:ℝ) ≤ (Real.log (X:ℝ))^(1/625:ℝ) := by
      calc
        _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^(1/5:ℝ) :=
          Real.rpow_le_rpow hW0.le hWX (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hL0.le]; norm_num
    linarith
  have hQH : (majorArcWorkingLength H W:ℝ)/W^3 ≤ (majorArcWorkingLength H W:ℝ) :=
    div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hW1)
  constructor
  · have hh := Real.log_le_log hQ
      (hQH.trans (major_arc_working_length_exp_upper H hW0.le))
    rw [Real.log_exp] at hh
    exact hh.trans hroot
  · have hW3 : (2:ℝ) ≤ W^3 := hW.trans (le_self_pow₀ hW1 (by decide))
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (majorArcWorkingLength H W))
      (by norm_num : (0:ℝ)<2) hW3
    have hc : (majorArcWorkingLength H W:ℝ)+2 ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) := by
      exact_mod_cast hlength W hW1 hWX H
    linarith

theorem mrt_working_parameters_oai :
    ∃ W₀ : ℝ, ∃ X₀ : ℕ, ∀ W : ℝ, W₀ ≤ W →
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
    ∀ X : ℕ, X₀ ≤ X → W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      (2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧ 2 ≤ mrtBaseResolution P Q (1/100)) ∧
      (Real.log Q ≤ Real.sqrt (Real.log X)/2 ∧ 2*Q ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ)) ∧
      ∃ J : ℕ, 1 ≤ J ∧
        200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) ∧
        Real.sqrt (Real.log X)/2 < Real.log (mrtBandUpper Q (J+1)) ∧
        (∀ i ∈ Icc 1 J, Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log X)/2) ∧
        ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 4*X →
          200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log n)) := by
  obtain ⟨W₀,hW₀⟩ := Filter.eventually_atTop.mp mrt_working_prime_parameters
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp
    (mrt_working_outer_parameters.and mrt_quotient_common_final_band)
  refine ⟨W₀,X₀,?_⟩
  intro W hW H hH hLH hWH X hX hWX
  have hw := hW₀ W hW
  have hb := hw.2 H hH hLH hWH
  let P := W^(500000:ℕ)
  let Q := (majorArcWorkingLength H W:ℝ)/W^3
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hb.1.trans hb.2.1)
  have hx := hX₀ X hX
  have ho := hx.1 W hw.1 hWX H hQ
  refine ⟨hb,ho,?_⟩
  exact hx.2 P Q ((show (1:ℝ)≤2 by norm_num).trans hb.2.2.1)
    hb.2.2.2.1 ho.1 hb.2.2.2.2.1

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_working_parameters_oai := @OAI.TwoPointCorrelations.mrt_working_parameters_oai
