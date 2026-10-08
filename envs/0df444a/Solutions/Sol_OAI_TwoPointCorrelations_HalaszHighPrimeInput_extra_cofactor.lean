-- Prove2me | solution 1 for OAI.TwoPointCorrelations.HalaszHighPrimeInput.extra_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:22.208564+00:00
-- url     : https://prove2.me/submissions/30b8ed86-c683-43eb-8992-b52e1ac12650

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_HalaszHighPrimeInput_distance_cutoff
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_exceptional_count_window

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators





lemma mrtPrimeAvoids_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeAvoids (P ∪ Q) n ↔ mrtPrimeAvoids P n ∧ mrtPrimeAvoids Q n := by
  simp only [mrtPrimeAvoids, mem_union]
  aesop

lemma mrtPrimeMask_union (P Q : Finset ℕ) (n : ℕ) :
    mrtPrimeMask (P ∪ Q) n = mrtPrimeMask P n * mrtPrimeMask Q n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_union]
  by_cases hp : mrtPrimeAvoids P n <;> by_cases hq : mrtPrimeAvoids Q n <;> simp [hp, hq]





lemma mrtPrimeMask_biUnion {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    mrtPrimeMask (J.biUnion P) n = ∏ j ∈ J, mrtPrimeMask (P j) n := by
  induction J using Finset.induction_on with
  | empty => simp [mrtPrimeMask, mrtPrimeAvoids]
  | @insert j J hj ih =>
    rw [biUnion_insert, mrtPrimeMask_union, prod_insert hj, ih]

lemma mrtTypical_prod {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ) (n : ℕ) :
    (∏ j ∈ J, (1 - mrtPrimeMask (P j) n)) = if mrtTypical J P n then 1 else 0 := by
  induction J using Finset.induction_on with
  | empty => simp [mrtTypical]
  | @insert j J hj ih =>
    rw [prod_insert hj, ih]
    have he : mrtTypical (insert j J) P n ↔
        (¬ mrtPrimeAvoids (P j) n) ∧ mrtTypical J P n := by
      simp only [mrtTypical, mem_insert, mrtPrimeAvoids]
      push Not
      aesop
    rw [he]
    by_cases ha : mrtPrimeAvoids (P j) n <;> by_cases ht : mrtTypical J P n <;>
      simp [mrtPrimeMask, ha, ht]

/-- Exact inclusion-exclusion over missing prime bands, the expansion in
MRT Appendix A before its near-twist mean-value estimate. -/
theorem mrtTypical_inclusion_exclusion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (n : ℕ) :
    (∑ I ∈ J.powerset, (-1 : ℝ) ^ I.card * mrtPrimeMask (I.biUnion P) n) =
      if mrtTypical J P n then 1 else 0 := by
  rw [← mrtTypical_prod, prod_sub]
  apply sum_congr rfl
  intro I _
  rw [prod_const_one, mul_one, mrtPrimeMask_biUnion]





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandPowerCost
namespace OAI

/-! The actual number of original bands costs only a small logarithmic
power in the inclusion-exclusion cofactor estimate. -/
namespace TwoPointCorrelations

open _root_.Filter

theorem halasz_band_power_cost :
    ∀ᶠ L : ℝ in atTop, ∀ (Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt L →
      (2:ℝ)^J ≤ L^(1/1000:ℝ) := by
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000*Real.exp 1000))]
    with L hL hlogL
  intro Q J hQ hU
  have hL0 : 0 < L := by linarith
  have hsqrt : 2*Real.sqrt L ≤ L := by
    have hh : Real.sqrt L ≤ L/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
    linarith
  have hlog2u : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hJ : (J:ℝ)*Real.log 2 ≤ Real.log L/1000 := by
    by_cases hj : (J:ℝ) ≤ Real.exp 1000
    · calc
        _ ≤ (J:ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2u
        _ ≤ Real.exp 1000 := hj
        _ ≤ _ := by linarith
    · have hjbig : Real.exp 1000 ≤ (J:ℝ) := le_of_not_ge hj
      have hj0 : (0:ℝ) < J := (Real.exp_pos _).trans_le hjbig
      have hj1 : (1:ℝ) ≤ J :=
        (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1000)).trans hjbig
      have hjlog : 1000 ≤ Real.log (J:ℝ) := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1000) hjbig
      have hjpow : (J:ℝ)^J ≤ Real.log (mrtBandUpper Q J) := by
        rw [mrtBandUpper,Real.log_exp]
        calc
          _ ≤ (J:ℝ)^(4*J+2) := pow_le_pow_right₀ hj1 (by omega)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hQ)
      have hJlog : (J:ℝ)*Real.log (J:ℝ) ≤ Real.log L := by
        have hh := Real.log_le_log (pow_pos hj0 J)
          (hjpow.trans (hU.trans hsqrt))
        simpa only [Real.log_pow] using hh
      have hh := mul_le_mul_of_nonneg_left hjlog (Nat.cast_nonneg J : (0:ℝ) ≤ J)
      nlinarith
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos hL0]
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalDecay
namespace OAI

/-! The fixed logarithmic saving retained after the actual band count. -/
namespace TwoPointCorrelations

open _root_.Filter

theorem halasz_exceptional_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ B u : ℝ, 0 ≤ B → B ≤ L^(1/1000:ℝ) →
      L^(1/16:ℝ)/2 ≤ |u| →
      C*B*((min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|))+1)*
        Real.exp (-min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|)))+Real.log L/L) ≤
      L^(-1/40:ℝ) := by
  have hK : 0 < C+1 := by linarith
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/250 by norm_num)).bound
    (show (0:ℝ)<1/(4*(C+1)) by positivity)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/250 by norm_num)).eventually
    (eventually_ge_atTop (4*(C+1)))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (100:ℝ))]
    with L hb hp hL hlog
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hlogbound : (C+1)*Real.log L ≤ (1/4:ℝ)*L^(1/250:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hb hK.le
    field_simp at hh
    nlinarith
  have hconst : C+1 ≤ (1/4:ℝ)*L^(1/250:ℝ) := by linarith
  have hcommon : C*((3/100:ℝ)*Real.log L+1) ≤ (1/2:ℝ)*L^(1/250:ℝ) := by
    have hh : C*((3/100:ℝ)*Real.log L+1) ≤ (C+1)*(Real.log L+1) := by nlinarith
    nlinarith
  have hlogC : C*Real.log L ≤ (1/2:ℝ)*L^(1/250:ℝ) := by nlinarith
  intro B u hB hBL hu
  have hbase : 0 < L^(1/16:ℝ)/2 := by positivity
  have hlogu := Real.log_le_log hbase (hu.trans (by linarith : |u| ≤ 1+|u|))
  rw [Real.log_div (by positivity : L^(1/16:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_rpow hL0] at hlogu
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hmin : min ((3/100:ℝ)*Real.log L) (Real.log (1+|u|)) =
      (3/100:ℝ)*Real.log L := min_eq_left (by linarith)
  rw [hmin]
  have he : Real.exp (-((3/100:ℝ)*Real.log L)) = L^(-3/100:ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    ring
  rw [he]
  have hprod : L^(1/1000:ℝ)*L^(-3/100:ℝ) = L^(-29/1000:ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hquot : L^(1/1000:ℝ)/L = L^(-999/1000:ℝ) := by
    rw [div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hL0]
    norm_num
  calc
    _ ≤ C*L^(1/1000:ℝ)*(((3/100:ℝ)*Real.log L+1)*L^(-3/100:ℝ)+Real.log L/L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBL hC) (by positivity)
    _ = C*((3/100:ℝ)*Real.log L+1)*(L^(1/1000:ℝ)*L^(-3/100:ℝ))+
        (C*Real.log L)*(L^(1/1000:ℝ)/L) := by ring
    _ = C*((3/100:ℝ)*Real.log L+1)*L^(-29/1000:ℝ)+
        (C*Real.log L)*L^(-999/1000:ℝ) := by rw [hprod,hquot]
    _ ≤ ((1/2:ℝ)*L^(1/250:ℝ))*L^(-29/1000:ℝ)+
        ((1/2:ℝ)*L^(1/250:ℝ))*L^(-999/1000:ℝ) := by gcongr
    _ = (1/2:ℝ)*L^(-1/40:ℝ)+(1/2:ℝ)*L^(-199/200:ℝ) := by
      simp only [mul_assoc,← Real.rpow_add hL0]
      norm_num
    _ ≤ L^(-1/40:ℝ) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hL (show (-199/200:ℝ) ≤ -1/40 by norm_num)
      linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells
namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset


@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCost
namespace OAI

/-! Absorbing the integer-kernel error at the actual sparse-sample scale. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter



lemma halasz_extra_cofactor_length {L N a : ℝ} (hL : 0 ≤ L)
    (hlog : 1000 ≤ Real.log L) (ha : 0 < a)
    (haU : a ≤ Real.exp (L/Real.log L)) (hN : Real.exp L ≤ N) :
    Real.exp ((999/1000:ℝ)*L) ≤ N/a := by
  have hlog0 : 0 < Real.log L := by linarith
  have hq : L/Real.log L ≤ L/1000 :=
    div_le_div_of_nonneg_left hL (by norm_num) hlog
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ Real.exp ((999/1000:ℝ)*L)*Real.exp (L/1000) :=
      mul_le_mul_of_nonneg_left (haU.trans (Real.exp_le_exp.mpr hq)) (Real.exp_pos _).le
    _ = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ N := hN





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalWindow
namespace OAI

/-! Exact remaining-band inclusion--exclusion inside the fixed-window
cofactor. The resulting pointwise bound keeps its finite `2^#J` cost
explicit. No estimate for the typical polynomial is assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrtTypicalCoefficient_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    mrtTypicalCoefficient J P F n =
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        mrtMissingCoefficient F (I.biUnion P) n := by
  have he := congrArg (fun r : ℝ => (r : ℂ))
    (mrtTypical_inclusion_exclusion J P n)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one] at he
  calc
    _ = F n * (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        (mrtPrimeMask (I.biUnion P) n : ℂ)) := by
      rw [he]
      by_cases h : mrtTypical J P n <;>
        simp [mrtTypicalCoefficient, h]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro I _
      unfold mrtMissingCoefficient
      ring

lemma mrt_typical_cofactor_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (Q : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a t : ℝ) :
    mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t =
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        mrtCofactorPolynomial Q (mrtMissingCoefficient F (I.biUnion P)) N a t := by
  unfold mrtCofactorPolynomial
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  by_cases hc : (N : ℝ) < a * n ∧ a * n ≤ 2 * N
  · simp only [if_pos hc]
    unfold mrtDirichletAtom
    rw [mrtTypicalCoefficient_expansion]
    simp only [sum_mul, sum_div]
    apply sum_congr rfl
    intro I _
    ring
  · simp only [if_neg hc, mul_zero, sum_const_zero]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalCofactor
namespace OAI

/-! Actual cofactor bounds with a local frequency hypothesis. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate


/-- Remaining-band inclusion--exclusion preserves the local frequency window. -/
theorem halasz_exceptional_typical_window :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (ι : Type*) (J : Finset ι) (P : ι → Finset ℕ) (Q : Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → (∀ p ∈ Q, p.Prime) →
    ∀ (t τ M : ℝ), 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 →
        1/2 ≤ |v-τ| → 2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t‖ ≤
        (2 : ℝ) ^ J.card * C * ((min M (Real.log (1+|τ-t|)) + 1) * Real.exp (-min M (Real.log (1+|τ-t|))) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  obtain ⟨C, K, X₀, hC, hK, hb⟩ := halasz_exceptional_count_window
  refine ⟨C, K, X₀, hC, hK, ?_⟩
  intro N a ha hN F hF1 hFm hFb ι J P Q hP hQ t τ M hM hd
  rw [mrt_typical_cofactor_expansion]
  calc
    _ ≤ ∑ I ∈ J.powerset,
        ‖(-1 : ℂ) ^ I.card *
          mrtCofactorPolynomial Q (mrtMissingCoefficient F (I.biUnion P)) N a t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I ∈ J.powerset, C * ((min M (Real.log (1+|τ-t|)) + 1) * Real.exp (-min M (Real.log (1+|τ-t|))) +
        Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
          Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
      apply sum_le_sum
      intro I hI
      rw [norm_mul, norm_pow]
      simp only [norm_neg, norm_one, one_pow, one_mul]
      apply hb N a ha hN F hF1 hFm hFb (I.biUnion P) Q _ hQ t τ M hM hd
      intro p hp
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
      exact hP j ((mem_powerset.mp hI) hj) p hpj
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCofactorBandCount
namespace OAI

/-! The actual original prime bands fit the cofactor inclusion-exclusion
budget even when their cutoff is specified at the original scale. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem halasz_cofactor_band_count :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      (2:ℝ)^(Icc 1 J).card ≤ (Real.log n)^(1/1000:ℝ) := by
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually halasz_band_power_cost,eventually_ge_atTop 2]
    with n hcost hn
  intro X hnX hX Q J hQ hband
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0< n by omega)
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hln : 0 ≤ Real.log (n:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤ n by omega))
  have hlogX : Real.log (X:ℝ) ≤ 3*Real.log (n:ℝ) := by
    have hh := Real.log_le_log hX0 (show (X:ℝ) ≤ (n:ℝ)^3 by exact_mod_cast hX)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hsqrt : Real.sqrt (Real.log (X:ℝ)) ≤ 2*Real.sqrt (Real.log (n:ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hln]
  have hupper : Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt (Real.log (n:ℝ)) := by
    have hpos : 0 < mrtBandUpper Q J := by unfold mrtBandUpper; positivity
    have hh := Real.log_le_log hpos hband
    rw [Real.log_exp] at hh
    exact hh.trans hsqrt
  have hh := hcost Q J hQ hupper
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszOffCenterCofactor
namespace OAI

/-! The actual-band cofactor estimate on the entire off-center region,
conditional only on the precisely cited high-frequency prime estimate. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem HalaszHighPrimeInput.actual_cofactor (hhigh : HalaszHighPrimeInput) :
    ∃ X₀ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N:ℝ)/a⌋₊:ℝ) →
      n = ⌊(2*N:ℝ)/a⌋₊ → ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∀ t τ : ℝ,
      |τ| ≤ X →
      (∀ v : ℝ, |v| ≤ X → squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X) →
      |t|+(Real.log n)^8 ≤ X → (Real.log n)^(1/16:ℝ)/2 ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        (Real.log n)^(-1/40:ℝ) := by
  obtain ⟨C,K,X₀,hC,hK,hcofactor⟩ := halasz_exceptional_typical_window
  refine ⟨X₀,?_⟩
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hhigh.distance_cutoff K,halasz_cofactor_band_count,
    hlog.eventually (halasz_exceptional_decay C hC.le),
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with n hcut hcount hdec hln
  intro N a ha hbase hn X hnX hX F hF1 hFm hFb P Q J hQ hband A hA t τ hτ hmin ht haway
  have hM : 0 ≤ (3/100:ℝ)*Real.log (Real.log n) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hln)
  have hd : ∀ v:ℝ, |v-t| ≤ (Real.log n)^8 → 1/2 ≤ |v-τ| →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
    intro v hv hunit
    have hvX : |v| ≤ X := by
      have hh := abs_add_le (v-t) t
      rw [sub_add_cancel] at hh
      linarith
    exact hcut X hnX hX F hFb v τ hvX hτ hunit (hmin v hvX)
  have hb := hcofactor N a ha hbase F hF1 hFm hFb ℕ (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) A
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hA t τ
    ((3/100:ℝ)*Real.log (Real.log n)) hM (by simpa only [← hn] using hd)
  have hsave := hdec ((2:ℝ)^(Icc 1 J).card) (τ-t) (by positivity)
    (hcount X hnX hX Q J hQ hband) (by simpa only [abs_sub_comm] using haway)
  apply hb.trans
  simpa only [← hn,mul_comm C] using hsave

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCofactorScale
namespace OAI

/-! The cutoffs of extra-prime cofactors stay at the original logarithmic
scale. These bounds include the floors used in the actual polynomials. -/
namespace TwoPointCorrelations

open _root_.Filter

theorem halasz_cofactor_floor_scale (X₀ : ℝ) (n₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, 1 ≤ a →
      a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      let m := ⌊(N:ℝ)/a⌋₊
      let n := ⌊(2*N:ℝ)/a⌋₊
      X₀ ≤ (m:ℝ) ∧ n₀ ≤ n ∧ n ≤ 2*N ∧ 2*N ≤ n^3 ∧
      Real.log N/2 ≤ Real.log (n:ℝ) ∧ Real.log (n:ℝ) ≤ 2*Real.log N ∧
      Real.log (n:ℝ)^8 ≤ N := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (isLittleO_pow_exp_pos_mul_atTop 8 (b := 1) (by norm_num)).bound
    (show (0:ℝ)<1/256 by norm_num)
  filter_upwards [hlog.eventually hb,
    hlog.eventually (eventually_ge_atTop (10+2*|X₀|+2*(n₀:ℝ))),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1000:ℝ)),
    eventually_ge_atTop 2] with N hb hL hLL hN
  intro a ha haU
  let L := Real.log (N:ℝ)
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hL0 : 0 < L := by dsimp [L]; nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have ha0 : 0 < a := by linarith
  have hlen := halasz_extra_cofactor_length hL0.le hLL ha0 haU
    (show Real.exp L ≤ N by rw [Real.exp_log hN0])
  have hbig : X₀+1 ≤ Real.exp ((999/1000:ℝ)*L) ∧
      (n₀:ℝ) ≤ Real.exp ((999/1000:ℝ)*L) ∧ 2 ≤ Real.exp ((999/1000:ℝ)*L) := by
    have he := Real.add_one_le_exp ((999/1000:ℝ)*L)
    have hx := le_abs_self X₀
    dsimp [L] at he
    constructor
    · nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
    · constructor <;> nlinarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hx : 2 ≤ (N:ℝ)/a := hbig.2.2.trans hlen
  have hmX : X₀ ≤ (m:ℝ) := by
    have hf := Nat.lt_floor_add_one ((N:ℝ)/a)
    change (N:ℝ)/a < (m:ℝ)+1 at hf
    linarith [hbig.1.trans hlen]
  have hnlow : (N:ℝ)/a ≤ (n:ℝ) := by
    have hf := Nat.lt_floor_add_one ((2*N:ℝ)/a)
    change (2*N:ℝ)/a < (n:ℝ)+1 at hf
    have he : (2*N:ℝ)/a=2*((N:ℝ)/a) := by ring
    rw [he] at hf
    linarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hnscale := hlen.trans hnlow
  have hnlarge : n₀ ≤ n := by exact_mod_cast hbig.2.1.trans hnscale
  have hnupper : n ≤ 2*N := by
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      div_le_self (show (0:ℝ) ≤ 2*N by positivity) ha
  have hn0 : 0 < (n:ℝ) := (Real.exp_pos _).trans_le hnscale
  have hloglow : (999/1000:ℝ)*L ≤ Real.log (n:ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hnscale
  have hlogupper : Real.log (n:ℝ) ≤ 2*L := by
    have hh := Real.log_le_log hn0
      (show (n:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast hnupper)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    have htwo := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    dsimp [L]
    linarith [abs_nonneg X₀,Nat.cast_nonneg (α:=ℝ) n₀]
  have hncube : 2*N ≤ n^3 := by
    have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hpow := pow_le_pow_left₀ (Real.exp_pos ((999/1000:ℝ)*L)).le hnscale 3
    have hNexp : (N:ℝ)^2=Real.exp (2*L) := by
      rw [show 2*L=L+L by ring,Real.exp_add,Real.exp_log hN0]
      ring
    have hexp : Real.exp (2*L) ≤ (Real.exp ((999/1000:ℝ)*L))^3 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num
      nlinarith
    have hh : 2*(N:ℝ) ≤ (n:ℝ)^3 := by nlinarith
    exact_mod_cast hh
  have hwidth : Real.log (n:ℝ)^8 ≤ N := by
    have hnlog0 : 0 ≤ Real.log (n:ℝ) := by nlinarith
    have hp := pow_le_pow_left₀ hnlog0 hlogupper 8
    change ‖L^8‖ ≤ (1/256:ℝ)*‖Real.exp (1*L)‖ at hb
    rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ L^8),
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos L),Real.exp_log hN0] at hb
    norm_num [mul_pow] at hp
    nlinarith
  exact ⟨hmX,hnlarge,hnupper,hncube,by nlinarith,hlogupper,hwidth⟩

lemma halasz_cofactor_scale_decay {L l : ℝ} (hL : 0 < L)
    (hlow : L/2 ≤ l) (hupp : l ≤ 2*L) :
    l^(1/16:ℝ)/2 ≤ L^(1/16:ℝ) ∧ l^(-1/40:ℝ) ≤ 2*L^(-1/40:ℝ) := by
  have hl : 0 < l := by linarith
  have hp1 : (2:ℝ)^(1/16:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤2 by norm_num) (show (1/16:ℝ)≤1 by norm_num)
  have hp2 : (2:ℝ)^(1/40:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤2 by norm_num) (show (1/40:ℝ)≤1 by norm_num)
  constructor
  · have hh := Real.rpow_le_rpow hl.le hupp (show (0:ℝ)≤1/16 by norm_num)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hL.le] at hh
    nlinarith [mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hL.le (1/16))]
  · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0< L/2) hlow
      (show (-1/40:ℝ)≤0 by norm_num)
    have he : (2:ℝ)^(-1/40:ℝ)=((2:ℝ)^(1/40:ℝ))⁻¹ := by
      rw [show (-1/40:ℝ)=-(1/40:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [Real.div_rpow hL.le (by norm_num : (0:ℝ)≤2),he,div_inv_eq_mul] at hh
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hp2 (Real.rpow_nonneg hL.le (-1/40))])

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszExtraCofactor
namespace OAI

/-! The actual extra-prime cofactor has uniform decay off the original
minimizing twist. All floor and band-count losses have been absorbed. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem HalaszHighPrimeInput.extra_cofactor_oai (hhigh : HalaszHighPrimeInput) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t τ : ℝ, |t| ≤ N → |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      (Real.log N)^(1/16:ℝ) ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ) := by
  obtain ⟨X₀,hcofactor⟩ := hhigh.actual_cofactor
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hcofactor
  filter_upwards [halasz_cofactor_floor_scale X₀ n₀,eventually_ge_atTop 2]
    with N hscale hN
  intro F hF1 hFm hFb P Q J hQ hband A hA a ha haU t τ ht hτ hmin haway
  let n := ⌊(2*N:ℝ)/a⌋₊
  obtain ⟨hbase,hnlarge,hnupper,hncube,hloglow,hlogupper,hwidth⟩ := hscale a ha haU
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hLN : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1< N by omega))
  have hdec := halasz_cofactor_scale_decay hLN hloglow hlogupper
  have hband' : mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log (2*N:ℕ))) := by
    apply hband.trans
    apply Real.exp_le_exp.mpr
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log hN0
    exact_mod_cast (show N≤2*N by omega)
  have ht' : |t|+Real.log (n:ℝ)^8 ≤ (2*N:ℕ) := by
    push_cast
    linarith
  have hτ' : |τ| ≤ (2*N:ℕ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hτ
  have hmin' : ∀ v:ℝ, |v| ≤ (2*N:ℕ) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmin
  have hh := hn₀ n hnlarge N a ha hbase rfl (2*N) hnupper hncube
    F hF1 hFm hFb P Q J hQ hband' A hA t τ hτ' hmin' ht' (hdec.1.trans haway)
  exact hh.trans hdec.2

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.HalaszHighPrimeInput.extra_cofactor_oai := @OAI.TwoPointCorrelations.HalaszHighPrimeInput.extra_cofactor_oai
