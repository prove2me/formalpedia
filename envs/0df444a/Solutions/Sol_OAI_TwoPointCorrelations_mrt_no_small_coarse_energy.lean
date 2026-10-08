-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_no_small_coarse_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:01.151162+00:00
-- url     : https://prove2.me/submissions/40d0b0df-aefb-4e54-8710-f28495b9d359

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_HalaszPrimeSparseInput_large_prime_product_energy
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_final_samples
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_small_cofactor_integral

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset _root_.Set
open scoped _root_.BigOperators _root_.ComplexConjugate









lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeProducts
namespace OAI

/-! The factorial multiplicity of a product of primes.  Sorting gives
an injective permutation code on each product fiber, including tuples
with repeated primes.  This is the arithmetic input for high moments
of prime Dirichlet polynomials. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma mrt_norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖a i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i‖)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRestrictedEnergy
namespace OAI

/-! Finite energy bounds on arbitrary measurable frequency classes.
They retain the explicit coarse-bin count and permit the coefficient
bounds to vary from bin to bin. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_continuous_square_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    IntegrableOn (fun t => ‖F t‖ ^ 2) E := by
  have hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hF.norm.pow 2).intervalIntegrable _ _)
  exact hi.mono_set hE




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical
namespace OAI

/-! The actual typical-set Ramaré approximation for ordinary
multiplicative functions. Prime squares account for every failure of
complete multiplicativity, before any frequency-class witness cover. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrtCofactorPolynomial_continuous (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a : ℝ) : Continuous (mrtCofactorPolynomial P F N a) := by
  unfold mrtCofactorPolynomial
  apply continuous_finsetSum
  intro m _
  by_cases hw : (N : ℝ) < a * m ∧ a * m ≤ 2 * N
  · simp only [if_pos hw]
    unfold mrtDirichletAtom
    fun_prop
  · simp only [if_neg hw]
    exact continuous_const



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPoissonBound
namespace OAI

/-! Summing the stationary and nonstationary Poisson modes. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma halasz_integer_square_mass_nonneg : 0 ≤ halaszIntegerSquareMass :=
  tsum_nonneg (fun _ => by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiscaleEnergy
namespace OAI

/-! The actual typical-set polynomial on a later MRT frequency class.
The preceding short prime polynomial is large, while each current-bin
polynomial is small. Amplification is applied before extending the
cofactor energy to the whole frequency interval. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_restricted_product_sum_energy_local {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j)) (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPrimeBins
namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrt_prime_log_lower_one {H : ℝ} (hH : 0 < H) (k : ℕ) :
    1 ≤ mrtPrimeLogLower H k :=
  Real.one_le_exp (div_nonneg (Nat.cast_nonneg k) hH.le)

lemma mrt_prime_log_bin_bounds {H : ℝ} (hH : 0 < H) {p : ℕ} (hp : 1 ≤ p) :
    mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (1 / H) * mrtPrimeLogLower H (mrtPrimeLogBin H p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
  have hlo : (mrtPrimeLogBin H p : ℝ) ≤ H * Real.log p :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hp1))
  have hhi : H * Real.log p < (mrtPrimeLogBin H p : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · calc
      _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr
        ((div_le_iff₀ hH).mpr (by nlinarith))
      _ = _ := Real.exp_log hp0
  · calc
      (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ Real.exp (1 / H + (mrtPrimeLogBin H p : ℝ) / H) := by
        apply Real.exp_le_exp.mpr
        rw [← add_div]
        apply (le_div_iff₀ hH).mpr
        nlinarith
      _ = _ := by rw [Real.exp_add]; rfl


lemma mrt_prime_log_width {H : ℝ} (hH : 2 ≤ H) :
    1 ≤ Real.exp (1 / H) ∧ Real.exp (1 / H) ≤ 2 ∧
      Real.exp (1 / H) - 1 ≤ 2 / H := by
  have hH0 : 0 < H := by linarith
  have hi0 : (0 : ℝ) ≤ 1 / H := by positivity
  have hi : (1 : ℝ) / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH
  have he := Real.exp_bound' hi0 (show (1 : ℝ) / H ≤ 1 by linarith) (n := 1) (by norm_num)
  norm_num at he
  have he' : Real.exp (1 / H) ≤ 1 + (1 / H) * 2 := by simpa only [one_div] using he
  refine ⟨Real.one_le_exp hi0, ?_, ?_⟩
  · nlinarith [he']
  · simpa only [div_eq_mul_inv, one_mul] using
      (show Real.exp (1 / H) - 1 ≤ 2 * (1 / H) by linarith [he'])

lemma mrt_prime_log_lower_le_upper {H Q : ℝ} (hH : 0 < H) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ≤ ⌊H * Real.log Q⌋₊) : mrtPrimeLogLower H k ≤ Q := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hQ))
  have hkR : (k : ℝ) ≤ ⌊H * Real.log Q⌋₊ := by exact_mod_cast hk
  calc
    _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr
      ((div_le_iff₀ hH).mpr (by nlinarith))
    _ = _ := Real.exp_log hQ0


lemma mrt_log_bin_card {H Q P : ℝ} (hH : 0 ≤ H) (hQ : 1 ≤ Q) :
    ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ H * Real.log Q + 1 := by
  have hc : (Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card ≤ ⌊H * Real.log Q⌋₊ + 1 := by
    rw [Nat.card_Icc]
    omega
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH (Real.log_nonneg hQ))
  have hcR : ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤
      (⌊H * Real.log Q⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogBinEndpoints
namespace OAI

/-! Endpoint control for every logarithmic bin, including the first
partially filled bin below the original lower endpoint. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma mrt_log_bin_lower_endpoint {H P : ℝ} (hH : 1 ≤ H) (hP : 0 < P)
    {k : ℕ} (hk : ⌊H * Real.log P⌋₊ ≤ k) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k := by
  have hH0 : 0 < H := by linarith
  have hkR : (⌊H * Real.log P⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  have hf : H * Real.log P < (k : ℝ) + 1 :=
    (Nat.lt_floor_add_one (H * Real.log P)).trans_le (by linarith)
  have hi : (1 : ℝ) / H ≤ 1 := (div_le_one hH0).mpr hH
  have hl : Real.log P - 1 ≤ (k : ℝ) / H := by
    have hh : Real.log P < ((k : ℝ) + 1) / H :=
      (lt_div_iff₀ hH0).mpr (by nlinarith)
    rw [add_div] at hh
    linarith
  calc
    _ = Real.exp (Real.log P - 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hl



end TwoPointCorrelations

end OAI

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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTResolution
namespace OAI

/-! The logarithmic bin resolution used in the multiscale partition.
Its balance with the first prime threshold is exact. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma mrtBaseResolution_pos (P Q η : ℝ) : 0 < mrtBaseResolution P Q η :=
  Real.exp_pos _


lemma mrtResolution_pos (P Q η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    0 < mrtResolution P Q η j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact mul_pos (sq_pos_of_pos hj0) (mrtBaseResolution_pos P Q η)

lemma mrt_base_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) : mrtBaseResolution P Q η ≤ P := by
  have hp0 : 0 < P := by linarith
  have hlp := Real.log_nonneg hP
  have hlq := Real.log_nonneg hQ
  have he : (1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q) ≤
      Real.log P := by nlinarith [mul_nonneg hη hlp]
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hp0)

lemma mrt_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (j : ℕ) :
    mrtResolution P Q η j ≤ (j : ℝ) ^ 2 * P :=
  mul_le_mul_of_nonneg_left (mrt_base_resolution_le hP hQ hη) (sq_nonneg _)





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCost
namespace OAI

/-! Absorbing the integer-kernel error at the actual sparse-sample scale. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter


lemma halasz_sparse_error_constant_pos : 0 < halaszSparseErrorConstant := by
  unfold halaszSparseErrorConstant
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg)

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

lemma halasz_no_small_card_budget {L R K : ℝ}
    (hcard : R ≤ K*Real.exp ((99/200:ℝ)*L))
    (hK : K ≤ Real.exp ((3/1000:ℝ)*L)) :
    R ≤ Real.exp ((249/500:ℝ)*L) := by
  calc
    _ ≤ K*Real.exp ((99/200:ℝ)*L) := hcard
    _ ≤ Real.exp ((3/1000:ℝ)*L)*Real.exp ((99/200:ℝ)*L) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma halasz_sparse_error_exponential {L M T : ℝ} (hL : 0 ≤ L)
    (hM : 1 ≤ M) (_hT : 0 ≤ T) (hTU : T ≤ Real.exp L) :
    halaszSparseKernelError M T ≤ halaszSparseErrorConstant * Real.exp (L/2) := by
  have hM0 : 0 < M := by linarith
  have he1 : 1 ≤ Real.exp (L/2) := Real.one_le_exp (by positivity)
  have hroot : Real.sqrt (2*T) ≤ Real.sqrt 2 * Real.exp (L/2) := by
    calc
      _ ≤ Real.sqrt (2*Real.exp L) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num),← Real.exp_half]
  have htail : (512/(M*(2*Real.pi)^2))*halaszIntegerSquareMass ≤
      ((512/(2*Real.pi)^2)*halaszIntegerSquareMass)*Real.exp (L/2) := by
    calc
      _ ≤ (512/(2*Real.pi)^2)*halaszIntegerSquareMass := by
        apply mul_le_mul_of_nonneg_right _ halasz_integer_square_mass_nonneg
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [sq_nonneg (2*Real.pi)]
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg) he1
  unfold halaszSparseKernelError halaszSparseErrorConstant
  nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 440/Real.pi by positivity)]

theorem halasz_sparse_sample_cost :
    ∀ᶠ L : ℝ in atTop, ∀ M T R : ℝ,
      Real.exp ((999/1000:ℝ)*L) ≤ M → 0 ≤ T → T ≤ Real.exp L →
      0 ≤ R → R ≤ Real.exp ((249/500:ℝ)*L) →
      R*halaszSparseKernelError M T ≤ M := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_ge_atTop (1000*Real.log halaszSparseErrorConstant)] with L hL hc
  intro M T R hM hT hTU hR hRU
  have hM1 : 1 ≤ M := (Real.one_le_exp (by positivity)).trans hM
  have he := halasz_sparse_error_exponential hL hM1 hT hTU
  have hsmall : Real.log halaszSparseErrorConstant ≤ L/1000 := by linarith
  calc
    _ ≤ Real.exp ((249/500:ℝ)*L)*
        (halaszSparseErrorConstant*Real.exp (L/2)) :=
      mul_le_mul hRU he (by
        unfold halaszSparseKernelError
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) halasz_integer_square_mass_nonneg)) (by positivity)
    _ = Real.exp (Real.log halaszSparseErrorConstant+(499/500:ℝ)*L) := by
      rw [Real.exp_add,Real.exp_log halasz_sparse_error_constant_pos]
      rw [show (499/500:ℝ)*L=(249/500:ℝ)*L+L/2 by ring,Real.exp_add]
      ring
    _ ≤ Real.exp ((999/1000:ℝ)*L) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ M := hM


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassData
namespace OAI

/-! Literal logarithmic prime polynomials and their small/large frequency
sets. These sets supply the hypotheses of the general cofactor estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical




lemma mrt_log_prime_polynomial_continuous (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (k : ℕ) : Continuous (mrtLogPrimePolynomial S F H k) :=
  mrtExponentialPolynomial_continuous _ _ _





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBandGeometry
namespace OAI

/-! The additional large-prime interval used after the last ordinary
band. A factor two in its lower logarithm absorbs bin rounding. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical




theorem mrt_extra_band_geometry :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ mrtExtraPrimeResolution L ∧
      Real.exp (Real.sqrt L) < mrtExtraPrimeLower L ∧
      mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L ∧
      mrtExtraPrimeUpper L ≤ Real.exp (L/1000) ∧
      ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L)
        (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
      1 < mrtPrimeLogLower (mrtExtraPrimeResolution L) k ∧
      L^(79/80:ℝ) ≤ Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ∧
      Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ≤ L := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hres := (tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hb,hres,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))]
    with L hb hres hL hLL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlogL.le,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hsmall : 2*Real.log L ≤ L^(1/80:ℝ) := by linarith
  have hpow : 1 ≤ L^(79/80:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hmul : L^(79/80:ℝ)*L^(1/80:ℝ)=L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hPQ : mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hlogL).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le (79/80))
    rw [hmul] at hh
    nlinarith
  have hsep : Real.exp (Real.sqrt L) < mrtExtraPrimeLower L := by
    apply Real.exp_lt_exp.mpr
    have hh : Real.sqrt L ≤ L^(79/80:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    linarith
  have hupper : mrtExtraPrimeUpper L ≤ Real.exp (L/1000) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL0.le (by norm_num) hLL
  refine ⟨hres,hsep,hPQ,hupper,?_⟩
  intro k hk
  let Y := mrtPrimeLogLower (mrtExtraPrimeResolution L) k
  have hYlow : L^(79/80:ℝ) ≤ Real.log Y := by
    have hh := mrt_log_bin_lower_endpoint (show 1 ≤ mrtExtraPrimeResolution L by
      change 1 ≤ L^(1/80:ℝ)
      linarith)
      (Real.exp_pos _) (mem_Icc.mp hk).1
    have hh' := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hh
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp] at hh'
    simp only [Real.log_exp] at hh'
    change -1+2*L^(79/80:ℝ) ≤ Real.log Y at hh'
    linarith
  have hY : 1 < Y := by
    change 1 < Real.exp ((k:ℝ)/mrtExtraPrimeResolution L)
    apply Real.one_lt_exp_iff.mpr
    have hh : 0 < Real.log Y := by linarith
    simpa only [Y,mrtPrimeLogLower,Real.log_exp] using hh
  have hQ1 : 1 ≤ mrtExtraPrimeUpper L := Real.one_le_exp (by positivity)
  have hYhi := mrt_prime_log_lower_le_upper (show 0 < mrtExtraPrimeResolution L by
    change 0 < L^(1/80:ℝ)
    linarith)
    hQ1 (mem_Icc.mp hk).2
  have hl : Real.log Y ≤ L/Real.log L := by
    simpa only [mrtExtraPrimeUpper,Real.log_exp] using
      Real.log_le_log (show 0 < Y by linarith) hYhi
  exact ⟨hY,hYlow,hl.trans (div_le_self hL0.le (by linarith))⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBinCost
namespace OAI

/-! The full extra-bin multiplicity fits the cofactor saving. A crude
Cauchy sum suffices; no loss involving the number of original bands occurs. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma mrt_extra_bin_card {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤
      2*mrtExtraPrimeResolution L*L/Real.log L := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log L := by linarith
  have hH : 1 ≤ mrtExtraPrimeResolution L := Real.one_le_rpow hL (by norm_num)
  have hq : 1 ≤ L/Real.log L := (le_div_iff₀ hlog0).mpr (by
    linarith [Real.log_le_sub_one_of_pos hL0])
  have hQ : 1 ≤ mrtExtraPrimeUpper L := Real.one_le_exp (by positivity)
  have hh := mrt_log_bin_card (P := mrtExtraPrimeLower L) (by linarith :
    0 ≤ mrtExtraPrimeResolution L) hQ
  have hprod := one_le_mul_of_one_le_of_one_le hH hq
  calc
    _ ≤ mrtExtraPrimeResolution L*Real.log (mrtExtraPrimeUpper L)+1 := hh
    _ = mrtExtraPrimeResolution L*(L/Real.log L)+1 := by
      rw [mrtExtraPrimeUpper,Real.log_exp]
    _ ≤ 2*(mrtExtraPrimeResolution L*(L/Real.log L)) := by linarith
    _ = _ := by ring

theorem mrt_extra_bin_cofactor_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ)^2) /
      (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2) ≤ 4*L^(3/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < mrtExtraPrimeResolution L := Real.rpow_pos_of_pos hL0 _
  have hcard := mrt_extra_bin_card hL hlog
  have hratio : L/Real.log L ≤ L := div_le_self hL0.le hlog
  have hc : ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤ 2*mrtExtraPrimeResolution L*L := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*mrtExtraPrimeResolution L by positivity)
    exact hcard.trans (by simpa only [mul_div_assoc] using hh)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hp : (L^(79/80:ℝ))^2=L^(79/40:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  have he : (2*mrtExtraPrimeResolution L*L)^2 /
      (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2) = 4*L^(3/80:ℝ) := by
    calc
      _ = 4*(mrtExtraPrimeResolution L*L^2)/(L^(79/80:ℝ))^2 := by
        field_simp [hH0.ne']
        ring
      _ = 4*(L^(1/80:ℝ)*L^(2:ℝ))/L^(79/40:ℝ) := by
        rw [hp,Real.rpow_two]
        rfl
      _ = 4*L^(161/80:ℝ)/L^(79/40:ℝ) := by
        rw [← Real.rpow_add hL0]
        norm_num
      _ = _ := by
        rw [mul_div_assoc,← Real.rpow_sub hL0]
        norm_num
  exact (div_le_div_of_nonneg_right hsq (by positivity)).trans_eq he

/-- The retained cofactor exponent 1/40 pays all extra-bin factors. -/
theorem mrt_extra_bin_saved_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (L^(-1/40:ℝ))^2 *
      ((((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L)).card:ℝ)^2) /
        (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2)) ≤ 4*L^(-1/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hh := mul_le_mul_of_nonneg_left (mrt_extra_bin_cofactor_cost hL hlog)
    (sq_nonneg (L^(-1/40:ℝ)))
  apply hh.trans_eq
  have he : (L^(-1/40:ℝ))^2=L^(-1/20:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  rw [he]
  calc
    _ = 4*(L^(-1/20:ℝ)*L^(3/80:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraEnergySum
namespace OAI

/-! Finite Cauchy summation of the actual additional logarithmic bins.
The two per-bin estimates retain their separate small- and large-value
costs, and the full bin count is absorbed by the proved power saving. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_product_energy_split (Q R : ℝ → ℂ) (hQ : Continuous Q) (hR : Continuous R)
    {T θ A B : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T)
    (hsmall : (∫ t in E \ {t | θ ≤ ‖Q t‖}, ‖Q t*R t‖^2) ≤ A)
    (hlarge : (∫ t in E ∩ {t | θ ≤ ‖Q t‖}, ‖Q t*R t‖^2) ≤ B) :
    (∫ t in E, ‖Q t*R t‖^2) ≤ A+B := by
  have hset : MeasurableSet {t | θ ≤ ‖Q t‖} :=
    (isClosed_le continuous_const hQ.norm).measurableSet
  have hi := mrt_continuous_square_integrable (hQ.mul hR) hT hET
  have he := integral_inter_add_sdiff hset hi
  simp only [Pi.mul_apply] at he
  linarith

lemma mrt_bin_sum_energy {ι : Type*} (K : Finset ι) (G : ι → ℝ → ℂ)
    (hG : ∀ k ∈ K, Continuous (G k)) {T : ℝ} (hT : 0 ≤ T)
    {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖∑ k ∈ K, G k t‖^2) ≤
      (K.card:ℝ)*∑ k ∈ K, (∫ t in E, ‖G k t‖^2) := by
  have hh := mrt_restricted_product_sum_energy_local K (fun _ _ => (1:ℂ)) G hG
    (fun _ => (1:ℝ)) hT hET (by intros; simp)
  simpa only [one_mul,one_pow] using hh

lemma mrt_extra_small_bin_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ)^2)*(L^(-100:ℝ))^2 ≤ 4*L^(-1/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hH : mrtExtraPrimeResolution L ≤ L := by
    exact (Real.rpow_le_rpow_of_exponent_le hL (show (1/80:ℝ) ≤ 1 by norm_num)).trans_eq
      (Real.rpow_one L)
  have hc := mrt_extra_bin_card hL hlog
  have hratio : L/Real.log L ≤ L := div_le_self hL0.le hlog
  have hcard : ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤ 2*L^2 := by
    calc
      _ ≤ 2*mrtExtraPrimeResolution L*(L/Real.log L) := by simpa only [mul_div_assoc] using hc
      _ ≤ 2*L*L := mul_le_mul (by linarith) hratio (by positivity) (by positivity)
      _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg (L^(-100:ℝ)))
  have he : (2*L^2)^2*(L^(-100:ℝ))^2 = 4*L^(-196:ℝ) := by
    have hpow : (L^(-100:ℝ))^2 = L^(-200:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [show (2*L^2)^2=4*L^4 by ring]
    rw [hpow]
    rw [show L^(4:ℕ)=L^(4:ℝ) from (Real.rpow_natCast L 4).symm]
    rw [mul_assoc,← Real.rpow_add hL0]
    norm_num
  rw [he] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL (show (-196:ℝ) ≤ -1/80 by norm_num))
    (by norm_num))

theorem mrt_extra_coarse_energy {ι : Type*} {L T C₀ C₁ : ℝ}
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hT : 0 ≤ T)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (J : Finset ι) (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ)
    {E : Set ℝ} (hET : E ⊆ Set.Ioc (-T) T)
    (hlow : ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L), L^(79/80:ℝ) ≤ Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k))
    (hbin : ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L),
      (∫ t in E, ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t *
        mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
          (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖^2) ≤
        C₀*(L^(-100:ℝ))^2 + C₁*(L^(-1/40:ℝ))^2 /
          (mrtExtraPrimeResolution L*(Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k))^2)) :
    (∫ t in E, ‖mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
      (4*C₀+4*C₁)*L^(-1/80:ℝ) := by
  let K := mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let G := fun k t => mrtLogPrimePolynomial A F H k t *
    mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower H k) t
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := Real.rpow_pos_of_pos hL0 _
  have hg := mrt_bin_sum_energy K G (fun k _ =>
    (mrt_log_prime_polynomial_continuous _ _ _ _).mul
      (mrtCofactorPolynomial_continuous _ _ _ _)) hT hET
  change (∫ t in E, ‖mrtExtraCoarsePolynomial L J P F N t‖^2) ≤ _ at hg
  have hb : ∀ k ∈ K, (∫ t in E, ‖G k t‖^2) ≤
      C₀*(L^(-100:ℝ))^2 + C₁*(L^(-1/40:ℝ))^2/(H*(L^(79/80:ℝ))^2) := by
    intro k hk
    apply (hbin k hk).trans
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hH0.le
    exact pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) (hlow k hk) 2
  have hsum := mul_le_mul_of_nonneg_left (sum_le_sum hb) (Nat.cast_nonneg K.card)
  have hs := mrt_extra_small_bin_cost hL hlog
  have hl := mrt_extra_bin_saved_cost hL hlog
  have hcs := mul_le_mul_of_nonneg_left hs hC₀
  have hcl := mul_le_mul_of_nonneg_left hl hC₁
  calc
    _ ≤ (K.card:ℝ)*∑ k ∈ K, (∫ t in E, ‖G k t‖^2) := hg
    _ ≤ (K.card:ℝ)*∑ _k ∈ K,
        (C₀*(L^(-100:ℝ))^2+C₁*(L^(-1/40:ℝ))^2/(H*(L^(79/80:ℝ))^2)) := hsum
    _ = C₀*((K.card:ℝ)^2*(L^(-100:ℝ))^2)+
        C₁*((L^(-1/40:ℝ))^2*((K.card:ℝ)^2/(H*(L^(79/80:ℝ))^2))) := by
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ C₀*(4*L^(-1/80:ℝ))+C₁*(4*L^(-1/80:ℝ)) := add_le_add hcs hcl
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalBinCount
namespace OAI

/-! Actual logarithmic-bin cardinality at the maximal-band cutoff.
The resolution is controlled by the original prime endpoint, so the
number of bins contributes only exp(o(log N)). -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

lemma mrt_final_bin_count_coarse {L P Q η : ℝ} (hL : 1 ≤ L)
    (hP : 1 ≤ P) (hPQ : P ≤ Q) (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η)
    (j : ℕ) (hupper : Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L) :
    ((mrtLogFamilyBins P Q η j).card:ℝ) ≤ L^2*Real.exp (Real.sqrt L)+1 := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := by linarith
  have hj : (j+1:ℕ) ≥ 1 := by omega
  have hindex : ((j+1:ℕ):ℝ) ≤ Real.sqrt L :=
    (mrt_band_index_le_log_upper Q (j+1) hj hQ).trans hupper
  have hj2 : (((j+1:ℕ):ℝ))^2 ≤ L := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (j+1)) hindex 2
    simpa only [Real.sq_sqrt hL0.le] using hh
  have hlogQ : Real.log Q ≤ Real.sqrt L := by
    have hh := (mrt_band_upper_log_mono hQ (i := 1) (j := j+1) (by omega) (by omega)).trans hupper
    simpa [mrtBandUpper] using hh
  have hlogP : Real.log P ≤ Real.sqrt L :=
    (Real.log_le_log hP0 hPQ).trans hlogQ
  have hPupper : P ≤ Real.exp (Real.sqrt L) := by
    simpa only [Real.exp_log hP0] using Real.exp_le_exp.mpr hlogP
  have hH : mrtResolution P Q η (j+1) ≤ L*Real.exp (Real.sqrt L) :=
    (mrt_resolution_le hP hQ hη (j+1)).trans
      (mul_le_mul hj2 hPupper (by positivity) hL0.le)
  have hBU : 1 ≤ mrtBandUpper Q (j+1) := by
    have hq0 : 0 ≤ Real.log Q := by linarith
    unfold mrtBandUpper
    exact Real.one_le_exp (by positivity)
  have hH0 : 0 ≤ mrtResolution P Q η (j+1) :=
    (mrtResolution_pos P Q η hj).le
  have hcard := mrt_log_bin_card (P := mrtBandLower P Q (j+1)) hH0 hBU
  change ((mrtLogFamilyBins P Q η j).card:ℝ) ≤
    mrtResolution P Q η (j+1)*Real.log (mrtBandUpper Q (j+1))+1 at hcard
  apply hcard.trans
  have hroot := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hbound := mul_le_mul hH (hupper.trans hroot)
    (Real.log_nonneg hBU) (by positivity)
  nlinarith

lemma mrt_eventually_bin_count_budget :
    ∀ᶠ L : ℝ in atTop, L^2*Real.exp (Real.sqrt L)+1 ≤
      Real.exp ((3/1000:ℝ)*L) := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).bound
    (show (0:ℝ)<1/4000 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (1000000:ℝ)] with L hb hL
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL1),Real.norm_eq_abs,
    Real.rpow_one,abs_of_pos hL0] at hb
  have hroot : Real.sqrt L ≤ L/1000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh := mul_nonneg (show 0 ≤ L-1000000 by linarith) hL0.le
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he1 : 1 ≤ Real.exp (Real.sqrt L) := Real.one_le_exp (Real.sqrt_nonneg L)
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL1
  have hprod : 1 ≤ L^2*Real.exp (Real.sqrt L) :=
    one_le_mul_of_one_le_of_one_le hL2 he1
  have he : Real.exp (2*Real.log L)=L^2 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using Real.exp_nat_mul (Real.log L) 2
  calc
    _ ≤ 2*L^2*Real.exp (Real.sqrt L) := by nlinarith
    _ = Real.exp (Real.log 2+2*Real.log L+Real.sqrt L) := by
      conv_rhs => rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),he]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem mrt_final_bin_count :
    ∀ᶠ L : ℝ in atTop, ∀ P Q η : ℝ,
      1 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 0 ≤ η → ∀ j : ℕ,
      Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
      ((mrtLogFamilyBins P Q η j).card:ℝ) ≤ Real.exp ((3/1000:ℝ)*L) := by
  filter_upwards [mrt_eventually_bin_count_budget,eventually_ge_atTop (1:ℝ)] with L hb hL
  intro P Q η hP hPQ hQ hη j hupper
  exact (mrt_final_bin_count_coarse hL hP hPQ hQ hη j hupper).trans hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCard
namespace OAI

/-! The actual final original band gives the cardinality needed by the
integer-kernel estimate on every separated subset of the no-small class. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem mrt_no_small_card_at_scale :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ S : Finset ℝ,
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (S.card:ℝ) ≤ Real.exp ((249/500:ℝ)*L) := by
  filter_upwards [mrt_no_small_final_samples,mrt_final_bin_count] with L hs hk
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU S hfreq hsep hno
  exact halasz_no_small_card_budget
    (hs V F hF J j hj P Q hQ hres hp hrange hlo hhi T hT hTU S hfreq hsep hno)
    (hk P Q (1/100) hP hPQ hQ (by norm_num) j hhi)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSmallIntegral
namespace OAI

/-! Small additional-prime values on the actual no-small class. The
integer-kernel error is paid by the final original-band sample count. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem mrt_extra_small_integral :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ N : ℕ, Real.exp L ≤ N →
    ∀ B : ℕ → ℂ, OneBounded B → ∀ k ∈
      mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
    ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (-T) T →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ t ∈ E, ‖mrtLogPrimePolynomial
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
        (mrtExtraPrimeResolution L) k t‖ ≤ L^(-100:ℝ)) →
    (∫ t in E, ‖mrtLogPrimePolynomial
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
        (mrtExtraPrimeResolution L) k t *
      mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        B N (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖^2) ≤
      1190408*(L^(-100:ℝ))^2 := by
  filter_upwards [mrt_no_small_card_at_scale,halasz_sparse_sample_cost,
    mrt_extra_band_geometry,Filter.eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1000:ℝ))]
    with L hcard hcost hg hL hlog
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU N hN B hB k hk
    E hE hET hno hsmall
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let a := mrtPrimeLogLower H k
  have hL0 : 0 ≤ L := by linarith
  have hH : 0 < H := by change 0 < mrtExtraPrimeResolution L; linarith [hg.1]
  have ha : 1 ≤ a := mrt_prime_log_lower_one hH k
  have ha0 : 0 < a := by linarith
  have haU : a ≤ Real.exp (L/Real.log L) := by
    exact mrt_prime_log_lower_le_upper hH (Real.one_le_exp (by positivity)) (mem_Icc.mp hk).2
  have hM := halasz_extra_cofactor_length hL0 hlog ha0 haU hN
  have hM2 : 2 ≤ (N:ℝ)/a := by
    have hh := Real.add_one_le_exp ((999/1000:ℝ)*L)
    linarith
  apply mrt_small_cofactor_integral A B hB N ha hM2 (by linarith : 0 ≤ T)
    (mrtLogPrimePolynomial A F H k) (mrt_log_prime_polynomial_continuous A F H k) hE hET
  · intro S hS hsep
    have hfreq : ∀ t ∈ S, |t| ≤ T := by
      intro t ht
      obtain ⟨hl,hu⟩ := hET (hS t ht)
      exact abs_le.mpr ⟨by linarith,hu⟩
    have hc := hcard V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU
      S hfreq hsep (fun t ht => hno t (hS t ht))
    exact hcost ((N:ℝ)/a) T S.card hM (by linarith) hTU (Nat.cast_nonneg _) hc
  · exact hsmall

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCoarse
namespace OAI

/-! Complete additional-prime coarse-polynomial energy on the actual
no-small class. The prime sparse theorem and the pointwise cofactor saving
are explicit; all sample counts, set splits and bin sums are discharged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_no_small_coarse_energy_oai (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtExtraCoarsePolynomial L (Icc 1 J) V F N t‖^2) ≤ C*L^(-1/80:ℝ) := by
  obtain ⟨C,B₀,hC,hB₀,hlarge⟩ := hprime.large_prime_product_energy
  refine ⟨4*1190408+4*(4*C),by positivity,?_⟩
  filter_upwards [hlarge,mrt_extra_small_integral,mrt_extra_band_geometry,
    (tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).eventually
      (Filter.eventually_ge_atTop B₀),
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hlarge hsmall hg hHlarge hL hlog
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi N hN E hE hET hno hpoint
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let B := mrtTypicalCoefficient (Icc 1 J) V F
  let K := mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  have hL0 : 0 < L := by linarith
  have hH : 2 ≤ H := hg.1
  have hH0 : 0 < H := by linarith
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hF
  have hT : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL0
  apply mrt_extra_coarse_energy hL hlog (Real.exp_pos L).le
    (by norm_num : (0:ℝ) ≤ 1190408) (show 0 ≤ 4*C by positivity) (Icc 1 J) V F N hET
    (fun k hk => (hg.2.2.2.2 k hk).2.1)
  intro k hk
  let Y := mrtPrimeLogLower H k
  let Qk := mrtLogPrimePolynomial A F H k
  let Rk := mrtCofactorPolynomial A B N Y
  let D := {t | L^(-100:ℝ) ≤ ‖Qk t‖}
  have hQc : Continuous Qk := mrt_log_prime_polynomial_continuous _ _ _ _
  have hRc : Continuous Rk := mrtCofactorPolynomial_continuous _ _ _ _
  have hD : MeasurableSet D := (isClosed_le continuous_const hQc.norm).measurableSet
  have hS : (∫ t in E \ D, ‖Qk t*Rk t‖^2) ≤ 1190408*(L^(-100:ℝ))^2 := by
    apply hsmall V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi
      (Real.exp L) hT le_rfl N hN B hB k hk (E \ D) (hE.diff hD)
      (fun t ht => hET ht.1) (fun t ht => hno t ht.1)
    intro t ht
    exact (lt_of_not_ge ht.2).le
  have hY := hg.2.2.2.2 k hk
  have hY0 : 0 < Y := by change 0 < mrtPrimeLogLower H k; exact lt_trans zero_lt_one hY.1
  have hlogY : 1 ≤ Real.log Y :=
    (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 79/80)).trans hY.2.1
  have hY2 : 2 ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hHY : H^2 ≤ Y := by
    have he : H^2=L^(1/40:ℝ) := by
      change (L^(1/80:ℝ))^2=L^(1/40:ℝ)
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [he]
    calc
      _ ≤ L^(79/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ Real.log Y := hY.2.1
      _ ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hdata (p : ℕ) (hp' : p ∈ A.filter (fun p => mrtPrimeLogBin H p=k)) :
      p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y := by
    have hpp := mrtPrimeBand_prime (mem_filter.mp hp').1
    have hh := mrt_prime_log_bin_bounds hH0 hpp.one_lt.le
    rw [(mem_filter.mp hp').2] at hh
    refine ⟨hpp,hh.1,hh.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mrt_prime_log_width hH).2.1 hY0.le
  have hwindow (p : ℕ) (hp' : p ∈ A.filter (fun p => mrtPrimeLogBin H p=k)) :
      Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H := by
    have hpp := (hdata p hp').1
    have hh := mrt_prime_log_bin_bounds hH0 hpp.one_lt.le
    rw [(mem_filter.mp hp').2] at hh
    refine ⟨Real.log_le_log hY0 hh.1,?_⟩
    have hu := Real.log_le_log (by exact_mod_cast hpp.pos) hh.2
    change Real.log (p:ℝ) ≤ Real.log (Real.exp (1/H)*Y) at hu
    simpa only [Real.log_mul (Real.exp_ne_zero _) hY0.ne',Real.log_exp,add_comm] using hu
  have hG := hlarge H Y hHlarge hY2 hHY hY.2.1 hY.2.2 hlogY
    (A.filter (fun p => mrtPrimeLogBin H p=k)) F hdata hwindow hF
    A B N Y (2*L^(-1/40:ℝ)) (by positivity) E hE hET (hpoint k hk)
  have hh := mrt_product_energy_split Qk Rk hQc hRc (Real.exp_pos L).le hET hS hG
  convert (preTransparency := .instances) hh using 1
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_no_small_coarse_energy_oai := @OAI.TwoPointCorrelations.mrt_no_small_coarse_energy_oai
