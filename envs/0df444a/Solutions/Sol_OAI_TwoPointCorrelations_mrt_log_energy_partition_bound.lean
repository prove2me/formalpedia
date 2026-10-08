-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_log_energy_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:05:22.580317+00:00
-- url     : https://prove2.me/submissions/a1d3d16e-a9f2-4745-8989-7d25b4687beb

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_general_typical_small_prime_energy
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_later_log_class_energy

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



lemma mrtBandLower_one (P Q : ℝ) (hP : 0 < P) : mrtBandLower P Q 1 = P := by
  simp [mrtBandLower, Real.exp_log hP]

lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyExponents
namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations


lemma mrtFrequencyExponent_zero (η : ℝ) :
    mrtFrequencyExponent η 0 = 1 / 4 - 3 * η / 2 := by
  unfold mrtFrequencyExponent
  norm_num
  ring






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyPartition
namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical




lemma mrt_small_frequency_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtSmallFrequencyBand K Q A j) := by
  have he : mrtSmallFrequencyBand K Q A j =
      ⋂ k ∈ K j, {t | ‖Q j k t‖ ≤ A j k} := by
    ext t
    simp [mrtSmallFrequencyBand]
  rw [he]
  exact (K j).measurableSet_biInter (fun k _ =>
    (isClosed_le (hQ j k).norm continuous_const).measurableSet)

lemma mrt_first_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtFirstSmallBand K Q A j) :=
  (mrt_small_frequency_band_measurable K Q A hQ j).diff
    ((range j).measurableSet_biUnion (fun i _ =>
      mrt_small_frequency_band_measurable K Q A hQ i))


lemma mrt_first_small_band_disjoint {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (mrtFirstSmallBand K Q A i) (mrtFirstSmallBand K Q A j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨mem_range.mpr hlt, hi.1⟩⟩)
  · exact hi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hgt, hj.1⟩⟩)

theorem mrt_frequency_partition {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) (S : Set ℝ) :
    S = (S ∩ mrtNoSmallBand K Q A J) ∪
      ⋃ j ∈ range J, S ∩ mrtFirstSmallBand K Q A j := by
  ext t
  constructor
  · intro ht
    by_cases he : ∃ j < J, t ∈ mrtSmallFrequencyBand K Q A j
    · right
      let j := Nat.find he
      have hj := Nat.find_spec he
      apply Set.mem_iUnion.mpr
      refine ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj.1, ht, hj.2, ?_⟩⟩
      intro hprev
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hprev
      obtain ⟨hij, hit⟩ := Set.mem_iUnion.mp hi
      have hil : i < j := mem_range.mp hij
      exact Nat.find_min he hil ⟨hil.trans hj.1, hit⟩
    · left
      refine ⟨ht, ?_⟩
      intro hsmall
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hsmall
      obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
      exact he ⟨j, mem_range.mp hjJ, hjt⟩
  · rintro (ht | ht)
    · exact ht.1
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
      obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
      exact hjt.1

theorem mrt_later_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {j : ℕ} (hj : 0 < j)
    {t : ℝ} (ht : t ∈ mrtFirstSmallBand K Q A j) :
    ∃ k ∈ K (j - 1), A (j - 1) k < ‖Q (j - 1) k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A (j - 1) := by
    intro hsmall
    exact ht.2 (Set.mem_iUnion.mpr ⟨j - 1,
      Set.mem_iUnion.mpr ⟨mem_range.mpr (by omega), hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn


theorem mrt_frequency_partition_integral {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S) :
    (∫ t in S, f t) = (∫ t in S ∩ mrtNoSmallBand K Q A J, f t) +
      ∑ j ∈ range J, ∫ t in S ∩ mrtFirstSmallBand K Q A j, f t := by
  let E := S ∩ mrtNoSmallBand K Q A J
  let B := fun j => S ∩ mrtFirstSmallBand K Q A j
  have hBsub (j : ℕ) : B j ⊆ S := Set.inter_subset_left
  have hBmeas (j : ℕ) : MeasurableSet (B j) :=
    hS.inter (mrt_first_small_band_measurable K Q A hQ j)
  have hBdis : Set.Pairwise (↑(range J)) (fun i j => Disjoint (B i) (B j)) := by
    intro i _ j _ hij
    exact (mrt_first_small_band_disjoint K Q A hij).mono
      Set.inter_subset_right Set.inter_subset_right
  have hsum := integral_biUnion_finset (range J) (fun j _ => hBmeas j) hBdis
    (fun j _ => hf.mono_set (hBsub j))
  have hdis : Disjoint E (⋃ j ∈ range J, B j) := by
    apply Set.disjoint_left.mpr
    intro t ht hU
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
    obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
    exact ht.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hjt.2.1⟩⟩)
  have hUsub : (⋃ j ∈ range J, B j) ⊆ S := by
    intro t ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
    exact hjt.1
  conv_lhs => rw [mrt_frequency_partition K Q A J S]
  rw [setIntegral_union hdis ((range J).measurableSet_biUnion (fun j _ => hBmeas j))
    (hf.mono_set Set.inter_subset_left) (hf.mono_set hUsub), hsum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeometricBins
namespace OAI

/-! The exponential sum over the first MRT prime band. Its constant is
independent of the number of coarse bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_exp_geometric_sum {β H : ℝ} (hβ : 0 < β) (hH : 0 < H) (m n : ℕ) :
    (∑ k ∈ Icc m n, Real.exp (-β * (k : ℝ) / H)) ≤
      Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) := by
  let q := Real.exp (-β / H)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by linarith : -β < 0) hH
  have he (k : ℕ) : Real.exp (-β * (k : ℝ) / H) = q ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Icc m n = Ico m (n + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  simp_rw [he]
  rw [hs]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

lemma mrt_geometric_denominator_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 / (1 - Real.exp (-x)) ≤ 2 / x := by
  have hex : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hex
  have hgap : x / 2 ≤ 1 - Real.exp (-x) := by
    calc
      _ ≤ x / (1 + x) := div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      _ = 1 - 1 / (1 + x) := by
        field_simp [show (1 : ℝ) + x ≠ 0 by positivity]
        ring
      _ ≤ _ := sub_le_sub_left hinv 1
  calc
    _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hgap
    _ = _ := by ring

theorem mrt_first_band_exponential_sum {β H P : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H) (hP : 1 ≤ P) (n : ℕ) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ n, Real.exp (-β * (k : ℝ) / H)) ≤
      (2 * Real.exp 1 * H / β) * P ^ (-β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  let m : ℕ := ⌊H * Real.log P⌋₊
  have hfloor : H * Real.log P < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase : -β * (m : ℝ) / H ≤ -β * Real.log P + β / H := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hfloor.le hβ.le
    field_simp [hH.ne']
    nlinarith
  have hpower : Real.exp (-β * (m : ℝ) / H) ≤ Real.exp 1 * P ^ (-β) := by
    calc
      _ ≤ Real.exp (-β * Real.log P + β / H) := Real.exp_le_exp.mpr hbase
      _ = Real.exp (β / H) * P ^ (-β) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hP0]
        rw [show -β * Real.log P = Real.log P * (-β) by ring, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((div_le_one hH).mpr hβH)) (Real.rpow_nonneg hP0.le _)
  have hgap : 0 < 1 - Real.exp (-β / H) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith : -β < 0) hH))
  have hden : 1 / (1 - Real.exp (-β / H)) ≤ 2 / (β / H) := by
    simpa only [neg_div] using mrt_geometric_denominator_bound (div_pos hβ hH)
      ((div_le_one hH).mpr hβH)
  calc
    _ ≤ Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) :=
      mrt_exp_geometric_sum hβ hH m n
    _ ≤ (Real.exp 1 * P ^ (-β)) * (2 / (β / H)) := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul hpower hden (le_of_lt (one_div_pos.mpr hgap)) (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

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

lemma mrt_prime_log_bin_range {H P Q : ℝ} (hH : 0 ≤ H)
    (hP : 0 < P) {p : ℕ} (hp : P ≤ p) (hq : (p : ℝ) ≤ Q) :
    mrtPrimeLogBin H p ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊ := by
  have hp0 : (0 : ℝ) < p := hP.trans_le hp
  apply mem_Icc.mpr
  constructor
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hP hp) hH)
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hq) hH)

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

/-- The complete first-band scalar sum; the number of coarse bins does
not appear in the geometric part of the bound. -/
theorem mrt_log_bin_weighted_sum {β H P Q N T : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hN : 0 < N) (hT : 0 ≤ T) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
      Real.exp (-β * (k : ℝ) / H) * (T * mrtPrimeLogLower H k / N + 1)) ≤
      ((2 * Real.exp 1 * H / β) * P ^ (-β)) * (T * Q / N + 1) := by
  calc
    _ ≤ ∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
        Real.exp (-β * (k : ℝ) / H) * (T * Q / N + 1) := by
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mrt_prime_log_lower_le_upper hH hQ (mem_Icc.mp hk).2) hT)
        hN.le
    _ = (∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
        Real.exp (-β * (k : ℝ) / H)) * (T * Q / N + 1) := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mrt_first_band_exponential_sum hβ hH hβH hP _) (by positivity)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandLogGrowth
namespace OAI

/-! Uniform scalar growth estimates for the actual MRT band endpoints.
These estimates bound the mixed-moment factorial cost for every band. -/

namespace TwoPointCorrelations


lemma mrt_log_band_lower_fourth (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (j : ℝ) ^ 4 * Real.log P ≤ Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : (j : ℝ) ^ 4 ≤ (j : ℝ) ^ (4 * j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q ^ (j - 1) := one_le_pow₀ hQ
  simp only [mrtBandLower, Real.log_exp]
  apply mul_le_mul_of_nonneg_right _ hP
  exact hp.trans (le_mul_of_one_le_right (by positivity) hq)




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

lemma mrtResolution_one (P Q η : ℝ) : mrtResolution P Q η 1 = mrtBaseResolution P Q η := by
  simp [mrtResolution]

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

lemma mrt_resolution_log_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (j : ℕ) (hj : 1 ≤ j) :
    Real.log (mrtResolution P Q η j) ≤ 2 * Real.log (j : ℝ) + Real.log P := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hh := Real.log_le_log (mrtResolution_pos P Q η hj)
    (mrt_resolution_le hP hQ hη j)
  rwa [Real.log_mul (pow_ne_zero _ hj0.ne') (by linarith : P ≠ 0),
    Real.log_pow, Nat.cast_ofNat] at hh

lemma mrt_base_resolution_balance (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 3 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) = 1 := by
  have hq : 0 < Real.log Q := Real.log_pos hQ
  unfold mrtBaseResolution
  rw [← Real.exp_nat_mul]
  have he : (3 : ℝ) * ((1 / 6 - η) * Real.log P -
      (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
      (-2 * mrtFrequencyExponent η 0 * Real.log P) = 0 := by
    rw [mrtFrequencyExponent_zero]
    ring
  calc
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q))) * Real.exp (Real.log (Real.log Q)) *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) := by
      rw [Real.exp_log hq]
      norm_num
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
          (-2 * mrtFrequencyExponent η 0 * Real.log P)) := by
      rw [Real.exp_add, Real.exp_add]
    _ = 1 := by rw [he, Real.exp_zero]

lemma mrt_base_resolution_first_cost (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 2 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) =
      (mrtBaseResolution P Q η)⁻¹ := by
  have hh := mrt_base_resolution_balance P Q η hQ
  have hH := mrtBaseResolution_pos P Q η
  rw [← one_div]
  apply (eq_div_iff hH.ne').mpr
  convert (preTransparency := .instances) hh using 1
  ring

lemma mrt_resolution_inverse_sum (P Q η : ℝ) (J : ℕ) :
    (∑ j ∈ Icc 1 J, (mrtResolution P Q η j)⁻¹) ≤
      2 * (mrtBaseResolution P Q η)⁻¹ := by
  have hs : (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have he : Icc 1 J = Ioo 0 (J + 1) := by ext j; simp; omega
    rw [he]
    simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1)
  calc
    _ = (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) * (mrtBaseResolution P Q η)⁻¹ := by
      simp only [mrtResolution, mul_inv_rev, sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (mrtBaseResolution_pos P Q η).le)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFirstBinSum
namespace OAI

/-! The first small-prime frequency class has exactly the reciprocal
resolution saving dictated by the cubic balance. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem mrt_first_bin_moment_sum {η P Q N T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 12) (hP : 1 ≤ P) (hQ0 : 0 < Q) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N) (hT : 0 ≤ T) :
    64 * Real.exp 1 * ((mrtLogBins (mrtBaseResolution P Q η) P Q).card : ℝ) *
        ∑ k ∈ mrtLogBins (mrtBaseResolution P Q η) P Q,
          (Real.exp (-mrtFrequencyExponent η 0 *
              Real.log (mrtPrimeLogLower (mrtBaseResolution P Q η) k))) ^ 2 *
            (T * mrtPrimeLogLower (mrtBaseResolution P Q η) k / N + 1) ≤
      1024 * Real.exp 2 * (T * Q / N + 1) * (mrtBaseResolution P Q η)⁻¹ := by
  let H := mrtBaseResolution P Q η
  let β := 2 * mrtFrequencyExponent η 0
  have hβ : 1 / 4 ≤ β := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hβ' : β ≤ 1 / 2 := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hH0 : 0 < H := mrtBaseResolution_pos P Q η
  have hQ1 : 1 < Q := by
    have hh : 1 < Real.exp (Real.log Q) := Real.one_lt_exp_iff.mpr (by linarith)
    simpa only [Real.exp_log hQ0] using hh
  have he (k : ℕ) :
      (Real.exp (-mrtFrequencyExponent η 0 * Real.log (mrtPrimeLogLower H k))) ^ 2 =
        Real.exp (-β * (k : ℝ) / H) := by
    rw [← Real.exp_nat_mul]
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    congr 1
    ring
  dsimp only [H] at he
  simp_rw [he]
  have hs := mrt_log_bin_weighted_sum (by linarith : 0 < β) hH0
    (by dsimp [H]; linarith : β ≤ H) hP hQ1.le hN hT
  have hc := mrt_log_bin_card (P := P) hH0.le hQ1.le
  have hc' : ((mrtLogBins H P Q).card : ℝ) ≤ 2 * H * Real.log Q := by
    have hh : 1 ≤ H * Real.log Q := by dsimp [H]; nlinarith
    change ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ _
    linarith
  have hi : 1 / β ≤ 4 := (div_le_iff₀ (by linarith : 0 < β)).mpr (by linarith)
  have hbalance : H ^ 2 * Real.log Q * P ^ (-β) = H⁻¹ := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < P)]
    dsimp [β, H]
    rw [show Real.log P * -(2 * mrtFrequencyExponent η 0) =
      -2 * mrtFrequencyExponent η 0 * Real.log P by ring]
    exact mrt_base_resolution_first_cost P Q η hQ1
  calc
    _ ≤ 64 * Real.exp 1 * (2 * H * Real.log Q) *
        (((2 * Real.exp 1 * H / β) * P ^ (-β)) * (T * Q / N + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hc' (by positivity)
      · exact hs
      · exact sum_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le
          (by unfold mrtPrimeLogLower; positivity))
      · positivity
    _ = 256 * Real.exp 2 * (T * Q / N + 1) *
        (H ^ 2 * Real.log Q * P ^ (-β)) * (1 / β) := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      ring
    _ ≤ 256 * Real.exp 2 * (T * Q / N + 1) * H⁻¹ * 4 := by
      rw [hbalance]
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [H]; ring

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




lemma mrt_log_bin_prime_data (S : Finset ℕ) {H P Q : ℝ} (hH : 2 ≤ H)
    (hP : 0 < P) (hprime : ∀ p ∈ S, p.Prime)
    (hrange : ∀ p ∈ S, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q) :
    (∀ p ∈ S, mrtPrimeLogBin H p ∈ mrtLogBins H P Q) ∧
    (∀ p ∈ S, mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (1/H)*mrtPrimeLogLower H (mrtPrimeLogBin H p)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact mrt_prime_log_bin_range (by linarith) hP (hrange p hp).1 (hrange p hp).2
  · intro p hp
    exact mrt_prime_log_bin_bounds (by linarith) (hprime p hp).one_le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtractionErrors
namespace OAI

/-! The prime-square and coarse-bin errors sum independently of the
number of MRT bands. The only input is their actual lower endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_finite_reciprocal_square_tail (S : Finset ℕ) {y : ℝ} (hy : 1 ≤ y)
    (hS : ∀ n ∈ S, y ≤ (n:ℝ)) : (∑ n ∈ S, 1/(n:ℝ)^2) ≤ 2/y := by
  let k := ⌈y⌉₊-1
  have hc : 1 ≤ ⌈y⌉₊ := by
    exact_mod_cast hy.trans (Nat.le_ceil y)
  have hk : k+1 = ⌈y⌉₊ := by dsimp [k]; omega
  have hsub : S ⊆ Ioo k (S.sup id+1) := by
    intro n hn
    have hcn : ⌈y⌉₊ ≤ n := Nat.ceil_le.mpr (hS n hn)
    exact mem_Ioo.mpr ⟨by dsimp [k]; omega, Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  calc
    _ ≤ ∑ n ∈ Ioo k (S.sup id+1), ((n:ℝ)^2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2/((k:ℝ)+1) := sum_Ioo_inv_sq_le (α := ℝ) k (S.sup id+1)
    _ = 2/(⌈y⌉₊:ℝ) := by
      have hkr : (k:ℝ)+1 = (⌈y⌉₊:ℝ) := by exact_mod_cast hk
      rw [hkr]
    _ ≤ 2/y := div_le_div_of_nonneg_left (by norm_num) (by linarith) (Nat.le_ceil y)

lemma mrt_resolution_le_band_lower {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) : mrtResolution P Q η j ≤ mrtBandLower P Q j := by
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0:ℝ) < j := by linarith
  have hp1 : 1 ≤ P := by
    rw [← Real.exp_log hP0]
    exact Real.one_le_exp (by linarith)
  have hr := mrt_resolution_log_le hp1 hQ hη j hj
  have hl := mrt_log_band_lower_fourth P Q j hj (by linarith) hQ
  have hlogj := Real.log_le_sub_one_of_pos hj0
  have hj2 : 1 ≤ (j:ℝ)^2 := one_le_pow₀ hj1
  have hp := mul_nonneg (sub_nonneg.mpr hj2) (by linarith : 0 ≤ Real.log P-1)
  have hsq := sq_nonneg ((j:ℝ)-1)
  have hpow : (j:ℝ)^2 ≤ (j:ℝ)^4 := pow_le_pow_right₀ hj1 (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hpow (by linarith : 0 ≤ Real.log P)
  have hlogs : Real.log (mrtResolution P Q η j) ≤ Real.log (mrtBandLower P Q j) := by
    nlinarith
  calc
    _ = Real.exp (Real.log (mrtResolution P Q η j)) :=
      (Real.exp_log (mrtResolution_pos P Q η hj)).symm
    _ ≤ Real.exp (Real.log (mrtBandLower P Q j)) := Real.exp_le_exp.mpr hlogs
    _ = _ := Real.exp_log (Real.exp_pos _)

lemma mrt_prime_extraction_error (S : Finset ℕ) {y H : ℝ} (hH : 2 ≤ H)
    (hHy : H ≤ y) (hS : ∀ n ∈ S, y ≤ (n:ℝ)) :
    (∑ n ∈ S, 1/(n:ℝ)^2)+(∑ n ∈ S, 1/(n:ℝ)^2)^2+2/H ≤ 6/H := by
  let A := ∑ n ∈ S, 1/(n:ℝ)^2
  have hA0 : 0 ≤ A := sum_nonneg (fun _ _ => by positivity)
  have hA : A ≤ 2/H := (mrt_finite_reciprocal_square_tail S (by linarith) hS).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hHy)
  have hA1 : A ≤ 1 := hA.trans ((div_le_one (by linarith : 0 < H)).mpr hH)
  have hs : A^2 ≤ A := by nlinarith
  change A+A^2+2/H ≤ 6/H
  have he : 6/H = 3*(2/H) := by ring
  rw [he]
  linarith

theorem mrt_prime_extraction_error_sum (V : ℕ → Finset ℕ) (J : ℕ)
    {P Q η : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, mrtBandLower P Q j ≤ (p:ℝ)) :
    (∑ j ∈ Icc 1 J,
      ((∑ p ∈ V j, 1/(p:ℝ)^2)+(∑ p ∈ V j, 1/(p:ℝ)^2)^2+
        2/mrtResolution P Q η j)) ≤ 12*(mrtBaseResolution P Q η)⁻¹ := by
  have hres (j : ℕ) (hj : j ∈ Icc 1 J) : 2 ≤ mrtResolution P Q η j := by
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    have hs : 1 ≤ (j:ℝ)^2 := one_le_pow₀ hj1
    unfold mrtResolution
    nlinarith [mrtBaseResolution_pos P Q η]
  calc
    _ ≤ ∑ j ∈ Icc 1 J, 6/mrtResolution P Q η j := by
      apply sum_le_sum
      intro j hj
      exact mrt_prime_extraction_error (V j) (hres j hj)
        (mrt_resolution_le_band_lower hP0 hP hQ hη j (mem_Icc.mp hj).1) (hrange j hj)
    _ = 6*(∑ j ∈ Icc 1 J, (mrtResolution P Q η j)⁻¹) := by
      rw [mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ 6*(2*(mrtBaseResolution P Q η)⁻¹) :=
      mul_le_mul_of_nonneg_left (mrt_resolution_inverse_sum P Q η J) (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFirstClassEnergy
namespace OAI

/-! The first frequency-class estimate for actual logarithmic prime bins.
Prime membership, bin width, and the complete scalar sum are derived here. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

theorem mrt_first_log_class_energy {ι : Type*} (J : Finset ι) (V : ι → Finset ℕ)
    (hprime : ∀ j ∈ J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) V) {j : ι} (hj : j ∈ J)
    {P Q η : ℝ} (hP : 1 ≤ P) (hQ0 : 0 < Q) (hQ : 1 ≤ Real.log Q)
    (hη : 0 ≤ η) (hη' : η ≤ 1/12)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ p ∈ V j, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc (-T) T ∩ mrtLogSmallSet (V j) F (mrtBaseResolution P Q η)
        (mrtLogBins (mrtBaseResolution P Q η) P Q) (mrtFrequencyExponent η 0),
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ V j, 1/(p:ℝ)^2)+(∑ p ∈ V j, 1/(p:ℝ)^2)^2+
          2/mrtBaseResolution P Q η) +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ := by
  let H := mrtBaseResolution P Q η
  let K := mrtLogBins H P Q
  let E := Ioc (-T) T ∩ mrtLogSmallSet (V j) F H K (mrtFrequencyExponent η 0)
  have hH0 : 0 < H := mrtBaseResolution_pos P Q η
  have hQ1 : 1 ≤ Q := by
    have hh := Real.one_le_exp (by linarith : 0 ≤ Real.log Q)
    simpa only [Real.exp_log hQ0] using hh
  have hdata := mrt_log_bin_prime_data (V j) hH (by linarith : 0 < P)
    (hprime j hj) hrange
  have hwidth := mrt_prime_log_width hH
  have hupper (k : ℕ) (hk : k ∈ K) : 2 ≤ (N:ℝ)/mrtPrimeLogLower H k := by
    have hkQ : mrtPrimeLogLower H k ≤ Q :=
      mrt_prime_log_lower_le_upper hH0 hQ1 (mem_Icc.mp hk).2
    exact (le_div_iff₀ (Real.exp_pos _)).mpr
      ((mul_le_mul_of_nonneg_left hkQ (by norm_num : (0:ℝ) ≤ 2)).trans hsize)
  have hb := mrt_general_typical_small_prime_energy J V hprime hdis hj K
    (mrtPrimeLogBin H) hdata.1 (mrtPrimeLogLower H) hN hwidth.1 hwidth.2.1 hdata.2
    (fun k _ => mrt_prime_log_lower_one hH0 k) hupper F hF hFb hT E
    inter_subset_left (fun k => Real.exp (-mrtFrequencyExponent η 0 *
      Real.log (mrtPrimeLogLower H k))) (fun k hk t ht => ht.2 k hk)
  have hs := mrt_first_bin_moment_sum (N := (N:ℝ)) (T := T) hη hη' hP hQ0 hQ hH
    (by exact_mod_cast hN) hT.le
  change (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤ _
  apply hb.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (by linarith [hwidth.2.2]) (by positivity)) hs

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogPartition
namespace OAI

/-! The actual logarithmic prime-polynomial family in the finite
first-small partition. Index `r` corresponds to prime band `r+1`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical





lemma mrt_first_log_class_zero (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    {P Q η : ℝ} (hP : 0 < P) (hQ : 0 < Q) (T : ℝ) :
    mrtFirstLogClass V F P Q η 0 T =
      Ioc (-T) T ∩ mrtLogSmallSet (V 1) F (mrtBaseResolution P Q η)
        (mrtLogBins (mrtBaseResolution P Q η) P Q) (mrtFrequencyExponent η 0) := by
  ext t
  simp [mrtFirstLogClass, mrtFirstSmallBand, mrtSmallFrequencyBand, mrtLogFamilyBins,
    mrtLogFamilyPolynomial, mrtLogFamilyThreshold, mrtResolution_one,
    mrtBandLower_one _ _ hP, mrtBandUpper_one _ hQ, mrtLogSmallSet]

lemma mrt_first_log_class_succ_subset (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (j : ℕ) (T : ℝ) :
    mrtFirstLogClass V F P Q η (j+1) T ⊆
      mrtLaterLogClass (V (j+1)) (V (j+2)) F P Q η j T := by
  intro t ht
  obtain ⟨b, hb, hlarge⟩ := mrt_later_band_large_witness
    (mrtLogFamilyBins P Q η) (mrtLogFamilyPolynomial V F P Q η)
    (mrtLogFamilyThreshold P Q η) (by omega : 0 < j+1) ht.2
  have he : j+1-1 = j := by omega
  rw [he] at hb hlarge
  refine ⟨ht.1, ?_, b, hb, hlarge⟩
  intro k hk
  have hh := ht.2.1 k hk
  simpa only [mrtLogFamilyPolynomial, mrtLogFamilyThreshold, Nat.add_assoc] using hh

theorem mrt_log_partition_integral (V : ℕ → Finset ℕ) (J : ℕ)
    (F : ℕ → ℂ) (P Q η : ℝ) {N : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) =
      (∫ t in Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) +
      ∑ r ∈ range J, ∫ t in mrtFirstLogClass V F P Q η r T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact mrt_frequency_partition_integral (mrtLogFamilyBins P Q η)
    (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η)
    (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) J measurableSet_Ioc
    (fun t => ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2)
    (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _) hT
      (Subset.refl _))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassBounds
namespace OAI

/-! Uniform bounds for the actual first-small logarithmic classes.
The first-band cost occurs once; the later costs form an inverse-square sum. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical


theorem mrt_log_class_energy (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) {r : ℕ} (hr : r ∈ range J) :
    (∫ t in mrtFirstLogClass V F P Q η r T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*mrtLogExtractionError V P Q η (r+1) +
      (if r = 0 then
        1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ else 0) +
      (T/N+1)*P⁻¹*(((r:ℝ)+1)^2)⁻¹ := by
  have hp1 : 1 ≤ P := by
    rw [← Real.exp_log hP0]
    exact Real.one_le_exp (by linarith)
  have hlast : r+1 ∈ Finset.Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hr; omega⟩
  have hnon : 0 ≤ (T/N+1)*P⁻¹*(((r:ℝ)+1)^2)⁻¹ := by positivity
  by_cases hzero : r = 0
  · subst r
    have hrange1 : ∀ p ∈ V 1, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q := by
      simpa only [mrtBandLower_one P Q hP0, mrtBandUpper_one Q hQ0] using hrange 1 hlast
    have hb := mrt_first_log_class_energy (Finset.Icc 1 J) V hprime hdis hlast hp1 hQ0 hQ
      hη.le hη' hH hrange1 hN hsize F hF hFb hT
    rw [mrt_first_log_class_zero V F hP0 hQ0]
    simp only [Nat.zero_add, ite_true, mrtLogExtractionError, mrtResolution_one]
    exact hb.trans (le_add_of_nonneg_right hnon)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hprev : j+1 ∈ Finset.Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hr; omega⟩
    have hb := mrt_later_log_class_energy (Finset.Icc 1 J) V hprime hdis hlast
      (V (j+1)) (hprime (j+1) hprev) hP0 hP hQ hPQ hη (by linarith) hbudget hH j
      (hrange (j+1) hprev) (hrange (j+2) hlast) hN F hF hFb hT
    have hi : (∫ t in mrtFirstLogClass V F P Q η (j+1) T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
        ∫ t in mrtLaterLogClass (V (j+1)) (V (j+2)) F P Q η j T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2 :=
      setIntegral_mono_set
        (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _)
          hT.le inter_subset_left)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (mrt_first_log_class_succ_subset V F P Q η j T))
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_one_ne_zero,
      ite_false, add_zero, mrtLogExtractionError, Nat.cast_add, Nat.cast_one,
      add_assoc, show (1:ℕ)+1 = 2 by decide,
      show (1:ℝ)+1 = 2 by norm_num] using hi.trans hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmallClassSum
namespace OAI

/-! The full small-class contribution, with all actual prime-bin and
extraction costs summed independently of the number of bands. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical

lemma mrt_sum_range_succ (f : ℕ → ℝ) (J : ℕ) :
    (∑ r ∈ range J, f (r+1)) = ∑ j ∈ Finset.Icc 1 J, f j := by
  rw [range_eq_Ico, sum_Ico_add' f 0 J 1]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma mrt_shifted_inverse_square_sum (J : ℕ) :
    (∑ r ∈ range J, (((r:ℝ)+1)^2)⁻¹) ≤ 2 := by
  have he : Finset.Icc 1 J = Finset.Ioo 0 (J+1) := by ext j; simp; omega
  have hs := mrt_sum_range_succ (fun j => ((j:ℝ)^2)⁻¹) J
  simp only [Nat.cast_add, Nat.cast_one] at hs
  rw [hs, he]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J+1)

theorem mrt_small_log_class_sum (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∑ r ∈ range J, ∫ t in mrtFirstLogClass V F P Q η r T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      33792*Real.exp 1*(T/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      2*(T/N+1)*P⁻¹ := by
  let C := 2816*Real.exp 1*(T/N+1)
  let D := (T/N+1)*P⁻¹
  let B := 1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have herr : (∑ r ∈ range J, mrtLogExtractionError V P Q η (r+1)) ≤
      12*(mrtBaseResolution P Q η)⁻¹ := by
    rw [mrt_sum_range_succ]
    exact mrt_prime_extraction_error_sum V J hP0 hP hQ hη.le hH
      (fun j hj p hp => (hrange j hj p hp).1)
  have hone : (∑ r ∈ range J, if r = 0 then B else 0) ≤ B := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hB
  calc
    _ ≤ ∑ r ∈ range J, (C*mrtLogExtractionError V P Q η (r+1) +
        (if r = 0 then B else 0) + D*(((r:ℝ)+1)^2)⁻¹) := by
      apply sum_le_sum
      intro r hr
      exact mrt_log_class_energy V J hprime hdis hP0 hQ0 hP hQ hPQ hη hη'
        hbudget hH hrange hN hsize F hF hFb hT hr
    _ = C*(∑ r ∈ range J, mrtLogExtractionError V P Q η (r+1)) +
        (∑ r ∈ range J, if r = 0 then B else 0) +
        D*(∑ r ∈ range J, (((r:ℝ)+1)^2)⁻¹) := by
      simp only [sum_add_distrib, mul_sum]
    _ ≤ C*(12*(mrtBaseResolution P Q η)⁻¹) + B + D*2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left herr hC) hone)
        (mul_le_mul_of_nonneg_left (mrt_shifted_inverse_square_sum J) hD)
    _ = _ := by dsimp [C, D, B]; ring

theorem mrt_log_energy_partition_bound_oai (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      (∫ t in Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) +
      (33792*Real.exp 1*(T/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      2*(T/N+1)*P⁻¹) := by
  rw [mrt_log_partition_integral V J F P Q η hT.le]
  exact add_le_add le_rfl (mrt_small_log_class_sum V J hprime hdis hP0 hQ0 hP hQ hPQ
    hη hη' hbudget hH hrange hN hsize F hF hFb hT)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_log_energy_partition_bound_oai := @OAI.TwoPointCorrelations.mrt_log_energy_partition_bound_oai
