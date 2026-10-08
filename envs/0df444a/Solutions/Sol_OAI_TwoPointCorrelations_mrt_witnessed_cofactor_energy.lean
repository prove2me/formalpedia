-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_witnessed_cofactor_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:01.154021+00:00
-- url     : https://prove2.me/submissions/7474e404-8c2e-4426-be2f-04baf6eef18b

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_short_class_cofactor_energy_chosen

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorWindow
namespace OAI

/-! The cofactor polynomial has an actual fixed multiplicative window.
Finite partial summation turns its ordinary reciprocal-count prefix bound
into a pointwise bound for that polynomial. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_cofactor_window_set (N : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    ((Icc 1 (4 * N)).filter (fun m : ℕ => (N : ℝ) < a * (m : ℝ) ∧ a * (m : ℝ) ≤ 2 * N)) =
      Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfloor : ⌊(2 * N : ℝ) / a⌋₊ ≤ 4 * N := by
    apply Nat.floor_le_of_le
    have hdiv : (2 * N : ℝ) / a ≤ 2 * N := div_le_self (by positivity) ha
    push_cast
    linarith
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hlo, hhi⟩ := mem_filter.mp hm
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (div_nonneg hN0 ha0.le)).mpr
      apply (div_lt_iff₀ ha0).mpr
      simpa only [mul_comm] using hlo
    · apply Nat.le_floor
      apply (le_div_iff₀ ha0).mpr
      simpa only [mul_comm] using hhi
  · intro hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    have hloR := (Nat.floor_lt (div_nonneg hN0 ha0.le)).mp hlo
    have hhiR : (m : ℝ) ≤ (2 * N : ℝ) / a :=
      (Nat.le_floor_iff (by positivity)).mp hhi
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hhi.trans hfloor⟩, ?_⟩
    constructor
    · simpa only [mul_comm] using (div_lt_iff₀ ha0).mp hloR
    · simpa only [mul_comm] using (le_div_iff₀ ha0).mp hhiR





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMean
namespace OAI

/-! A mean-square bound for the actual fixed-window cofactor polynomial.
The reciprocal-count weight is a contraction, so this estimate is uniform
in all remaining typical-factorization masks. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_cofactor_exponential_polynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold mrtDirichletAtom
  ring



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyCover
namespace OAI

/-! Refinement of a later frequency class by its actual preceding-bin
large-value witnesses. The witnesses may overlap; the finite sum charges
each preceding bin explicitly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_nonnegative_integral_cover {ι : Type*} (I : Finset ι)
    (E : ι → Set ℝ) (hE : ∀ i ∈ I, MeasurableSet (E i)) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hcover : ∀ t ∈ S, ∃ i ∈ I, t ∈ E i) :
    (∫ t in S, f t) ≤ ∑ i ∈ I, ∫ t in S ∩ E i, f t := by
  have hi (i : ι) (hmem : i ∈ I) : IntegrableOn ((E i).indicator f) S :=
    hf.indicator (hE i hmem)
  calc
    _ ≤ ∫ t in S, ∑ i ∈ I, (E i).indicator f t := by
      apply setIntegral_mono_on hf (integrable_finsetSum I hi) hS
      intro t ht
      obtain ⟨i, hiI, hit⟩ := hcover t ht
      calc
        f t = (E i).indicator f t := (Set.indicator_of_mem hit f).symm
        _ ≤ ∑ i ∈ I, (E i).indicator f t := by
          apply single_le_sum _ hiI
          intro k _
          by_cases hk : t ∈ E k
          · rw [Set.indicator_of_mem hk f]
            exact hf0 t ht
          · rw [Set.indicator_of_notMem hk f]
    _ = ∑ i ∈ I, ∫ t in S, (E i).indicator f t := integral_finsetSum I hi
    _ = _ := by
      apply sum_congr rfl
      intro i hiI
      exact setIntegral_indicator (hE i hiI)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRealPrimeBins
namespace OAI

/-! Real short-prime bins, as used in the Ramaré decomposition, fit the
integer endpoint mixed-moment theorem without moving any prime. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrt_real_prime_bin_subset (P : Finset ℕ) {Y : ℝ}
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) :
    P ⊆ Icc ⌈Y⌉₊ (2 * ⌈Y⌉₊) := by
  intro p hp
  refine mem_Icc.mpr ⟨Nat.ceil_le.mpr (hbin p hp).1, ?_⟩
  have hh : (p : ℝ) ≤ 2 * (⌈Y⌉₊ : ℝ) :=
    (hbin p hp).2.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num))
  exact_mod_cast hh

lemma mrt_real_prime_bin_ceil {Y : ℝ} (hY : 1 < Y) :
    1 < ⌈Y⌉₊ ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ 2 * Y ∧
      Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log Y + Real.log 2 := by
  have hY0 : 0 < Y := by linarith
  have hlo : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hhi : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have hh := Nat.ceil_lt_add_one hY0.le
    linarith
  refine ⟨Nat.lt_ceil.mpr (by simpa using hY), hlo, hhi, ?_⟩
  calc
    _ ≤ Real.log (2 * Y) := Real.log_le_log (hY0.trans_le hlo) hhi
    _ = _ := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY0.ne']; ring

theorem mrt_real_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y)
    {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
          ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder ⌈Y⌉₊ u) := by
  exact mrt_short_class_cofactor_energy_chosen P Q hP
    (mrt_real_prime_bin_ceil hY).1 hN
    (mrt_real_prime_bin_subset P hbin) a ha F hF hu hT hV hE hlarge

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWitnessedEnergy
namespace OAI

/-! The coarse energy on a later MRT class, summed over actual large
preceding-bin witnesses. The Ramaré error is deliberately absent here:
it is charged once, before this finite cover is used. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem mrt_witnessed_cofactor_energy_oai {κ β : Type*}
    (K : Finset κ) (Q : κ → ℝ → ℂ) (A lower : κ → ℝ)
    (P : Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) (hlower : ∀ k ∈ K, 1 ≤ lower k)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hPprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (a : β → ℕ → ℂ) (ha : ∀ b ∈ B, ∀ p ∈ Pprev b, ‖a b p‖ ≤ 1)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S)
    (hST : S ⊆ Set.Ioc (-T) T) (hQ : ∀ k ∈ K, Continuous (Q k))
    (hsmall : ∀ k ∈ K, ∀ t ∈ S, ‖Q k t‖ ≤ A k)
    (hcover : ∀ t ∈ S, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in S, ‖∑ k ∈ K, Q k t * mrtCofactorPolynomial P F N (lower k) t‖ ^ 2) ≤
      ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial P F N (lower k)
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  let E : β → Set ℝ := fun b => {t | V b ≤
    ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t‖}
  have hR (k : κ) (hk : k ∈ K) : Continuous (R k) := by
    have he : R k = mrtExponentialPolynomial
        (Ioc ⌊(N : ℝ) / lower k⌋₊ ⌊(2 * N : ℝ) / lower k⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial P F N (hlower k hk))
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk => (hQ k hk).mul (hR k hk))
  have hE (b : β) : MeasurableSet (E b) :=
    (isClosed_le continuous_const
      (mrtExponentialPolynomial_continuous _ _ _).norm).measurableSet
  have hiG : IntegrableOn (fun t => ‖G t‖ ^ 2) S :=
    mrt_continuous_square_integrable hG hT.le hST
  change (∫ t in S, ‖G t‖ ^ 2) ≤ _
  apply (mrt_nonnegative_integral_cover B E (fun b _ => hE b) hS
    (fun t => ‖G t‖ ^ 2) hiG (fun _ _ => sq_nonneg _) hcover).trans
  apply sum_le_sum
  intro b hb
  change (∫ t in S ∩ E b, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
  have hsub : S ∩ E b ⊆ Set.Ioc (-T) T := Set.inter_subset_left.trans hST
  apply (mrt_restricted_product_sum_energy_local K Q R hR A hT.le hsub
    (fun k hk t ht => hsmall k hk t ht.1)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact mrt_real_short_class_cofactor_energy (Pprev b) P (hPprev b hb) (hY b hb)
    (hprevbin b hb) hN (a b) (ha b hb) F hF (hlower k hk) hT (hV b hb)
    hsub (fun t ht => ht.2)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_witnessed_cofactor_energy_oai := @OAI.TwoPointCorrelations.mrt_witnessed_cofactor_energy_oai
