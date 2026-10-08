-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_typical_near_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:37:05.819154+00:00
-- url     : https://prove2.me/submissions/bfd18ec0-20ff-4040-be37-dc77333aa1e7

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeightedPrefix
namespace OAI

/-! Finite partial summation from ordinary prefix cancellation to a
normalized Dirichlet polynomial on a bounded-ratio interval. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_range_zero_extension (F : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else F i) = ∑ i ∈ Icc 1 n, F i := by
  rw [Nat.range_succ_eq_Icc_zero,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [if_neg (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_reciprocal_summation_by_parts (F : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, F i / (i : ℂ)) =
      ((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i) -
      ((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i) -
      ∑ i ∈ Ioc m (n - 1),
        (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
          (∑ j ∈ Icc 1 i, F j) := by
  have he := sum_Ioc_by_parts
    (fun i : ℕ => ((1 / (i : ℝ) : ℝ) : ℂ))
    (fun i : ℕ => if i = 0 then (0 : ℂ) else F i) hmn
  simp only [smul_eq_mul, mrt_range_zero_extension] at he
  convert (preTransparency := .instances) he using 1
  apply sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := (mem_Ioc.mp hi).1; omega
  simp only [if_neg hi0, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  ring

lemma mrt_reciprocal_gap {i : ℕ} (hi : 0 < i) :
    |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * i =
      1 / ((i + 1 : ℕ) : ℝ) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hle : 1 / ((i + 1 : ℕ) : ℝ) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le hiR (by norm_num)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  push_cast
  field_simp
  ring

/-- A prefix bound on the same scale controls the normalized polynomial
on every interval of ratio at most three. -/
theorem mrt_weighted_prefix_bound (F : ℕ → ℂ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (hn3 : n ≤ 3 * m)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ k ∈ Icc m n, ‖∑ i ∈ Icc 1 k, F i‖ ≤ A * k) :
    ‖∑ i ∈ Ioc m n, F i / (i : ℂ)‖ ≤ 5 * A := by
  by_cases he : m = n
  · subst n
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty, norm_zero]
    positivity
  have hmn' : m < n := lt_of_le_of_ne hmn he
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (hm.trans_le hmn)
  have htop : ‖((1 / (n : ℝ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 n, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / (n : ℝ)) * (A * n) :=
        mul_le_mul_of_nonneg_left (hF n (mem_Icc.mpr ⟨hmn, le_rfl⟩)) (by positivity)
      _ = _ := by field_simp
  have hbot : ‖((1 / (m + 1 : ℕ) : ℝ) : ℂ) * (∑ i ∈ Icc 1 m, F i)‖ ≤ A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      _ ≤ (1 / ((m + 1 : ℕ) : ℝ)) * (A * m) :=
        mul_le_mul_of_nonneg_left (hF m (mem_Icc.mpr ⟨le_rfl, hmn⟩)) (by positivity)
      _ ≤ A := by
        rw [one_div, inv_mul_eq_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
        push_cast
        nlinarith
  have hterm (i : ℕ) (hi : i ∈ Ioc m (n - 1)) :
      ‖(((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ A / (m : ℝ) := by
    have hi0 : 0 < i := hm.trans (mem_Ioc.mp hi).1
    have hin : i ≤ n := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |1 / ((i + 1 : ℕ) : ℝ) - 1 / (i : ℝ)| * (A * i) :=
        mul_le_mul_of_nonneg_left (hF i (mem_Icc.mpr ⟨(mem_Ioc.mp hi).1.le, hin⟩))
          (abs_nonneg _)
      _ = A * (1 / ((i + 1 : ℕ) : ℝ)) := by
        rw [mul_left_comm, mrt_reciprocal_gap hi0]
      _ ≤ A * (1 / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply one_div_le_one_div_of_le hmR
        exact_mod_cast (show m ≤ i + 1 by have := (mem_Ioc.mp hi).1; omega)
      _ = _ := by ring
  have hsum : ‖∑ i ∈ Ioc m (n - 1),
      (((1 / (i + 1 : ℕ) : ℝ) : ℂ) - ((1 / (i : ℝ) : ℝ) : ℂ)) *
        (∑ j ∈ Icc 1 i, F j)‖ ≤ 3 * A := by
    calc
      _ ≤ ∑ i ∈ Ioc m (n - 1), A / (m : ℝ) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = ((Ioc m (n - 1)).card : ℝ) * (A / (m : ℝ)) := by simp
      _ ≤ (n : ℝ) * (A / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hA hmR.le)
        exact_mod_cast (show (Ioc m (n - 1)).card ≤ n by rw [Nat.card_Ioc]; omega)
      _ ≤ (3 * (m : ℝ)) * (A / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn3) (div_nonneg hA hmR.le)
      _ = _ := by field_simp
  rw [mrt_reciprocal_summation_by_parts F hmn']
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (A + A) + 3 * A :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add htop hbot)) hsum
    _ = 5 * A := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNearEnergy
namespace OAI

/-! Conversion of the centered prefix comparison into the actual dyadic
Fourier energy. The main term is integrated with its exact Cauchy kernel. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory

lemma halasz_dyadic_phase (F : ℕ → ℂ) (N : ℕ) (u : ℝ) :
    mrtDyadicPolynomial F N u =
      ∑ n ∈ Ioc N (2 * N), (F n * halaszPowerPhase u n) / (n : ℂ) := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  have he : Complex.exp (((-Real.log (n : ℝ)) * u : ℝ) * Complex.I) =
      halaszPowerPhase u n := by
    unfold halaszPowerPhase
    congr 2
    push_cast
    ring
  rw [he]
  ring

lemma halasz_phase_factor_sq (u : ℝ) :
    (‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹) ^ 2 = 1 / (1 + u ^ 2) := by
  rw [inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma halasz_near_dyadic_bound (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E u : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    ‖mrtDyadicPolynomial F N u‖ ≤
      5 * (‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹ * A + E) := by
  rw [halasz_dyadic_phase]
  apply mrt_weighted_prefix_bound (fun n => F n * halaszPowerPhase u n) hN
    (by omega) (by omega) (by positivity)
  intro k hk
  change ‖halaszPhaseMean F u k‖ ≤ _
  have hc := hcenter k hk
  have hn := hnear k hk
  let w := halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)
  have hw : ‖w‖ = ‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹ := by
    simp [w]
  calc
    _ = ‖(halaszPhaseMean F u k - w * halaszPhaseMean F 0 k) +
        w * halaszPhaseMean F 0 k‖ := by congr 1; ring
    _ ≤ ‖halaszPhaseMean F u k - w * halaszPhaseMean F 0 k‖ +
        ‖w * halaszPhaseMean F 0 k‖ := norm_add_le _ _
    _ ≤ E * k + ‖w‖ * (A * k) := add_le_add hn
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg w))
    _ = _ := by rw [hw]; ring

lemma halasz_near_dyadic_square (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E u : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    ‖mrtDyadicPolynomial F N u‖ ^ 2 ≤ 50 * (A ^ 2 / (1 + u ^ 2) + E ^ 2) := by
  have hb := halasz_near_dyadic_bound F hN A E u hA hE hcenter hnear
  have hs := pow_le_pow_left₀ (norm_nonneg (mrtDyadicPolynomial F N u)) hb 2
  let K := ‖(1 : ℂ) + (-u : ℂ) * Complex.I‖⁻¹
  have he : K ^ 2 = 1 / (1 + u ^ 2) := halasz_phase_factor_sq u
  have hsq : (K * A + E) ^ 2 ≤ 2 * (K ^ 2 * A ^ 2 + E ^ 2) := by
    nlinarith [sq_nonneg (K * A - E)]
  calc
    _ ≤ (5 * (K * A + E)) ^ 2 := hs
    _ ≤ 50 * (K ^ 2 * A ^ 2 + E ^ 2) := by nlinarith
    _ = _ := by rw [he]; ring

/-- Only the squared renormalization error pays for the length of the
near-center frequency interval. -/
theorem halasz_near_dyadic_energy (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (A E U : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hU : 0 ≤ U)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ u ∈ Set.Icc (-U) U, ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    (∫ u in -U..U, ‖mrtDyadicPolynomial F N u‖ ^ 2) ≤
      50 * Real.pi * A ^ 2 + 100 * U * E ^ 2 := by
  have hf : Continuous (fun u => ‖mrtDyadicPolynomial F N u‖ ^ 2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hg : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
    fun_prop (disch := intro u; nlinarith [sq_nonneg u])
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -U ≤ U)
    (hf.intervalIntegrable _ _)
    (((hg.mul_const (A ^ 2)).add (continuous_const : Continuous (fun _ : ℝ => E ^ 2))).const_mul 50
      |>.intervalIntegrable (-U) U)
    (fun u hu => ?_)
  · simp only [Pi.add_apply] at hh
    have hi : (∫ u in -U..U, 50 * ((1 / (1 + u ^ 2)) * A ^ 2 + E ^ 2)) =
        50 * ((Real.arctan U - Real.arctan (-U)) * A ^ 2 + (2 * U) * E ^ 2) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hg.mul_const (A ^ 2)).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_mul_const, integral_one_div_one_add_sq,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hi] at hh
    have ha := Real.arctan_lt_pi_div_two U
    rw [Real.arctan_neg] at hh
    have hm := mul_le_mul_of_nonneg_right (show 2 * Real.arctan U ≤ Real.pi by linarith) (sq_nonneg A)
    nlinarith
  · convert (preTransparency := .instances) halasz_near_dyadic_square F hN A E u hA hE hcenter (hnear u hu) using 1
    dsimp only [Pi.add_apply]
    ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearBound
namespace OAI

/-! Near-center energy from a bound on the literal typical prefix,
without an additive density comparison. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory

lemma halasz_typical_near_bound (B : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (C D L M : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hcenter : ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B 0 k‖ ≤ C*(Real.exp (-2*M/5)+L^(-1/4:ℝ))*k)
    (hnear : ∀ u ∈ Set.Icc (-(L^(1/16:ℝ))) (L^(1/16:ℝ)), ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k-
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*halaszPhaseMean B 0 k‖ ≤
          (D*L^(-3/50:ℝ))*k) :
    (∫ u in -(L^(1/16:ℝ))..(L^(1/16:ℝ)), ‖mrtDyadicPolynomial B N u‖^2) ≤
      (100*Real.pi*C^2+100*D^2)*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hh := halasz_near_dyadic_energy B hN
    (C*(Real.exp (-2*M/5)+L^(-1/4:ℝ))) (D*L^(-3/50:ℝ)) (L^(1/16:ℝ))
    (by positivity) (by positivity) (by positivity) hcenter hnear
  apply hh.trans
  have he : Real.exp (-2*M/5)^2=Real.exp (-4*M/5) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hp : (L^(-1/4:ℝ))^2 ≤ L^(-1/32:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have ha : (C*(Real.exp (-2*M/5)+L^(-1/4:ℝ)))^2 ≤
      2*C^2*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
    have hsum : (Real.exp (-2*M/5)+L^(-1/4:ℝ))^2 ≤
        2*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
      nlinarith [sq_nonneg (Real.exp (-2*M/5)-L^(-1/4:ℝ))]
    have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg C)
    nlinarith
  have hb : L^(1/16:ℝ)*(D*L^(-3/50:ℝ))^2 ≤ D^2*L^(-1/32:ℝ) := by
    have hpow : L^(1/16:ℝ)*(L^(-3/50:ℝ))^2=L^(-23/400:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hL0.le,←Real.rpow_add hL0]
      norm_num
    calc
      _ = D^2*(L^(1/16:ℝ)*(L^(-3/50:ℝ))^2) := by ring
      _ = D^2*L^(-23/400:ℝ) := by rw [hpow]
      _  ≤  _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (sq_nonneg D)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 50*Real.pi by positivity)
  have hb' := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 100 by norm_num)
  have hde := mul_nonneg (sq_nonneg D) (Real.exp_pos (-4*M/5)).le
  nlinarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_typical_near_bound := @OAI.TwoPointCorrelations.halasz_typical_near_bound
