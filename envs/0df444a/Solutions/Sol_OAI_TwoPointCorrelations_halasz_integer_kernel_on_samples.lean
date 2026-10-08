-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_integer_kernel_on_samples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:53:21.083655+00:00
-- url     : https://prove2.me/submissions/f5631add-65c7-48c3-97c3-723cb722845d

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_triangle_stationary_abs

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogOscillation
namespace OAI

/-! Calculus for the logarithmic phases in the sparse Dirichlet Gram
kernel. The linear frequency is kept real for the later Poisson sum. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory




lemma halasz_log_phase_norm (u v x : ℝ) : ‖halaszLogPhase u v x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma halasz_log_phase_deriv (u v x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (halaszLogPhase u v)
      (Complex.I*(halaszLogSlope u v x:ℂ)*halaszLogPhase u v x) x := by
  have hf := ((Real.hasDerivAt_log hx).const_mul u).sub ((hasDerivAt_id x).const_mul v)
  have hh := (hf.ofReal_comp.mul_const Complex.I).cexp
  convert (preTransparency := .instances) hh using 1
  · rfl
  · dsimp only [halaszLogPhase, halaszLogSlope, Pi.sub_apply, id_eq]
    simp only [mul_one]
    push_cast
    ring

lemma halasz_log_reciprocal_deriv (u v x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (fun y => (halaszLogSlope u v y)⁻¹)
      (halaszLogReciprocalDeriv u v x) x := by
  have hh := (((hasDerivAt_const x u).div (hasDerivAt_id x) hx).sub_const v).inv hd
  convert (preTransparency := .instances) hh using 1
  · rfl
  · change u / (x^2*(u/x-v)^2) = -((0*x-u*1)/x^2)/(u/x-v)^2
    simp only [halaszLogSlope] at hd
    field_simp [hx, hd]
    ring



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFirstDerivative
namespace OAI

/-! A first-derivative oscillatory-integral estimate for the logarithmic
phase, to be used on the nonstationary pieces of the Poisson kernel. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_log_phase_continuousOn (u v a b : ℝ) (ha : 0 < a) :
    ContinuousOn (halaszLogPhase u v) (Set.Icc a b) := by
  intro x hx
  exact (halasz_log_phase_deriv u v x (ha.trans_le hx.1).ne').continuousAt.continuousWithinAt



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleOscillation
namespace OAI

/-! Two integrations by parts for an affine-weighted logarithmic phase.
The exact boundary formula is used on the two sides of a triangular weight. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory




lemma halasz_log_amplitude0_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogAmplitude0 u v m c)
      (m/(halaszLogSlope u v x) +
        (m*x+c)*halaszLogReciprocalDeriv u v x) x := by
  have hh := (((hasDerivAt_id x).const_mul m).add_const c).mul
    (halasz_log_reciprocal_deriv u v x hx hd)
  convert (preTransparency := .instances) hh using 1
  · funext y
    simp only [halaszLogAmplitude0, div_eq_mul_inv, Pi.mul_apply, id_eq]
  · dsimp only [id_eq]
    ring

lemma halasz_log_amplitude2_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogAmplitude2 u v m c)
      (halaszLogAmplitude2Deriv u v m c x) x := by
  have hD : HasDerivAt (halaszLogSlope u v) (-u/x^2) x := by
    convert (preTransparency := .instances) ((hasDerivAt_const x u).div (hasDerivAt_id x) hx).sub_const v using 1
    · rfl
    · simp only [id_eq, zero_mul, mul_one, zero_sub, neg_div]
  have hw := ((hasDerivAt_id x).const_mul m).add_const c
  have h1 := (hasDerivAt_const x m).div (hD.pow 2) (pow_ne_zero 2 hd)
  have h2 := (hw.mul_const u).div
    (((hasDerivAt_id x).pow 2).mul (hD.pow 3))
    (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 3 hd))
  convert (preTransparency := .instances) h1.add h2 using 1
  · rfl
  · dsimp only [halaszLogAmplitude2Deriv, id_eq, Pi.pow_apply, Pi.mul_apply]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub]
    field_simp [hx, hd]
    ring


lemma halasz_log_double_primitive_deriv (u v m c x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (halaszLogDoublePrimitive u v m c)
      (((m*x+c:ℝ):ℂ)*halaszLogPhase u v x +
        (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x) x := by
  have hh := (halasz_log_phase_deriv u v x hx).mul
    ((halasz_log_amplitude2_deriv u v m c x hx hd).ofReal_comp.sub
      ((halasz_log_amplitude0_deriv u v m c x hx hd).ofReal_comp.const_mul Complex.I))
  convert (preTransparency := .instances) hh using 1
  · rfl
  · dsimp only [halaszLogAmplitude0, halaszLogAmplitude2, halaszLogReciprocalDeriv, Pi.sub_apply]
    push_cast
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
    have hd' : (halaszLogSlope u v x:ℂ) ≠ 0 := by exact_mod_cast hd
    field_simp [hx', hd']
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma halasz_log_amplitude2_deriv_continuousOn (u v m c a b : ℝ) (ha : 0 < a)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    ContinuousOn (halaszLogAmplitude2Deriv u v m c) (Set.Icc a b) := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  have hD : ContinuousOn (halaszLogSlope u v) (Set.Icc a b) :=
    (continuousOn_const.div continuousOn_id hx).sub continuousOn_const
  have hw : ContinuousOn (fun x : ℝ => m*x+c) (Set.Icc a b) :=
    (continuousOn_const.mul continuousOn_id).add continuousOn_const
  apply ContinuousOn.add
  · apply ContinuousOn.sub
    · exact continuousOn_const.div ((continuousOn_id.pow 2).mul (hD.pow 3))
        (fun x h => mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 3 (hd x h)))
    · exact ((continuousOn_const.mul hw).mul continuousOn_const).div
        ((continuousOn_id.pow 3).mul (hD.pow 3))
        (fun x h => mul_ne_zero (pow_ne_zero 3 (hx x h)) (pow_ne_zero 3 (hd x h)))
  · exact ((continuousOn_const.mul hw).mul continuousOn_const).div
      ((continuousOn_id.pow 4).mul (hD.pow 4))
      (fun x h => mul_ne_zero (pow_ne_zero 4 (hx x h)) (pow_ne_zero 4 (hd x h)))

theorem halasz_log_double_integral (u v m c a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) =
      halaszLogDoublePrimitive u v m c b - halaszLogDoublePrimitive u v m c a -
        ∫ x in a..b, (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x := by
  have hphase := halasz_log_phase_continuousOn u v a b ha
  have hwi : IntervalIntegrable (fun x => ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).add continuousOn_const)).mul hphase).intervalIntegrable_of_Icc hab
  have hdi : IntervalIntegrable (fun x => (halaszLogAmplitude2Deriv u v m c x:ℂ)*
      halaszLogPhase u v x) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn
      (halasz_log_amplitude2_deriv_continuousOn u v m c a b ha hd)).mul hphase).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_log_double_primitive_deriv u v m c x
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa only [Set.uIcc_of_le hab] using hx).1).ne'
      (hd x (by simpa only [Set.uIcc_of_le hab] using hx))) (hwi.add hdi)
  rw [intervalIntegral.integral_add hwi hdi] at he
  exact eq_sub_of_add_eq he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszOscillationBounds
namespace OAI

/-! Pointwise bounds for the exact twice-integrated affine amplitude. -/
namespace TwoPointCorrelations


lemma halasz_log_amplitude2_deriv_bound (u v m c x a lam W : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hlam : 0 < lam)
    (hs : lam ≤ |halaszLogSlope u v x|) (hw : |m*x+c| ≤ W) :
    |halaszLogAmplitude2Deriv u v m c x| ≤
      3*|m| *|u|/(a^2*lam^3) + 2*W*|u|/(a^3*lam^3) +
        3*W*u^2/(a^4*lam^4) := by
  have hx : 0 ≤ x := (ha.trans_le hax).le
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  unfold halaszLogAmplitude2Deriv
  calc
    _ ≤ |3*m*u/(x^2*(halaszLogSlope u v x)^3)| +
        |2*(m*x+c)*u/(x^3*(halaszLogSlope u v x)^3)| +
        |3*(m*x+c)*u^2/(x^4*(halaszLogSlope u v x)^4)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 3*|m| *|u|/(x^2*|halaszLogSlope u v x|^3) +
        2*|m*x+c| *|u|/(x^3*|halaszLogSlope u v x|^3) +
        3*|m*x+c| *u^2/(x^4*|halaszLogSlope u v x|^4) := by
      simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hx,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), sq_abs]
    _ ≤ _ := by
      gcongr

open _root_.MeasureTheory

lemma halasz_log_remainder_integral (u v m c A a b lam W : ℝ)
    (hA : 0 < A) (hAa : A ≤ a) (hab : a ≤ b) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc a b, lam ≤ |halaszLogSlope u v x|)
    (hw : ∀ x ∈ Set.Icc a b, |m*x+c| ≤ W) :
    ‖∫ x in a..b, (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x‖ ≤
      (3*|m| *|u|/(A^2*lam^3) + 2*W*|u|/(A^3*lam^3) +
        3*W*u^2/(A^4*lam^4))*(b-a) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (C := 3*|m| *|u|/(A^2*lam^3) + 2*W*|u|/(A^3*lam^3) + 3*W*u^2/(A^4*lam^4))
    (f := fun x => (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x) (by
      intro x hx
      have hx' : x ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact halasz_log_amplitude2_deriv_bound u v m c x A lam W hA
        (hAa.trans hx'.1) hlam (hs x hx') (hw x hx'))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleIntegral
namespace OAI

/-! The compact triangular majorant used for a dyadic Dirichlet kernel. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory



lemma halasz_triangle_boundary (N u v : ℝ) (hN : 0 < N) :
    halaszLogDoublePrimitive u v (2/N) (-1) (3*N/2) -
      halaszLogDoublePrimitive u v (2/N) (-1) (N/2) +
      halaszLogDoublePrimitive u v (-(2/N)) 5 (5*N/2) -
      halaszLogDoublePrimitive u v (-(2/N)) 5 (3*N/2) =
    ((2/N:ℝ):ℂ) *
      (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
        halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
        halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2) := by
  have hLa : 2/N*(N/2)+(-1) = 0 := by field_simp [hN.ne']; ring
  have hLb : 2/N*(3*N/2)+(-1) = 2 := by field_simp [hN.ne']; ring
  have hRb : -(2/N)*(3*N/2)+5 = 2 := by field_simp [hN.ne']; ring
  have hRc : -(2/N)*(5*N/2)+5 = 0 := by field_simp [hN.ne']; ring
  unfold halaszLogDoublePrimitive halaszLogAmplitude0 halaszLogAmplitude2
  rw [hLa, hLb, hRb, hRc]
  push_cast
  ring

theorem halasz_triangle_double_integral (N u v : ℝ) (hN : 0 < N)
    (hd : ∀ x ∈ Set.Icc (N/2) (5*N/2), halaszLogSlope u v x ≠ 0) :
    halaszTriangleIntegral N u v =
      ((2/N:ℝ):ℂ) *
        (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
          halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
          halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2) -
      ((∫ x in N/2..3*N/2, (halaszLogAmplitude2Deriv u v (2/N) (-1) x:ℂ)*
        halaszLogPhase u v x) +
       ∫ x in 3*N/2..5*N/2, (halaszLogAmplitude2Deriv u v (-(2/N)) 5 x:ℂ)*
        halaszLogPhase u v x) := by
  have h1 := halasz_log_double_integral u v (2/N) (-1) (N/2) (3*N/2)
    (by positivity) (by linarith) (fun x hx => hd x ⟨hx.1, by linarith [hx.2]⟩)
  have h2 := halasz_log_double_integral u v (-(2/N)) 5 (3*N/2) (5*N/2)
    (by positivity) (by linarith) (fun x hx => hd x ⟨by linarith [hx.1], hx.2⟩)
  have he := halasz_triangle_boundary N u v hN
  dsimp only [halaszTriangleIntegral]
  simp only [sub_eq_add_neg] at h1 h2 he ⊢
  rw [h1, h2]
  linear_combination he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleTail
namespace OAI

/-! Summable nonstationary tails of the smoothed logarithmic kernel. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_triangle_boundary_bound (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖((2/N:ℝ):ℂ) *
      (2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 -
        halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2 -
        halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2)‖ ≤
      8/(N*lam^2) := by
  have hp (x : ℝ) (hx : x ∈ Set.Icc (N/2) (5*N/2)) :
      ‖halaszLogPhase u v x/(halaszLogSlope u v x:ℂ)^2‖ ≤ 1/lam^2 := by
    simp only [norm_div, norm_pow, halasz_log_phase_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hs x hx
  have hpa := hp (N/2) ⟨le_rfl, by linarith⟩
  have hpb := hp (3*N/2) ⟨by linarith, by linarith⟩
  have hpc := hp (5*N/2) ⟨by linarith, le_rfl⟩
  have he : 2*halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2 =
      2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2) := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hN), he]
  have hb := norm_sub_le
    (2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2) -
      halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2)
    (halaszLogPhase u v (5*N/2)/(halaszLogSlope u v (5*N/2):ℂ)^2)
  have hb' := norm_sub_le
    (2*(halaszLogPhase u v (3*N/2)/(halaszLogSlope u v (3*N/2):ℂ)^2))
    (halaszLogPhase u v (N/2)/(halaszLogSlope u v (N/2):ℂ)^2)
  rw [norm_mul] at hb'
  have htwo : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [htwo] at hb'
  calc
    _ ≤ (2/N)*(4/lam^2) := by
      gcongr
      simp only [div_eq_mul_inv] at hb hb' hpa hpb hpc ⊢
      linarith
    _ = _ := by ring

lemma halasz_triangle_remainder_bound (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖(∫ x in N/2..3*N/2, (halaszLogAmplitude2Deriv u v (2/N) (-1) x:ℂ)*
        halaszLogPhase u v x) +
       ∫ x in 3*N/2..5*N/2, (halaszLogAmplitude2Deriv u v (-(2/N)) 5 x:ℂ)*
        halaszLogPhase u v x‖ ≤
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
  have h1 := halasz_log_remainder_integral u v (2/N) (-1) (N/2) (N/2) (3*N/2) lam 2
    (by positivity) le_rfl (by linarith) hlam
    (fun x hx => hs x ⟨hx.1, by linarith [hx.2]⟩) (by
      intro x hx
      apply abs_le.mpr
      have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have h2 := halasz_log_remainder_integral u v (-(2/N)) 5 (N/2) (3*N/2) (5*N/2) lam 2
    (by positivity) (by linarith) (by linarith) hlam
    (fun x hx => hs x ⟨by linarith [hx.1], hx.2⟩) (by
      intro x hx
      apply abs_le.mpr
      have he : (-(2/N)*x)*N = -2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have hpos : 0 < 2/N := by positivity
  rw [abs_of_pos hpos] at h1
  rw [abs_neg, abs_of_pos hpos] at h2
  have he :
      (3*(2/N)*|u| /((N/2)^2*lam^3) + 2*2*|u| /((N/2)^3*lam^3) +
        3*2*u^2/((N/2)^4*lam^4))*(3*N/2-N/2) +
      (3*(2/N)*|u| /((N/2)^2*lam^3) + 2*2*|u| /((N/2)^3*lam^3) +
        3*2*u^2/((N/2)^4*lam^4))*(5*N/2-3*N/2) =
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
    field_simp
    ring
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq he)

theorem halasz_triangle_nonstationary (N u v lam : ℝ) (hN : 0 < N) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc (N/2) (5*N/2), lam ≤ |halaszLogSlope u v x|) :
    ‖halaszTriangleIntegral N u v‖ ≤ 8/(N*lam^2) +
      112*|u| /(N^2*lam^3) + 192*u^2/(N^3*lam^4) := by
  rw [halasz_triangle_double_integral N u v hN (by
    intro x hx
    exact abs_pos.mp (hlam.trans_le (hs x hx)))]
  exact (norm_sub_le _ _).trans (by
    have h1 := halasz_triangle_boundary_bound N u v lam hN hlam hs
    have h2 := halasz_triangle_remainder_bound N u v lam hN hlam hs
    linarith)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleFar
namespace OAI

/-! The part of the Fourier kernel whose linear frequency stays away
from the logarithmic derivative. -/
namespace TwoPointCorrelations

lemma halasz_log_far_slope (N u v x : ℝ) (hN : 0 < N) (hx : N/2 ≤ x)
    (hfar : 4*|u| ≤ N*|v|) : |v|/2 ≤ |halaszLogSlope u v x| := by
  have hxp : 0 < x := (half_pos hN).trans_le hx
  have hu : |u/x| ≤ 2*|u|/N := by
    rw [abs_div, abs_of_pos hxp]
    calc
      _ ≤ |u|/(N/2) := div_le_div_of_nonneg_left (abs_nonneg u) (half_pos hN) hx
      _ = _ := by ring
  have hv : 2*|u|/N ≤ |v|/2 := (div_le_iff₀ hN).mpr (by nlinarith)
  have hh := abs_add_le (v-u/x) (u/x)
  rw [sub_add_cancel, abs_sub_comm v (u/x)] at hh
  unfold halaszLogSlope
  linarith

theorem halasz_triangle_far (N u v : ℝ) (hN : 0 < N) (hv : v ≠ 0)
    (hfar : 4*|u| ≤ N*|v|) :
    ‖halaszTriangleIntegral N u v‖ ≤ 512/(N*v^2) := by
  have hvp : 0 < |v| := abs_pos.mpr hv
  apply (halasz_triangle_nonstationary N u v (|v|/2) hN (half_pos hvp)
    (fun x hx => halasz_log_far_slope N u v x hN hx.1 hfar)).trans
  have hs : (4*|u|)^2 ≤ (N*|v|)^2 :=
    pow_le_pow_left₀ (by positivity) hfar 2
  have hm := mul_le_mul_of_nonneg_right hfar (mul_nonneg hN.le (abs_nonneg v))
  rw [← sq_abs v, ← sq_abs u]
  field_simp
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleZero
namespace OAI

/-! The zero Fourier mode has quadratic logarithmic-frequency decay. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_triangle_trivial (N u v : ℝ) (hN : 0 < N) :
    ‖halaszTriangleIntegral N u v‖ ≤ 4*N := by
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := N/2) (b := 3*N/2) (C := (2:ℝ))
    (f := fun x => ((2/N*x-1:ℝ):ℂ)*halaszLogPhase u v x) (by
      intro x hx
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [Set.uIoc_of_le (by linarith : N/2 ≤ 3*N/2)] at hx
      apply abs_le.mpr
      have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 3*N/2) (b := 5*N/2) (C := (2:ℝ))
    (f := fun x => ((-(2/N)*x+5:ℝ):ℂ)*halaszLogPhase u v x) (by
      intro x hx
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [Set.uIoc_of_le (by linarith : 3*N/2 ≤ 5*N/2)] at hx
      apply abs_le.mpr
      have he : (-(2/N)*x)*N = -2*x := by field_simp [hN.ne']
      constructor <;> nlinarith [hx.1,hx.2])
  rw [abs_of_nonneg (by linarith : 0 ≤ 3*N/2-N/2)] at h1
  rw [abs_of_nonneg (by linarith : 0 ≤ 5*N/2-3*N/2)] at h2
  exact (norm_add_le _ _).trans (by linarith)

lemma halasz_triangle_zero_decay (N u : ℝ) (hN : 0 < N) (hu : u ≠ 0) :
    ‖halaszTriangleIntegral N u 0‖ ≤ 9300*N/u^2 := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hlam : 0 < 2*|u|/(5*N) := by positivity
  apply (halasz_triangle_nonstationary N u 0 (2*|u|/(5*N)) hN hlam (by
    intro x hx
    have hxp : 0 < x := (half_pos hN).trans_le hx.1
    simp only [halaszLogSlope, sub_zero, abs_div, abs_of_pos hxp]
    calc
      _ = |u|/(5*N/2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg u) hxp hx.2)).trans_eq
  rw [← sq_abs u]
  field_simp [hN.ne', hu0.ne']
  ring

theorem halasz_triangle_zero (N u : ℝ) (hN : 0 < N) :
    ‖halaszTriangleIntegral N u 0‖ ≤ 18600*N/(1+u^2) := by
  by_cases hsmall : u^2 ≤ 1
  · apply (halasz_triangle_trivial N u 0 hN).trans
    apply (le_div_iff₀ (by positivity : 0 < 1+u^2)).mpr
    nlinarith [sq_nonneg u]
  · have hu : u ≠ 0 := by intro hu; subst u; norm_num at hsmall
    apply (halasz_triangle_zero_decay N u hN hu).trans
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hu) (by positivity : 0 < 1+u^2)).mpr
    nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleWeight
namespace OAI

/-! A continuous compactly supported majorant of a dyadic interval.
The adjoining affine pieces have exactly the integrals already estimated. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory




lemma halasz_triangle_weight_left_zero (N x : ℝ) (hN : 0 < N) (hx : x ≤ N/2) :
    halaszTriangleWeight N x = 0 := by
  unfold halaszTriangleWeight
  apply max_eq_left
  apply (min_le_left _ _).trans
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  nlinarith

lemma halasz_triangle_weight_right_zero (N x : ℝ) (hN : 0 < N) (hx : 5*N/2 ≤ x) :
    halaszTriangleWeight N x = 0 := by
  unfold halaszTriangleWeight
  apply max_eq_left
  apply (min_le_right _ _).trans
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  nlinarith

lemma halasz_triangle_weight_left (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc (N/2) (3*N/2)) : halaszTriangleWeight N x = 2/N*x-1 := by
  unfold halaszTriangleWeight
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  rw [min_eq_left (by nlinarith [hx.2]), max_eq_right (by nlinarith [hx.1])]

lemma halasz_triangle_weight_right (N x : ℝ) (hN : 0 < N)
    (hx : x ∈ Set.Icc (3*N/2) (5*N/2)) : halaszTriangleWeight N x = -(2/N)*x+5 := by
  unfold halaszTriangleWeight
  have he : (2/N*x)*N = 2*x := by field_simp [hN.ne']
  rw [min_eq_right (by nlinarith [hx.1]), max_eq_right (by nlinarith [hx.2])]
  ring



lemma halasz_triangle_function_zero (N u v x : ℝ) (hN : 0 < N)
    (hx : x ∉ Set.Icc (N/2) (5*N/2)) : halaszTriangleFunction N u v x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · simp only [not_le] at hx
    simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx.le,
      Complex.ofReal_zero, zero_mul]
  · simp only [not_le] at hx
    simp only [halaszTriangleFunction, halasz_triangle_weight_right_zero N x hN hx.le,
      Complex.ofReal_zero, zero_mul]

lemma halasz_triangle_function_continuous (N u v : ℝ) (hN : 0 < N) :
    Continuous (halaszTriangleFunction N u v) := by
  have hw : Continuous (halaszTriangleWeight N) := by unfold halaszTriangleWeight; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : halaszTriangleFunction N u v =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds (half_pos hN)] with x hx
      simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx.le,
        Complex.ofReal_zero, zero_mul]
    exact he.continuousAt
  · exact (Complex.continuous_ofReal.comp hw).continuousAt.mul
      (halasz_log_phase_deriv u v x hx).continuousAt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleFourier
namespace OAI

/-! Identification of the compact triangular Fourier transform with the
oscillatory integrals estimated above. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory
open scoped _root_.FourierTransform

lemma halasz_triangle_integral_function (N u v : ℝ) (hN : 0 < N) :
    (∫ x, halaszTriangleFunction N u v x) = halaszTriangleIntegral N u v := by
  have hz (x : ℝ) (hx : x ∉ Set.Ioc (N/2) (5*N/2)) :
      halaszTriangleFunction N u v x = 0 := by
    rw [Set.mem_Ioc, not_and_or] at hx
    rcases hx with hx | hx
    · simp only [not_lt] at hx
      simp only [halaszTriangleFunction, halasz_triangle_weight_left_zero N x hN hx,
        Complex.ofReal_zero, zero_mul]
    · apply halasz_triangle_function_zero N u v x hN
      intro hx'
      exact hx hx'.2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← intervalIntegral.integral_of_le (by linarith : N/2 ≤ 5*N/2)]
  have hc := halasz_triangle_function_continuous N u v hN
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (N/2) (3*N/2)) (hc.intervalIntegrable (3*N/2) (5*N/2))]
  unfold halaszTriangleIntegral
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : N/2 ≤ 3*N/2)] at hx
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_left N x hN hx]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : 3*N/2 ≤ 5*N/2)] at hx
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_right N x hN hx]

lemma halasz_log_phase_fourier (u ξ x : ℝ) :
    Complex.exp (((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I)*halaszLogPhase u 0 x =
      halaszLogPhase u (2*Real.pi*ξ) x := by
  unfold halaszLogPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem halasz_triangle_fourier (N u ξ : ℝ) (hN : 0 < N) :
    𝓕 (halaszTriangleFunction N u 0) ξ =
      halaszTriangleIntegral N u (2*Real.pi*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) :
      Complex.exp (((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I) • halaszTriangleFunction N u 0 x =
        halaszTriangleFunction N u (2*Real.pi*ξ) x := by
    rw [smul_eq_mul]
    unfold halaszTriangleFunction
    rw [← mul_assoc, mul_comm _ (halaszTriangleWeight N x:ℂ), mul_assoc,
      halasz_log_phase_fourier]
  simp_rw [he]
  exact halasz_triangle_integral_function N u (2*Real.pi*ξ) hN

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTrianglePoisson
namespace OAI

/-! Poisson summation for the compact triangular logarithmic weight. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Filter _root_.Asymptotics
open scoped _root_.FourierTransform

lemma halasz_triangle_decay (N u : ℝ) (hN : 0 < N) :
    (halaszTriangleFunction N u 0) =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [(isCompact_Icc : IsCompact (Set.Icc (N/2) (5*N/2))).compl_mem_cocompact] with x hx
  rw [halasz_triangle_function_zero N u 0 x hN hx, norm_zero]
  positivity

lemma halasz_triangle_fourier_decay (N u : ℝ) (hN : 0 < N) :
    (𝓕 (halaszTriangleFunction N u 0)) =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
  let R := max 1 (2*|u|/(Real.pi*N))
  apply IsBigO.of_bound (512/(N*(2*Real.pi)^2))
  filter_upwards [(isCompact_Icc : IsCompact (Set.Icc (-R) R)).compl_mem_cocompact] with ξ hx
  have hξ : R < |ξ| := by
    by_contra hn
    apply hx
    exact abs_le.mp (le_of_not_gt hn)
  have hξ0 : ξ ≠ 0 := by
    have h1 : 1 < |ξ| := (le_max_left _ _).trans_lt hξ
    exact abs_pos.mp (lt_trans zero_lt_one h1)
  have hpos : 0 < Real.pi*N := mul_pos Real.pi_pos hN
  have hlow : 2*|u| ≤ |ξ| *(Real.pi*N) :=
    (div_le_iff₀ hpos).mp ((le_max_right _ _).trans hξ.le)
  have hfar : 4*|u| ≤ N*|2*Real.pi*ξ| := by
    rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith
  have hfreq : 2*Real.pi*ξ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ0
  rw [halasz_triangle_fourier N u ξ hN]
  apply (halasz_triangle_far N u (2*Real.pi*ξ) hN hfreq hfar).trans_eq
  have hg : ‖|ξ|^(-2:ℝ)‖ = 1/ξ^2 := by
    rw [Real.rpow_neg (abs_nonneg ξ) 2, Real.rpow_two, norm_inv, Real.norm_eq_abs,
      abs_pow, abs_abs, sq_abs]
    rw [one_div]
  rw [hg]
  ring

theorem halasz_triangle_poisson (N u : ℝ) (hN : 0 < N) :
    (∑' n : ℤ, halaszTriangleFunction N u 0 n) =
      ∑' k : ℤ, halaszTriangleIntegral N u (2*Real.pi*k) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay
    (halasz_triangle_function_continuous N u 0 hN) (by norm_num : (1:ℝ)<2)
    (halasz_triangle_decay N u hN) (halasz_triangle_fourier_decay N u hN) 0
  simpa only [zero_add, fourier_coe_apply, mul_zero, neg_zero, Complex.ofReal_zero,
    zero_mul, zero_div, Complex.exp_zero, mul_one, halasz_triangle_fourier N u _ hN] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPoissonModes
namespace OAI

/-! Counting the nonzero integer Fourier modes near a stationary point. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_mem_near_modes (R : ℝ) (k : ℤ) :
    k ∈ halaszNearModes R ↔ k ≠ 0 ∧ |(k:ℝ)| ≤ R := by
  unfold halaszNearModes
  simp only [mem_erase, mem_Icc]
  constructor
  · rintro ⟨hk,hlo,hhi⟩
    refine ⟨hk,abs_le.mpr ⟨?_,Int.le_floor.mp hhi⟩⟩
    have hh : -k ≤ ⌊R⌋ := by omega
    have hr := Int.le_floor.mp hh
    push_cast at hr
    linarith
  · rintro ⟨hk,hr⟩
    have hh := abs_le.mp hr
    refine ⟨hk,?_,Int.le_floor.mpr hh.2⟩
    have hneg : ((-k:ℤ):ℝ) ≤ R := by push_cast; linarith [hh.1]
    have hi := Int.le_floor.mpr hneg
    omega

lemma halasz_near_modes_card (R : ℝ) (hR : 0 ≤ R) :
    ((halaszNearModes R).card:ℝ) ≤ 2*R := by
  have hm : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  have hz : (0:ℤ) ∈ Icc (-⌊R⌋) ⌊R⌋ := mem_Icc.mpr ⟨by omega,hm⟩
  have he := card_erase_add_one hz
  have hc := Int.card_Icc_of_le (a := -⌊R⌋) (b := ⌊R⌋) (by omega)
  have heR : ((halaszNearModes R).card:ℝ)+1 = ((Icc (-⌊R⌋) ⌊R⌋).card:ℝ) := by
    exact_mod_cast he
  have hcR : ((Icc (-⌊R⌋) ⌊R⌋).card:ℝ) = 2*(⌊R⌋:ℝ)+1 := by
    have hc' : ((Icc (-⌊R⌋) ⌊R⌋).card:ℤ) = 2*⌊R⌋+1 := by omega
    exact_mod_cast hc'
  have hf := Int.floor_le R
  linarith

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



theorem halasz_triangle_poisson_bound (N u : ℝ) (hN : 0 < N) :
    ‖∑' n : ℤ, halaszTriangleFunction N u 0 n‖ ≤
      18600*N/(1+u^2) + (440/Real.pi)*Real.sqrt |u| +
        (512/(N*(2*Real.pi)^2))*halaszIntegerSquareMass := by
  let R := 2*|u|/(Real.pi*N)
  let S := halaszNearModes R
  let Z := 18600*N/(1+u^2)
  let B := 110*N/Real.sqrt |u|
  let C := 512/(N*(2*Real.pi)^2)
  let a : ℤ → ℝ := fun k => if k=0 then Z else 0
  let b : ℤ → ℝ := fun k => if k ∈ S then B else 0
  let c : ℤ → ℝ := fun k => C*(1/(k:ℝ)^2)
  have ha : Summable a := summable_of_ne_finset_zero (s := {0}) (by
    intro k hk
    dsimp [a]
    simp only [mem_singleton] at hk
    exact if_neg hk)
  have hb : Summable b := summable_of_ne_finset_zero (s := S) (by
    intro k hk
    exact if_neg hk)
  have hc : Summable c :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1<2)).mul_left C
  have hterm (k : ℤ) : ‖halaszTriangleIntegral N u (2*Real.pi*k)‖ ≤ a k+b k+c k := by
    by_cases hk : k=0
    · subst k
      simpa [a,b,c,Z,S,halasz_mem_near_modes] using halasz_triangle_zero N u hN
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    have hp : 0 < |(k:ℝ)| := abs_pos.mpr hkR
    have hv : 2*Real.pi*(k:ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hkR
    by_cases hs : k ∈ S
    · have hks := (halasz_mem_near_modes R k).mp hs
      have hu : u ≠ 0 := by
        intro hu
        subst u
        have hR : R=0 := by simp [R]
        rw [hR] at hks
        linarith [hks.2]
      have h := halasz_triangle_stationary_abs N u (2*Real.pi*k) hN hu
      have hcn : 0 ≤ c k := by dsimp [c,C]; positivity
      simpa only [a,b,if_neg hk,if_pos hs,zero_add] using h.trans (le_add_of_nonneg_right hcn)
    · have hout : R < |(k:ℝ)| := by
        by_contra hn
        exact hs ((halasz_mem_near_modes R k).mpr ⟨hk,le_of_not_gt hn⟩)
      have hfar : 4*|u| ≤ N*|2*Real.pi*(k:ℝ)| := by
        have hpN : 0 < Real.pi*N := mul_pos Real.pi_pos hN
        have hh := (div_lt_iff₀ hpN).mp hout
        rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
        nlinarith
      have h := halasz_triangle_far N u (2*Real.pi*k) hN hv hfar
      have he : 512/(N*(2*Real.pi*(k:ℝ))^2) = c k := by dsimp [c,C]; ring
      simpa only [a,b,if_neg hk,if_neg hs,zero_add] using h.trans_eq he
  have hnorm : Summable (fun k : ℤ => ‖halaszTriangleIntegral N u (2*Real.pi*k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm ((ha.add hb).add hc)
  have hZA : (∑' k : ℤ, a k) = Z := by
    rw [tsum_eq_sum (s := {0}) (fun k hk => by
      dsimp [a]
      simp only [mem_singleton] at hk
      exact if_neg hk)]
    simp [a]
  have hSB : (∑' k : ℤ, b k) = (S.card:ℝ)*B := by
    rw [tsum_eq_sum (s := S) (fun k hk => if_neg hk)]
    simp
  have hTC : (∑' k : ℤ, c k) = C*halaszIntegerSquareMass := by
    exact tsum_mul_left
  have hcard : (S.card:ℝ) ≤ 2*R :=
    halasz_near_modes_card R (by dsimp [R]; positivity)
  have hmode : (2*R)*B = (440/Real.pi)*Real.sqrt |u| := by
    by_cases hu : u=0
    · subst u
      simp [R,B]
    have hsu : 0 < Real.sqrt |u| := Real.sqrt_pos.mpr (abs_pos.mpr hu)
    have he := Real.sq_sqrt (abs_nonneg u)
    dsimp [R,B]
    field_simp
    nlinarith
  rw [halasz_triangle_poisson N u hN]
  calc
    _ ≤ ∑' k : ℤ, ‖halaszTriangleIntegral N u (2*Real.pi*k)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℤ, (a k+b k+c k) := hnorm.tsum_le_tsum hterm ((ha.add hb).add hc)
    _ = Z+(S.card:ℝ)*B+C*halaszIntegerSquareMass := by
      rw [(ha.add hb).tsum_add hc,ha.tsum_add hb,hZA,hSB,hTC]
    _ ≤ Z+(2*R)*B+C*halaszIntegerSquareMass := by gcongr
    _ = _ := by rw [hmode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszIntegerKernel
namespace OAI

/-! The actual finite weighted integer kernel used by sparse cofactor energy. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_triangle_nat_zero (N u : ℝ) (hN : 0 < N) (n : ℕ)
    (hn : n ∉ halaszTriangleSupport N) :
    halaszTriangleFunction N u 0 n = 0 := by
    have hnat : ⌈5*N/2⌉₊ < n := by simpa [halaszTriangleSupport] using hn
    have hreal : (⌈5*N/2⌉₊:ℝ) < n := by exact_mod_cast hnat
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_right_zero N n hN ((Nat.le_ceil _).trans hreal.le),
      Complex.ofReal_zero,zero_mul]
lemma halasz_triangle_neg_zero (N u : ℝ) (hN : 0 < N) (n : ℕ) :
    halaszTriangleFunction N u 0 (-(n+1:ℝ)) = 0 := by
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_left_zero N _ hN (by
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith),Complex.ofReal_zero,zero_mul]

lemma halasz_triangle_finite_sum (N u : ℝ) (hN : 0 < N) :
    (∑' n : ℤ, halaszTriangleFunction N u 0 n) =
      ∑ n ∈ halaszTriangleSupport N, halaszTriangleFunction N u 0 n := by
  have hn := halasz_triangle_nat_zero N u hN
  have hs : Summable (fun n : ℕ => halaszTriangleFunction N u 0 n) :=
    summable_of_ne_finset_zero hn
  have hneg : (fun n : ℕ => halaszTriangleFunction N u 0 (-(n+1:ℝ))) = 0 := by
    funext n
    exact halasz_triangle_neg_zero N u hN n
  have hsn : Summable (fun n : ℕ => halaszTriangleFunction N u 0 (-(n+1:ℝ))) := by
    rw [hneg]
    exact summable_zero
  have he := tsum_of_nat_of_neg_add_one (f := fun n : ℤ =>
    halaszTriangleFunction N u 0 n) (by simpa only [Int.cast_natCast] using hs)
    (by simpa only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one] using hsn)
  simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one] at he
  rw [hneg] at he
  simp only [Pi.zero_def,tsum_zero,add_zero] at he
  exact he.trans (tsum_eq_sum hn)

lemma halasz_triangle_polynomial (N t : ℝ) (hN : 0 < N) :
    mrtExponentialPolynomial (halaszTriangleSupport N)
      (fun n => (halaszTriangleWeight N n:ℂ)) (fun n => -Real.log n) t =
      ∑' n : ℤ, halaszTriangleFunction N (-t) 0 n := by
  rw [halasz_triangle_finite_sum N (-t) hN]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold halaszTriangleFunction halaszLogPhase
  congr 2
  push_cast
  ring

theorem halasz_integer_kernel (N t : ℝ) (hN : 0 < N) :
    ‖mrtExponentialPolynomial (halaszTriangleSupport N)
      (fun n => (halaszTriangleWeight N n:ℂ)) (fun n => -Real.log n) t‖ ≤
      18600*N/(1+t^2) + (440/Real.pi)*Real.sqrt |t| +
        (512/(N*(2*Real.pi)^2))*halaszIntegerSquareMass := by
  rw [halasz_triangle_polynomial N t hN]
  simpa only [neg_sq,abs_neg] using halasz_triangle_poisson_bound N (-t) hN

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCofactor
namespace OAI

/-! The proved integer kernel attached to actual reciprocal-count cofactors. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma halasz_integer_kernel_on_samples (M T : ℝ) (hM : 0 < M) (_hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T) :
    ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial (halaszTriangleSupport M)
        (fun n => (halaszTriangleWeight M n:ℂ)) (fun n => -Real.log n) (t-s)‖ ≤
      (18600*M)/(1+(t-s)^2)+halaszSparseKernelError M T := by
  intro t ht s hs
  apply (halasz_integer_kernel M (t-s) hM).trans
  have hts : |t-s| ≤ 2*T := by
    have hh := abs_sub t s
    linarith [hS t ht,hS s hs]
  have hroot := Real.sqrt_le_sqrt hts
  dsimp [halaszSparseKernelError]
  rw [← add_assoc]
  gcongr


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_integer_kernel_on_samples := @OAI.TwoPointCorrelations.halasz_integer_kernel_on_samples
