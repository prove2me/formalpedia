-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_triangle_stationary_abs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:36:35.407699+00:00
-- url     : https://prove2.me/submissions/395a5131-6e87-4485-9896-8088fbdb8782

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

lemma halasz_log_phase_primitive_deriv (u v x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (fun y => -Complex.I * halaszLogPhase u v y *
      ((halaszLogSlope u v y)⁻¹:ℝ))
      (halaszLogPhase u v x - Complex.I * halaszLogPhase u v x *
        (halaszLogReciprocalDeriv u v x:ℂ)) x := by
  have hh := ((halasz_log_phase_deriv u v x hx).const_mul (-Complex.I)).mul
    (halasz_log_reciprocal_deriv u v x hx hd).ofReal_comp
  convert (preTransparency := .instances) hh using 1
  push_cast
  have hd' : (halaszLogSlope u v x:ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp [hd']
  linear_combination (halaszLogPhase u v x) * Complex.I_sq

lemma halasz_log_reciprocal_integral (u v a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    (∫ x in a..b, halaszLogReciprocalDeriv u v x) =
      (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  have hc : ContinuousOn (halaszLogReciprocalDeriv u v) (Set.Icc a b) := by
    apply continuousOn_const.div
      ((continuousOn_id.pow 2).mul (((continuousOn_const.div continuousOn_id hx).sub
        continuousOn_const).pow 2))
    intro x h
    exact mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 2 (hd x h))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x h => halasz_log_reciprocal_deriv u v x
      (hx x (by simpa only [Set.uIcc_of_le hab] using h))
      (hd x (by simpa only [Set.uIcc_of_le hab] using h)))
    (hc.intervalIntegrable_of_Icc hab)

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

lemma halasz_log_reciprocal_deriv_continuousOn (u v a b : ℝ) (ha : 0 < a)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    ContinuousOn (halaszLogReciprocalDeriv u v) (Set.Icc a b) := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  apply continuousOn_const.div
    ((continuousOn_id.pow 2).mul (((continuousOn_const.div continuousOn_id hx).sub
      continuousOn_const).pow 2))
  intro x h
  exact mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 2 (hd x h))

theorem halasz_log_first_derivative (u v a b lam : ℝ) (hu : 0 ≤ u)
    (ha : 0 < a) (hab : a ≤ b) (hlam : 0 < lam)
    (hslope : ∀ x ∈ Set.Icc a b, lam ≤ |halaszLogSlope u v x|) :
    ‖∫ x in a..b, halaszLogPhase u v x‖ ≤ 4/lam := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : halaszLogSlope u v x ≠ 0 := by
    have hh := hslope x hx
    exact abs_pos.mp (hlam.trans_le hh)
  have hiF : IntervalIntegrable (halaszLogPhase u v) volume a b := (halasz_log_phase_continuousOn u v a b ha).intervalIntegrable_of_Icc hab
  let K : ℝ → ℂ := fun x => Complex.I*halaszLogPhase u v x*
    (halaszLogReciprocalDeriv u v x:ℂ)
  have hiK : IntervalIntegrable K volume a b :=
    ((continuousOn_const.mul (halasz_log_phase_continuousOn u v a b ha)).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (halasz_log_reciprocal_deriv_continuousOn u v a b ha hd))).intervalIntegrable_of_Icc hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_log_phase_primitive_deriv u v x
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa only [Set.uIcc_of_le hab] using hx).1).ne'
      (hd x (by simpa only [Set.uIcc_of_le hab] using hx))) (hiF.sub hiK)
  have hKn (x : ℝ) : ‖K x‖ = halaszLogReciprocalDeriv u v x := by
    simp only [K, norm_mul, Complex.norm_I, one_mul, halasz_log_phase_norm,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by unfold halaszLogReciprocalDeriv; positivity)
  have hKI : ‖∫ x in a..b, K x‖ ≤
      (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := K) hab
    simp_rw [hKn] at hh
    rwa [halasz_log_reciprocal_integral u v a b ha hab hd] at hh
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |(halaszLogSlope u v x)⁻¹| ≤ 1/lam := by
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hlam (hslope x hx)
  have hBa := hbound a ⟨le_rfl, hab⟩
  have hBb := hbound b ⟨hab, le_rfl⟩
  have hR : (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ ≤ 2/lam := by
    have haa := le_abs_self (-(halaszLogSlope u v a)⁻¹)
    rw [abs_neg] at haa
    have hbb := le_abs_self ((halaszLogSlope u v b)⁻¹)
    simp only [div_eq_mul_inv] at hBa hBb ⊢
    linarith
  have hHnorm (x : ℝ) :
      ‖-Complex.I*halaszLogPhase u v x*((halaszLogSlope u v x)⁻¹:ℝ)‖ =
        |(halaszLogSlope u v x)⁻¹| := by
    simp only [norm_mul, norm_neg, Complex.norm_I, halasz_log_phase_norm,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hidentity : (∫ x in a..b, halaszLogPhase u v x) =
      -Complex.I*halaszLogPhase u v b*((halaszLogSlope u v b)⁻¹:ℝ) -
      (-Complex.I*halaszLogPhase u v a*((halaszLogSlope u v a)⁻¹:ℝ)) +
      ∫ x in a..b, K x := by
    rw [intervalIntegral.integral_sub hiF hiK] at hFTC
    exact sub_eq_iff_eq_add.mp hFTC
  rw [hidentity]
  apply (norm_add_le _ _).trans
  have hh := norm_sub_le
    (-Complex.I*halaszLogPhase u v b*((halaszLogSlope u v b)⁻¹:ℝ))
    (-Complex.I*halaszLogPhase u v a*((halaszLogSlope u v a)⁻¹:ℝ))
  simp only [hHnorm] at hh
  simp only [div_eq_mul_inv] at hBa hBb hR ⊢
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszStationaryPhase
namespace OAI

/-! Locate the unique possible stationary point and quantify the slope
away from it on a positive finite interval. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_log_slope_drop (u v b x y : ℝ) (hu : 0 ≤ u)
    (hx : 0 < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    u*(y-x)/b^2 ≤ halaszLogSlope u v x-halaszLogSlope u v y := by
  have hy : 0 < y := hx.trans_le hxy
  have hb : 0 < b := hy.trans_le hyb
  have hprod : x*y ≤ b^2 := by nlinarith
  calc
    _ ≤ u*(y-x)/(x*y) := div_le_div_of_nonneg_left
      (mul_nonneg hu (sub_nonneg.mpr hxy)) (mul_pos hx hy) hprod
    _ = _ := by unfold halaszLogSlope; field_simp; ring

lemma halasz_log_stationary_center (u v a b : ℝ) (hu : 0 ≤ u)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ c ∈ Set.Icc a b,
      (∀ x ∈ Set.Icc a b, x < c → u*(c-x)/b^2 ≤ halaszLogSlope u v x) ∧
      (∀ x ∈ Set.Icc a b, c < x → u*(x-c)/b^2 ≤ -halaszLogSlope u v x) := by
  by_cases hb : 0 ≤ halaszLogSlope u v b
  · refine ⟨b, ⟨hab, le_rfl⟩, ?_, ?_⟩
    · intro x hx hxb
      have hh := halasz_log_slope_drop u v b x b hu (ha.trans_le hx.1) hxb.le le_rfl
      linarith
    · intro x hx hbx
      exact (not_lt_of_ge hx.2 hbx).elim
  by_cases ha' : halaszLogSlope u v a ≤ 0
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_, ?_⟩
    · intro x hx hxa
      exact (not_lt_of_ge hx.1 hxa).elim
    · intro x hx hax
      have hh := halasz_log_slope_drop u v b a x hu ha hax.le hx.2
      linarith
  have hc : ContinuousOn (halaszLogSlope u v) (Set.Icc a b) :=
    (continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')).sub
      continuousOn_const
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc' hab hc
    (show (0:ℝ) ∈ Set.Icc (halaszLogSlope u v b) (halaszLogSlope u v a) by
      exact ⟨(lt_of_not_ge hb).le, (lt_of_not_ge ha').le⟩)
  refine ⟨c, hc, ?_, ?_⟩
  · intro x hx hxc
    have hh := halasz_log_slope_drop u v b x c hu (ha.trans_le hx.1) hxc.le hc.2
    linarith
  · intro x hx hcx
    have hh := halasz_log_slope_drop u v b c x hu (ha.trans_le hc.1) hcx.le hx.2
    linarith

/-- Uniform square-root cancellation for an individual Poisson integral. -/
theorem halasz_log_stationary_integral (u v a b : ℝ) (hu : 0 < u)
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, halaszLogPhase u v x‖ ≤ 10*b/Real.sqrt u := by
  have hb : 0 < b := ha.trans_le hab
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  let r := b/Real.sqrt u
  let lam := Real.sqrt u/b
  have hr : 0 < r := div_pos hb hsu
  have hlam : 0 < lam := div_pos hsu hb
  have he : u*r/b^2 = lam := by
    dsimp [r, lam]
    have hs := Real.sq_sqrt hu.le
    field_simp
    nlinarith
  have hrec : 4/lam = 4*r := by dsimp [lam, r]; field_simp
  obtain ⟨c, hc, hleft, hright⟩ := halasz_log_stationary_center u v a b hu.le ha hab
  let l := max a (c-r)
  let q := min b (c+r)
  have hal : a ≤ l := le_max_left _ _
  have hlc : l ≤ c := max_le hc.1 (by linarith)
  have hcq : c ≤ q := le_min hc.2 (by linarith)
  have hqb : q ≤ b := min_le_left _ _
  have hlq : l ≤ q := hlc.trans hcq
  have hi (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) :
      IntervalIntegrable (halaszLogPhase u v) volume x y :=
    (halasz_log_phase_continuousOn u v x y (ha.trans_le hax)).intervalIntegrable_of_Icc hxy
  have hLI : ‖∫ x in a..l, halaszLogPhase u v x‖ ≤ 4*r := by
    by_cases hla : l = a
    · simp only [hla, intervalIntegral.integral_same, norm_zero]
      positivity
    have hal' : a < l := lt_of_le_of_ne hal (Ne.symm hla)
    have hl : l = c-r := max_eq_right (by
      have hh : a < max a (c-r) := hal'
      exact (lt_max_iff.mp hh).resolve_left (lt_irrefl a) |>.le)
    have hh := halasz_log_first_derivative u v a l lam hu.le ha hal hlam (by
      intro x hx
      have hxc : x < c := by rw [hl] at hx; linarith [hx.2]
      have hd := hleft x ⟨hx.1, hx.2.trans (hlc.trans hc.2)⟩ hxc
      have hdist : r ≤ c-x := by rw [hl] at hx; linarith [hx.2]
      have hscale := mul_le_mul_of_nonneg_left hdist hu.le
      have hd' : lam ≤ halaszLogSlope u v x := by
        rw [← he]
        exact (div_le_div_of_nonneg_right hscale (sq_nonneg b)).trans hd
      exact hd'.trans (le_abs_self _))
    rwa [hrec] at hh
  have hRI : ‖∫ x in q..b, halaszLogPhase u v x‖ ≤ 4*r := by
    by_cases hqb' : q = b
    · simp only [hqb', intervalIntegral.integral_same, norm_zero]
      positivity
    have hqb'' : q < b := lt_of_le_of_ne hqb hqb'
    have hq : q = c+r := min_eq_right (by
      have hh : min b (c+r) < b := hqb''
      exact (min_lt_iff.mp hh).resolve_left (lt_irrefl b) |>.le)
    have hh := halasz_log_first_derivative u v q b lam hu.le (ha.trans_le (hc.1.trans hcq)) hqb hlam (by
      intro x hx
      have hcx : c < x := by rw [hq] at hx; linarith [hx.1]
      have hd := hright x ⟨(hc.1.trans hcq).trans hx.1, hx.2⟩ hcx
      have hdist : r ≤ x-c := by rw [hq] at hx; linarith [hx.1]
      have hscale := mul_le_mul_of_nonneg_left hdist hu.le
      have hd' : lam ≤ -halaszLogSlope u v x := by
        rw [← he]
        exact (div_le_div_of_nonneg_right hscale (sq_nonneg b)).trans hd
      exact hd'.trans (neg_le_abs _))
    rwa [hrec] at hh
  have hMI : ‖∫ x in l..q, halaszLogPhase u v x‖ ≤ 2*r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := q) (C := (1:ℝ)) (f := halaszLogPhase u v)
      (fun x _ => (halasz_log_phase_norm u v x).le)
    rw [abs_of_nonneg (sub_nonneg.mpr hlq), one_mul] at hh
    have hll : c-r ≤ l := le_max_right _ _
    have hqq : q ≤ c+r := min_le_right _ _
    linarith
  have hsplit : (∫ x in a..b, halaszLogPhase u v x) =
      (∫ x in a..l, halaszLogPhase u v x) +
        (∫ x in l..q, halaszLogPhase u v x) +
        ∫ x in q..b, halaszLogPhase u v x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi a l le_rfl hal) (hi l q hal hlq),
      intervalIntegral.integral_add_adjacent_intervals (hi a q le_rfl (hal.trans hlq)) (hi q b (hal.trans hlq) hqb)]
  rw [hsplit]
  have hn := norm_add_le
    ((∫ x in a..l, halaszLogPhase u v x)+(∫ x in l..q, halaszLogPhase u v x))
    (∫ x in q..b, halaszLogPhase u v x)
  have hn' := norm_add_le (∫ x in a..l, halaszLogPhase u v x)
    (∫ x in l..q, halaszLogPhase u v x)
  have he10 : 10*b/Real.sqrt u = 10*r := by dsimp [r]; ring
  rw [he10]
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszAffineAmplitude
namespace OAI

/-! Affine amplitudes for the two pieces of a compact triangular weight. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_affine_amplitude_bound (f : ℝ → ℂ) (a b m c B : ℝ)
    (hab : a ≤ b) (hi : IntervalIntegrable f volume a b)
    (hc : ∀ x ∈ Set.Icc a b, ContinuousAt f x) (hm : StronglyMeasurable f)
    (hB : ∀ x ∈ Set.Icc a b, ‖∫ y in a..x, f y‖ ≤ B) :
    ‖∫ x in a..b, (m*x+c : ℝ)*f x‖ ≤ (|m*b+c|+|m| *(b-a))*B := by
  let F : ℝ → ℂ := fun x => ∫ y in a..x, f y
  have hF : ContinuousOn F (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hi (Set.left_mem_uIcc)
  have hdF (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt F (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right
      (hi.mono_set (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1] using
        Set.Icc_subset_Icc le_rfl hx.2))
      hm.stronglyMeasurableAtFilter (hc x hx)
  have hdm (x : ℝ) : HasDerivAt (fun y : ℝ => (m*y+c : ℂ)) (m:ℂ) x := by
    convert (preTransparency := .instances) (((hasDerivAt_id x).const_mul m).add_const c).ofReal_comp using 1 <;> simp
  have hmc : ContinuousOn (fun x : ℝ => (m*x+c : ℂ)) (Set.uIcc a b) :=
    (continuous_const.mul Complex.continuous_ofReal |>.add continuous_const).continuousOn
  have hmi : IntervalIntegrable (fun _ : ℝ => (m:ℂ)) volume a b := intervalIntegrable_const
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hmc hF
    (fun x _ => hdm x)
    (fun x hx => hdF x (by
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact ⟨hx.1.le, hx.2.le⟩)) hmi hi
  change (∫ x in a..b, (m*x+c : ℂ)*f x) = _ at he
  have hzero : F a = 0 := intervalIntegral.integral_same
  rw [hzero, mul_zero, sub_zero] at he
  have hnorm : ‖∫ x in a..b, (m:ℂ)*F x‖ ≤ |m| *B*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := |m| *B) (f := fun x => (m:ℂ)*F x) (by
        intro x hx
        have hx' : x ∈ Set.Icc a b := by
          rw [Set.uIoc_of_le hab] at hx
          exact ⟨hx.1.le, hx.2⟩
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB x hx') (abs_nonneg m))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hb := hB b ⟨hab, le_rfl⟩
  have hprod : ‖(m*b+c : ℂ)*F b‖ ≤ |m*b+c| *B := by
    rw [norm_mul]
    norm_cast
    simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hb (abs_nonneg (m*b+c))
  push_cast
  rw [he]
  exact (norm_sub_le _ _).trans (by nlinarith)

lemma halasz_log_stationary_affine (u v a b m c : ℝ) (hu : 0 < u)
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, (m*x+c : ℝ)*halaszLogPhase u v x‖ ≤
      (|m*b+c|+|m| *(b-a))*(10*b/Real.sqrt u) := by
  apply halasz_affine_amplitude_bound _ _ _ _ _ _ hab
    ((halasz_log_phase_continuousOn u v a b ha).intervalIntegrable_of_Icc hab)
    (fun x hx => (halasz_log_phase_deriv u v x (ha.trans_le hx.1).ne').continuousAt)
    (by
      have hm : Measurable (halaszLogPhase u v) := by unfold halaszLogPhase; fun_prop
      exact hm.stronglyMeasurable)
  intro x hx
  exact (halasz_log_stationary_integral u v a x hu ha hx.1).trans
    (div_le_div_of_nonneg_right (by linarith [hx.2]) (Real.sqrt_nonneg u))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleIntegral
namespace OAI

/-! The compact triangular majorant used for a dyadic Dirichlet kernel. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory


lemma halasz_triangle_stationary (N u v : ℝ) (hN : 0 < N) (hu : 0 < u) :
    ‖halaszTriangleIntegral N u v‖ ≤ 110*N/Real.sqrt u := by
  have h1 := halasz_log_stationary_affine u v (N/2) (3*N/2) (2/N) (-1) hu
    (by positivity) (by linarith)
  have h2 := halasz_log_stationary_affine u v (3*N/2) (5*N/2) (-(2/N)) 5 hu
    (by positivity) (by linarith)
  have he1 : 2/N*(3*N/2)+(-1) = 2 := by field_simp [hN.ne']; ring
  have he2 : -(2/N)*(5*N/2)+5 = 0 := by field_simp [hN.ne']; ring
  have he3 : |2/N| = 2/N := abs_of_pos (by positivity)
  have he4 : |-(2/N)| = 2/N := by rw [abs_neg, he3]
  rw [he1, he3, abs_of_pos (by norm_num : (0:ℝ)<2)] at h1
  rw [he2, he4, abs_zero] at h2
  have hr1 : (2+2/N*(3*N/2-N/2))*(10*(3*N/2)/Real.sqrt u) =
      60*N/Real.sqrt u := by field_simp [hN.ne']; ring
  have hr2 : (0+2/N*(5*N/2-3*N/2))*(10*(5*N/2)/Real.sqrt u) =
      50*N/Real.sqrt u := by field_simp [hN.ne']; ring
  rw [hr1] at h1
  rw [hr2] at h2
  exact (norm_add_le _ _).trans (by
    change ‖_‖ + ‖_‖ ≤ _
    simp only [sub_eq_add_neg, div_eq_mul_inv] at h1 h2 ⊢
    linarith)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseConjugation
namespace OAI

/-! Reflection of the logarithmic phase, needed for both signs of a
frequency difference in the sparse Gram kernel. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Complex
open scoped _root_.ComplexConjugate

lemma halasz_log_phase_neg (u v x : ℝ) :
    halaszLogPhase (-u) (-v) x = conj (halaszLogPhase u v x) := by
  unfold halaszLogPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, conj_ofReal, conj_I, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg]
  ring

lemma halasz_log_affine_integral_neg (u v m c a b : ℝ) :
    (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase (-u) (-v) x) =
      conj (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) := by
  simp_rw [halasz_log_phase_neg]
  have he (x : ℝ) : ((m*x+c:ℝ):ℂ)*conj (halaszLogPhase u v x) =
      conj (((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) := by simp
  simp_rw [he]
  unfold intervalIntegral
  rw [integral_conj, integral_conj, map_sub]

lemma halasz_triangle_integral_neg (N u v : ℝ) :
    halaszTriangleIntegral N (-u) (-v) = conj (halaszTriangleIntegral N u v) := by
  unfold halaszTriangleIntegral
  simp only [sub_eq_add_neg]
  rw [halasz_log_affine_integral_neg, halasz_log_affine_integral_neg, map_add]

lemma halasz_triangle_stationary_abs (N u v : ℝ) (hN : 0 < N) (hu : u ≠ 0) :
    ‖halaszTriangleIntegral N u v‖ ≤ 110*N/Real.sqrt |u| := by
  rcases lt_or_gt_of_ne hu with hn | hp
  · have hh := halasz_triangle_stationary N (-u) (-v) hN (neg_pos.mpr hn)
    rw [halasz_triangle_integral_neg, norm_conj, ← abs_of_neg hn] at hh
    exact hh
  · simpa only [abs_of_pos hp] using halasz_triangle_stationary N u v hN hp

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_triangle_stationary_abs := @OAI.TwoPointCorrelations.halasz_triangle_stationary_abs
