-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_mixed_real_bin_separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:35:20.515879+00:00
-- url     : https://prove2.me/submissions/6060594f-e1dd-4e04-ac64-a25a206d9160

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplificationPower
namespace OAI

/-! The explicit amplification order used between two successive MRT
prime scales. The integer ceiling satisfies the exact support inequalities
needed by the mixed cofactor moment. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_nat_pow_eq_exp {Y : ℝ} (hY : 0 < Y) (r : ℕ) :
    Y ^ r = Real.exp ((r : ℝ) * Real.log Y) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hY]
  congr 1
  ring

theorem mrt_amplification_order_bounds {Y u : ℝ} (hY : 1 < Y) (hu : 1 ≤ u) :
    u ≤ Y ^ mrtAmplificationOrder Y u ∧
      Y ^ mrtAmplificationOrder Y u ≤ u * Y ∧
      (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hquot : 0 ≤ Real.log u / Real.log Y :=
    div_nonneg (Real.log_nonneg hu) hlogY.le
  have hlo : Real.log u / Real.log Y ≤ (mrtAmplificationOrder Y u : ℝ) :=
    Nat.le_ceil _
  have hhi : (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 :=
    Nat.ceil_lt_add_one hquot
  refine ⟨?_, ?_, hhi⟩
  · calc
      u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ ≤ Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hlogY).mp hlo)
      _ = _ := (mrt_nat_pow_eq_exp hY0 _).symm
  · have hh : (mrtAmplificationOrder Y u : ℝ) * Real.log Y <
        Real.log u + Real.log Y := by
      have hh := (mul_lt_mul_of_pos_right hhi hlogY)
      rw [add_mul, div_mul_cancel₀ _ hlogY.ne', one_mul] at hh
      exact hh
    calc
      _ = Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        mrt_nat_pow_eq_exp hY0 _
      _ ≤ Real.exp (Real.log u + Real.log Y) := Real.exp_le_exp.mpr hh.le
      _ = u * Y := by rw [Real.exp_add, Real.exp_log hu0, Real.exp_log hY0]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyExponents
namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations



lemma mrtFrequencyExponent_bounds {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    1 / 4 - 3 * η / 2 ≤ mrtFrequencyExponent η j ∧
      mrtFrequencyExponent η j ≤ 1 / 4 - η := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hi : (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hi0 : (0 : ℝ) ≤ 1 / (2 * ((j : ℝ) + 1)) := by positivity
  unfold mrtFrequencyExponent
  constructor
  · have hh := mul_le_mul_of_nonneg_left hi hη
    nlinarith
  · have hh := mul_nonneg hη hi0
    nlinarith

lemma mrtFrequencyExponent_nonneg {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 6)
    (j : ℕ) : 0 ≤ mrtFrequencyExponent η j := by
  have hh := (mrtFrequencyExponent_bounds hη j).1
  linarith

lemma mrtFrequencyExponent_gap (η : ℝ) (j : ℕ) :
    mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j =
      η / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  unfold mrtFrequencyExponent
  push_cast
  field_simp [h1, h2]
  ring

lemma mrtFrequencyExponent_gap_lower {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    η / (2 * ((j : ℝ) + 2) ^ 2) ≤
      mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j := by
  rw [mrtFrequencyExponent_gap]
  apply div_le_div_of_nonneg_left hη (by positivity)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- After paying half of the threshold gap for the mixed-moment
factorial, the remaining exponential saving is still summable. -/
lemma mrt_frequency_gap_saving {η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (j : ℕ) :
    2 * x * (mrtFrequencyExponent η j - mrtFrequencyExponent η (j + 1) +
      η / (4 * ((j : ℝ) + 2) ^ 2)) ≤ -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have hh := mul_le_mul_of_nonneg_left (mrtFrequencyExponent_gap_lower hη j)
    (show 0 ≤ 2 * x by positivity)
  have he : 2 * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η / (2 * ((j : ℝ) + 2) ^ 2) := by
    field_simp
    ring
  rw [show -η * x / (2 * ((j : ℝ) + 2) ^ 2) =
      -x * (η / (2 * ((j : ℝ) + 2) ^ 2)) by ring]
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplificationGrowth
namespace OAI

/-! Explicit factorial and ceiling costs in the multiscale mixed moment.
These estimates keep the numerical scale requirements visible. -/

namespace TwoPointCorrelations

lemma mrt_factorial_square_exp (r : ℕ) :
    (r.factorial : ℝ) ^ 2 ≤
      Real.exp (2 * (r : ℝ) * Real.log (max 1 (r : ℝ))) := by
  by_cases hr : r = 0
  · subst r
    norm_num
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    calc
      _ ≤ ((r : ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) hf 2
      _ = _ := by
        rw [max_eq_right hrR, mrt_nat_pow_eq_exp (by positivity : (0 : ℝ) < r),
          ← Real.exp_nat_mul]
        congr 1
        ring

lemma mrt_amplification_log_cost {Y u : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    (mrtAmplificationOrder Y u : ℝ) *
        Real.log (max 1 (mrtAmplificationOrder Y u : ℝ)) ≤
      (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  let r : ℕ := mrtAmplificationOrder Y u
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  change (r : ℝ) ≤ Real.log u / Real.log Y + 1 at hr
  have hx0 : 0 < Real.log u := by linarith
  have hquot : Real.log u / Real.log Y ≤ Real.log u :=
    div_le_self hx0.le hY
  have hmax : max 1 (r : ℝ) ≤ 2 * Real.log u := by
    apply max_le
    · linarith
    · linarith
  have hlog : Real.log (max 1 (r : ℝ)) ≤ Real.log (Real.log u) + 1 := by
    calc
      _ ≤ Real.log (2 * Real.log u) := Real.log_le_log (by positivity) hmax
      _ = Real.log 2 + Real.log (Real.log u) := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul hr hlog (Real.log_nonneg (le_max_left _ _))
    (by positivity)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedThreshold
namespace OAI

/-! The factorial and support growth in the amplified cofactor moment
are paid from half of the gap between successive prime thresholds. -/

namespace TwoPointCorrelations


lemma mrt_mixed_threshold_exponent {η x y : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (j r : ℕ)
    (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    -2 * mrtFrequencyExponent η (j + 1) * x +
      (((r : ℝ) + 1) * Real.log 2 + y) +
      2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) +
      2 * (r : ℝ) * mrtFrequencyExponent η j * y ≤
      -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * mrtFrequencyExponent η j
    by positivity)
  have hg := mrt_frequency_gap_saving hη hx j
  have he : 2 * x * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η * x / (2 * ((j : ℝ) + 2) ^ 2) := by field_simp; ring
  unfold mrtAmplificationCost at hcost
  nlinarith

theorem mrt_mixed_threshold_bound {η x y τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ : 0 ≤ τ)
    (j r : ℕ) (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        (τ + (2 : ℝ) ^ (r + 1) * Real.exp y) * (r.factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) ≤
      (τ + 1) * Real.exp (-η * x / (2 * ((j : ℝ) + 2) ^ 2)) := by
  let g := ((r : ℝ) + 1) * Real.log 2 + y
  let f := 2 * (r : ℝ) * Real.log (max 1 (r : ℝ))
  let d := -(2 * (r : ℝ) * mrtFrequencyExponent η j * y)
  have hpow : (2 : ℝ) ^ (r + 1) * Real.exp y = Real.exp g := by
    rw [mrt_nat_pow_eq_exp (by norm_num), ← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have hden : Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) =
      Real.exp d := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [d]
    push_cast
    ring
  have hg0 : 0 ≤ g := by
    dsimp [g]
    positivity
  have hg1 : 1 ≤ Real.exp g := Real.one_le_exp_iff.mpr hg0
  have hsum : τ + Real.exp g ≤ (τ + 1) * Real.exp g := by nlinarith
  rw [hpow, hden]
  calc
    _ ≤ Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        ((τ + 1) * Real.exp g) * Real.exp f / Real.exp d := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos d).le
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      · exact mrt_factorial_square_exp r
      · positivity
      · positivity
    _ = (τ + 1) * Real.exp
        (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) := by
      have he : Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) =
          Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
            Real.exp g * Real.exp f / Real.exp d := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_add]
      rw [he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ τ + 1)
      apply Real.exp_le_exp.mpr
      dsimp [g, f, d]
      convert (preTransparency := .instances) mrt_mixed_threshold_exponent hη hη' hx j r hr hcost using 1
      ring

lemma mrt_amplification_cost_bound {Y u a : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      (Real.log u / Real.log Y + 2) * Real.log 2 + Real.log Y +
        2 * (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) +
        2 * a * Real.log Y := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  have hc := mrt_amplification_log_cost hY hu hY0 hu0
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (add_le_add_right hr 1) hlog2
  unfold mrtAmplificationCost
  nlinarith

theorem mrt_mixed_threshold_amplification {η Y u τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hY : 1 < Y) (hu : 1 ≤ u) (hτ : 0 ≤ τ) (j : ℕ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
        ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder Y u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hy := Real.log_pos hY
  have hr := mul_le_mul_of_nonneg_right
    (mrt_amplification_order_bounds hY hu).2.2.le hy.le
  rw [add_mul, div_mul_cancel₀ _ hy.ne', one_mul] at hr
  simpa only [Real.exp_log (by linarith : 0 < Y)] using
    mrt_mixed_threshold_bound hη hη' (Real.log_nonneg hu) hy.le hτ j
      (mrtAmplificationOrder Y u) hr hcost

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedScale
namespace OAI

/-! Explicit sufficient logarithmic scale separations for the amplified
moment. The factorial budget is derived, rather than assumed. -/

namespace TwoPointCorrelations

lemma mrt_amplification_cost_coarse {Y u a : ℝ}
    (hY0 : 0 < Y) (hu0 : 0 < u) (hY : 1 ≤ Real.log Y)
    (hYu : Real.log Y ≤ Real.log u) (ha : a ≤ 1 / 4) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      8 * (Real.log u / Real.log Y) * (Real.log (Real.log u) + 1) +
        2 * Real.log Y := by
  have hu : 1 ≤ Real.log u := hY.trans hYu
  have hx0 : 0 ≤ Real.log u := by linarith
  have hy0 : 0 < Real.log Y := by linarith
  have hq : 1 ≤ Real.log u / Real.log Y := (le_div_iff₀ hy0).mpr (by simpa using hYu)
  have hl : 1 ≤ Real.log (Real.log u) + 1 := by
    linarith [Real.log_nonneg hu]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left hlog1
    (show 0 ≤ Real.log u / Real.log Y + 2 by positivity)
  have hql := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ Real.log u / Real.log Y by positivity)
  have hq1 := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ Real.log (Real.log u) + 1 by positivity)
  have hay := mul_le_mul_of_nonneg_right ha hy0.le
  have hc := mrt_amplification_cost_bound hY hu hY0 hu0 (a := a)
  nlinarith

lemma mrt_mixed_scale_guard {η x y d : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hd : 0 < d)
    (hsep : 32 * d * (Real.log x + 1) ≤ η * y)
    (hsize : 8 * d * y ≤ η * x) :
    8 * (x / y) * (Real.log x + 1) + 2 * y ≤ η * x / (2 * d) := by
  have hh := mul_le_mul_of_nonneg_left hsep (div_nonneg hx hy.le)
  have he : x / y * (η * y) = η * x := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
  nlinarith

theorem mrt_amplification_cost_of_separation {η Y u : ℝ}
    (hη : 0 ≤ η) (j : ℕ) (hY0 : 0 < Y) (hu0 : 0 < u)
    (hY : 1 ≤ Real.log Y) (hYu : Real.log Y ≤ Real.log u)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * Real.log Y ≤ η * Real.log u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2) := by
  apply (mrt_amplification_cost_coarse hY0 hu0 hY hYu
    (show mrtFrequencyExponent η j ≤ 1 / 4 by
      have hh := (mrtFrequencyExponent_bounds hη j).2
      linarith)).trans
  exact mrt_mixed_scale_guard (by linarith : 0 ≤ Real.log u)
    (by linarith : 0 < Real.log Y) (by positivity) hsep hsize


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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedRealBins
namespace OAI

/-! The actual real prime-bin threshold survives the integer endpoint
used by the finite mixed-moment theorem. -/

namespace TwoPointCorrelations

theorem mrt_mixed_real_bin_threshold {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hu : 1 ≤ u) (hτ : 0 ≤ τ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder ⌈Y⌉₊ u)
        (Real.log (⌈Y⌉₊ : ℝ)) (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hden : Real.exp (-mrtFrequencyExponent η j * Real.log (⌈Y⌉₊ : ℝ)) ≤
      Real.exp (-mrtFrequencyExponent η j * Real.log Y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (by linarith))
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hden
    (2 * mrtAmplificationOrder ⌈Y⌉₊ u)
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  exact mrt_mixed_threshold_amplification hη hη'
    (by exact_mod_cast hc.1) hu hτ j hcost

theorem mrt_mixed_real_bin_separation_oai {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hlogY : 1 ≤ Real.log Y)
    (hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u) (hu0 : 0 < u) (hτ : 0 ≤ τ)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  apply mrt_mixed_real_bin_threshold hη hη' j hY
    ((Real.log_nonneg_iff hu0).mp (by linarith)) hτ
  apply mrt_amplification_cost_of_separation hη j
    (by exact_mod_cast (show 0 < ⌈Y⌉₊ by omega)) hu0 (hlogY.trans hlog) hYu
  · exact hsep.trans (mul_le_mul_of_nonneg_left hlog hη)
  · exact (mul_le_mul_of_nonneg_left hc.2.2.2 (by positivity)).trans hsize

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_mixed_real_bin_separation_oai := @OAI.TwoPointCorrelations.mrt_mixed_real_bin_separation_oai
