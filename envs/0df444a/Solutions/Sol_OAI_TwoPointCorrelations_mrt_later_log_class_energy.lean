-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_later_log_class_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:02:21.112447+00:00
-- url     : https://prove2.me/submissions/6f5775fe-9f04-45f8-bafd-f17245d9fcce

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_actual_bin_moment_sum
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_general_typical_witnessed_energy

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandLogGrowth
namespace OAI

/-! Uniform scalar growth estimates for the actual MRT band endpoints.
These estimates bound the mixed-moment factorial cost for every band. -/

namespace TwoPointCorrelations

lemma mrt_log_log_band_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hQ : 1 ≤ Real.log Q) :
    Real.log (Real.log (mrtBandUpper Q j)) + 1 ≤
      8 * (j : ℝ) ^ 2 * (Real.log (Real.log Q) + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hq0 : 0 < Real.log Q := by linarith
  have hl0 : 0 ≤ Real.log (Real.log Q) := Real.log_nonneg hQ
  have hlj : Real.log (j : ℝ) ≤ j :=
    (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hlj
    (show 0 ≤ 4 * (j : ℝ) + 2 by positivity)
  have hq := mul_le_mul_of_nonneg_right hj2 hl0
  simp only [mrtBandUpper, Real.log_exp]
  rw [Real.log_mul (pow_ne_zero _ hj0.ne') (pow_ne_zero _ hq0.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandPowerSaving
namespace OAI

/-! The later-band exponential is much smaller than the remaining
polynomial bin factors, uniformly in the band index. -/

namespace TwoPointCorrelations

lemma mrt_log_later_band_lower (P Q : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (k : ℝ) ^ 8 * Real.log Q * Real.log P ≤
      Real.log (mrtBandLower P Q k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hpow : (k : ℝ) ^ 8 ≤ (k : ℝ) ^ (4 * k) :=
    pow_le_pow_right₀ hk1 (by omega)
  have hq : Real.log Q ≤ Real.log Q ^ (k - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hQ (show 1 ≤ k - 1 by omega)
  simp only [mrtBandLower, Real.log_exp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hpow hq (by linarith) (by positivity)) hP

theorem mrt_later_band_exponential_budget {η P Q : ℝ} (hη : 0 ≤ η)
    (k : ℕ) (hk : 2 ≤ k) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 ≤ η * Real.log Q) :
    2048 * (k : ℝ) ^ 6 * Real.log P ≤
      η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h1 := mul_le_mul_of_nonneg_left (mrt_log_later_band_lower P Q k hk hP hQ) hη
  have h2 := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ (k : ℝ) ^ 8 * Real.log P by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 4 * (k : ℝ) ^ 2)).mpr
  have he : (2048 * (k : ℝ) ^ 6 * Real.log P) * (4 * (k : ℝ) ^ 2) =
      8192 * (k : ℝ) ^ 8 * Real.log P := by ring
  rw [he]
  nlinarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBinPrefactor
namespace OAI

/-! Explicit polynomial factors in the later-band estimate are absorbed
by a small part of the saving from the true band endpoints. -/

namespace TwoPointCorrelations

lemma mrt_log_band_upper_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q k) := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hi.trans hik)
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  simp only [mrtBandUpper, Real.log_exp]
  apply mul_le_mul
  · exact (pow_le_pow_left₀ hi0 hik' _).trans
      (pow_le_pow_right₀ hk1 (by omega))
  · exact pow_le_pow_right₀ hQ hik
  · positivity
  · positivity

lemma mrt_bin_prefactor_exponential {P L η k : ℝ}
    (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hL : 1 ≤ L) (hη : 0 < η)
    (hlogL : Real.log L ≤ 8 * k ^ 2 * Real.log P)
    (hinv : η⁻¹ ≤ Real.log P) :
    512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 / η ≤
      Real.exp (1024 * k ^ 2 * Real.log P) := by
  have hk0 : 0 ≤ k := by linarith
  have hc : (512 : ℝ) ≤ Real.exp 512 := by
    linarith [Real.add_one_le_exp (512 : ℝ)]
  have hkexp : k ^ 8 ≤ Real.exp (8 * k) := by
    have hh : k ≤ Real.exp k := by linarith [Real.add_one_le_exp k]
    exact (pow_le_pow_left₀ hk0 hh 8).trans_eq (Real.exp_nat_mul k 8).symm
  have hpexp : P ^ 3 = Real.exp (3 * Real.log P) := by
    rw [show Real.exp (3 * Real.log P) = (Real.exp (Real.log P)) ^ 3 by
      simpa using Real.exp_nat_mul (Real.log P) 3, Real.exp_log hP0]
  have hLexp : L ^ 2 ≤ Real.exp (16 * k ^ 2 * Real.log P) := by
    calc
      L ^ 2 = Real.exp (2 * Real.log L) := by
        rw [show Real.exp (2 * Real.log L) = (Real.exp (Real.log L)) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log L) 2, Real.exp_log (by linarith : 0 < L)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hPexp := hpexp.le
  have hηexp : η⁻¹ ≤ Real.exp (Real.log P) :=
    hinv.trans (by linarith [Real.add_one_le_exp (Real.log P)])
  have hk2 : k ≤ k ^ 2 := by nlinarith
  have hk2p : k ≤ k ^ 2 * Real.log P := by nlinarith
  have hpp : Real.log P ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 1 by nlinarith) (by linarith : 0 ≤ Real.log P)]
  have hbase : 8 ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 4 by nlinarith) (by linarith : 0 ≤ Real.log P - 2)]
  calc
    _ = 512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 * η⁻¹ := by ring
    _ ≤ Real.exp 512 * Real.exp 11 * Real.exp (8 * k) *
        Real.exp (3 * Real.log P) * Real.exp (16 * k ^ 2 * Real.log P) *
        Real.exp (Real.log P) := by gcongr
    _ = Real.exp (523 + 8 * k + 4 * Real.log P + 16 * k ^ 2 * Real.log P) := by
      simp only [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem mrt_actual_bin_prefactor {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2))) ≤
      Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) := by
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hP1 : 1 ≤ P := (Real.one_lt_exp_iff.mpr (by linarith : 0 < Real.log P)).le.trans_eq
    (Real.exp_log hP0)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hpη : 1 ≤ η * Real.log P := by nlinarith
  have hinv : η⁻¹ ≤ Real.log P := by
    rw [← one_div, div_le_iff₀ hη]
    nlinarith
  have hyP : Real.log (Real.log Q) + 1 ≤ Real.log P := by
    nlinarith [mul_le_mul_of_nonneg_right hη' (by linarith : 0 ≤ Real.log P)]
  have hL : 1 ≤ Real.log (mrtBandUpper Q k) :=
    (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)).trans
      (mrt_band_index_le_log_upper Q k (by omega) hQ)
  have hlogL : Real.log (Real.log (mrtBandUpper Q k)) ≤
      8 * (k : ℝ) ^ 2 * Real.log P := by
    have hh := mrt_log_log_band_upper Q k (by omega) hQ
    have hh' := mul_le_mul_of_nonneg_left hyP (show 0 ≤ 8 * (k : ℝ) ^ 2 by positivity)
    linarith
  have hH₁ := mrt_resolution_le hP1 hQ hη.le k
  have hH₀ : mrtResolution P Q η (k - 1) ≤ (k : ℝ) ^ 2 * P := by
    apply (mrt_resolution_le hP1 hQ hη.le (k - 1)).trans
    gcongr
    exact_mod_cast Nat.sub_le k 1
  have hU := mrt_log_band_upper_mono hQ (show 1 ≤ k - 1 by omega) (Nat.sub_le k 1)
  have hH₀0 : 0 ≤ mrtResolution P Q η (k - 1) := (mrtResolution_pos P Q η (by omega)).le
  have hH₁0 : 0 ≤ mrtResolution P Q η k := (mrtResolution_pos P Q η (by omega)).le
  have hU₀0 : 0 ≤ Real.log (mrtBandUpper Q (k - 1)) := by
    have hh := mrt_band_index_le_log_upper Q (k - 1) (by omega) hQ
    exact (Nat.cast_nonneg _).trans hh
  have hB : 1 ≤ (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by nlinarith) hP1) hL
  have hF₀ : mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul hH₀ hU hU₀0 (by positivity : 0 ≤ (k : ℝ) ^ 2 * P)
    nlinarith
  have hF₁ : mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul_of_nonneg_right hH₁ (by linarith : 0 ≤ Real.log (mrtBandUpper Q k))
    nlinarith
  calc
    _ ≤ 64 * Real.exp 11 *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (((k : ℝ) ^ 2 * P) / (η / (2 * (k : ℝ) ^ 2))) := by gcongr
    _ = 512 * Real.exp 11 * (k : ℝ) ^ 8 * P ^ 3 *
        Real.log (mrtBandUpper Q k) ^ 2 / η := by field_simp; ring
    _ ≤ _ := mrt_bin_prefactor_exponential hk1 hP0 hP hL hη hlogL hinv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLaterBinSum
namespace OAI

/-! The later frequency classes have a summable bound, with the true
resolution and all witness-bin choices included. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma mrt_later_bin_prefactor_saving {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    (64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2)))) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) ≤
      P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hηQ : 8192 ≤ η * Real.log Q := by
    have hh := mul_le_mul_of_nonneg_left hPQ hη.le
    nlinarith
  have hlarge := mrt_later_band_exponential_budget (P := P) (Q := Q) hη.le k hk
    (by linarith) hQ hηQ
  have hkpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  have hkp : (k : ℝ) ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hpp : Real.log P ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    nlinarith
  have hlogk : Real.log (k : ℝ) ≤ k :=
    (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hsave : 1024 * (k : ℝ) ^ 2 * Real.log P + Real.log P + 2 * Real.log (k : ℝ) ≤
      η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hkpow (by linarith : 0 ≤ Real.log P)
    have he : η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) =
        2 * (η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2)) := by ring
    rw [he]
    nlinarith
  have hL0 : 0 < mrtBandLower P Q k := Real.exp_pos _
  calc
    _ ≤ Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_right (mrt_actual_bin_prefactor hη hη' k hk hP0 hP hQ hbudget)
        (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P -
        η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2)) := by
      rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log P - 2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log hP0,
        show Real.exp (2 * Real.log (k : ℝ)) = (Real.exp (Real.log (k : ℝ))) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log (k : ℝ)) 2,
        Real.exp_log hk0]
      ring

theorem mrt_later_bin_moment_sum {η P Q τ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins (mrtResolution P Q η (j + 1))
        (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
      ∑ k ∈ mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
        mrtMixedBinCost η j τ
          (mrtPrimeLogLower (mrtResolution P Q η (j + 1)) b)
          (mrtPrimeLogLower (mrtResolution P Q η (j + 2)) k) ≤
      (τ + 1) * P⁻¹ * (((j : ℝ) + 2) ^ 2)⁻¹ := by
  have hresolution (k : ℕ) (hk : 1 ≤ k) : 2 ≤ mrtResolution P Q η k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpow : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    dsimp [mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hh := mrt_actual_bin_moment_sum hη hη' j hP hQ hbudget
    (hresolution (j + 1) (by omega)) (hresolution (j + 2) (by omega)) hτ
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_left
    (mrt_later_bin_prefactor_saving hη hη' (j + 2) (by omega) hP0 hP hQ hPQ hbudget)
    (show 0 ≤ τ + 1 by linarith)
  have hj : j + 2 - 1 = j + 1 := by omega
  simp only [hj, Nat.cast_add, Nat.cast_ofNat] at hs
  convert (preTransparency := .instances) hs using 1 <;> ring

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

lemma mrt_log_small_set_measurable (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) :
    MeasurableSet (mrtLogSmallSet S F H K a) := by
  have he : mrtLogSmallSet S F H K a = ⋂ k ∈ K,
      {t | ‖mrtLogPrimePolynomial S F H k t‖ ≤
        Real.exp (-a*Real.log (mrtPrimeLogLower H k))} := by
    ext t
    simp [mrtLogSmallSet]
  rw [he]
  exact K.measurableSet_biInter (fun k _ =>
    (isClosed_le (mrt_log_prime_polynomial_continuous S F H k).norm continuous_const).measurableSet)

lemma mrt_log_large_set_measurable (S : Finset ℕ) (F : ℕ → ℂ)
    (H : ℝ) (K : Finset ℕ) (a : ℝ) :
    MeasurableSet (mrtLogLargeSet S F H K a) := by
  have he : mrtLogLargeSet S F H K a = ⋃ k ∈ K,
      {t | Real.exp (-a*Real.log (mrtPrimeLogLower H k)) <
        ‖mrtLogPrimePolynomial S F H k t‖} := by
    ext t
    simp [mrtLogLargeSet]
  rw [he]
  exact K.measurableSet_biUnion (fun k _ =>
    (isOpen_lt continuous_const (mrt_log_prime_polynomial_continuous S F H k).norm).measurableSet)

lemma mrt_log_bin_lower_gt_one {H P Q : ℝ} (hH : 2 ≤ H)
    (hP : 0 < P) (hlogP : 2 ≤ Real.log P) {k : ℕ}
    (hk : k ∈ mrtLogBins H P Q) : 1 < mrtPrimeLogLower H k := by
  have hl := mrt_log_bin_lower_endpoint (by linarith : 1 ≤ H) hP (mem_Icc.mp hk).1
  have he : Real.exp 1 ≤ Real.exp (-1)*P := by
    rw [show Real.exp (-1)*P = Real.exp (Real.log P-1) by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log hP]; ring]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le (he.trans hl)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLaterClassEnergy
namespace OAI

/-! Actual adjacent logarithmic prime bins give the summable later-class
energy bound. The preceding large witness is part of the frequency set. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory _root_.Set
open scoped _root_.Classical


theorem mrt_later_log_class_energy_oai {ι : Type*} (J : Finset ι) (V : ι → Finset ℕ)
    (hprime : ∀ ν ∈ J, ∀ p ∈ V ν, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) V) {ν : ι} (hν : ν ∈ J)
    (S₀ : Finset ℕ) (hprime₀ : ∀ p ∈ S₀, p.Prime)
    {P Q η : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : Real.log P ≤ Real.log Q)
    (hη : 0 < η) (hη' : η ≤ 1/6)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (j : ℕ)
    (hrange₀ : ∀ p ∈ S₀, mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1))
    (hrange₁ : ∀ p ∈ V ν, mrtBandLower P Q (j+2) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+2))
    {N : ℕ} (hN : 0 < N) (F : ℕ → ℂ)
    (hF : Multiplicative F) (hFb : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in mrtLaterLogClass S₀ (V ν) F P Q η j T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ V ν, 1/(p:ℝ)^2)+(∑ p ∈ V ν, 1/(p:ℝ)^2)^2+
          2/mrtResolution P Q η (j+2)) +
      (T/N+1)*P⁻¹*(((j:ℝ)+2)^2)⁻¹ := by
  let H₀ := mrtResolution P Q η (j+1)
  let H₁ := mrtResolution P Q η (j+2)
  let B := mrtLogBins H₀ (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  let K := mrtLogBins H₁ (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2))
  let E := mrtLaterLogClass S₀ (V ν) F P Q η j T
  have hres (k : ℕ) (hk : 1 ≤ k) : 2 ≤ mrtResolution P Q η k := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hs : 1 ≤ (k:ℝ)^2 := one_le_pow₀ hk1
    unfold mrtResolution
    nlinarith [mrtBaseResolution_pos P Q η]
  have hH₀ : 2 ≤ H₀ := hres _ (by omega)
  have hH₁ : 2 ≤ H₁ := hres _ (by omega)
  have hlowlog (k : ℕ) (hk : 1 ≤ k) : 2 ≤ Real.log (mrtBandLower P Q k) := by
    have hh := mrt_log_band_lower_fourth P Q k hk (by linarith) hQ
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hp : 1 ≤ (k:ℝ)^4 := one_le_pow₀ hk1
    nlinarith
  have hd₁ := mrt_log_bin_prime_data (V ν) hH₁ (Real.exp_pos _)
    (hprime ν hν) hrange₁
  have hd₀ := mrt_log_bin_prime_data S₀ hH₀ (Real.exp_pos _) hprime₀ hrange₀
  have hwidth := mrt_prime_log_width hH₁
  have hY (b : ℕ) (hb : b ∈ B) : 1 < mrtPrimeLogLower H₀ b :=
    mrt_log_bin_lower_gt_one hH₀ (Real.exp_pos _) (hlowlog _ (by omega)) hb
  have hp₀ (b : ℕ) (_hb : b ∈ B) (p : ℕ)
      (hp : p ∈ S₀.filter (fun p => mrtPrimeLogBin H₀ p = b)) : p.Prime :=
    hprime₀ p (mem_filter.mp hp).1
  have hbin₀ (b : ℕ) (_hb : b ∈ B) (p : ℕ)
      (hp : p ∈ S₀.filter (fun p => mrtPrimeLogBin H₀ p = b)) :
      mrtPrimeLogLower H₀ b ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*mrtPrimeLogLower H₀ b := by
    have hx := hd₀.2 p (mem_filter.mp hp).1
    have hh := And.intro hx.1 (hx.2.trans (mul_le_mul_of_nonneg_right
      (mrt_prime_log_width hH₀).2.1 (Real.exp_pos _).le))
    simpa only [(mem_filter.mp hp).2] using hh
  have hEm : MeasurableSet E := measurableSet_Ioc.inter
    ((mrt_log_small_set_measurable _ _ _ _ _).inter
      (mrt_log_large_set_measurable _ _ _ _ _))
  have hb := mrt_general_typical_witnessed_energy J V hprime hdis hν K
    (mrtPrimeLogBin H₁) hd₁.1 (mrtPrimeLogLower H₁) hN hwidth.1 hwidth.2.1 hd₁.2
    (fun k _ => mrt_prime_log_lower_one (by linarith) k) F hF hFb B
    (fun b => S₀.filter (fun p => mrtPrimeLogBin H₀ p = b))
    (mrtPrimeLogLower H₀) hY hp₀ hbin₀
    (fun b => Real.exp (-mrtFrequencyExponent η j*Real.log (mrtPrimeLogLower H₀ b)))
    (fun _ _ => Real.exp_pos _) hT hEm inter_subset_left
    (fun k => Real.exp (-mrtFrequencyExponent η (j+1)*Real.log (mrtPrimeLogLower H₁ k)))
    (fun k hk t ht => ht.2.1 k hk) (fun t ht => by
      obtain ⟨b, hb, hl⟩ := ht.2.2
      exact ⟨b, hb, hl.le⟩)
  have hs := mrt_later_bin_moment_sum hη hη' j hP0 hP hQ hPQ hbudget hH
    (div_nonneg hT.le (Nat.cast_nonneg N))
  have hcost : (2 * ∑ b ∈ B, (K.card:ℝ) * ∑ k ∈ K,
      (Real.exp (-mrtFrequencyExponent η (j+1)*Real.log (mrtPrimeLogLower H₁ k)))^2 *
        ((16*Real.exp 10*(T/N+(2:ℝ)^(mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊
          (mrtPrimeLogLower H₁ k)+1)*⌈mrtPrimeLogLower H₀ b⌉₊)*
          ((mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊ (mrtPrimeLogLower H₁ k)).factorial:ℝ)^2)/
          (Real.exp (-mrtFrequencyExponent η j*Real.log (mrtPrimeLogLower H₀ b)))^
            (2*mrtAmplificationOrder ⌈mrtPrimeLogLower H₀ b⌉₊ (mrtPrimeLogLower H₁ k)))) ≤
      (T/N+1)*P⁻¹*(((j:ℝ)+2)^2)⁻¹ := hs
  change (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J V F) N t‖^2) ≤ _
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (by linarith [hwidth.2.2]) (by positivity)) hcost)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_later_log_class_energy_oai := @OAI.TwoPointCorrelations.mrt_later_log_class_energy_oai
