-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_typical_kernel_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:14:13.555788+00:00
-- url     : https://prove2.me/submissions/c667242c-a432-4790-b5fa-42e33b47ce03

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_HalaszHighPrimeInput_extra_cofactor
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_large_minimum_extra_cofactor
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_near_actual
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_energy_sharp

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

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPretentiousCenter
namespace OAI

/-! The minimizing twist and the elementary part of MRT Lemma A.4(ii).
Two nearby candidates for the minimum force a lower bound by an explicit
prime cosine sum. Analytic estimates for that prime sum are kept separate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_distance_continuous (F : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => squaredDistance F (mrtArchimedeanTwist t) N) := by
  unfold squaredDistance mrtArchimedeanTwist
  fun_prop

theorem halasz_minimizing_twist (F : ℕ → ℂ) (N : ℕ) :
    ∃ t₁ : ℝ, |t₁| ≤ (N : ℝ) ∧ ∀ t : ℝ, |t| ≤ (N : ℝ) →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  have hn : -(N : ℝ) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hn) (halasz_distance_continuous F N).continuousOn
  refine ⟨t₁, abs_le.mpr ht₁, fun t ht => hmin (abs_le.mp ht)⟩






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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNearRestriction
namespace OAI

/-! Transfer the proved centered energy to the actual frequency subsets
in the logarithmic prime-band partition. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Set

lemma halasz_restricted_near_energy (b : ℕ → ℂ) (N : ℕ)
    (t U A : ℝ) (hU : 0 ≤ U)
    (hnear : (∫ u in -U..U, ‖mrtDyadicPolynomial b N (t + u)‖^2) ≤ A)
    (E : Set ℝ) (hE : E ⊆ Ioc (t-U) (t+U)) :
    (∫ s in E, ‖mrtDyadicPolynomial b N s‖^2) ≤ A := by
  have hc : Continuous (fun s => ‖mrtDyadicPolynomial b N s‖^2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hab : t-U ≤ t+U := by linarith
  have he : (∫ u in -U..U, ‖mrtDyadicPolynomial b N (t + u)‖^2) =
      ∫ s in (t-U)..(t+U), ‖mrtDyadicPolynomial b N s‖^2 := by
    simpa only [sub_eq_add_neg, add_comm] using
      (intervalIntegral.integral_comp_add_left
        (fun s => ‖mrtDyadicPolynomial b N s‖^2) t (a := -U) (b := U))
  rw [he, intervalIntegral.integral_of_le hab] at hnear
  apply le_trans _ hnear
  exact setIntegral_mono_set
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (hc.intervalIntegrable _ _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)

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


lemma mrt_no_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) :
    MeasurableSet (mrtNoSmallBand K Q A J) :=
  ((range J).measurableSet_biUnion (fun j _ =>
    mrt_small_frequency_band_measurable K Q A hQ j)).compl






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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszOriginalNearRestriction
namespace OAI

/-! Near-center energy restricted to the lower half of the frequency
range, where the original published height controls all required twists. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_center_window_quarter_room :
    ∀ᶠ N : ℕ in atTop,
      Real.log (2*N:ℕ)^8+(Real.log N)^(1/16:ℝ) ≤ (N:ℝ)/4 := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (isLittleO_pow_exp_pos_mul_atTop 8 (b := 1) (by norm_num)).bound
    (show (0:ℝ)<1/2048 by norm_num)
  filter_upwards [hlog.eventually hb,hlog.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop 2] with N hb hLN hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hLN0 : 0 ≤ Real.log (N:ℝ) := by linarith
  have hL2 : 0 ≤ Real.log (2*N:ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤2*N by omega))
  have hup : Real.log (2*N:ℕ) ≤ 2*Real.log (N:ℝ) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne']
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hp := pow_le_pow_left₀ hL2 hup 8
  norm_num [mul_pow] at hp
  have hpow : Real.log (N:ℝ) ≤ Real.log (N:ℝ)^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hLN (show 1≤8 by norm_num)
  have hr := Real.rpow_le_self_of_one_le hLN (show (1/16:ℝ)≤1 by norm_num)
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤ Real.log (N:ℝ)^8),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_log hN0] at hb
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at ⊢
  nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearRestriction
namespace OAI

/-! Restricted typical energy at the original pretentious cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

theorem halasz_typical_near_original_restriction : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → (∀ a b, 0< a → 0< b → F (a*b)=F a*F b) → OneBounded F →
      ∀ τ M : ℝ, 0 ≤ M →
      (∀ v:ℝ, |v| ≤ (N:ℝ)/2 → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ E : Set ℝ, E ⊆ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4) →
      E ⊆ Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ)) →
      (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*(Real.exp (-4*M/5)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C,hC,hnear⟩ := halasz_typical_near_actual
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear,halasz_center_window_quarter_room,eventually_ge_atTop 2] with N hnear hroom hN2
  intro P Q J hP hPQ hlogP hJ hmax X _hNX hXN F hF1 hFm hFb τ M hM hd hsmall E hEN hEt
  by_cases hE : E.Nonempty
  · obtain ⟨t,ht⟩ := hE
    have hN := hEN ht
    have hT := hEt ht
    have hτ : |τ| ≤ (N:ℝ)/4+(Real.log N)^(1/16:ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hN.1,hN.2,hT.1,hT.2]
    have hroom' : |τ|+Real.log (2*N:ℕ)^8 ≤ (N:ℝ)/2 := by linarith
    exact halasz_restricted_near_energy _ N τ ((Real.log N)^(1/16:ℝ)) _
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤ N by omega))) _)
      (hnear P Q J hP hPQ hlogP hJ hmax F hF1 hFm hFb X τ ((N:ℝ)/2) M hXN hM hroom' hd hsmall) E hEt
  · rw [Set.not_nonempty_iff_eq_empty.mp hE]
    simp only [MeasureTheory.setIntegral_empty]
    positivity

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonFinalBand
namespace OAI

/-! One final original band works for both dyadic polynomials at N and
2N. The lower-endpoint margin absorbs the change in log-log scale, while
the upper endpoint remains below the smaller square-root cutoff. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset


lemma mrt_dyadic_log_comparison {N k : ℕ} (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log (N:ℝ)) (hLL : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hNk : N ≤ k) (hk : k ≤ 2*N) :
    Real.log (N:ℝ) ≤ Real.log (k:ℝ) ∧
    Real.log (k:ℝ) ≤ 2*Real.log (N:ℝ) ∧
    Real.log (Real.log (k:ℝ)) ≤ 2*Real.log (Real.log (N:ℝ)) := by
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hk0 : 0 < (k:ℝ) := hN0.trans_le (by exact_mod_cast hNk)
  have hLN0 : 0 < Real.log (N:ℝ) := by linarith
  have hlow := Real.log_le_log hN0 (show (N:ℝ) ≤ k by exact_mod_cast hNk)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hu : Real.log (k:ℝ) ≤ 2*Real.log (N:ℝ) := by
    have hh := Real.log_le_log hk0 (show (k:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast hk)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    linarith
  refine ⟨hlow,hu,?_⟩
  have hh := Real.log_le_log (hLN0.trans_le hlow) hu
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hLN0.ne'] at hh
  linarith







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallOffCenter
namespace OAI

/-! The no-small energy at the literal scale L=log N and outside the
neighborhood of an actual minimizing twist. The cofactor estimates follow
from off-center cancellation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_no_small_off_center_measurable (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) (τ : ℝ) :
    MeasurableSet (mrtNoSmallOffCenter P Q J N F τ) := by
  apply MeasurableSet.inter
  · exact measurableSet_Ioc.inter (mrt_no_small_band_measurable _ _ _
      (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) J)
  · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).abs).measurableSet

theorem mrt_no_small_off_center_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      2 ≤ mrtBaseResolution P Q (1/100) →
    ∀ J : ℕ, 1 ≤ J →
      200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
    ∀ τ : ℝ, |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
    (∫ t in mrtNoSmallOffCenter P Q J N F τ,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
      C*Real.log (Real.log N)/(Real.log N)^(1/80:ℝ) := by
  obtain ⟨C,hC,henergy⟩ := mrt_no_small_energy_sharp hprime
  refine ⟨C,hC,?_⟩
  have hlog : Filter.Tendsto (fun N:ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually henergy,hhigh.extra_cofactor,
    hlog.eventually mrt_extra_band_geometry,Filter.eventually_ge_atTop 2,
    hlog.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with N henergy hcofactor hg hN hL1
  intro F hF1 hFm hFb P Q hP hPQ hQ hres J hJ hlo hupper τ hτ hmin
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let L := Real.log (N:ℝ)
  let E := mrtNoSmallOffCenter P Q J N F τ
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (show 1< N by omega))
  have hLL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hp : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hupperlog : Real.log (mrtBandUpper Q J) ≤ Real.sqrt L := by
    calc
      _ ≤ Real.log (Real.exp (Real.sqrt L)) :=
        Real.log_le_log (show 0 < mrtBandUpper Q J from Real.exp_pos _) hupper
      _ = _ := Real.log_exp _
  have hmax : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
    intro i hi p hp'
    have hpU := (mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp').2
    have hu := (mrt_band_upper_log_mono hQ (mem_Icc.mp hi).1 (mem_Icc.mp hi).2).trans hupperlog
    have he := Real.exp_le_exp.mpr hu
    rw [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _)] at he
    exact hpU.trans he
  have hj : J-1 < J := by omega
  have hji : J-1+1=J := by omega
  have hET : E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) := by
    rw [Real.exp_log hN0]
    exact fun _ ht => ht.1.1
  apply henergy V F hFm hFb J (J-1) hj hp hmax P Q hP hPQ hQ hres
  · intro p hp'
    rw [hji] at hp' ⊢
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp'
    exact ⟨hh.1.le,hh.2⟩
  · simpa only [hji] using hlo
  · simpa only [hji] using hupperlog
  · exact (Real.exp_log hN0).le
  · exact mrt_no_small_off_center_measurable P Q J N F τ
  · exact hET
  · exact fun _ ht => ht.1.2
  · intro k hk t ht _hlarge
    let H := mrtExtraPrimeResolution L
    let a := mrtPrimeLogLower H k
    have hH : 0 < H := by change 0 < mrtExtraPrimeResolution L; linarith [hg.1]
    have ha : 1 ≤ a := mrt_prime_log_lower_one hH k
    have haU : a ≤ Real.exp (L/Real.log L) :=
      mrt_prime_log_lower_le_upper hH (Real.one_le_exp (by positivity)) (mem_Icc.mp hk).2
    exact hcofactor F hF1 hFm hFb P Q J hQ hupper
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
      (fun _ hp' => mrtPrimeBand_prime hp') a ha haU t τ
      (abs_le.mpr ⟨ht.1.1.1.le,ht.1.1.2⟩) hτ hmin ht.2


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallFull
namespace OAI

/-! Full actual no-small energy under a uniform cofactor estimate.
Unlike the off-center specialization, this statement has no high-prime
input and no minimizing-twist hypothesis. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrt_actual_no_small_measurable (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) :
    MeasurableSet (mrtActualNoSmall P Q J N F) :=
  measurableSet_Ioc.inter (mrt_no_small_band_measurable _ _ _
    (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) J)


lemma mrt_actual_bands_bounded {P Q B : ℝ} (hQ : 1 ≤ Real.log Q) (J : ℕ)
    (hupper : mrtBandUpper Q J ≤ B) :
    ∀ i ∈ Icc 1 J, ∀ p ∈ mrtPrimeBand (mrtBandLower P Q i) (mrtBandUpper Q i),
      (p:ℝ) ≤ B := by
  intro i hi p hp
  have hpU := (mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp).2
  have hu := mrt_band_upper_log_mono hQ (mem_Icc.mp hi).1 (mem_Icc.mp hi).2
  have he := Real.exp_le_exp.mpr hu
  rw [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _),
    Real.exp_log (show 0 < mrtBandUpper Q J from Real.exp_pos _)] at he
  exact hpU.trans (he.trans hupper)

theorem mrt_no_small_full_energy_sharp (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      2 ≤ mrtBaseResolution P Q (1/100) →
    ∀ J : ℕ, 1 ≤ J →
      200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
    (∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial
        (mrtPrimeBand (mrtExtraPrimeLower (Real.log N)) (mrtExtraPrimeUpper (Real.log N)))
        (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ)) →
    (∫ t in mrtActualNoSmall P Q J N F,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
      C*Real.log (Real.log N)/(Real.log N)^(1/80:ℝ) := by
  obtain ⟨C,hC,henergy⟩ := mrt_no_small_energy_sharp hprime
  refine ⟨C,hC,?_⟩
  have hlog : Filter.Tendsto (fun N:ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually henergy,hlog.eventually mrt_extra_band_geometry,
    Filter.eventually_ge_atTop 2,hlog.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with N henergy hg hN hL1
  intro F hFm hFb P Q hP hPQ hQ hres J hJ hlo hupper hcap
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let L := Real.log (N:ℝ)
  let E := mrtActualNoSmall P Q J N F
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hLL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hp : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hmax : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L) :=
    mrt_actual_bands_bounded hQ J hupper
  have hupperlog : Real.log (mrtBandUpper Q J) ≤ Real.sqrt L := by
    calc
      _ ≤ Real.log (Real.exp (Real.sqrt L)) :=
        Real.log_le_log (show 0 < mrtBandUpper Q J from Real.exp_pos _) hupper
      _ = _ := Real.log_exp _
  have hj : J-1 < J := by omega
  have hji : J-1+1=J := by omega
  have hET : E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) := by
    rw [Real.exp_log hN0]
    exact fun _ ht => ht.1
  apply henergy V F hFm hFb J (J-1) hj hp hmax P Q hP hPQ hQ hres
  · intro p hp'
    rw [hji] at hp' ⊢
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp'
    exact ⟨hh.1.le,hh.2⟩
  · simpa only [hji] using hlo
  · simpa only [hji] using hupperlog
  · exact (Real.exp_log hN0).le
  · exact mrt_actual_no_small_measurable P Q J N F
  · exact hET
  · exact fun _ ht => ht.2
  · intro k hk t ht _hlarge
    let H := mrtExtraPrimeResolution L
    let a := mrtPrimeLogLower H k
    have hH : 0 < H := by change 0 < mrtExtraPrimeResolution L; linarith [hg.1]
    exact hcap a (mrt_prime_log_lower_one hH k)
      (mrt_prime_log_lower_le_upper hH (Real.one_le_exp (by positivity)) (mem_Icc.mp hk).2)
      t (abs_le.mpr ⟨ht.1.1.le,ht.1.2⟩)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNoSmallSharp
namespace OAI

/-! Low-frequency no-small energy with the original published distance
cutoff and height. The upper half of the kernel is handled by its decay. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

theorem halasz_original_typical_no_small_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0< a → 0< b → F (a*b)=F a*F b) → OneBounded F →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ Real.log Q →
        2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
        200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
        mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ M : ℝ, 0 ≤ M →
        (∀ v : ℝ, |v| ≤ (N:ℝ)/2 → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      (∫ t in mrtActualNoSmall P Q J N F ∩ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*(Real.exp (-4*M/5)+
          Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)) := by
  obtain ⟨C₁,hC₁,hnear⟩ := halasz_typical_near_original_restriction
  obtain ⟨C₂,hC₂,hoff⟩ := mrt_no_small_off_center_energy_sharp hprime hhigh
  obtain ⟨C₃,hC₃,hfull⟩ := mrt_no_small_full_energy_sharp hprime
  refine ⟨C₁+C₂+C₃,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnear,hoff,hfull,halasz_large_minimum_extra_cofactor,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ))]
    with N hnear hoff hfull hlarge hL hLL
  intro F hF1 hFc hFb P Q hP hPQ hlogP hQ hres J hJ hlo hu X hNX hXN M hM hd
  have hFm : Multiplicative F := fun a b ha hb _ => hFc a b ha hb
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := mrtTypicalCoefficient (Icc 1 J) V F
  let E := mrtActualNoSmall P Q J N F ∩ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4)
  let G := fun t:ℝ => ‖mrtDyadicPolynomial B N t‖^2
  let δ := Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)
  let R : ℝ := 0
  have hR : 0 ≤ R := le_rfl
  have hδ : 0 ≤ δ := div_nonneg (by exact hLL.trans' (by norm_num)) (by positivity)
  have hE : E ⊆ Set.Ioc (-(N:ℝ)) N := fun _ ht => ht.1.1
  have hmax : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj
    have hh := Real.exp_le_exp.mpr (mrt_band_upper_log_mono hQ
      (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)
    rw [Real.exp_log (show 0 < mrtBandUpper Q j from Real.exp_pos _),
      Real.exp_log (show 0 < mrtBandUpper Q J from Real.exp_pos _)] at hh
    exact hh.trans hu
  have hGc : Continuous G := (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hGi : IntegrableOn G (Set.Ioc (-(N:ℝ)) N) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Nat.cast_nonneg (α:=ℝ) N])).mp
      (hGc.intervalIntegrable _ _)
  obtain ⟨τ,hτ,hmin⟩ := halasz_minimizing_twist F (2*N)
  have hτ' : |τ| ≤ 2*(N:ℝ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hτ
  have hmin' : ∀ v:ℝ, |v| ≤ 2*N →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmin
  by_cases hsmall : squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
      Real.log (Real.log (2*N:ℕ))/10
  · let I := Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ))
    have hn := hnear P Q J hP hPQ hlogP hJ hmax X hNX hXN
      F hF1 hFc hFb τ M hM hd hsmall (E∩I)
      (fun _ ht => ht.1.2) Set.inter_subset_right
    have ho := hoff F hF1 hFm hFb P Q (by linarith) hPQ hQ hres J hJ hlo hu τ hτ' hmin'
    have hsub : E \ I ⊆ mrtNoSmallOffCenter P Q J N F τ := by
      intro t ht
      refine ⟨ht.1.1,?_⟩
      change (Real.log N)^(1/16:ℝ) ≤ |t-τ|
      have hout := ht.2
      change ¬(τ-(Real.log N)^(1/16:ℝ) < t ∧ t ≤ τ+(Real.log N)^(1/16:ℝ)) at hout
      by_cases htlo : τ-(Real.log N)^(1/16:ℝ) < t
      · have hhi : τ+(Real.log N)^(1/16:ℝ) < t := by
          push Not at hout
          exact hout htlo
        rw [abs_of_nonneg (by
          have hp := Real.rpow_nonneg (show 0≤ Real.log (N:ℝ) by linarith) (1/16:ℝ)
          linarith)]
        linarith
      · have hle : t ≤ τ-(Real.log N)^(1/16:ℝ) := le_of_not_gt htlo
        rw [abs_of_nonpos (by
          have hp := Real.rpow_nonneg (show 0≤ Real.log (N:ℝ) by linarith) (1/16:ℝ)
          linarith)]
        linarith
    have hOff : mrtNoSmallOffCenter P Q J N F τ ⊆ Set.Ioc (-(N:ℝ)) N :=
      fun _ ht => ht.1.1
    have ho₀ : (∫ t in mrtNoSmallOffCenter P Q J N F τ, G t) ≤ C₂*δ := by
      simpa only [G,B,V,δ,mul_div_assoc] using ho
    have ho' : (∫ t in E \ I, G t) ≤ C₂*δ := by
      apply le_trans _ ho₀
      exact setIntegral_mono_set (hGi.mono_set hOff)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall hsub)
    have hpow : (Real.log N)^(-1/32:ℝ) ≤ δ := by
      calc
        _ ≤ (Real.log N)^(-1/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
        _ = 1/(Real.log N)^(1/80:ℝ) := by
          rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg (by linarith : 0≤ Real.log (N:ℝ))]
          simp only [one_div]
        _ ≤ δ := div_le_div_of_nonneg_right hLL (by positivity)
    have hn' : (∫ t in E∩I, G t) ≤ C₁*(R+Real.exp (-4*M/5)+δ) := by
      apply hn.trans
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      dsimp only [R]
      linarith
    have hsplit := integral_inter_add_sdiff (f := G) (s := E) (t := I)
      measurableSet_Ioc (hGi.mono_set hE)
    change (∫ t in E, G t) ≤ _
    rw [← hsplit]
    have hs := add_le_add hn' ho'
    have he : 0 ≤ Real.exp (-4*M/5) := (Real.exp_pos _).le
    dsimp [R] at *
    nlinarith [mul_nonneg hC₂.le (add_nonneg hR he),
      mul_nonneg hC₃.le (add_nonneg (add_nonneg hR he) hδ)]
  · have hminlarge : ∀ v:ℝ, |v| ≤ 2*N →
        (1/10:ℝ)*Real.log (Real.log (2*N:ℕ)) ≤
          squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
      intro v hv
      have hh := hmin' v hv
      linarith
    have hb := hlarge F hF1 hFm hFb hminlarge P Q J hQ hu
      (mrtPrimeBand (mrtExtraPrimeLower (Real.log N)) (mrtExtraPrimeUpper (Real.log N)))
      (fun _ hp => mrtPrimeBand_prime hp)
    have hh := hfull F hFm hFb P Q (by linarith) hPQ hQ hres J hJ hlo hu hb
    change (∫ t in E, G t) ≤ _
    have hh' : (∫ t in E, G t) ≤ C₃*δ := by
      apply le_trans _ (show (∫ t in mrtActualNoSmall P Q J N F,G t) ≤ C₃*δ by
        simpa only [G,B,V,δ,mul_div_assoc] using hh)
      exact setIntegral_mono_set
        (hGi.mono_set (fun _ ht => ht.1))
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun _ ht => ht.1))
    have he : 0 ≤ Real.exp (-4*M/5) := (Real.exp_pos _).le
    dsimp [R] at *
    nlinarith [mul_nonneg (add_nonneg hC₁.le hC₂.le) hδ,
      mul_nonneg (show 0≤ C₁+C₂+C₃ by positivity) (add_nonneg hR he)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalKernelSharp
namespace OAI

/-! The lower half of the short-window kernel uses distance information
only up to the original published cutoff and height. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_dyadic_log_error_sharp {N k : ℕ} (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log (N:ℝ)) (hLL : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hNk : N ≤ k) (hk : k ≤ 2*N) :
    Real.log (Real.log (k:ℝ))/(Real.log k)^(1/80:ℝ) ≤
      2*(Real.log (Real.log (N:ℝ))/(Real.log N)^(1/80:ℝ)) := by
  obtain ⟨hlow,_,hu⟩ := mrt_dyadic_log_comparison hN hL hLL hNk hk
  have hLN0 : 0 < Real.log (N:ℝ) := by linarith
  have hlpow := Real.rpow_le_rpow hLN0.le hlow (show (0:ℝ)≤1/80 by norm_num)
  calc
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log k)^(1/80:ℝ) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log N)^(1/80:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlpow
    _ = _ := by ring

theorem halasz_typical_kernel_bound_sharp_oai
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0< a → 0< b → F (a*b)=F a*F b) → OneBounded F →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ Real.log Q →
        2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u:ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      ∀ k ∈ ({N,2*N}:Finset ℕ), ∀ v:ℝ, 0 ≤ v → v ≤ (k:ℝ)/4 →
      (∫ t in Set.Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
          (mrtLogFamilyPolynomial
            (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
          (mrtLogFamilyThreshold P Q (1/100)) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) k t‖^2) ≤
        C*(Real.exp (-4*M/5)+
          Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))*(v/k+1) := by
  obtain ⟨C,hC,henergy⟩ := halasz_original_typical_no_small_energy_sharp hprime hhigh
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp henergy
  refine ⟨2*C,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ))]
    with N hNN hN2 hL hLL
  intro F hF1 hFm hFb P Q hP hPQ hlogP hQ hres J hJ hband X hNX hXN M hM hd k hk v hv hvk
  have hNk : N ≤ k := by simp only [mem_insert,mem_singleton] at hk; omega
  have hkN : k ≤ 2*N := by simp only [mem_insert,mem_singleton] at hk; omega
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0< k by omega)
  obtain ⟨hlo,hu⟩ := hband k hk
  have he := hN₀ k (hNN.trans hNk) F hF1 hFm hFb P Q hP hPQ hlogP hQ hres J hJ hlo hu
    X (by omega) (hXN.trans (by gcongr)) M hM
    (fun u hu => hd u (hu.trans (by
      have hh : (k:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hkN
      have hNXr : (N:ℝ) ≤ X := by exact_mod_cast hNX
      linarith)))
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  let G := fun t:ℝ => ‖mrtDyadicPolynomial B k t‖^2
  let E := Set.Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
    (mrtLogFamilyPolynomial
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
    (mrtLogFamilyThreshold P Q (1/100)) J
  let E₀ := mrtActualNoSmall P Q J k F ∩ Set.Ioc (-((k:ℝ)/4)) ((k:ℝ)/4)
  have hsub : E ⊆ E₀ := by
    intro t ht
    refine ⟨⟨⟨?_,?_⟩,ht.2⟩,⟨?_,?_⟩⟩ <;> linarith [ht.1.1,ht.1.2]
  have hGc : Continuous G := (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hGi : IntegrableOn G E₀ := by
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(k:ℝ)≤ k)).mp
      (hGc.intervalIntegrable (-(k:ℝ)) k)).mono_set
    exact fun _ ht => ht.1.1
  have htrunc : (∫ t in E,G t) ≤ ∫ t in E₀,G t :=
    setIntegral_mono_set hGi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hsub)
  have hδ := halasz_dyadic_log_error_sharp hN2 hL hLL hNk hkN
  let R := Real.exp (-4*M/5)
  let δ := Real.log (Real.log N)/(Real.log N)^(1/80:ℝ)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hδ0 : 0 ≤ δ := div_nonneg (zero_le_one.trans hLL) (by positivity)
  have hb : (∫ t in E,G t) ≤ (2*C)*(R+δ) := by
    apply htrunc.trans (he.trans ?_)
    dsimp only [R,δ] at ⊢
    nlinarith [mul_le_mul_of_nonneg_left hδ hC.le, mul_nonneg hC.le hR]
  change (∫ t in E,G t) ≤ _
  apply hb.trans
  change (2*C)*(R+δ) ≤ (2*C)*(R+δ)*(v/k+1)
  exact le_mul_of_one_le_right (by positivity) (by
    have hh : 0 ≤ v/(k:ℝ) := div_nonneg hv hk0.le
    linarith)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_typical_kernel_bound_sharp_oai := @OAI.TwoPointCorrelations.halasz_typical_kernel_bound_sharp_oai
