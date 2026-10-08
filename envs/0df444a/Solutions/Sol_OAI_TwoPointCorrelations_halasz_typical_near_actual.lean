-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_typical_near_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:40:07.815603+00:00
-- url     : https://prove2.me/submissions/d3fdbbc6-0157-414b-b320-2cb44fd52ff9

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_near_renormalization
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_mean_value
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_near_bound

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate



lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _






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

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





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











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance
namespace OAI

/-! Mertens turns the exact smooth Euler product into the usual
`log N * exp(-distance)` estimate, uniformly in the bounded coefficient. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_sievePrimesUpTo_nat (N : ℕ) : sievePrimesUpTo (N : ℝ) = primesUpTo N := by
  ext p
  simp only [sievePrimesUpTo, primesUpTo, mem_filter, mem_Iic, Nat.floor_natCast,
    mem_range, Nat.lt_succ_iff]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothBounds
namespace OAI

/-! Continuity and uniform bounds for the actual smooth Euler series on
the Perron line. Only values at positive integers are bounded. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

lemma halasz_distance_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    0 ≤ squaredDistance f (mrtArchimedeanTwist t) N := by
  unfold squaredDistance
  apply sum_nonneg
  intro p hp
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hn : ‖f p * star (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDistanceCutoff
namespace OAI

/-! A fixed-power change of the prime cutoff changes the squared
pretentious distance by an absolute constant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.ComplexConjugate

lemma halasz_prime_cutoff_subset {n N : ℕ} (hn : n ≤ N) : primesUpTo n ⊆ primesUpTo N := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega), hprime⟩

theorem halasz_distance_cutoff_loss : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (n N : ℕ), 2 ≤ n → n ≤ N → N ≤ n ^ 3 →
    ∀ t : ℝ, squaredDistance f (mrtArchimedeanTwist t) N ≤
      squaredDistance f (mrtArchimedeanTwist t) n + K := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  let K := 2 * (Real.log 3 + 2 * |C|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro f hf n N hn hnN hNcube t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlNn : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNcube)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hll : Real.log (Real.log (N : ℝ)) - Real.log (Real.log (n : ℝ)) ≤ Real.log 3 := by
    have h := Real.log_le_log hlN hlNn
    rw [Real.log_mul (by norm_num) hln.ne'] at h
    linarith
  have hmN := hC (N : ℝ) (by exact_mod_cast (show 2 ≤ N by omega))
  have hmn := hC (n : ℝ) (by exact_mod_cast hn)
  rw [mrt_sievePrimesUpTo_nat] at hmN hmn
  have hmass : (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
      (∑ p ∈ primesUpTo n, (1 : ℝ) / p) ≤ Real.log 3 + 2 * |C| := by
    have ha := (abs_le.mp hmN).2
    have hb := (abs_le.mp hmn).1
    linarith [le_abs_self C]
  let P := primesUpTo N \ primesUpTo n
  have hsub := halasz_prime_cutoff_subset hnN
  have hterm (p : ℕ) (hp : p ∈ P) :
      (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) := by
    have hprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hnrm : ‖f p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
      simpa only [norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
    have hre := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hnrm)
    have hnum : 1 - (f p * conj (mrtArchimedeanTwist t p)).re ≤ 2 := by linarith
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hnum (Nat.cast_nonneg p)
  have hs := sum_le_sum (fun p hp => hterm p hp)
  rw [← mul_sum] at hs
  have heDist := sum_sdiff hsub (f := fun p : ℕ =>
    (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ))
  have heMass := sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
  change (∑ p ∈ P, (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ)) +
    squaredDistance f (mrtArchimedeanTwist t) n = squaredDistance f (mrtArchimedeanTwist t) N at heDist
  change (∑ p ∈ P, (1 : ℝ) / p) + (∑ p ∈ primesUpTo n, (1 : ℝ) / p) =
    (∑ p ∈ primesUpTo N, (1 : ℝ) / p) at heMass
  dsimp [K]
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTwistedMean
namespace OAI

/-! Height translation for the ordinary mean estimate. This is the
form applied to Dirichlet polynomials on a vertical line. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_twist_add (t u : ℝ) (n : ℕ) :
    mrtArchimedeanTwist (t + u) n = mrtArchimedeanTwist t n * mrtArchimedeanTwist u n := by
  simp only [mrtArchimedeanTwist, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_twist_mul (t : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    mrtArchimedeanTwist t (a * b) = mrtArchimedeanTwist t a * mrtArchimedeanTwist t b := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [mrtArchimedeanTwist, Nat.cast_mul, Real.log_mul har.ne' hbr.ne',
    mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]


lemma halasz_twisted_one (f : ℕ → ℂ) (hf : f 1 = 1) (t : ℝ) :
    halaszTwistedFunction f t 1 = 1 := by simp [halaszTwistedFunction, mrtArchimedeanTwist, hf]

lemma halasz_twisted_mul (f : ℕ → ℂ)
    (hf : ∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b)
    (t : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    halaszTwistedFunction f t (a * b) = halaszTwistedFunction f t a * halaszTwistedFunction f t b := by
  simp only [halaszTwistedFunction, hf a b ha hb, halasz_twist_mul t ha hb, map_mul]
  ring

lemma halasz_twisted_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (t : ℝ) :
    OneBounded (halaszTwistedFunction f t) := by
  intro n hn
  simpa only [halaszTwistedFunction, norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one]
    using hf n hn

lemma halasz_twisted_distance (f : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    squaredDistance (halaszTwistedFunction f t) (mrtArchimedeanTwist u) N =
      squaredDistance f (mrtArchimedeanTwist (t + u)) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [halaszTwistedFunction, halasz_twist_add, map_mul, mul_assoc]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalScale
namespace OAI

/-! The cutoff above the typical bands costs a power of log N and keeps
the central distance saving. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma halasz_typical_decay {M : ℝ} (_hM : 0 ≤ M) :
    (M+1)*Real.exp (-M/2)  ≤  10*Real.exp (-2*M/5) := by
  have hh := Real.add_one_le_exp (M/10)
  have hm : M+1  ≤  10*Real.exp (M/10) := by linarith
  calc
    _  ≤  (10*Real.exp (M/10))*Real.exp (-M/2) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,←Real.exp_add]
      rw [show M/10 + -M/2 = -2*M/5 by ring]

lemma halasz_typical_cutoff_scale :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.exp (Real.sqrt (Real.log (N:ℝ))) ∧
      Real.log (N:ℝ)^16 ≤ Real.exp (Real.sqrt (Real.log (N:ℝ))) ∧
      Real.exp (Real.sqrt (Real.log (N:ℝ))) ≤ (N:ℝ)/2 ∧
      (1+Real.log (Real.exp (Real.sqrt (Real.log (N:ℝ)))))*
        Real.log (Real.log N)/Real.log N  ≤  (Real.log N)^(-1/4:ℝ) := by
  have hl : Tendsto (fun N:ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/4 by norm_num)).bound
    (show (0:ℝ) < 1/32 by norm_num)
  filter_upwards [hl.eventually hsmall,
    hl.eventually (eventually_ge_atTop (max 16 (4*Real.log 2))),
    eventually_ge_atTop 2] with N hsmall hL hN
  let L := Real.log (N:ℝ)
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hp : 0 ≤ L^(1/4:ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.norm_eq_abs,abs_of_nonneg hlog,Real.norm_eq_abs,
    abs_of_nonneg hp] at hsmall
  have hquarter : L^(1/4:ℝ) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hroot : Real.sqrt L ≤ L/2 := by
    nlinarith [Real.sq_sqrt hL0.le,Real.sqrt_nonneg L]
  refine ⟨Real.one_le_exp (Real.sqrt_nonneg _),?_,?_,?_⟩
  · have hpos : 0 < L^16 := pow_pos hL0 16
    rw [←Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp [L] at hquarter hsmall ⊢
    linarith
  · apply (le_div_iff₀ (show (0:ℝ) < 2 by norm_num)).mpr
    change Real.exp (Real.sqrt L)*2 ≤ (N:ℝ)
    have hlog2 : 4*Real.log 2 ≤ L := (le_max_right _ _).trans hL
    calc
      _ = Real.exp (Real.sqrt L+Real.log 2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hN0
  · rw [Real.log_exp]
    change (1+Real.sqrt L)*Real.log L/L ≤ L^(-1/4:ℝ)
    calc
      _  ≤  (2*Real.sqrt L)*((1/2:ℝ)*L^(1/4:ℝ))/L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul
        · linarith
        · linarith
        · exact hlog
        · positivity
      _ = L^(-1/4:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have he : L^(1/2:ℝ)*L^(1/4:ℝ)/L=L^(-1/4:ℝ) := by
          rw [←Real.rpow_add hL0]
          calc
            _ = L^((1/2:ℝ)+1/4)/L^(1:ℝ) := by rw [Real.rpow_one]
            _ = L^((1/2:ℝ)+1/4-1) := (Real.rpow_sub hL0 _ _).symm
            _ = _ := by norm_num
        convert (preTransparency := .instances) he using 1
        ring

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






lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandSeparation
namespace OAI

/-! The actual MRT bands are disjoint, as required by the corrected
Ramaré decomposition; no disjointness hypothesis on those bands remains. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_adjacent_band_gap (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q j < mrtBandLower P Q (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hpow : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  apply Real.exp_lt_exp.mpr
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogQ.le j)
  have hp : 0 < (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by positivity
  nlinarith

lemma mrt_band_lower_monotone (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandLower P Q i ≤ mrtBandLower P Q j := by
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  refine Nat.le_induction le_rfl (fun k hk ih => ?_) j hij
  exact ih.trans (((mrt_band_endpoints P Q k (hi.trans hk) hP hPQ hlogQ).2).trans
    (mrt_adjacent_band_gap P Q k (hi.trans hk) hP hPQ hlogP).le)

lemma mrt_band_gap (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q i < mrtBandLower P Q j :=
  (mrt_adjacent_band_gap P Q i hi hP hPQ hlogP).trans_le
    (mrt_band_lower_monotone P Q (i + 1) j (by omega) (by omega) hP hPQ hlogP)

theorem mrt_actual_bands_pairwise_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Set.univ : Set {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)})
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := mem_Icc.mp i.property
  have hj := mem_Icc.mp j.property
  have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hip := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q i hi.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpi
  have hjp := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q j hj.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpj
  change mrtBandLower P Q i < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q i at hip
  change mrtBandLower P Q j < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q j at hjp
  rcases lt_or_gt_of_ne hn with hij' | hji'
  · have hgap := mrt_band_gap P Q i j hi.1 hij' hP hPQ hlogP
    linarith
  · have hgap := mrt_band_gap P Q j i hj.1 hji' hP hPQ hlogP
    linarith

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





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseTranslation
namespace OAI

/-! Frequency translation and the actual typical-set coefficient. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_power_phase_frequency_add (t u x : ℝ) :
    halaszPowerPhase (t + u) x = halaszPowerPhase t x * halaszPowerPhase u x := by
  simp only [halaszPowerPhase, neg_add, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_power_phase_twist (t : ℝ) (n : ℕ) :
    conj (mrtArchimedeanTwist t n) = halaszPowerPhase t n := by
  rw [mrtArchimedeanTwist, ← Complex.exp_conj]
  unfold halaszPowerPhase
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring


lemma halasz_twisted_dyadic (F : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    mrtDyadicPolynomial (halaszTwistedFunction F t) N u = mrtDyadicPolynomial F N (t + u) := by
  rw [halasz_dyadic_phase, halasz_dyadic_phase]
  apply sum_congr rfl
  intro n _
  rw [halaszTwistedFunction, halasz_power_phase_twist, halasz_power_phase_frequency_add]
  ring

lemma halasz_typical_twist {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtTypicalCoefficient J P (halaszTwistedFunction F t) =
      halaszTwistedFunction (mrtTypicalCoefficient J P F) t := by
  funext n
  by_cases ht : mrtTypical J P n <;>
    simp [mrtTypicalCoefficient, halaszTwistedFunction, ht]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCenteredPrefix
namespace OAI

/-! Centered prefix cancellation from the proved general Halasz theorem.
The lower bound on distance stays at the original large cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.ComplexConjugate

lemma halasz_distance_monotone (F : ℕ → ℂ) (hF : OneBounded F) (t : ℝ) :
    Monotone (fun N => squaredDistance F (mrtArchimedeanTwist t) N) := by
  intro n N hnN
  unfold squaredDistance
  apply sum_le_sum_of_subset_of_nonneg (halasz_prime_cutoff_subset hnN)
  intro p hp _
  have hp0 := (mem_filter.mp hp).2.pos
  have hn : ‖F p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_conj, mrtArchimedeanTwist_norm, mul_one] using hF p hp0
  exact div_nonneg (sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)) (Nat.cast_nonneg p)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNearScales
namespace OAI

/-! The near-center comparison is uniform on every prefix of the actual
dyadic interval, with the pretentious condition at the original cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.ComplexConjugate

lemma halasz_loglog_power_cutoff (N X : ℕ) (hN : 2 ≤ N) (hX2 : 2 ≤ X) (hX : X ≤ N ^ 3) :
    Real.log (Real.log X) ≤ Real.log (Real.log N) + Real.log 3 := by
  have hX1 : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := Real.log_le_log (zero_lt_one.trans hX1)
    (show (X : ℝ) ≤ (N : ℝ) ^ 3 by exact_mod_cast hX)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hh' := Real.log_le_log (Real.log_pos hX1) hh
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hLN.ne'] at hh'
  linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandDensity
namespace OAI

/-! Literal natural-indexed MRT bands in the dyadic density and
pairwise-disjointness interfaces used by the energy estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma halasz_actual_bands_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Icc 1 J : Set ℕ)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  have hh := mrt_actual_bands_pairwise_disjoint P Q J hP hPQ hlogP
  intro i hi j hj hij
  exact @hh ⟨i, hi⟩ (Set.mem_univ _) ⟨j, hj⟩ (Set.mem_univ _)
    (fun he => hij (congrArg Subtype.val he))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalPrefix
namespace OAI

/-! Uniform centered typical prefixes. The distance and frequency range
are still imposed at the original cutoff, while the typical bands remain
fixed as the prefix varies. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem halasz_typical_centered_prefix : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, X ≤ N^3 →
      ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ t T M : ℝ, 0 ≤ M → |t|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ u : ℝ, |u| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → Set.PairwiseDisjoint (J : Set ι) P →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖  ≤
        C*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ))*k := by
  obtain ⟨C₀,X₀,hC₀,hmean⟩ := halasz_typical_mean_value
  obtain ⟨K,hK,hcut⟩ := halasz_distance_cutoff_loss
  let C := C₀*(10*Real.exp (2*K/5)+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  obtain ⟨N₀,hscale⟩ := eventually_atTop.mp halasz_typical_cutoff_scale
  have hx : ∀ᶠ N : ℕ in atTop, X₀ ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X₀)
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop 2,hx,hl]
    with N hNN hN2 hXN hLN
  intro X hX F hF1 hFm hFb t T M _hM hT hdist ι J P hP hdis hupper k hk
  have hNk := (mem_Icc.mp hk).1
  have hk2 : 2 ≤ k := hN2.trans hNk
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlogk : Real.log (N:ℝ) ≤ Real.log (k:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hNk)
  have hlk : 0 < Real.log (k:ℝ) := by linarith
  obtain ⟨hR,hRlo,hRhi,herr⟩ := hscale k (hNN.trans hNk)
  let G := halaszTwistedFunction F t
  let M' := max 0 (M-K)
  have hPk : ∀ j ∈ J, P j ⊆ primesUpTo k := by
    intro j hj p hp
    have hu := (hupper j hj p hp).trans
      (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogk))
    have hpN : (p:ℝ) ≤ k := hu.trans (hRhi.trans (by linarith))
    exact mem_filter.mpr ⟨mem_range.mpr (by exact_mod_cast (show (p:ℝ) < (k:ℝ)+1 by linarith)),hP j hj p hp⟩
  have hd : ∀ u ∈ Set.Icc (-(Real.log (k:ℝ)^8)) (Real.log (k:ℝ)^8),
      M' ≤ squaredDistance G (mrtArchimedeanTwist u) k := by
    intro u hu
    rw [halasz_twisted_distance]
    apply max_le
    · exact halasz_distance_nonneg F hFb k (t+u)
    · have hloghi : Real.log (k:ℝ) ≤ Real.log (2*N:ℕ) :=
        Real.log_le_log hk0 (by exact_mod_cast (mem_Icc.mp hk).2)
      have hheight : |t+u| ≤ T := calc
        |t+u| ≤ |t|+|u| := abs_add_le _ _
        _  ≤  |t|+Real.log (k:ℝ)^8 := add_le_add le_rfl (abs_le.mpr hu)
        _  ≤  |t|+Real.log (2*N:ℕ)^8 := by gcongr
        _  ≤  T := hT
      have hb := hdist (t+u) hheight
      by_cases hkX : k ≤ X
      · have hc := hcut F hFb k X hk2 hkX (hX.trans (by gcongr)) (t+u)
        linarith
      · have hc := halasz_distance_monotone F hFb (t+u) (by omega : X ≤ k)
        linarith
  have hh := hmean k (hXN.trans (by exact_mod_cast hNk)) G
    (halasz_twisted_one F hF1 t) (halasz_twisted_mul F hFm t)
    (halasz_twisted_oneBounded F hFb t) J P hPk hdis
    (Real.exp (Real.sqrt (Real.log (k:ℝ)))) hR hRlo hRhi
    (fun j hj p hp => (hupper j hj p hp).trans
      (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogk))) M' (le_max_left _ _) hd
  have hdec : (M'+1)*Real.exp (-M'/2) ≤
      10*Real.exp (2*K/5)*Real.exp (-2*M/5) := by
    apply (halasz_typical_decay (le_max_left 0 (M-K))).trans
    calc
      10*Real.exp (-2*M'/5) ≤ 10*Real.exp (-2*(M-K)/5) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have := le_max_right 0 (M-K)
        dsimp [M']
        linarith
      _ = _ := by
        rw [show -2*(M-K)/5 = 2*K/5 + (-2*M/5) by ring,Real.exp_add]
        ring
  have hpow : (Real.log (k:ℝ))^(-1/4:ℝ) ≤ (Real.log N)^(-1/4:ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlogk (by norm_num)
  have hfinal : C₀*((M'+1)*Real.exp (-M'/2)+
      (1+Real.log (Real.exp (Real.sqrt (Real.log (k:ℝ)))))*Real.log (Real.log k)/Real.log k)  ≤
      C*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ)) := by
    have he : 0 ≤ Real.exp (-2*M/5) := (Real.exp_pos _).le
    have hp : 0 ≤ (Real.log N)^(-1/4:ℝ) := Real.rpow_nonneg (by linarith) _
    have hc : 0 ≤ 10*Real.exp (2*K/5) := by positivity
    calc
      _ ≤ C₀*(10*Real.exp (2*K/5)*Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hdec (herr.trans hpow)) hC₀.le
      _ ≤ C₀*((10*Real.exp (2*K/5)+1)*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hC₀.le
        nlinarith [mul_nonneg hc hp]
      _ = _ := by dsimp [C]; ring
  have heq : halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k =
      ∑ n ∈ Icc 1 k, mrtTypicalCoefficient J P G n := by
    rw [halasz_typical_twist]
    simp [halaszPhaseMean,halaszPowerPhase]
  rw [heq]
  apply hh.trans
  calc
    _ = (C₀*((M'+1)*Real.exp (-M'/2)+
      (1+Real.log (Real.exp (Real.sqrt (Real.log (k:ℝ)))))*Real.log (Real.log k)/Real.log k))*k := by ring
    _  ≤  _ := mul_le_mul_of_nonneg_right hfinal hk0.le

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



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearMaskSum
namespace OAI

/-! Summing the phase-shaped near-center approximation over missing-band
masks. The error is summed before integration; the centered typical prefix
is retained, so its density contribution will be squared in energy. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma mrt_typical_phase_mean_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (t u : ℝ) (k : ℕ) :
    halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k =
      ∑ I ∈ J.powerset, (-1 : ℂ)^I.card *
        halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k := by
  unfold halaszPhaseMean halaszTwistedFunction
  simp_rw [mrtTypicalCoefficient_expansion, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro I _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  ring

lemma mrt_typical_phase_error {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (t u : ℝ) (k : ℕ) (E : ℝ)
    (hE : ∀ I ∈ J.powerset,
      ‖halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) 0 k‖ ≤ E) :
    ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k -
      (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
        halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖ ≤
      (2 : ℝ)^J.card * E := by
  rw [mrt_typical_phase_mean_expansion, mrt_typical_phase_mean_expansion, mul_sum,
    ← sum_sub_distrib]
  calc
    _ ≤ ∑ I ∈ J.powerset, ‖(-1 : ℂ)^I.card *
        halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k -
      (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
        ((-1 : ℂ)^I.card *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) 0 k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I ∈ J.powerset, E := by
      apply sum_le_sum
      intro I hI
      have he (a b c d : ℂ) : a*b-c*(a*d)=a*(b-c*d) := by ring
      rw [he, norm_mul, norm_pow]
      simpa only [norm_neg, norm_one, one_pow, one_mul] using hE I hI
    _ = _ := by simp [sum_const, nsmul_eq_mul, card_powerset]

/-- A missing-prime mask is allowed uniformly at each prefix, while the
small-distance hypothesis stays at the single original cutoff `2*N`. -/
theorem mrt_missing_near_prefix :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) (2*N) ≤
        Real.log (Real.log (2*N : ℕ))/10 →
      ∀ u : ℝ, |u| ≤ (Real.log N)^(1/(16:ℝ)) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F Q) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F Q) t) 0 k‖ ≤
        (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-1/(16:ℝ)) * k := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp halasz_near_renormalization
  have hLL : ∀ᶠ N : ℕ in atTop, 4*Real.log 3 ≤ Real.log (Real.log (N:ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 4,hLL] with N hNK hN4 hLLN
  intro F hF1 hFm hFb Q hQ hQcut t hD u hu k hk
  have hNk := (mem_Icc.mp hk).1
  have hk2 := (mem_Icc.mp hk).2
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0< N by omega)
  have hLN : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1< N by omega))
  have hLNk : Real.log (N:ℝ) ≤ Real.log k := Real.log_le_log hN0 (by exact_mod_cast hNk)
  have hLLNk : Real.log (Real.log (N:ℝ)) ≤ Real.log (Real.log k) :=
    Real.log_le_log hLN hLNk
  have hpow : 2*N ≤ N^3 := by
    have hs : 2 ≤ N^2 := by nlinarith
    calc
      2*N ≤ N^2*N := Nat.mul_le_mul_right N hs
      _ = N^3 := by ring
  have hLL2 := halasz_loglog_power_cutoff N (2*N) (by omega) (by omega) hpow
  have hDk : squaredDistance F (mrtArchimedeanTwist t) k ≤ Real.log (Real.log k)/8 := by
    have hm := halasz_distance_monotone F hFb t hk2
    linarith
  have hcut (p : ℕ) (hp : p ∈ Q) : (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log k)) :=
    (hQcut p hp).trans (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hLNk))
  have huk : |u| ≤ (Real.log k)^(1/(16:ℝ)) :=
    hu.trans (Real.rpow_le_rpow hLN.le hLNk (by norm_num))
  have hh := hK k (hNK.trans hNk) F hF1 hFm hFb Q hQ hcut t hDk u huk
  apply hh.trans
  have hr := Real.rpow_le_rpow_of_nonpos hLN hLNk (by norm_num : (-1/(16:ℝ))≤0)
  have hc : 0 ≤ 36*(halaszPrimePowerLogConstant+1)*Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) * k *
        (Real.log N)^(-1/(16:ℝ)) := by gcongr
    _ = _ := by ring

/-- Finite inclusion-exclusion preserves the centered typical prefix. -/
theorem mrt_typical_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) (2*N) ≤
        Real.log (Real.log (2*N : ℕ))/10 →
      ∀ u : ℝ, |u| ≤ (Real.log N)^(1/(16:ℝ)) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖ ≤
        (2:ℝ)^J.card * (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-1/(16:ℝ)) * k := by
  filter_upwards [mrt_missing_near_prefix] with N hn
  intro ι J P hP hcut F hF1 hFm hFb t hD u hu k hk
  have hh := mrt_typical_phase_error J P F t u k
    ((36*(halaszPrimePowerLogConstant+1)*Real.exp 8) * (Real.log N)^(-1/(16:ℝ)) * k) ?_
  · convert (preTransparency := .instances) hh using 1; ring
  intro I hI
  apply hn F hF1 hFm hFb (I.biUnion P) _ _ t hD u hu k hk
  · intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    exact hP j (mem_powerset.mp hI hj) p hp
  · intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    exact hcut j (mem_powerset.mp hI hj) p hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearBandSum
namespace OAI

/-! The actual MRT band count absorbs the finite near-mask sum into a
uniform logarithmic error while retaining the centered typical amplitude. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

/-- Near-center renormalization for the literal family of original bands.
The `-3/50` exponent leaves room for the finite inclusion-exclusion cost. -/
theorem mrt_band_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ P Q : ℝ, ∀ J : ℕ,
      1≤ Real.log Q → 1≤ J →
      (∀ j∈Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ τ : ℝ, squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ u : ℝ, |u|≤(Real.log N)^(1/16:ℝ) → ∀ k∈Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) τ) u k -
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*
          halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J)
            (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) τ) 0 k‖ ≤
        (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-3/50:ℝ)*k := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [mrt_typical_near_renormalization,hlog.eventually halasz_band_power_cost,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with N hnear hcost hLN
  intro P Q J hQ hJ hmax F hF1 hFm hFb τ hsmall u hu k hk
  have hupper : Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt (Real.log N) := by
    have hh := Real.log_le_log (show 0 < mrtBandUpper Q J from Real.exp_pos _)
      (hmax J (mem_Icc.mpr ⟨hJ,le_rfl⟩))
    rw [Real.log_exp] at hh
    linarith [Real.sqrt_nonneg (Real.log (N:ℝ))]
  have hcount : (2:ℝ)^(Icc 1 J).card ≤ (Real.log N)^(1/1000:ℝ) := by
    simpa using hcost Q J hQ hupper
  have hb : ∀ j∈Icc 1 J, ∀ p∈mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j),
      (p:ℝ)≤ Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj p hp
    exact ((mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp).2).trans (hmax j hj)
  have hh := hnear (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hb F hF1 hFm hFb τ hsmall u hu k hk
  have hL0 : 0< Real.log (N:ℝ) := by linarith
  have hc : 0≤36*(halaszPrimePowerLogConstant+1)*Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  apply hh.trans
  calc
    _ ≤ (Real.log N)^(1/1000:ℝ) * (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
        (Real.log N)^(-1/16:ℝ)*k := by gcongr
    _ = (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
        ((Real.log N)^(1/1000:ℝ)*(Real.log N)^(-1/16:ℝ))*k := by ring
    _ ≤ _ := by
      rw [← Real.rpow_add hL0]
      have hp := Real.rpow_le_rpow_of_exponent_le hLN
        (show (1/1000:ℝ)+(-1/16:ℝ)≤(-3/50:ℝ) by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (Nat.cast_nonneg k)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearActual
namespace OAI

/-! The actual typical-band near energy retains exponential saving,
with no discarded-density term in the amplitude. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

theorem halasz_typical_near_actual_oai : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ (X : ℕ) (τ T M : ℝ), X ≤ N^3 → 0 ≤ M → |τ|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤ Real.log (Real.log (2*N:ℕ))/10 →
      (∫ u in -((Real.log N)^(1/16:ℝ))..((Real.log N)^(1/16:ℝ)),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N (τ+u)‖^2) ≤
        C*(Real.exp (-4*M/5)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C₀,hC₀,hcenter⟩ := halasz_typical_centered_prefix
  let D := 36*(halaszPrimePowerLogConstant+1)*Real.exp 8
  refine ⟨100*Real.pi*C₀^2+100*D^2,by positivity,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hcenter,mrt_band_near_renormalization,hl,eventually_ge_atTop 2]
    with N hcenter hnear hL hN
  intro P Q J hP hPQ hlogP hJ hmax F hF1 hFm hFb X τ T M hX hM hT hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J) V F) τ
  have hQ : 1 ≤ Real.log Q := hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hpr : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hupper : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj p hp
    exact ((mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp).2).trans (hmax j hj)
  have hc := hcenter X hX F hF1 hFm hFb τ T M hM hT hd (Icc 1 J) V hpr
    (halasz_actual_bands_disjoint P Q J hP hPQ hlogP) hupper
  have hD : 0 ≤ D := by dsimp [D,halaszPrimePowerLogConstant]; positivity
  have hn : ∀ u ∈ Set.Icc (-((Real.log N)^(1/16:ℝ))) ((Real.log N)^(1/16:ℝ)),
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k-(halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*
        halaszPhaseMean B 0 k‖ ≤ (D*(Real.log N)^(-3/50:ℝ))*k := by
    intro u hu k hk
    exact hnear P Q J hQ hJ hmax F hF1 (fun a b ha hb _ => hFm a b ha hb) hFb
      τ hsmall u (abs_le.mpr hu) k hk
  have hh := halasz_typical_near_bound B (by omega) C₀ D (Real.log N) M hC₀.le hD hL hc hn
  simpa only [B,halasz_twisted_dyadic] using hh

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_typical_near_actual_oai := @OAI.TwoPointCorrelations.halasz_typical_near_actual_oai
