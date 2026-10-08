-- Prove2me | solution 1 for OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.short_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:52:17.792482+00:00
-- url     : https://prove2.me/submissions/266dfef3-228c-41dc-84cd-66f25aa49cdc

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_logderiv
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_short_exponential_of_prime_estimates

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCosineMinorant
namespace OAI

/-! A three-harmonic minorant for the prime-phase defect in corrected
MRT Lemma A.4(ii). Its mean is 81/256, enough to retain the needed 1/10
after restricting primes above exp((log X)^(27/40)). -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_sqrt_polynomial_minorant (a : ℝ) (ha : 0 ≤ a) :
    (1-a^2)/2+(1-a^2)^2/8+(1-a^2)^3/16 ≤ 1-a := by
  have h : 0 ≤ (a-1)^4*(a^2+4*a+5)/16 := by positivity
  nlinarith only [h]

lemma halasz_cosine_three_harmonics (x : ℝ) :
    (81/256:ℝ)-(175/512)*Real.cos (2*x)+(7/256)*Real.cos (4*x)-
      (1/512)*Real.cos (6*x) ≤ 1-|Real.cos x| := by
  have h := halasz_sqrt_polynomial_minorant |Real.cos x| (abs_nonneg _)
  have hsq : |Real.cos x|^2 = Real.cos x^2 := sq_abs _
  rw [hsq] at h
  have hfour : Real.cos (4*x) = 2*(2*Real.cos x^2-1)^2-1 := by
    rw [show 4*x=2*(2*x) by ring,Real.cos_two_mul,Real.cos_two_mul]
  have hsix : Real.cos (6*x) = 4*(2*Real.cos x^2-1)^3-3*(2*Real.cos x^2-1) := by
    rw [show 6*x=3*(2*x) by ring,Real.cos_three_mul,Real.cos_two_mul]
  rw [hfour,hsix,Real.cos_two_mul]
  convert (preTransparency := .instances) h using 1; ring

/-- Three bounded prime-phase sums suffice; no Fourier approximation or
limit interchange is needed for this part of the repulsion argument. -/
theorem halasz_weighted_cosine_repulsion {ι : Type*} (P : Finset ι)
    (w θ : ι → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (E : ℝ)
    (h₁ : |∑ p ∈ P, w p*Real.cos (θ p)| ≤ E)
    (h₂ : |∑ p ∈ P, w p*Real.cos (2*θ p)| ≤ E)
    (h₃ : |∑ p ∈ P, w p*Real.cos (3*θ p)| ≤ E) :
    (81/256:ℝ)*(∑ p ∈ P, w p)-(95/256)*E ≤
      ∑ p ∈ P, w p*(1-|Real.cos (θ p/2)|) := by
  have hpoint (p : ι) (hp : p ∈ P) :=
    mul_le_mul_of_nonneg_left (halasz_cosine_three_harmonics (θ p/2)) (hw p hp)
  have hsum := sum_le_sum hpoint
  have hphase (p : ι) :
      2*(θ p/2)=θ p ∧ 4*(θ p/2)=2*θ p ∧ 6*(θ p/2)=3*θ p := by
    constructor
    · ring
    constructor <;> ring
  simp only [(hphase _).1,(hphase _).2.1,(hphase _).2.2,
    mul_sub,mul_add,sum_sub_distrib,sum_add_distrib] at hsum
  have hm (c : ℝ) (f : ι → ℝ) :
      (∑ p ∈ P, w p*(c*f p)) = c*(∑ p ∈ P, w p*f p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hm,hm,hm,← sum_mul] at hsum
  have ha := (abs_le.mp h₁).2
  have hb := (abs_le.mp h₂).1
  have hc := (abs_le.mp h₃).2
  simp only [mul_sub,sum_sub_distrib]
  linarith only [hsum,ha,hb,hc]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.PretentiousDistance
namespace OAI

/-!
# The pretentious distance used in ordinary two-point correlations

These definitions use the prime cutoff and the twist-height cutoff at the same
integer scale.  The finite-prime perturbation estimate below is Lemma
`lem:finite-prime-stability` of *Ordinary two-point correlations of
multiplicative functions* (24 September 2026).  It is elementary and does not
assume any analytic input.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter _root_.Finset





lemma characterTwist_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ‖characterTwist χ t n‖ ≤ 1 := by
  simpa only [characterTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
    χ.norm_le_one (n : ZMod q)








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














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


lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1


lemma mrtPrimeBand_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) =
      (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
        ∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ) := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p) (mrt_sievePrimesUpTo_mono hPQ)

/-- Uniform bounded-error reciprocal mass for every positive prime band. -/
theorem mrt_prime_band_mertens : ∃ C : ℝ, 0 ≤ C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      |(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) -
        (Real.log (Real.log Q) - Real.log (Real.log P))| ≤ C := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨2 * C, by positivity, ?_⟩
  intro P Q hP hPQ
  rw [mrtPrimeBand_mass hPQ]
  have hQ := hP.trans hPQ
  have he : (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
      (∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) -
      (Real.log (Real.log Q) - Real.log (Real.log P)) =
      ((∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) - Real.log (Real.log Q)) -
      ((∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) - Real.log (Real.log P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hC Q hQ, hC P hP])


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx

lemma halasz_prime_band_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) =
      (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
        ∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => Real.log (p : ℝ) / p)
    (mrt_sievePrimesUpTo_mono hPQ)

lemma halasz_prime_band_mertens {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    |(∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) -
        (Real.log Q - Real.log P)| ≤ 2 * halaszMertensConstant := by
  rw [halasz_prime_band_mass hPQ]
  have he : (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
      (∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) -
      (Real.log Q - Real.log P) =
      ((∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) - Real.log Q) -
      ((∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) - Real.log P) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by
    linarith [halasz_prime_prefix_mass hP, halasz_prime_prefix_mass (hP.trans hPQ)])

lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]

lemma halasz_prime_band_mass_le {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) ≤
      Real.log Q - Real.log P + 2 * halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_band_mertens hP hPQ)).2]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeTailMass
namespace OAI

/-! Mertens mass on power-logarithmic prime tails, uniformly in the
exponent. This is the common finite prime range in both VK applications. -/

namespace TwoPointCorrelations

open _root_.Finset


theorem mrt_prime_power_tail_mass :
    ∃ C : ℝ, 0≤ C ∧ ∀ a : ℝ, 0≤ a → a≤1 → ∀ X : ℕ,
      1≤ Real.log (X:ℝ) →
      (1-a)*Real.log (Real.log (X:ℝ))-C ≤
        ∑ p ∈ mrtPrimePowerTail a X, 1/(p:ℝ) := by
  obtain ⟨C,hC,hm⟩ := mrt_prime_band_mertens
  refine ⟨C,hC,?_⟩
  intro a ha ha1 X hL
  have hL0 : 0< Real.log (X:ℝ) := by linarith
  have hX0 : (0:ℝ)< X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL0)
  have hpow : 1≤(Real.log (X:ℝ))^a := Real.one_le_rpow hL ha
  have hP : 2≤ Real.exp ((Real.log (X:ℝ))^a) := by
    linarith [Real.add_one_le_exp ((Real.log (X:ℝ))^a)]
  have hPX : Real.exp ((Real.log (X:ℝ))^a) ≤ (X:ℝ) := by
    calc
      _ ≤ Real.exp (Real.log (X:ℝ)) := Real.exp_le_exp.mpr
        (Real.rpow_le_self_of_one_le hL ha1)
      _ = _ := Real.exp_log hX0
  have hh := (abs_le.mp (hm _ _ hP hPX)).1
  rw [Real.log_exp,Real.log_rpow hL0] at hh
  change (1-a)*Real.log (Real.log (X:ℝ))-C ≤
    ∑ p ∈ mrtPrimeBand (Real.exp ((Real.log (X:ℝ))^a)) X, 1/(p:ℝ)
  linarith

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

lemma mrt_prime_inverse_square_sum (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have hs : primesUpTo N ⊆ Ioo 0 (N + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨(mem_filter.mp hp).2.pos, mem_range.mp (mem_filter.mp hp).1⟩
  calc
    _ ≤ ∑ n ∈ Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEuler
namespace OAI

/-! The finite character Euler product and the real prime sum differ,
after taking log norm, by an absolute prime-square error. This reduces
the Liouville prime-tail estimate to a genuine Euler-product lower bound. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate _root_.Classical

lemma mrt_local_euler_log_error {z : ℂ} (hz : ‖z‖≤1/2) :
    |Real.log ‖(1-z)⁻¹‖-z.re| ≤ ‖z‖^2 := by
  have hz1 : ‖z‖<1 := by linarith
  have hi : (1-‖z‖)⁻¹≤2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0<1-‖z‖)).mpr
    linarith
  have hr : ‖Complex.log (1-z)⁻¹-z‖≤‖z‖^2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖^2*2/2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hh := (Complex.abs_re_le_norm (Complex.log (1-z)⁻¹-z)).trans hr
  simpa only [Complex.sub_re,Complex.log_re] using hh


theorem mrt_character_euler_log_error {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (N : ℕ) (S : Finset ℕ) (hS : S⊆primesUpTo N) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      (∑ p ∈ S, characterTwist χ t p/(p:ℂ)).re| ≤ 2 := by
  let z := fun p : ℕ => characterTwist χ t p/(p:ℂ)
  have hz (p : ℕ) (hp : p∈S) : ‖z p‖≤1/(p:ℝ) := by
    dsimp only [z]
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) (Nat.cast_nonneg p)
  have hhalf (p : ℕ) (hp : p∈S) : ‖z p‖≤1/2 := by
    have hp2 : (2:ℝ)≤ p := by exact_mod_cast (mem_filter.mp (hS hp)).2.two_le
    exact (hz p hp).trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hne (p : ℕ) (hp : p∈S) : 1-z p≠0 := by
    intro he
    have he' : z p=1 := (sub_eq_zero.mp he).symm
    have hh := hhalf p hp
    rw [he',norm_one] at hh
    norm_num at hh
  have hlog : Real.log ‖mrtCharacterPrimeEuler χ t S‖ =
      ∑ p ∈ S, Real.log ‖(1-z p)⁻¹‖ := by
    unfold mrtCharacterPrimeEuler
    rw [norm_prod]
    exact Real.log_prod (fun p hp => norm_ne_zero_iff.mpr (inv_ne_zero (hne p hp)))
  have hsq : (∑ p ∈ S, ‖z p‖^2) ≤ 2 := by
    calc
      _ ≤ ∑ p ∈ S, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        calc
          _ ≤ (1/(p:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) (hz p hp) 2
          _ = _ := by rw [div_pow,one_pow]
      _ ≤ ∑ p ∈ primesUpTo N, 1/(p:ℝ)^2 :=
        sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)
      _ ≤ 2 := mrt_prime_inverse_square_sum N
  rw [hlog,Complex.re_sum]
  change |(∑ p ∈ S, Real.log ‖(1-z p)⁻¹‖)-(∑ p ∈ S, (z p).re)|≤2
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans
    ((sum_le_sum (fun p hp => mrt_local_euler_log_error (hhalf p hp))).trans hsq)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerShift
namespace OAI

/-! Moving the finite character Euler product from Re(s)=1 to
Re(s)=1+delta costs a bounded amount when delta=1/log X. All constants
are independent of the character modulus and of the imaginary part. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_log_lipschitz_half {a b : ℝ} (ha : 1/2≤ a) (hb : 1/2≤ b) :
    |Real.log a-Real.log b|≤2*|a-b| := by
  have ha0 : 0< a := by linarith
  have hb0 : 0< b := by linarith
  have upper {x y : ℝ} (hx : 0< x) (hy : 1/2≤ y) :
      Real.log x-Real.log y≤2*|x-y| := by
    have hy0 : 0< y := by linarith
    calc
      _ = Real.log (x/y) := (Real.log_div (ne_of_gt hx) (ne_of_gt hy0)).symm
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hx hy0)
      _ = (x-y)/y := by field_simp
      _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hy0)
      _ ≤ 2*|x-y| := (div_le_iff₀ hy0).mpr (by nlinarith [abs_nonneg (x-y)])
  apply abs_le.mpr
  constructor
  · have hh := upper hb0 ha
    rw [abs_sub_comm b a] at hh
    linarith
  · exact upper ha0 hb

lemma mrt_local_euler_log_lipschitz {z w : ℂ}
    (hz : ‖z‖≤1/2) (hw : ‖w‖≤1/2) :
    |Real.log ‖(1-z)⁻¹‖-Real.log ‖(1-w)⁻¹‖|≤2*‖z-w‖ := by
  have hza : 1/2≤‖(1:ℂ)-z‖ := by
    have hh := norm_sub_norm_le (1:ℂ) z
    rw [norm_one] at hh
    linarith
  have hwa : 1/2≤‖(1:ℂ)-w‖ := by
    have hh := norm_sub_norm_le (1:ℂ) w
    rw [norm_one] at hh
    linarith
  have hn : |‖(1:ℂ)-z‖-‖(1:ℂ)-w‖|≤‖z-w‖ := by
    have hh := abs_norm_sub_norm_le ((1:ℂ)-z) ((1:ℂ)-w)
    rw [show (1-z)-(1-w)=w-z by ring, norm_sub_rev w z] at hh
    exact hh
  calc
    _ = |Real.log ‖(1:ℂ)-z‖-Real.log ‖(1:ℂ)-w‖| := by
      rw [norm_inv,norm_inv,Real.log_inv,Real.log_inv,neg_sub_neg,abs_sub_comm]
    _ ≤ 2*|‖(1:ℂ)-z‖-‖(1:ℂ)-w‖| := mrt_log_lipschitz_half hza hwa
    _ ≤ 2*‖z-w‖ := mul_le_mul_of_nonneg_left hn (by norm_num)


lemma mrt_character_euler_shift_local {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {δ : ℝ} (hδ : 0≤δ) {p : ℕ} (hp : p.Prime) :
    |Real.log ‖(1-characterTwist χ t p/(p:ℂ))⁻¹‖-
      Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹‖| ≤
          2*δ*(Real.log (p:ℝ)/(p:ℝ)) := by
  let z : ℂ := characterTwist χ t p/(p:ℂ)
  let r : ℝ := Real.exp (-δ*Real.log (p:ℝ))
  have hp0 : (0:ℝ)< p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ)≤ p := by exact_mod_cast hp.two_le
  have hl : 0≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hr0 : 0≤ r := (Real.exp_pos _).le
  have hr1 : r≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hr : 1-r≤δ*Real.log (p:ℝ) := by
    have hh := Real.add_one_le_exp (-δ*Real.log (p:ℝ))
    dsimp only [r]
    linarith
  have hz : ‖z‖≤1/(p:ℝ) := by
    dsimp only [z]
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) hp0.le
  have hz2 : ‖z‖≤1/2 := hz.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hzr : ‖z*(r:ℂ)‖≤1/2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
    exact (mul_le_of_le_one_right (norm_nonneg z) hr1).trans hz2
  have hd : ‖z-z*(r:ℂ)‖≤δ*(Real.log (p:ℝ)/(p:ℝ)) := by
    calc
      _ = ‖z‖*(1-r) := by
        rw [show z-z*(r:ℂ)=z*(1-(r:ℂ)) by ring, norm_mul,
          ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hr1)]
      _ ≤ (1/(p:ℝ))*(δ*Real.log (p:ℝ)) :=
        mul_le_mul hz hr (sub_nonneg.mpr hr1) (by positivity)
      _ = _ := by ring
  exact (mrt_local_euler_log_lipschitz hz2 hzr).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2))

theorem mrt_character_euler_shift_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {δ : ℝ} (hδ : 0≤δ) (X : ℕ) (S : Finset ℕ)
    (hS : S⊆primesUpTo X) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      Real.log ‖mrtCharacterShiftedEuler χ t δ S‖| ≤
        2*δ*(∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) := by
  have hp (p : ℕ) (hh : p∈S) : p.Prime := (mem_filter.mp (hS hh)).2
  have hz (p : ℕ) (hh : p∈S) : ‖characterTwist χ t p/(p:ℂ)‖≤1/2 := by
    rw [norm_div,Complex.norm_natCast]
    have h2 : (2:ℝ)≤ p := by exact_mod_cast (hp p hh).two_le
    exact (div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p)
      (Nat.cast_nonneg p)).trans (one_div_le_one_div_of_le (by norm_num) h2)
  have hr (p : ℕ) (hh : p∈S) :
      0≤ Real.exp (-δ*Real.log (p:ℝ)) ∧ Real.exp (-δ*Real.log (p:ℝ))≤1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have h1 : (1:ℝ)≤ p := by exact_mod_cast (hp p hh).one_le
    nlinarith [Real.log_nonneg h1]
  have hne {z : ℂ} (hh : ‖z‖≤1/2) : 1-z≠0 := by
    intro he
    have he' : z=1 := (sub_eq_zero.mp he).symm
    rw [he',norm_one] at hh
    norm_num at hh
  have hns (p : ℕ) (hh : p∈S) :
      1-(characterTwist χ t p/(p:ℂ))*(Real.exp (-δ*Real.log (p:ℝ)):ℂ)≠0 := by
    apply hne
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hr p hh).1]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hr p hh).2).trans (hz p hh)
  have hlog1 : Real.log ‖mrtCharacterPrimeEuler χ t S‖ =
      ∑ p ∈ S, Real.log ‖(1-characterTwist χ t p/(p:ℂ))⁻¹‖ := by
    rw [mrtCharacterPrimeEuler,norm_prod]
    exact Real.log_prod (fun p hh => norm_ne_zero_iff.mpr (inv_ne_zero (hne (hz p hh))))
  have hlog2 : Real.log ‖mrtCharacterShiftedEuler χ t δ S‖ =
      ∑ p ∈ S, Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹‖ := by
    rw [mrtCharacterShiftedEuler,norm_prod]
    exact Real.log_prod (fun p hh => norm_ne_zero_iff.mpr (inv_ne_zero (hns p hh)))
  rw [hlog1,hlog2,← sum_sub_distrib,Finset.mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum (fun p hh => mrt_character_euler_shift_local χ t hδ (hp p hh)))

theorem mrt_character_euler_logarithmic_shift {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {X : ℕ}
    (hX : 1≤ Real.log (X:ℝ)) (S : Finset ℕ) (hS : S⊆primesUpTo X) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) S‖| ≤
        2+2*halaszMertensConstant := by
  have hl0 : 0< Real.log (X:ℝ) := by linarith
  have hX1 : (1:ℝ)≤ X := by
    by_contra hh
    have hh' : (X:ℝ)<1 := lt_of_not_ge hh
    have hnatlt : X<1 := by exact_mod_cast hh'
    have hnat : X=0 := by omega
    norm_num [hnat] at hX
  have hs : (∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ))≤
      Real.log (X:ℝ)+halaszMertensConstant := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hS ?_)
    · simpa only [mrt_sievePrimesUpTo_nat] using halasz_prime_prefix_mass_le hX1
    · intro p hp _
      have hp1 : (1:ℝ)≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_le
      exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg p)
  calc
    _ ≤ 2*(1/Real.log (X:ℝ))*(∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) :=
      mrt_character_euler_shift_bound χ t (by positivity) X S hS
    _ ≤ 2*(1/Real.log (X:ℝ))*(Real.log (X:ℝ)+halaszMertensConstant) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2+2*halaszMertensConstant/Real.log (X:ℝ) := by
      field_simp [ne_of_gt hl0]
    _ ≤ 2+2*halaszMertensConstant := by
      have hh := div_le_self
        (mul_nonneg (by norm_num : (0:ℝ)≤2) halaszMertensConstant_nonneg) hX
      linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLSeries
namespace OAI

/-! The shifted finite character Euler factors are the actual Dirichlet
L-series factors. The logarithmic identity below uses the absolutely
convergent Euler product only in the half-plane Re(s)>1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.LSeries.notation

lemma mrt_character_shifted_factor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t eps : ℝ) {p : ℕ} (hp : p≠0) :
    χ p*(p:ℂ)^(-(1+(eps:ℂ)-(t:ℂ)*Complex.I)) =
      (characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ) := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp
  have he : -(1+(eps:ℂ)-(t:ℂ)*Complex.I) =
      -1+(-(eps:ℂ)+(t:ℂ)*Complex.I) := by ring
  rw [he,Complex.cpow_add _ _ hpC,Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hpC,← Complex.natCast_log]
  have hs : (Real.log (p:ℝ):ℂ)*(-(eps:ℂ)+(t:ℂ)*Complex.I) =
      (-eps*Real.log (p:ℝ):ℝ)+((t*Real.log (p:ℝ):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [hs,Complex.exp_add,← Complex.ofReal_exp]
  unfold characterTwist
  ring

theorem mrt_character_shifted_euler_limit {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {eps : ℝ} (heps : 0< eps) :
    Tendsto (fun N : ℕ => mrtCharacterShiftedEuler χ t eps (primesUpTo N)) atTop
      (nhds (L ↗χ (1+(eps:ℂ)-(t:ℂ)*Complex.I))) := by
  have hs : 1<(1+(eps:ℂ)-(t:ℂ)*Complex.I).re := by
    simpa using heps
  have hh := χ.LSeries_eulerProduct hs
  have hN : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  convert (preTransparency := .instances) hh.comp hN using 1
  funext N
  change (∏ p ∈ primesUpTo N,
    (1-(characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹) = _
  change _ = ∏ p ∈ primesUpTo N,
    (1-χ p*(p:ℂ)^(-(1+(eps:ℂ)-(t:ℂ)*Complex.I)))⁻¹
  apply prod_congr rfl
  intro p hp
  rw [mrt_character_shifted_factor χ t eps (mem_filter.mp hp).2.ne_zero]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPrimeTail
namespace OAI

/-! A uniform absolute bound for the prime tail at sigma=1+1/log X.
The proof groups primes into intervals whose logarithms have width log X
and applies Mertens' first theorem in each interval. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_finite_exp_sum (S : Finset ℕ) :
    (∑ k ∈ S, Real.exp (-(k:ℝ)))≤2 := by
  let r : ℝ := Real.exp (-1)
  have hr0 : 0≤ r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hr2 : r≤1/2 := by
    dsimp only [r]
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith [Real.add_one_le_exp 1])
  have he (k : ℕ) : Real.exp (-(k:ℝ))=r^k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  calc
    _ ≤ ∑' k : ℕ, r^k :=
      (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum S (by intros; positivity)
    _ = (1-r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    _ ≤ 2 := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ (by linarith : 0<1-r)).mpr (by linarith)

theorem mrt_character_prime_tail_bound {X : ℕ} (hX : 1≤ Real.log (X:ℝ))
    (S : Finset ℕ) (hS : ∀ p∈S, p.Prime ∧ X< p) :
    (∑ p ∈ S, Real.exp (-Real.log (p:ℝ)/Real.log (X:ℝ))/(p:ℝ)) ≤
      4+4*halaszMertensConstant := by
  let L : ℝ := Real.log (X:ℝ)
  let bin : ℕ → ℕ := fun p => ⌊Real.log (p:ℝ)/L⌋₊
  let K := S.image bin
  have hL : 1≤ L := hX
  have hL0 : 0< L := by linarith
  have hC : 0≤ halaszMertensConstant := halaszMertensConstant_nonneg
  have hpdata (p : ℕ) (hp : p∈S) :
      0<(p:ℝ) ∧ L< Real.log (p:ℝ) ∧
      (bin p:ℝ)*L≤ Real.log (p:ℝ) ∧
      Real.log (p:ℝ)<((bin p:ℝ)+1)*L ∧ 1≤ bin p := by
    have hp0 : (0:ℝ)< p := by exact_mod_cast (hS p hp).1.pos
    have hXp : (X:ℝ)< p := by exact_mod_cast (hS p hp).2
    have hX0 : (0:ℝ)< X := by
      by_contra hh
      have hx : X=0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg X))
      norm_num [hx] at hX
    have hlog : L< Real.log (p:ℝ) := Real.strictMonoOn_log hX0 hp0 hXp
    have hratio : 1< Real.log (p:ℝ)/L := (lt_div_iff₀ hL0).mpr (by simpa using hlog)
    have hlo := Nat.floor_le (show 0≤ Real.log (p:ℝ)/L by linarith)
    have hhi := Nat.lt_floor_add_one (Real.log (p:ℝ)/L)
    refine ⟨hp0,hlog,?_,?_,?_⟩
    · exact (le_div_iff₀ hL0).mp hlo
    · exact (div_lt_iff₀ hL0).mp hhi
    · exact (Nat.one_le_floor_iff _).mpr hratio.le
  have hbin (k : ℕ) (hk : k∈K) :
      (∑ p ∈ S.filter (fun p => bin p=k), Real.log (p:ℝ)/(p:ℝ))≤
        2*L+2*halaszMertensConstant := by
    obtain ⟨p,hp,hpk⟩ := mem_image.mp hk
    have hk1 : (1:ℝ)≤ k := by exact_mod_cast (hpk ▸ (hpdata p hp).2.2.2.2)
    have ha : 1≤ Real.exp (((k:ℝ)-1)*L) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hL0.le)
    have hab : Real.exp (((k:ℝ)-1)*L)≤ Real.exp (((k:ℝ)+1)*L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsub : S.filter (fun p => bin p=k) ⊆
        mrtPrimeBand (Real.exp (((k:ℝ)-1)*L)) (Real.exp (((k:ℝ)+1)*L)) := by
      intro p hp
      obtain ⟨hp,hpk⟩ := mem_filter.mp hp
      obtain ⟨hp0,_,hlo,hhi,_⟩ := hpdata p hp
      rw [hpk] at hlo hhi
      have hlow : Real.exp (((k:ℝ)-1)*L)<(p:ℝ) := by
        rw [← Real.exp_log hp0]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      have hupp : (p:ℝ)≤ Real.exp (((k:ℝ)+1)*L) := by
        rw [← Real.exp_log hp0]
        exact Real.exp_le_exp.mpr hhi.le
      apply mem_sdiff.mpr
      constructor
      · exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mpr hupp),
          (hS p hp).1⟩
      · intro hh
        have hh' := (Nat.le_floor_iff (Real.exp_pos _).le).mp
          (mem_Iic.mp (mem_filter.mp hh).1)
        linarith
    calc
      _ ≤ ∑ p ∈ mrtPrimeBand (Real.exp (((k:ℝ)-1)*L))
          (Real.exp (((k:ℝ)+1)*L)), Real.log (p:ℝ)/(p:ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (by
          intro p hp _
          have hp1 : (1:ℝ)≤ p := by exact_mod_cast (mrtPrimeBand_prime hp).one_le
          exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg p))
      _ ≤ _ := by
        have hh := halasz_prime_band_mass_le ha hab
        rw [Real.log_exp,Real.log_exp] at hh
        nlinarith
  have hterm (p : ℕ) (hp : p∈S) :
      Real.exp (-Real.log (p:ℝ)/L)/(p:ℝ)≤
        (Real.exp (-(bin p:ℝ))/L)*(Real.log (p:ℝ)/(p:ℝ)) := by
    obtain ⟨hp0,hlog,hlo,_,_⟩ := hpdata p hp
    have he : Real.exp (-Real.log (p:ℝ)/L)≤ Real.exp (-(bin p:ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact (div_le_iff₀ hL0).mpr (by nlinarith)
    have hr : 1≤ Real.log (p:ℝ)/L :=
      (le_div_iff₀ hL0).mpr (by simpa only [one_mul] using hlog.le)
    calc
      _ ≤ Real.exp (-(bin p:ℝ))/(p:ℝ) := div_le_div_of_nonneg_right he hp0.le
      _ ≤ (Real.exp (-(bin p:ℝ))/(p:ℝ))*(Real.log (p:ℝ)/L) :=
        le_mul_of_one_le_right (by positivity) hr
      _ = _ := by ring
  have hmap : ∀p∈S,bin p∈K := fun p hp => mem_image.mpr ⟨p,hp,rfl⟩
  calc
    _ ≤ ∑ p ∈ S, (Real.exp (-(bin p:ℝ))/L)*(Real.log (p:ℝ)/(p:ℝ)) :=
      sum_le_sum hterm
    _ = ∑ k ∈ K, (Real.exp (-(k:ℝ))/L)*
        ∑ p ∈ S.filter (fun p => bin p=k), Real.log (p:ℝ)/(p:ℝ) := by
      rw [← sum_fiberwise_of_maps_to hmap]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ k ∈ K, (Real.exp (-(k:ℝ))/L)*(2*L+2*halaszMertensConstant) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hbin k hk) (by positivity))
    _ = ((2*L+2*halaszMertensConstant)/L)*∑ k ∈ K, Real.exp (-(k:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ ((2*L+2*halaszMertensConstant)/L)*2 :=
      mul_le_mul_of_nonneg_left (mrt_finite_exp_sum K) (by positivity)
    _ ≤ 4+4*halaszMertensConstant := by
      have hh : 2*L+2*halaszMertensConstant≤
          (2+2*halaszMertensConstant)*L := by
        nlinarith [halaszMertensConstant_nonneg]
      have hd := (div_le_iff₀ hL0).mpr hh
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerTail
namespace OAI

/-! Absolute truncation of the character Euler product at sigma=1+1/log X.
Together with the horizontal shift this identifies the finite prime sum
with the logarithm of the actual L-series, up to an absolute error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.LSeries.notation

lemma mrt_character_shifted_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤ eps) {p : ℕ} (hp : p.Prime) :
    ‖(characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ)‖≤1/2 := by
  have hp2 : (2:ℝ)≤ p := by exact_mod_cast hp.two_le
  have hn : ‖characterTwist χ t p/(p:ℂ)‖≤1/2 := by
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p)
      (Nat.cast_nonneg p)).trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have he : Real.exp (-eps*Real.log (p:ℝ))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg (show (1:ℝ)≤ p by linarith)
    nlinarith
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_of_le_one_right (norm_nonneg _) he).trans hn

lemma mrt_character_shifted_log_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤ eps) (S : Finset ℕ) (hS : ∀p∈S,p.Prime) :
    Real.log ‖mrtCharacterShiftedEuler χ t eps S‖ =
      ∑ p ∈ S, Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹‖ := by
  rw [mrtCharacterShiftedEuler,norm_prod]
  apply Real.log_prod
  intro p hp
  apply norm_ne_zero_iff.mpr
  apply inv_ne_zero
  intro he
  have hz := mrt_character_shifted_norm χ t heps (hS p hp)
  rw [show (characterTwist χ t p/(p:ℂ))*
    (Real.exp (-eps*Real.log (p:ℝ)):ℂ)=1 from (sub_eq_zero.mp he).symm,norm_one] at hz
  norm_num at hz

lemma mrt_character_shifted_log_local {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤ eps) {p : ℕ} (hp : p.Prime) :
    |Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
      (Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹‖| ≤
        2*Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ) := by
  have hh := mrt_local_euler_log_lipschitz (mrt_character_shifted_norm χ t heps hp)
    (show ‖(0:ℂ)‖≤1/2 by norm_num)
  simp only [sub_zero,inv_one,norm_one,Real.log_one] at hh
  have hb : ‖characterTwist χ t p/(p:ℂ)‖≤1/(p:ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) (Nat.cast_nonneg p)
  have hn : ‖(characterTwist χ t p/(p:ℂ))*
      (Real.exp (-eps*Real.log (p:ℝ)):ℂ)‖≤
      Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hb (Real.exp_pos (-eps*Real.log (p:ℝ))).le using 1
    ring
  apply hh.trans
  calc
    _ ≤ 2*(Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring

lemma mrt_character_shifted_finite_tail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X Y : ℕ} (hX : 1≤ Real.log (X:ℝ)) (hXY : X≤ Y) :
    |Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo Y)‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖| ≤
        8+8*halaszMertensConstant := by
  have heps : 0≤1/Real.log (X:ℝ) := by positivity
  have hsub : primesUpTo X⊆primesUpTo Y := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le (by omega)),hprime⟩
  let S := primesUpTo Y \ primesUpTo X
  have hS : ∀p∈S,p.Prime ∧ X< p := by
    intro p hp
    obtain ⟨hy,hx⟩ := mem_sdiff.mp hp
    have hprime := (mem_filter.mp hy).2
    refine ⟨hprime,?_⟩
    by_contra hh
    exact hx (mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩)
  rw [mrt_character_shifted_log_sum χ t heps (primesUpTo Y) (fun p hp => (mem_filter.mp hp).2),
    mrt_character_shifted_log_sum χ t heps (primesUpTo X) (fun p hp => (mem_filter.mp hp).2),
    ← sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ p ∈ S, |Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-(1/Real.log (X:ℝ))*Real.log (p:ℝ)):ℂ))⁻¹‖| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, 2*Real.exp (-(1/Real.log (X:ℝ))*Real.log (p:ℝ))/(p:ℝ) :=
      sum_le_sum (fun p hp => mrt_character_shifted_log_local χ t heps (hS p hp).1)
    _ = 2*∑ p ∈ S, Real.exp (-Real.log (p:ℝ)/Real.log (X:ℝ))/(p:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      rw [show -(1/Real.log (X:ℝ))*Real.log (p:ℝ)=
        -Real.log (p:ℝ)/Real.log (X:ℝ) by ring]
      ring
    _ ≤ 8+8*halaszMertensConstant := by
      have hh := mrt_character_prime_tail_bound hX S hS
      nlinarith

theorem mrt_character_LSeries_truncation {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X : ℕ} (hX : 1≤ Real.log (X:ℝ)) :
    |Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖| ≤
        8+8*halaszMertensConstant := by
  have heps : 0<1/Real.log (X:ℝ) := by positivity
  have hs : 1<(1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I).re := by
    simp only [Complex.sub_re,Complex.add_re,Complex.one_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
    linarith
  have hn := χ.LSeries_ne_zero_of_one_lt_re hs
  have ht := mrt_character_shifted_euler_limit χ t heps
  have hlog := (Real.continuousAt_log (norm_ne_zero_iff.mpr hn)).tendsto.comp ht.norm
  apply le_of_tendsto ((hlog.sub tendsto_const_nhds).abs)
  filter_upwards [eventually_ge_atTop X] with Y hXY
  exact mrt_character_shifted_finite_tail χ t hX hXY

theorem mrt_character_euler_LSeries_comparison {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X : ℕ} (hX : 1≤ Real.log (X:ℝ)) :
    |Real.log ‖mrtCharacterPrimeEuler χ t (primesUpTo X)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖| ≤
        10+10*halaszMertensConstant := by
  have hshift := mrt_character_euler_logarithmic_shift χ t hX (primesUpTo X) Subset.rfl
  have htail := mrt_character_LSeries_truncation χ t hX
  have hh := abs_sub_le (Real.log ‖mrtCharacterPrimeEuler χ t (primesUpTo X)‖)
    (Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖)
    (Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖)
  rw [abs_sub_comm] at htail
  linarith

theorem mrt_character_prime_tail_LSeries_ratio {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {Y X : ℕ}
    (hY : 1≤ Real.log (Y:ℝ)) (hX : 1≤ Real.log (X:ℝ)) (hYX : Y≤ X) :
    |(∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p/(p:ℂ)).re-
      (Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
        Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖)| ≤
        24+20*halaszMertensConstant := by
  have hsub : primesUpTo Y⊆primesUpTo X := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le (by omega)),hprime⟩
  rw [sum_sdiff_eq_sub hsub,Complex.sub_re]
  have hEX := abs_le.mp (mrt_character_euler_log_error χ t X (primesUpTo X) Subset.rfl)
  have hEY := abs_le.mp (mrt_character_euler_log_error χ t Y (primesUpTo Y) Subset.rfl)
  have hLX := abs_le.mp (mrt_character_euler_LSeries_comparison χ t hX)
  have hLY := abs_le.mp (mrt_character_euler_LSeries_comparison χ t hY)
  apply abs_le.mpr
  constructor <;> linarith [hEX.1,hEX.2,hEY.1,hEY.2,hLX.1,hLX.2,hLY.1,hLY.2]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogDerivative
namespace OAI

/-! Real-sigma integration of the logarithmic derivative. The real
logarithm of the norm is differentiated through normSq, so no branch
choice for the complex logarithm is needed. -/

namespace TwoPointCorrelations

open _root_.Set
open scoped _root_.Classical _root_.LSeries.notation

lemma mrt_hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x≠0) :
    HasDerivAt (fun y => Real.log ‖f y‖) (f'/f x).re x := by
  have hre : HasDerivAt (fun y => (f y).re) f'.re x := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun y => (f y).im) f'.im x := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hsq : HasDerivAt (fun y => Complex.normSq (f y))
      ((f'.re*(f x).re+(f x).re*f'.re)+(f'.im*(f x).im+(f x).im*f'.im)) x := by
    simpa only [Complex.normSq_apply, Pi.mul_apply, Pi.add_apply] using!
      (hre.mul hre).add (him.mul him)
  have hsq0 : Complex.normSq (f x)≠0 := by
    exact fun h => hne (Complex.normSq_eq_zero.mp h)
  have hh := (hsq.log hsq0).div_const 2
  have he : (fun y => Real.log (Complex.normSq (f y))/2) =
      (fun y => Real.log ‖f y‖) := by
    funext y
    rw [Complex.normSq_eq_norm_sq,Real.log_pow]
    ring
  rw [he] at hh
  convert (preTransparency := .instances) hh using 1
  rw [Complex.div_re]
  ring

lemma mrt_log_norm_sigma_bound {f f' : ℝ → ℂ} {a b K : ℝ}
    (hab : a≤ b) (hf : ∀x∈Icc a b,HasDerivAt f (f' x) x)
    (hne : ∀x∈Icc a b,f x≠0)
    (hbound : ∀x∈Ico a b,‖f' x/f x‖≤ K) :
    |Real.log ‖f b‖-Real.log ‖f a‖|≤ K*(b-a) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x => Real.log ‖f x‖)
    (f' := fun x => (f' x/f x).re)
    (fun x hx => (mrt_hasDerivAt_log_norm (hf x hx) (hne x hx)).hasDerivWithinAt)
    (fun x hx => (by
      simpa only [Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (f' x/f x)).trans (hbound x hx))) b (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs] using hh


lemma mrt_character_LSeries_real_deriv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0< q) (t : ℝ) {σ : ℝ} (hσ : 1<σ) :
    HasDerivAt (fun x : ℝ => L ↗χ ((x:ℂ)-(t:ℂ)*Complex.I))
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)) σ := by
  have hs : 1<((σ:ℂ)-(t:ℂ)*Complex.I).re := by simpa using hσ
  have hconv : LSeries.abscissaOfAbsConv ↗χ<((σ:ℂ)-(t:ℂ)*Complex.I).re := by
    rw [χ.absicssaOfAbsConv_eq_one (Nat.ne_of_gt hq)]
    exact_mod_cast hs
  have hc := (LSeries_hasDerivAt hconv).differentiableAt.hasDerivAt
  have hh := hc.comp (σ:ℂ) ((hasDerivAt_id (σ:ℂ)).sub_const ((t:ℂ)*Complex.I))
  simpa only [mul_one, Function.comp_apply, id_eq] using! hh.comp_ofReal

theorem mrt_character_LSeries_sigma_ratio {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hq : 0< q) (t : ℝ) {Y X : ℕ} (hY : 1≤ Real.log (Y:ℝ)) (hYX : Y≤ X)
    {K : ℝ} (hK : 0≤ K)
    (hbound : ∀ σ ∈ Ico (1+1/Real.log (X:ℝ)) (1+1/Real.log (Y:ℝ)),
      ‖logDeriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)‖≤ K*Real.log (Y:ℝ)) :
    |Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖|≤ K := by
  have hY0 : (0:ℝ)< Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hYXr : (Y:ℝ)≤ X := by exact_mod_cast hYX
  have hlog : Real.log (Y:ℝ)≤ Real.log (X:ℝ) := Real.log_le_log hY0 hYXr
  have hX : 1≤ Real.log (X:ℝ) := hY.trans hlog
  have hLY : 0< Real.log (Y:ℝ) := by linarith
  have hLX : 0< Real.log (X:ℝ) := by linarith
  let a := 1+1/Real.log (X:ℝ)
  let b := 1+1/Real.log (Y:ℝ)
  have hab : a≤ b := add_le_add_right (one_div_le_one_div_of_le hLY hlog) 1
  have ha : 1< a := by dsimp only [a]; linarith [one_div_pos.mpr hLX]
  have hf : ∀σ∈Icc a b,HasDerivAt
      (fun x : ℝ => L ↗χ ((x:ℂ)-(t:ℂ)*Complex.I))
      (deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)) σ :=
    fun σ hσ => mrt_character_LSeries_real_deriv χ hq t (ha.trans_le hσ.1)
  have hne : ∀σ∈Icc a b,L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)≠0 := by
    intro σ hσ
    apply χ.LSeries_ne_zero_of_one_lt_re
    simpa using ha.trans_le hσ.1
  have hbnd : ∀σ∈Ico a b,
      ‖deriv (L ↗χ) ((σ:ℂ)-(t:ℂ)*Complex.I)/
        L ↗χ ((σ:ℂ)-(t:ℂ)*Complex.I)‖≤ K*Real.log (Y:ℝ) := by
    intro σ hσ
    exact hbound σ hσ
  have hh := mrt_log_norm_sigma_bound hab hf hne hbnd
  have hwidth : b-a≤1/Real.log (Y:ℝ) := by
    dsimp only [a,b]
    linarith [one_div_pos.mpr hLX]
  have hcost : (K*Real.log (Y:ℝ))*(b-a)≤ K := by
    calc
      _ ≤ (K*Real.log (Y:ℝ))*(1/Real.log (Y:ℝ)) :=
        mul_le_mul_of_nonneg_left hwidth (mul_nonneg hK hLY.le)
      _ = K := by field_simp
  have hh' := hh.trans hcost
  rw [abs_sub_comm] at hh'
  simpa only [a,b,Complex.ofReal_add,Complex.ofReal_one] using hh'


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowth
namespace OAI

/-! Normalize the weak Hurwitz growth bound without losing a power of the
height. The logarithmic disk budget is O(1+log q+loglog |t|), uniformly in q. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical



lemma mrt_VKWeight_ge_one {q : ℕ} [NeZero q] {t : ℝ} (hH : 1 ≤ mrtVKLog t) :
    1 ≤ mrtVKWeight q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  unfold mrtVKWeight
  linarith [Real.log_nonneg hq, Real.log_nonneg hH]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowthWindow
namespace OAI

/-! The same weak Hurwitz estimate controls all nearby character disks.
Using radius R(2t)/16 leaves room for both the first and doubled heights. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

lemma mrt_VKLog_pos (t : ℝ) : 0 < mrtVKLog t :=
  Real.log_pos (by linarith [abs_nonneg t])





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKPrimeTail
namespace OAI

/-! The weak VK derivative estimate implies a uniform finite prime-tail
bound. Both the sigma-segment width and height budget are retained. -/

namespace TwoPointCorrelations

open _root_.Set
open scoped _root_.Classical _root_.LSeries.notation

theorem MRTWeakHurwitzGrowthInput.prime_tail (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (t : ℝ) (Y X : ℕ), 1 ≤ Real.log (Y : ℝ) → Y ≤ X → T ≤ |t| →
      1 / Real.log (Y : ℝ) ≤ mrtVKRadius (2 * t) / 16 →
      (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ Real.log (Y : ℝ) →
      |(∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨C, T, hC, hT, hbound⟩ := h.logderiv
  refine ⟨24 + 20 * halaszMertensConstant + C, T,
    by linarith [halaszMertensConstant_nonneg], hT, ?_⟩
  intro q _ χ t Y X hY hYX ht hwidth hcost
  have hYpos : (0 : ℝ) < Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hlog : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYX)
  have hX : 1 ≤ Real.log (X : ℝ) := hY.trans hlog
  have hLX : 0 < Real.log (X : ℝ) := by linarith
  have hHneg : mrtVKLog (2 * -t) = mrtVKLog (2 * t) := by
    unfold mrtVKLog
    rw [mul_neg, abs_neg]
  have hRneg : mrtVKRadius (2 * -t) = mrtVKRadius (2 * t) := by
    unfold mrtVKRadius
    rw [hHneg]
  have hWneg : mrtVKWeight q (2 * -t) = mrtVKWeight q (2 * t) := by
    unfold mrtVKWeight
    rw [hHneg]
  have hb : ∀ sigma ∈ Ico (1 + 1 / Real.log (X : ℝ)) (1 + 1 / Real.log (Y : ℝ)),
      ‖logDeriv (L ↗χ) ((sigma : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C * Real.log (Y : ℝ) := by
    intro sigma hsigma
    have hσ : 1 < sigma := by linarith [one_div_pos.mpr hLX, hsigma.1]
    have hσr : sigma ≤ 1 + mrtVKRadius (2 * -t) / 16 := by
      rw [hRneg]
      linarith [hsigma.2]
    have hh := hbound q χ (-t) sigma (by simpa using ht) hσ hσr
    rw [hHneg, hWneg] at hh
    have hpoint : (sigma : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        (sigma : ℂ) - (t : ℂ) * Complex.I := by push_cast; ring
    rw [hpoint] at hh
    have hs : 1 < ((sigma : ℂ) - (t : ℂ) * Complex.I).re := by simpa using hσ
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs] at hh
    apply hh.trans
    calc
      _ = C * ((mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcost hC.le
  have hr := mrt_character_LSeries_sigma_ratio χ (NeZero.pos q) t hY hYX hC.le hb
  have he := mrt_character_prime_tail_LSeries_ratio χ t hY hX hYX
  have ht := abs_add_le
    ((∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p / (p : ℂ)).re -
      (Real.log ‖L ↗χ (1 + (1 / Real.log (X : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖ -
        Real.log ‖L ↗χ (1 + (1 / Real.log (Y : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖))
    (Real.log ‖L ↗χ (1 + (1 / Real.log (X : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖ -
      Real.log ‖L ↗χ (1 + (1 / Real.log (Y : ℝ) : ℝ) - (t : ℂ) * Complex.I)‖)
  rw [sub_add_cancel] at ht
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHighPrimePhases
namespace OAI

/-! The high-frequency prime-repulsion step needs only three real prime
phases on the power-logarithmic tail, bounded uniformly over the
indicated height range. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem halasz_high_prime_of_three_phases
    (hphase : ∃ K : ℝ, ∀ᶠ X : ℕ in atTop,
      ∀ u : ℝ, (Real.log X)^20 ≤ |u| → |u| ≤ 2*X →
      ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        |∑ p ∈ mrtPrimePowerTail (27/40) X,
          Real.cos ((k:ℝ)*u*Real.log (p:ℝ))/(p:ℝ)| ≤ K) :
    HalaszHighPrimeInput := by
  obtain ⟨K,hphase⟩ := hphase
  obtain ⟨C,hC,hmass⟩ := mrt_prime_power_tail_mass
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (10240*((81/256)*C+(95/256)*K)))
  filter_upwards [hphase,hll,hlog.eventually (eventually_ge_atTop (1:ℝ))]
    with X hp hlarge hL
  intro u hu hux
  let P := mrtPrimePowerTail (27/40) X
  have hs : (13/40:ℝ)*Real.log (Real.log X)-C ≤ ∑ p ∈ P, 1/(p:ℝ) := by
    simpa only [show (1:ℝ)-27/40=13/40 by norm_num] using
      hmass (27/40) (by norm_num) (by norm_num) X hL
  have hsum (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
      |∑ p ∈ P, (1/(p:ℝ))*Real.cos ((k:ℝ)*(u*Real.log (p:ℝ)))| ≤ K := by
    simpa only [P,div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using
      hp u hu hux k hk hk3
  have h₁ := hsum 1 (by omega) (by omega)
  simp only [Nat.cast_one,one_mul] at h₁
  have h₂ := hsum 2 (by omega) (by omega)
  have h₃ := hsum 3 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h₂ h₃
  have hrep := halasz_weighted_cosine_repulsion P (fun p => 1/(p:ℝ))
    (fun p => u*Real.log (p:ℝ)) (fun p _ => by positivity) K h₁ h₂ h₃
  have hsub : P ⊆ primesUpTo X := by
    intro p hp
    have hh : p ∈ sievePrimesUpTo (X:ℝ) := (mem_sdiff.mp hp).1
    rwa [mrt_sievePrimesUpTo_nat] at hh
  have hfull : (∑ p ∈ P, (1/(p:ℝ))*(1-|Real.cos (u*Real.log (p:ℝ)/2)|)) ≤
      ∑ p ∈ primesUpTo X, (1-|Real.cos (u*Real.log (p:ℝ)/2)|)/(p:ℝ) := by
    have hh := sum_le_sum_of_subset_of_nonneg
      (f := fun p : ℕ => (1/(p:ℝ))*(1-|Real.cos (u*Real.log (p:ℝ)/2)|))
      hsub (fun p _ _ => mul_nonneg (by positivity)
        (sub_nonneg.mpr (Real.abs_cos_le_one _)))
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  apply le_trans _ hfull
  dsimp only [Function.comp_def] at hlarge
  have hll0 : 0 ≤ Real.log (Real.log (X:ℝ)) := Real.log_nonneg hL
  linarith only [hs,hrep,hlarge,hll0]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleLSeries
namespace OAI

/-! Reduction of the Liouville distance estimate to a uniform lower
bound for a Dirichlet L-value ratio. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.LSeries.notation


lemma mrt_sievePrimesUpTo_floor (x : ℝ) :
    sievePrimesUpTo x=primesUpTo ⌊x⌋₊ := by
  ext p
  simp only [sievePrimesUpTo,primesUpTo,mem_filter,mem_Iic,mem_range,Nat.lt_succ_iff]

lemma mrt_prime_power_tail_cutoff (a : ℝ) (X : ℕ) :
    mrtPrimePowerTail a X=primesUpTo X \ primesUpTo (mrtPrimePowerCutoff a X) := by
  rw [mrtPrimePowerTail,mrtPrimeBand,mrt_sievePrimesUpTo_nat,mrt_sievePrimesUpTo_floor]
  rfl

theorem mrt_prime_power_cutoff_eventually {a : ℝ} (ha : 0< a) (ha1 : a≤1) :
    ∀ᶠ X : ℕ in atTop, 1≤ Real.log (mrtPrimePowerCutoff a X:ℝ) ∧
      mrtPrimePowerCutoff a X≤ X := by
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun X:ℕ => Real.exp ((Real.log (X:ℝ))^a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlog)
  filter_upwards [hlog.eventually (eventually_ge_atTop (1:ℝ)),
    hexp.eventually (eventually_ge_atTop (Real.exp 1+1))] with X hL hE
  have hX0 : (0:ℝ)< X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp (by linarith))
  have hf : Real.exp 1<(mrtPrimePowerCutoff a X:ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp ((Real.log (X:ℝ))^a))
    change _<(⌊Real.exp ((Real.log (X:ℝ))^a)⌋₊:ℝ)
    linarith
  have hf0 : (0:ℝ)< mrtPrimePowerCutoff a X := (Real.exp_pos 1).trans hf
  refine ⟨?_,?_⟩
  · have hh := Real.strictMonoOn_log (Real.exp_pos 1) hf0 hf
    rw [Real.log_exp] at hh
    exact hh.le
  · have hp : Real.exp ((Real.log (X:ℝ))^a)≤(X:ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (X:ℝ)) :=
          Real.exp_le_exp.mpr (Real.rpow_le_self_of_one_le hL ha1)
        _ = _ := Real.exp_log hX0
    have hh := (Nat.floor_le ((Real.exp_pos ((Real.log (X:ℝ))^a)).le)).trans hp
    exact_mod_cast hh




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSmallHeight
namespace OAI

/-! A concrete low-height range in the original Liouville prime tail.
Only nonprincipal characters are covered here. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical

lemma mrt_prime_power_cutoff_log_lower {a : ℝ} (ha : 0 < a) :
    ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ a ≤
        Real.log (mrtPrimePowerCutoff a X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := ((tendsto_rpow_atTop ha).comp hlog).eventually
    (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  filter_upwards [hp] with X hX
  let A := (Real.log (X : ℝ)) ^ a
  have hA : 2 ≤ A := (le_max_left _ _).trans hX
  have hAl : 2 * Real.log 2 ≤ A := (le_max_right _ _).trans hX
  have hE : 2 ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have hf : Real.exp A / 2 ≤ (mrtPrimePowerCutoff a X : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp A)
    change Real.exp A / 2 ≤ (⌊Real.exp A⌋₊ : ℝ)
    linarith
  have hf0 : 0 < (mrtPrimePowerCutoff a X : ℝ) :=
    (div_pos (Real.exp_pos A) (by norm_num)).trans_le hf
  have hh := Real.log_le_log (div_pos (Real.exp_pos A) (by norm_num)) hf
  rw [Real.log_div (Real.exp_pos A).ne' (by norm_num), Real.log_exp] at hh
  change (1 / 2 : ℝ) * A ≤ _
  linarith




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalSmallHeight
namespace OAI

/-! The principal character in the low-height Liouville prime-tail range,
from the proved prime-number theorem and a uniform cosine integral bound. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical _root_.Topology


lemma mrt_principal_twist_re {q : ℕ} (hq : 0 < q) {p : ℕ}
    (hp : p.Prime) (hqp : q < p) (t : ℝ) :
    (characterTwist (1 : DirichletCharacter ℂ q) t p).re = Real.cos (t * Real.log (p : ℝ)) := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hqp) (Nat.le_of_dvd hq h))
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hcop
  unfold characterTwist
  rw [MulChar.one_apply hu, one_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    sub_zero, Real.exp_zero, one_mul]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKScale
namespace OAI

/-! Quantitative height bookkeeping for the original character range.
Every fixed tail exponent greater than 2/3 absorbs the two logarithmic
factors in the weak VK derivative estimate. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Classical

lemma mrt_VK_height_upper {X t : ℝ} (hX : 1 ≤ X)
    (hL : Real.log 15 ≤ Real.log X) (ht : |t| ≤ 6 * X) :
    mrtVKLog (2 * t) ≤ 2 * Real.log X := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh : |2 * t| + 3 ≤ 15 * X := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < |2 * t| + 3) hh
  rw [Real.log_mul (by norm_num) hX0.ne'] at hl
  exact hl.trans (by linarith)

lemma mrt_VK_weight_upper {q : ℕ} [NeZero q] {L t : ℝ}
    (hL : 0 < L) (hlogL : 1 ≤ Real.log L)
    (hq : (q : ℝ) ≤ L ^ (1 / 125 : ℝ))
    (hH : mrtVKLog (2 * t) ≤ 2 * L) :
    mrtVKWeight q (2 * t) ≤ 4 * Real.log L := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hq0 hq
  rw [Real.log_rpow hL] at hlogq
  have hlogH := Real.log_le_log (mrt_VKLog_pos (2 * t)) hH
  rw [Real.log_mul (by norm_num) hL.ne'] at hlogH
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  unfold mrtVKWeight
  linarith

lemma mrt_VK_log_square_decay {a : ℝ} (ha : (2 / 3 : ℝ) < a) :
    ∀ᶠ L : ℝ in atTop,
      512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) ≤ (1 / 2 : ℝ) * L ^ a := by
  let ε := (a - 2 / 3) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hs := (isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hs hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _)] at hs
  have hp : (L ^ ε) ^ 2 * L ^ (2 / 3 : ℝ) = L ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1
    dsimp [ε]
    ring
  calc
    _ ≤ 512 * (((1 / 32 : ℝ) * L ^ ε) ^ 2) * L ^ (2 / 3 : ℝ) := by
      gcongr
      exact Real.log_nonneg hL
    _ = (1 / 2 : ℝ) * ((L ^ ε) ^ 2 * L ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hp]

/-- Both explicit hypotheses of the finite prime-tail estimate hold in the
original modulus range and at every height up to X. -/
theorem mrt_VK_power_tail_parameters {a : ℝ} (ha : (2 / 3 : ℝ) < a) (_ha1 : a ≤ 1) :
    ∀ᶠ X : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ t : ℝ, |t| ≤ 6 * X → 1 ≤ mrtVKLog (2 * t) →
        (1 / Real.log (mrtPrimePowerCutoff a X : ℝ) ≤ mrtVKRadius (2 * t) / 16) ∧
        ((mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤
          Real.log (mrtPrimePowerCutoff a X : ℝ)) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloga : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 2 / 3) ha
  filter_upwards [hlog.eventually (mrt_VK_log_square_decay ha),
    hlog.eventually (eventually_ge_atTop (max (Real.exp 1) (Real.log 15))),
    mrt_prime_power_cutoff_log_lower hloga,
    eventually_ge_atTop (1 : ℕ)] with X hdecay hL hcut hX
  intro q _ hq t ht hH
  let L := Real.log (X : ℝ)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlogL : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hLe
    simpa using hh
  have hHupper := mrt_VK_height_upper (by exact_mod_cast hX)
    ((le_max_right _ _).trans hL) ht
  have hW := mrt_VK_weight_upper hL0 hlogL hq hHupper
  have hW0 : 0 ≤ mrtVKWeight q (2 * t) := zero_le_one.trans (mrt_VKWeight_ge_one hH)
  have hW2 := pow_le_pow_left₀ hW0 hW 2
  have hHp : (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ 2 * L ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ (2 * L) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (mrt_VKLog_pos _).le hHupper (by norm_num)
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (Real.rpow_nonneg hL0.le _)
  have hprod := mul_le_mul hW2 hHp (Real.rpow_nonneg (mrt_VKLog_pos _).le _) (sq_nonneg _)
  have hcost : 16 * ((mrtVKWeight q (2 * t)) ^ 2 *
      (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) ≤ Real.log (mrtPrimePowerCutoff a X : ℝ) := by
    have hfirst : 16 * ((mrtVKWeight q (2 * t)) ^ 2 *
        (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) ≤ 512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) := by
      nlinarith only [hprod]
    exact hfirst.trans (hdecay.trans hcut)
  have hW1 : 1 ≤ (mrtVKWeight q (2 * t)) ^ 2 := by
    nlinarith [mrt_VKWeight_ge_one (q := q) hH]
  have hHp0 : 0 < (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (mrt_VKLog_pos _) _
  have hmass : 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤
      Real.log (mrtPrimePowerCutoff a X : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hW1 hHp0.le
    nlinarith only [hh, hcost]
  constructor
  · have hh := one_div_le_one_div_of_le (by positivity :
        0 < 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ)) hmass
    apply hh.trans_eq
    rw [mrtVKRadius, Real.rpow_neg (mrt_VKLog_pos _).le]
    ring
  · have hn : 0 ≤ (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by positivity
    nlinarith only [hcost, hn]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKApplications
namespace OAI

/-! Actual character tails and the two required distance consequences of
weak Hurwitz growth. The growth proposition remains an explicit premise. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical

theorem MRTWeakHurwitzGrowthInput.power_prime_tail (h : MRTWeakHurwitzGrowthInput)
    {a : ℝ} (ha : (2 / 3 : ℝ) < a) (ha1 : a ≤ 1) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ᶠ X : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
        ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), T ≤ |t| → |t| ≤ 6 * X →
          |(∑ p ∈ mrtPrimePowerTail a X, characterTwist χ t p / (p : ℂ)).re| ≤ C := by
  obtain ⟨C, T, hC, hT, ht⟩ := h.prime_tail
  refine ⟨C, max T (Real.exp 1), hC, lt_of_lt_of_le hT (le_max_left _ _), ?_⟩
  filter_upwards [mrt_VK_power_tail_parameters ha ha1,
    mrt_prime_power_cutoff_eventually (lt_trans (by norm_num) ha) ha1] with X hp hc
  intro q _ hq χ t hheight htX
  have hTt : T ≤ |t| := (le_max_left _ _).trans hheight
  have hH : 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    have hh := (le_max_right T (Real.exp 1)).trans hheight
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨hw, hb⟩ := hp q hq t htX hH
  rw [mrt_prime_power_tail_cutoff]
  exact ht q χ t _ X hc.1 hc.2 hTt hw hb


/-- The three harmonic phases needed for high-prime repulsion use only the
principal character of modulus one. -/
theorem MRTWeakHurwitzGrowthInput.high_prime (h : MRTWeakHurwitzGrowthInput) :
    HalaszHighPrimeInput := by
  obtain ⟨C, T, _, _, ht⟩ := h.power_prime_tail (by norm_num : (2 / 3 : ℝ) < 27 / 40)
    (by norm_num)
  apply halasz_high_prime_of_three_phases
  refine ⟨C, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := ((tendsto_rpow_atTop (show (0 : ℝ) < 20 by norm_num)).comp hlog).eventually
    (eventually_ge_atTop T)
  filter_upwards [ht, he, hlog.eventually (eventually_ge_atTop (1 : ℝ))] with X ht he hL
  simp only [Function.comp_apply, Real.rpow_ofNat] at he
  intro u hu hux k hk hk3
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have hktu : T ≤ |(k : ℝ) * u| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact he.trans (hu.trans (le_mul_of_one_le_left hu0 hkR))
  have hktX : |(k : ℝ) * u| ≤ 6 * (X : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    have hXreal : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hh := mul_le_mul_of_nonneg_left hux hk0
    have hh' := mul_le_mul_of_nonneg_right hk3R (show (0 : ℝ) ≤ 2 * X by positivity)
    linarith
  have hq : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) :=
    Real.one_le_rpow hL (by norm_num)
  have hh := ht 1 (by simpa using hq) (1 : DirichletCharacter ℂ 1) ((k : ℝ) * u) hktu hktX
  have hid : (∑ p ∈ mrtPrimePowerTail (27 / 40) X,
      characterTwist (1 : DirichletCharacter ℂ 1) ((k : ℝ) * u) p / (p : ℂ)).re =
      ∑ p ∈ mrtPrimePowerTail (27 / 40) X,
        Real.cos ((k : ℝ) * u * Real.log (p : ℝ)) / (p : ℝ) := by
    simp only [Complex.re_sum]
    apply sum_congr rfl
    intro p hp
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, Complex.div_ofReal_re]
    rw [mrt_principal_twist_re (by norm_num) (mrtPrimeBand_prime hp)
      (mrtPrimeBand_prime hp).one_lt]
  rwa [hid] at hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKTheorem
namespace OAI

/-! Conditional assembly from the precise weak Hurwitz growth statement
and the still-explicit sparse prime mean-square input. -/

namespace TwoPointCorrelations

theorem MRTWeakHurwitzGrowthInput.short_exponential_oai (h : MRTWeakHurwitzGrowthInput)
    (hprime : HalaszPrimeSparseInput) : MRTShortExponentialInput :=
  mrt_short_exponential_of_prime_estimates hprime h.high_prime


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.short_exponential_oai := @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.short_exponential_oai
