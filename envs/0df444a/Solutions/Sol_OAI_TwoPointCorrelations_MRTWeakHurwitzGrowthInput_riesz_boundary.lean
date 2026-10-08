-- Prove2me | solution 1 for OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:05:22.544994+00:00
-- url     : https://prove2.me/submissions/894237c4-db3d-40d4-97fe-f2727d017d40

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_strip_logderiv
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_zeta_right_growth

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
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
















theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩







































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























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
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩



theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]


local notation (name := riemannzeta0) "ζ₀" => riemannZeta0



























































































































lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert (preTransparency := .instances) differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * Complex.I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * Complex.I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * Complex.I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + Complex.I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + Complex.I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + Complex.I * t₀) (by simp) zetaIsZero





open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaCompactStrip
namespace OAI

/-! A fixed bounded-height strip for the pole-corrected zeta logarithmic
derivative, from zero-free compactness. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Metric _root_.Set _root_.Filter
open scoped _root_.Topology

theorem mrt_zeta_compact_strip (B : ℝ) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ s : ℂ,
      1 - a ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
        riemannZeta s ≠ 0 ∧ ‖mrtZetaPoleCorrection s‖ ≤ C := by
  let U := |B| + 1
  obtain ⟨σ₀, hσ₀, hz⟩ := Erdos970.ZetaNoZerosInBox U
  let A := max σ₀ (1 / 2)
  have hA : A < 1 := max_lt hσ₀ (by norm_num)
  have hAh : 1 / 2 ≤ A := le_max_right _ _
  have hnon (s : ℂ) (hs : A ≤ s.re) (hn : ‖s‖ ≤ U) : riemannZeta s ≠ 0 := by
    have hi := (Complex.abs_im_le_norm s).trans hn
    have hh := hz s.im hi s.re ((le_max_left _ _).trans hs)
    simpa only [Complex.re_add_im] using hh
  obtain ⟨C₀, hC₀⟩ := Erdos970.riemannZetaLogDerivResidueBigO.bound
  have he : ∀ᶠ s : ℂ in 𝓝[({1}ᶜ)] 1, ‖mrtZetaPoleCorrection s‖ ≤ C₀ := by
    filter_upwards [hC₀] with s hs
    simpa only [mrtZetaPoleCorrection, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
      Pi.one_apply, norm_one, mul_one] using hs
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  let K : Set ℂ := closedBall 0 U ∩ {s : ℂ | A ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) U).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hE : IsCompact (K \ ball (1 : ℂ) r) := hK.diff isOpen_ball
  have hcont : ContinuousOn mrtZetaPoleCorrection (K \ ball (1 : ℂ) r) := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro heq
      apply hs.2
      rw [heq]
      exact mem_ball_self hr
    have hn : riemannZeta s ≠ 0 := hnon s hs.1.2 (by simpa using hs.1.1)
    have hd := (analyticOn_riemannZeta s hs1).deriv.continuousAt
    have hc := (differentiableAt_riemannZeta hs1).continuousAt
    exact ((hd.neg.div hc hn).sub
      ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs1))).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hE.exists_bound_of_continuousOn hcont
  refine ⟨1 - A, max 0 (max C₀ C₁), by linarith, by linarith, le_max_left _ _, ?_⟩
  intro s hs hn hs1
  have hsA : A ≤ s.re := by linarith
  have hnU : ‖s‖ ≤ U := hn.trans (by dsimp [U]; linarith [le_abs_self B])
  refine ⟨hnon s hsA hnU, ?_⟩
  by_cases hsr : s ∈ ball (1 : ℂ) r
  · exact (hlocal ⟨hsr, hs1⟩).trans ((le_max_left C₀ C₁).trans (le_max_right _ _))
  · have hm : s ∈ K \ ball (1 : ℂ) r := by
      exact ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hnU, hsA⟩, hsr⟩
    exact (hC₁ s hm).trans ((le_max_right C₀ C₁).trans (le_max_right _ _))

end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKScale
namespace OAI

/-! Quantitative height bookkeeping for the original character range.
Every fixed tail exponent greater than 2/3 absorbs the two logarithmic
factors in the weak VK derivative estimate. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Classical



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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseContourScale
namespace OAI

/-! Numerical compatibility of the narrower sparse-prime contour with the
weak VK strip, uniformly over its full finite height. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Topology

lemma mrt_sparse_contour_height {L t : ℝ} (hL : Real.log 11 ≤ L) (hL0 : 0 ≤ L)
    (ht : |t| ≤ 4 * Real.exp (2 * L)) : mrtVKLog (2 * t) ≤ 3 * L := by
  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by linarith)
  have hh : |2 * t| + 3 ≤ 11 * Real.exp (2 * L) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have he := Real.log_le_log (by positivity : 0 < |2 * t| + 3) hh
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at he
  exact he.trans (by linarith)

lemma mrt_sparse_contour_budget {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, |t| ≤ 4 * Real.exp (2 * L) →
      L ^ (-(3 / 4 : ℝ)) ≤ c * mrtVKRadius (2 * t) / mrtVKWeight 1 (2 * t) ∧
      (mrtVKWeight 1 (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ L ^ 2 := by
  have he := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).bound
    (show 0 < c / 12 by positivity)
  have hd := mrt_VK_log_square_decay (a := 2) (by norm_num)
  filter_upwards [he, hd, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (Real.log 11)] with L he hd hL1 hL11
  intro t ht
  have hL : 0 < L := (Real.exp_pos 1).trans_le hL1
  have hLge : 1 ≤ L := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hL).mpr hL1
  have hH : 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    linarith [Real.exp_one_lt_d9, abs_nonneg (2 * t)]
  have hHp := mrt_VKLog_pos (2 * t)
  have hHup := mrt_sparse_contour_height hL11 hL.le ht
  have hW : mrtVKWeight 1 (2 * t) ≤ 4 * Real.log L := by
    have hh := Real.log_le_log hHp hHup
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hL.ne'] at hh
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    simp only [mrtVKWeight, Nat.cast_one, Real.log_one, add_zero]
    linarith
  have hW0 : 0 < mrtVKWeight 1 (2 * t) :=
    zero_lt_one.trans_le (mrt_VKWeight_ge_one (q := 1) hH)
  have hpow : (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ 3 * L ^ (2 / 3 : ℝ) := by
    apply (Real.rpow_le_rpow hHp.le hHup (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hLge), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _)] at he
  have hp : (L ^ (-(3 / 4 : ℝ)) * (4 * Real.log L)) * (3 * L ^ (2 / 3 : ℝ)) ≤ c := by
    have hid : L ^ (-(3 / 4 : ℝ)) * L ^ (2 / 3 : ℝ) = (L ^ (1 / 12 : ℝ))⁻¹ := by
      rw [← Real.rpow_add hL, ← Real.rpow_neg hL.le]
      congr 1
      norm_num
    calc
      _ = 12 * Real.log L * (L ^ (1 / 12 : ℝ))⁻¹ := by rw [← hid]; ring
      _ ≤ 12 * ((c / 12) * L ^ (1 / 12 : ℝ)) * (L ^ (1 / 12 : ℝ))⁻¹ := by gcongr
      _ = c := by field_simp
  refine ⟨?_, ?_⟩
  · apply (le_div_iff₀ hW0).mpr
    rw [mrtVKRadius, Real.rpow_neg hHp.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hHp _)).mpr
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg hL.le _))
      hpow (Real.rpow_nonneg hHp.le _) (by positivity)).trans hp
  · have hs : (mrtVKWeight 1 (2 * t)) ^ 2 ≤ 16 * (Real.log L) ^ 2 := by nlinarith
    have hh := mul_le_mul hs hpow (Real.rpow_nonneg hHp.le _) (by positivity)
    have hd' : 512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) ≤ (1 / 2 : ℝ) * L ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using hd
    apply hh.trans
    calc
      16 * (Real.log L) ^ 2 * (3 * L ^ (2 / 3 : ℝ)) =
          (3 / 32 : ℝ) * (512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ)) := by ring
      _ ≤ (3 / 32 : ℝ) * ((1 / 2 : ℝ) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hd' (by norm_num)
      _ ≤ L ^ 2 := by nlinarith [sq_nonneg L]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaRectangle
namespace OAI

/-! The pole-corrected zeta logarithmic derivative on the entire sparse
Perron rectangle, including bounded heights and points left of one. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.Topology

theorem MRTWeakHurwitzGrowthInput.zeta_sparse_rectangle (h : MRTWeakHurwitzGrowthInput) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ s : ℂ,
      1 - L ^ (-(3 / 4 : ℝ)) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ 4 * Real.exp (2 * L) → s ≠ 1 →
        riemannZeta s ≠ 0 ∧ ‖mrtZetaPoleCorrection s‖ ≤ C * L ^ 2 := by
  obtain ⟨c, C₀, T₀, hc, hC₀, hT₀, hstrip⟩ := h.strip_logderiv
  obtain ⟨C₁, T₁, hC₁, hT₁, hright⟩ := h.zeta_right_growth
  let T := max 2 (max T₀ T₁)
  obtain ⟨a, B, ha, _, hB, hcompact⟩ := mrt_zeta_compact_strip (T + 2)
  have hdecay := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually
    (gt_mem_nhds (lt_min ha (by norm_num : (0 : ℝ) < 1 / 2)))
  have he := (mrt_sparse_contour_budget hc).and
    (hdecay.and ((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop (Real.log 11))))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp he
  refine ⟨C₀ + 9 * C₁ + B + 1, L₀, by positivity, ?_⟩
  intro L hL s hσ hσ2 ht hs1
  obtain ⟨hbudget, hδ, hL1, hL11⟩ := hL₀ L hL
  have hLa : L ^ (-(3 / 4 : ℝ)) ≤ a := hδ.le.trans (min_le_left _ _)
  have hLh : L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 := hδ.le.trans (min_le_right _ _)
  have hσh : 1 / 2 ≤ s.re := by linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  by_cases hheight : T ≤ |s.im|
  · have ht₀ : T₀ ≤ |s.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hheight)
    have ht₁ : T₁ ≤ |s.im| := (le_max_right _ _).trans ((le_max_right _ _).trans hheight)
    have ht₂ : 2 ≤ |s.im| := (le_max_left _ _).trans hheight
    have hpar := hbudget s.im ht
    have hH := mrt_sparse_contour_height hL11 (by linarith) ht
    have hsrep : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
      rw [mul_comm]
      exact Complex.re_add_im s
    have hg : riemannZeta s ≠ 0 ∧
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ (C₀ + 9 * C₁) * L ^ 2 := by
      by_cases hsupper : s.re ≤ 1 + mrtVKRadius (2 * s.im) / 16
      · have hh := hstrip 1 (1 : DirichletCharacter ℂ 1) s.im s.re ht₀
          (by linarith [hpar.1]) hsupper
        simp only [DirichletCharacter.LFunction_modOne_eq, hsrep] at hh
        exact ⟨hh.1, hh.2.trans (by
          have hh' := mul_le_mul_of_nonneg_left hpar.2 hC₀.le
          nlinarith [mul_nonneg hC₁.le (sq_nonneg L)])⟩
      · have hσ1 : 1 < s.re := by
          have hr := Real.rpow_pos_of_pos (mrt_VKLog_pos (2 * s.im)) (-(2 / 3 : ℝ))
          change 0 < mrtVKRadius (2 * s.im) at hr
          linarith
        have hh := hright s.re s.im ht₁ hσ1
        rw [Complex.re_add_im] at hh
        refine ⟨riemannZeta_ne_zero_of_one_le_re hσ1.le, hh.trans ?_⟩
        have hH0 := (mrt_VKLog_pos (2 * s.im)).le
        have hh' : (mrtVKLog (2 * s.im)) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
        have hh'' := mul_le_mul_of_nonneg_left hh' hC₁.le
        nlinarith [mul_nonneg hC₀.le (sq_nonneg L)]
    have hi : ‖(s - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have hn : 1 ≤ ‖s - 1‖ := by
        have hh := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
        linarith
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    refine ⟨hg.1, ?_⟩
    unfold mrtZetaPoleCorrection
    have hh := norm_sub_le (-deriv riemannZeta s / riemannZeta s) ((s - 1)⁻¹)
    rw [neg_div, norm_neg] at hh
    rw [neg_div]
    nlinarith [mul_nonneg hB (sq_nonneg L)]
  · have hn : ‖s‖ ≤ T + 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hh
      linarith
    have hh := hcompact s (by linarith) hn hs1
    refine ⟨hh.1, hh.2.trans ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hLsq hB,
      mul_nonneg hC₀.le (sq_nonneg L), mul_nonneg hC₁.le (sq_nonneg L)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszBoundary
namespace OAI

/-! Boundary bounds for the actual shifted zeta integrand. The pole is
kept separate, so bounded heights are included in the same rectangle. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter _root_.Set
open scoped _root_.Topology

lemma mrt_zeta_logderiv_of_correction {s : ℂ} {B D : ℝ}
    (hc : ‖mrtZetaPoleCorrection s‖ ≤ B) (hi : ‖(s - 1)⁻¹‖ ≤ D) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ B + D := by
  have hh := norm_add_le (mrtZetaPoleCorrection s) ((s - 1)⁻¹)
  have he : mrtZetaPoleCorrection s + (s - 1)⁻¹ =
      -deriv riemannZeta s / riemannZeta s := by
    unfold mrtZetaPoleCorrection
    ring
  rw [he] at hh
  exact hh.trans (add_le_add hc hi)

theorem MRTWeakHurwitzGrowthInput.riesz_boundary_oai (h : MRTWeakHurwitzGrowthInput) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ L : ℝ, L₀ ≤ L → 1 ≤ L →
      L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 → ∀ b T u : ℝ,
      1 < b → b ≤ 2 → 2 ≤ T → T ≤ 2 * Real.exp (2 * L) → |u| ≤ T / 2 →
      (∀ s ∈ Rectangle
        (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
        s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0) ∧
      (∀ t ∈ Icc (-T) T,
        ‖-deriv riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤
          K * L ^ 2) ∧
      (∀ σ ∈ Icc (1 - L ^ (-(3 / 4 : ℝ))) b, ∀ t : ℝ, |t| = T →
        ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ K * L ^ 2) := by
  obtain ⟨C, L₀, hC, hr⟩ := h.zeta_sparse_rectangle
  refine ⟨C + 1, L₀, by positivity, ?_⟩
  intro L hL₀ hL hδ b T u hb hb2 hT hTup hu
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hδ0 : 0 < L ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hheight {t : ℝ} (ht : |t| ≤ T) :
      |t + u| ≤ 4 * Real.exp (2 * L) := by
    have hh := abs_add_le t u
    linarith [Real.exp_pos (2 * L)]
  have happ {σ t : ℝ} (hσ : 1 - L ^ (-(3 / 4 : ℝ)) ≤ σ)
      (hσ2 : σ ≤ 2) (ht : |t| ≤ T)
      (hne : (σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I ≠ 1) :=
    hr L hL₀ ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)
      (by simpa using hσ) (by simpa using hσ2) (by simpa using hheight ht) hne
  refine ⟨?_, ?_, ?_⟩
  · intro s hs hs1
    have hab : 1 - L ^ (-(3 / 4 : ℝ)) ≤ b := by linarith
    have hm : s.re ∈ Icc (1 - L ^ (-(3 / 4 : ℝ))) b ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab,
        uIcc_of_le (show -T ≤ T by linarith)] using hs
    exact (hr L hL₀ (s + (u : ℂ) * Complex.I) (by simpa using hm.1.1)
      (by simpa using hm.1.2.trans hb2)
      (by simpa using hheight (abs_le.mpr hm.2)) hs1).1
  · intro t ht
    let s : ℂ := ((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) +
      (t : ℂ) * Complex.I + (u : ℂ) * Complex.I
    have hn : L ^ (-(3 / 4 : ℝ)) ≤ ‖s - 1‖ := by
      have hh := Complex.abs_re_le_norm (s - 1)
      have he : (s - 1).re = -L ^ (-(3 / 4 : ℝ)) := by simp [s]
      rw [he, abs_neg, abs_of_nonneg hδ0.le] at hh
      exact hh
    have hs1 : s ≠ 1 := by intro he; simp [he] at hn; linarith
    have hi : ‖(s - 1)⁻¹‖ ≤ L ^ 2 := by
      rw [norm_inv]
      have hi := one_div_le_one_div_of_le hδ0 hn
      simp only [one_div] at hi
      apply hi.trans
      rw [← Real.rpow_neg hL0.le, neg_neg, ← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    have hc := (happ le_rfl (by linarith) (abs_le.mpr ht) hs1).2
    exact (mrt_zeta_logderiv_of_correction hc hi).trans_eq (by ring)
  · intro σ hσ t ht
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I
    have hn : 1 ≤ ‖s - 1‖ := by
      have hh := Complex.abs_im_le_norm (s - 1)
      have ha := abs_add_le (t + u) (-u)
      rw [add_neg_cancel_right, abs_neg, ht] at ha
      have he : (s - 1).im = t + u := by simp [s]
      rw [he] at hh
      linarith
    have hs1 : s ≠ 1 := by intro he; norm_num [he] at hn
    have hi : ‖(s - 1)⁻¹‖ ≤ L ^ 2 := by
      rw [norm_inv]
      have hi : ‖s - 1‖⁻¹ ≤ 1 := by
        simpa only [one_div, inv_one] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
      exact hi.trans hLsq
    have hc := (happ hσ.1 (hσ.2.trans hb2) ht.le hs1).2
    exact (mrt_zeta_logderiv_of_correction hc hi).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_boundary_oai := @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_boundary_oai
