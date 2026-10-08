-- Prove2me | solution 1 for OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_sparse_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:08:23.146606+00:00
-- url     : https://prove2.me/submissions/73daa281-a44a-4009-8a8d-af8a08fe8032

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_boundary
import Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_far_tail

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





theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)






lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩


lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩



lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]





lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * Complex.I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * Complex.I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * Complex.I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * Complex.I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]





theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩





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

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + Complex.I • ?_ - Complex.I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]




theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorderNoPIntegrable hf.continuousOn
    (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := ContinuousOn.rectangleBorderIntegrable hf.continuousOn














theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * Complex.I)⁻¹ = (x - Complex.I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (preTransparency := .instances) (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * Complex.I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * Complex.I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * Complex.I) = A * x / (x ^ 2 + y ^ 2) - A * Complex.I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [Complex.inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * Complex.I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * Complex.I) =
    A / Complex.I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / Complex.I * Complex.I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * Complex.I) = A / Complex.I / (y + ↑(-x) * Complex.I) := by
    have e1 : x + y * Complex.I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + Complex.I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * Complex.I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * Complex.I) * (2 * Complex.I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]


lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

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

theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)

theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq




























end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel
namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open _root_.Complex


lemma modFive_perron_denominator_vertical {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (1 + t ^ 2) / 4 ≤
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 4 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t, sq_nonneg (σ - 1 / 2)]

lemma modFive_perron_denominator_horizontal (σ t : ℝ) :
    t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
      ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have h1 : |t| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have h2 : |t| ≤ ‖z + 1‖ := by simpa [z] using Complex.abs_im_le_norm (z + 1)
  have hm := mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
  simpa only [← sq, sq_abs, norm_mul] using hm

lemma modFive_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * x ^ σ / (1 + t ^ 2) := by
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  have hd := modFive_perron_denominator_vertical hσ t
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hp hd).trans_eq (by
    field_simp)

lemma modFive_perron_kernel_horizontal {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ x ^ σ / t ^ 2 := by
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (sq_pos_of_ne_zero ht)
    (modFive_perron_denominator_horizontal σ t)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszKernel
namespace OAI

/-! A positive quadratic Riesz weight and its exact Mellin kernel. The
third denominator gives the additional decay needed by sparse prime duality. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory
open scoped _root_.Classical



lemma mrt_riesz_square_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin mrtRieszSquare s (2 / (s * (s + 1) * (s + 2))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have h2 := hasMellin_cpow_Ioc (2 : ℂ) (s := s) (by simpa using (show 0 < s.re + 2 by linarith))
  have h11 := hasMellin_add h1.1 h1.1
  have hd := hasMellin_sub h0.1 h11.1
  have hf := hasMellin_add hd.1 h2.1
  have he : ∀ t ∈ Ioi (0 : ℝ), mrtRieszSquare t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        ((Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t +
         (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) +
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (2 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp only [mrtRieszSquare, max_eq_left (sub_nonneg.mpr ht1), indicator_of_mem hm,
        Complex.cpow_one, Complex.cpow_ofNat, Complex.ofReal_pow, Complex.ofReal_sub,
        Complex.ofReal_one]
      ring
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [mrtRieszSquare, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent mrtRieszSquare s :=
    hf.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin mrtRieszSquare s = mellin (fun t =>
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        ((Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t +
         (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) +
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (2 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - (1 / (s + 1) + 1 / (s + 1)) + 1 / (s + 2) := by
      rw [hf.2, hd.2, h11.2, h0.2, h1.2, h2.2]
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      have hs2 : s + 2 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma mrt_riesz_square_continuous : Continuous mrtRieszSquare := by
  unfold mrtRieszSquare
  fun_prop

lemma mrt_riesz_kernel_factor (x : ℝ) (s : ℂ) :
    mrtRieszKernel x s = modFivePerronKernel x s * (2 / (s + 2)) := by
  unfold mrtRieszKernel modFivePerronKernel
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma mrt_riesz_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 * x ^ σ / (1 + t ^ 2) := by
  have hl : (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖ := by
    have hh := Complex.re_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + 2)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, zero_mul, mul_zero, sub_self, add_zero] at hh
    norm_num at hh
    linarith
  have hf : ‖(2 : ℂ) / ((σ : ℂ) + (t : ℂ) * Complex.I + 2)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by linarith)).mpr hl
  rw [mrt_riesz_kernel_factor, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hf).trans
    (modFive_perron_kernel_vertical hx hσ t)

lemma mrt_riesz_kernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h2 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 2 ≠ 0 := by
    intro t he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  have hc : Continuous (fun t : ℝ => mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    simp only [mrt_riesz_kernel_factor]
    apply Continuous.mul
    · unfold modFivePerronKernel
      apply Continuous.div
      · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
          fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      · fun_prop
      · intro t
        apply mul_ne_zero
        · intro he
          have hh := congrArg Complex.re he
          norm_num at hh
          linarith
        · intro he
          have hh := congrArg Complex.re he
          norm_num at hh
          linarith
    · exact continuous_const.div (by fun_prop) h2
  have hm : Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  exact hm.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (mrt_riesz_kernel_vertical hx hσ))

lemma mrt_riesz_square_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin mrtRieszSquare) σ := by
  apply (mrt_riesz_kernel_integrable (by norm_num : (0 : ℝ) < 1) hσ).congr
  filter_upwards [] with t
  have hs : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simpa using (show 0 < σ by linarith)
  rw [(mrt_riesz_square_hasMellin hs).2]
  simp [mrtRieszKernel]

theorem mrt_riesz_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (mrtRieszKernel x) σ = mrtRieszSquare (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ mrtRieszSquare (one_div_pos.mpr hx)
    (mrt_riesz_square_hasMellin (by simpa using hsp)).1
    (mrt_riesz_square_verticalIntegrable hσ) (mrt_riesz_square_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin mrtRieszSquare ((σ : ℂ) + (t : ℂ) * Complex.I) =
          mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (mrt_riesz_square_hasMellin (by simpa using hsp)).2]
    unfold mrtRieszKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszSeries
namespace OAI

/-! Absolute series interchange and the exact finite quadratic Riesz
formula for arbitrary absolutely convergent Dirichlet series. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf CS Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err F_add F_mul F_neg F_sub H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR deriv_ofReal e e_apply f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta nnnorm_circle_smul nnnorm_eq_of_mem_circle riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators

lemma mrt_riesz_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * mrtRieszKernel x s =
      a n * mrtRieszKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold mrtRieszKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma mrt_riesz_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [mrt_riesz_term_kernel a hn hx]
    exact (mrt_riesz_kernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma mrt_riesz_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem mrt_riesz_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * mrtRieszKernel x s) σ =
      ∑' n : ℕ, VerticalIntegral'
        (fun s => LSeries.term a s n * mrtRieszKernel x s) σ := by
  have hi := mrt_riesz_kernel_integrable hx hσ
  have hterms := fun n => mrt_riesz_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [mrt_riesz_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma mrt_riesz_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    VerticalIntegral' (fun s => LSeries.term a s n * mrtRieszKernel x s) σ =
      a n * mrtRieszSquare ((n : ℝ) / x) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * mrtRieszKernel x s) =
      fun s => a n * mrtRieszKernel (x / (n : ℝ)) s := by
    funext s
    exact mrt_riesz_term_kernel a hn hx s
  rw [hk]
  have hconst : VerticalIntegral' (fun s => a n * mrtRieszKernel (x / (n : ℝ)) s) σ =
      a n * VerticalIntegral' (mrtRieszKernel (x / (n : ℝ))) σ := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst, mrt_riesz_inversion (div_pos hx hn') hσ]
  congr 2
  field_simp

theorem mrt_riesz_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * mrtRieszKernel x s) σ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * mrtRieszSquare ((n : ℝ) / x) := by
  rw [mrt_riesz_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * mrtRieszKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [mrt_riesz_term_value a hn0 hx hσ]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (Finset.mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hlarge
      have hquot : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by linarith)
      simp [mrtRieszSquare, max_eq_right (by linarith : 1 - (n : ℝ) / x ≤ 0)]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro n hn
  exact mrt_riesz_term_value a (by have hh := (Finset.mem_Icc.mp hn).1; omega) hx hσ

end TwoPointCorrelations

end OAI

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

































































































































open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveRectangleShift
namespace OAI

/-! The exact finite rectangle shift, with an explicit horizontal cost.
All functions are complex scalar functions, as needed for the three fixed
nonprincipal Dirichlet L-functions.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory _root_.intervalIntegral
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike DeltaSpikeContinuous I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of



lemma modFive_vertical_quadratic_bound {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc (-T) T, ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / (1 + t ^ 2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D * Real.pi := by
  rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  have hgi : IntervalIntegrable (fun t : ℝ => D / (1 + t ^ 2)) volume (-T) T := by
    simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul D).intervalIntegrable
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall fun t ht => hf t ⟨ht.1.le, ht.2⟩) hgi
  refine hb.trans ?_
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
  apply mul_le_mul_of_nonneg_left _ hD
  linarith [Real.arctan_lt_pi_div_two T, Real.neg_pi_div_two_lt_arctan (-T)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszBounds
namespace OAI

/-! Pointwise and finite-contour estimates for the quadratic Riesz kernel. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory _root_.intervalIntegral
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike DeltaSpikeContinuous I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of

lemma mrt_riesz_kernel_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) :
    DifferentiableAt ℂ (mrtRieszKernel x) s := by
  unfold mrtRieszKernel
  apply DifferentiableAt.div
  · exact ((hasDerivAt_id s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt.const_mul 2
  · fun_prop
  · exact mul_ne_zero (mul_ne_zero hs hs1) hs2

lemma mrt_riesz_kernel_cubic {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * x ^ σ / |t| ^ 3 := by
  have hn : |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + 2)
  have hf : ‖(2 : ℂ) / ((σ : ℂ) + (t : ℂ) * Complex.I + 2)‖ ≤ 2 / |t| := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr ht) hn
  rw [mrt_riesz_kernel_factor, norm_mul]
  calc
    _ ≤ (x ^ σ / t ^ 2) * (2 / |t|) :=
      mul_le_mul (modFive_perron_kernel_horizontal hx σ ht) hf (norm_nonneg _) (by positivity)
    _ = _ := by rw [← sq_abs t]; ring

lemma mrt_riesz_kernel_pole {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖mrtRieszKernel x (1 - (u : ℂ) * Complex.I)‖ ≤ 4 * x / (1 + u ^ 2) := by
  have he : (1 : ℂ) - (u : ℂ) * Complex.I = (1 : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  simpa using mrt_riesz_kernel_vertical hx (by norm_num : (1 / 2 : ℝ) ≤ 1) (-u)


lemma mrt_rectangle_pole_shift_bound {f : ℂ → ℂ} {a b T B : ℝ} {A : ℂ}
    (hab : a ≤ b)
    (hres : RectangleIntegral' f ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ)) = A)
    (hup : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B)
    (hdown : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A‖ ≤
      (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) / (2 * Real.pi) := by
  have htop : ‖HIntegral f a b T‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hup σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hbot : ‖HIntegral f a b (-T)‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hdown σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hid : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)) := by
    rw [← hres]
    simp only [RectangleIntegral', RectangleIntegral, smul_eq_mul, Complex.sub_re,
      Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add]
    ring
  rw [hid, norm_mul]
  have hn : ‖1 / (2 * (Real.pi : ℂ) * Complex.I)‖ = 1 / (2 * Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs, Real.pi_nonneg]
  rw [hn]
  have hm : ‖VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)‖ ≤
      ‖VIntegral f a (-T) T‖ + 2 * B * (b - a) := by
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszMangoldt
namespace OAI

/-! The positive quadratic Riesz prime majorant is exactly an integral
of the logarithmic derivative of zeta. No cutoff is moved or rounded. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970 _root_.Finset _root_.ArithmeticFunction
open scoped _root_.Classical



lemma mrt_mangoldt_twist_term (u : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (mrtMangoldtTwist u) s n =
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (s + (u : ℂ) * Complex.I) n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      mrtMangoldtTwist, Complex.cpow_neg, Complex.cpow_add _ _ hnC]
    ring

lemma mrt_mangoldt_twist_summable (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mrtMangoldtTwist u) s := by
  have ht : 1 < (s + (u : ℂ) * Complex.I).re := by simpa using hs
  exact (LSeriesSummable_vonMangoldt ht).congr (fun n => (mrt_mangoldt_twist_term u s n).symm)

lemma mrt_mangoldt_twist_LSeries (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrtMangoldtTwist u) s =
      -deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)]
  exact tsum_congr (mrt_mangoldt_twist_term u s)

lemma mrt_mangoldt_twist_phase (u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    mrtMangoldtTwist u n = (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (((-Real.log (n : ℝ) * u : ℝ) : ℂ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold mrtMangoldtTwist
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  push_cast
  ring

theorem mrt_riesz_mangoldt_finite_sum {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (u : ℝ) :
    VerticalIntegral' (mrtZetaRieszIntegrand x u) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, mrtMangoldtTwist u n * mrtRieszSquare ((n : ℝ) / x) := by
  have he := mrt_riesz_finite_sum (mrtMangoldtTwist u) hx (by linarith : 1 / 2 ≤ σ)
    (mrt_mangoldt_twist_summable u (by simpa using hσ))
  unfold VerticalIntegral' VerticalIntegral
  unfold VerticalIntegral' VerticalIntegral at he
  rw [← he]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mrtZetaRieszIntegrand, mrt_mangoldt_twist_LSeries u (by simpa using hσ)]

theorem mrt_riesz_prime_kernel_integral {Y σ : ℝ} (hY : 0 < Y) (hσ : 1 < σ) (u : ℝ) :
    mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
      (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
      (fun n => -Real.log (n : ℝ)) u =
        4 * VerticalIntegral' (mrtZetaRieszIntegrand (4 * Y) u) σ := by
  rw [mrt_riesz_mangoldt_finite_sum (by positivity) hσ]
  unfold mrtExponentialPolynomial mrtRieszPrimeSupport
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [mrt_mangoldt_twist_phase u (by have h := (mem_Icc.mp hn).1; omega)]
  unfold mrtRieszPrimeWeight mrtRieszSquare
  push_cast
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszPole
namespace OAI

/-! The actual shifted Riesz integrand has exactly the zeta pole, with
residue equal to the Riesz kernel at the shifted pole. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter _root_.Asymptotics
open scoped _root_.Topology

lemma mrt_riesz_integrand_simple_pole {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (mrtZetaRieszIntegrand x u - (fun s =>
      mrtRieszKernel x (1 - (u : ℂ) * Complex.I) / (s - (1 - (u : ℂ) * Complex.I))))
      =O[𝓝[≠] (1 - (u : ℂ) * Complex.I)] (1 : ℂ → ℂ) := by
  let p : ℂ := 1 - (u : ℂ) * Complex.I
  have hadd : Tendsto (fun s : ℂ => s + (u : ℂ) * Complex.I) (𝓝[≠] p) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun s : ℂ => s + (u : ℂ) * Complex.I) := by fun_prop
      have hh := hc.continuousAt.tendsto.mono_left
        (show 𝓝[≠] p ≤ 𝓝 p from nhdsWithin_le_nhds)
      have he : p + (u : ℂ) * Complex.I = 1 := by dsimp [p]; ring
      simpa only [he] using hh
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s + (u : ℂ) * Complex.I ≠ 1
      change s ≠ p at hs
      intro he
      apply hs
      dsimp [p]
      linear_combination he
  have hpole : (fun s : ℂ =>
      -deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) - (s - p)⁻¹)
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have hh := Erdos970.riemannZetaLogDerivResidueBigO.comp_tendsto hadd
    convert (preTransparency := .instances) hh using 1
    · funext s
      simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply]
      congr 1
      dsimp [p]
      ring
    · rfl
  have hk : DifferentiableAt ℂ (mrtRieszKernel x) p := by
    apply mrt_riesz_kernel_differentiableAt hx
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
    · intro he
      have hh := congrArg Complex.re he
      norm_num [p] at hh
  have hb : mrtRieszKernel x =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    hk.continuousAt.isBigO.mono nhdsWithin_le_nhds
  have hd : (fun s : ℂ => mrtRieszKernel x s - mrtRieszKernel x p)
      =O[𝓝[≠] p] (fun s : ℂ => s - p) := hk.isBigO_sub.mono nhdsWithin_le_nhds
  obtain ⟨C₁, hC₁, h₁⟩ := hpole.exists_nonneg
  obtain ⟨C₂, hC₂, h₂⟩ := hb.exists_nonneg
  obtain ⟨C₃, _, h₃⟩ := hd.exists_nonneg
  apply IsBigO.of_bound (C₁ * C₂ + C₃)
  filter_upwards [h₁.bound, h₂.bound, h₃.bound, self_mem_nhdsWithin] with s hs₁ hs₂ hs₃ hs
  change s ≠ p at hs
  simp only [Pi.one_apply, norm_one, mul_one] at hs₁ hs₂ ⊢
  have hq : ‖(mrtRieszKernel x s - mrtRieszKernel x p) / (s - p)‖ ≤ C₃ := by
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs))).mpr hs₃
  have hid : mrtZetaRieszIntegrand x u s - mrtRieszKernel x p / (s - p) =
      (-deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) - (s - p)⁻¹) * mrtRieszKernel x s +
          (mrtRieszKernel x s - mrtRieszKernel x p) / (s - p) := by
    unfold mrtZetaRieszIntegrand
    ring
  change ‖mrtZetaRieszIntegrand x u s - mrtRieszKernel x p / (s - p)‖ ≤ _
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul hs₁ hs₂ (norm_nonneg _) hC₁) hq

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszContour
namespace OAI

/-! The finite residue shift for the actual smoothed Mangoldt integrand.
Analytic input appears only as nonvanishing and boundary norm bounds. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970
open scoped _root_.Topology

lemma mrt_zeta_riesz_residue {x a b T u : ℝ} (hx : 0 < x)
    (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b) (hu : |u| < T)
    (hzero : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0) :
    RectangleIntegral' (mrtZetaRieszIntegrand x u)
      ((a : ℂ) - Complex.I * (T : ℂ)) ((b : ℂ) + Complex.I * (T : ℂ)) =
        mrtRieszKernel x (1 - (u : ℂ) * Complex.I) := by
  have hab : a ≤ b := by linarith
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  apply ResidueTheoremOnRectangleWithSimplePole' (p := 1 - (u : ℂ) * Complex.I)
  · simpa using hab
  · simp
    linarith
  · rw [rectangle_mem_nhds_iff]
    simpa [Complex.mem_reProdIm, uIoo_of_le hab, uIoo_of_le (show -T ≤ T by linarith),
      Complex.mul_re, Complex.mul_im] using
      (show (a < 1 ∧ 1 < b) ∧ -T < -u ∧ -u < T from ⟨⟨ha1, hb⟩, by
        have := abs_lt.mp hu
        linarith, by have := abs_lt.mp hu; linarith⟩)
  · intro s hs
    have hsr : a ≤ s.re := by
      have hh : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
        simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab,
          uIcc_of_le (show -T ≤ T by linarith)] using hs.1
      exact hh.1.1
    have hne : s + (u : ℂ) * Complex.I ≠ 1 := by
      intro he
      apply hs.2
      change s = 1 - (u : ℂ) * Complex.I
      linear_combination he
    have hn := hzero s hs.1 hne
    have hadd : DifferentiableAt ℂ (fun z : ℂ => z + (u : ℂ) * Complex.I) s := by fun_prop
    have hd := ((analyticOn_riemannZeta _ hne).deriv.differentiableAt.comp s hadd).neg
    have hz := (differentiableAt_riemannZeta hne).comp s hadd
    have hk := mrt_riesz_kernel_differentiableAt hx (s := s)
      (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; norm_num at hh; linarith)
    exact ((hd.div hz hn).mul hk).differentiableWithinAt
  · exact mrt_riesz_integrand_simple_pole hx u

theorem mrt_zeta_riesz_finite_shift {x a b T u B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b)
    (hu : |u| < T) (hB : 0 ≤ B)
    (hzero : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0)
    (hleft : ∀ t ∈ Icc (-T) T,
      ‖-deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B)
    (hside : ∀ σ ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
        4 * x / (1 + u ^ 2) +
          (4 * B * x ^ a * Real.pi + 4 * B * x ^ b / T ^ 3 * (b - a)) / (2 * Real.pi) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  have hab : a ≤ b := by linarith
  have hres := mrt_zeta_riesz_residue hx0 ha ha1 hb hu hzero
  have hsides (t : ℝ) (ht : |t| = T) : ∀ σ ∈ Icc a b,
      ‖mrtZetaRieszIntegrand x u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * B * x ^ b / T ^ 3 := by
    intro σ hσ
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    rw [mrtZetaRieszIntegrand, norm_mul]
    have hh := mul_le_mul (hside σ hσ t ht) (mrt_riesz_kernel_cubic hx0 σ ht0)
      (norm_nonneg _) hB
    rw [ht] at hh
    apply hh.trans
    have hp := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * B by positivity)
    calc
      B * (2 * x ^ σ / T ^ 3) = (2 * B * x ^ σ) / T ^ 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hm (by positivity)
  have hv : ‖VIntegral (mrtZetaRieszIntegrand x u) a (-T) T‖ ≤
      4 * B * x ^ a * Real.pi := by
    apply modFive_vertical_quadratic_bound hT.le (by positivity)
    intro t ht
    rw [mrtZetaRieszIntegrand, norm_mul]
    exact (mul_le_mul (hleft t ht) (mrt_riesz_kernel_vertical hx0 ha t)
      (norm_nonneg _) hB).trans_eq (by ring)
  have hh := mrt_rectangle_pole_shift_bound hab hres
    (hsides T (abs_of_pos hT)) (hsides (-T) (by simp [abs_of_pos hT]))
  have hadd := norm_add_le
    ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T - mrtRieszKernel x (1 - (u : ℂ) * Complex.I))
    (mrtRieszKernel x (1 - (u : ℂ) * Complex.I))
  rw [sub_add_cancel] at hadd
  apply hadd.trans
  have hp := mrt_riesz_kernel_pole hx0 u
  have hsum : ‖VIntegral (mrtZetaRieszIntegrand x u) a (-T) T‖ +
      2 * (2 * B * x ^ b / T ^ 3) * (b - a) ≤
      4 * B * x ^ a * Real.pi + 2 * (2 * B * x ^ b / T ^ 3) * (b - a) := by
    linarith only [hv]
  have hv' := div_le_div_of_nonneg_right hsum (show 0 ≤ 2 * Real.pi by positivity)
  exact (add_le_add (hh.trans hv') hp).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseAbscissa
namespace OAI

/-! Elementary abscissa and height choices for the sparse-prime contour.
The estimates are uniform in the positive cutoff, including arbitrarily
large cutoffs. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Topology

lemma mrt_sparse_right_abscissa {x : ℝ} (hx : 8 ≤ x) :
    1 < 1 + 1 / Real.log x ∧ 1 + 1 / Real.log x ≤ 2 ∧
      x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    linarith [Real.exp_one_lt_d9]
  have hl0 : 0 < Real.log x := by linarith
  refine ⟨by have hp := one_div_pos.mpr hl0; linarith, ?_, ?_⟩
  · have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlog
    norm_num at hh
    rw [one_div]
    linarith
  · rw [Real.rpow_def_of_pos hx0]
    have he : Real.log x * (1 + 1 / Real.log x) = 1 + Real.log x := by
      field_simp
      ring
    rw [he, Real.exp_add, Real.exp_log hx0]

lemma mrt_sparse_left_power {L Y : ℝ} (hL : 0 < L) (hY : 2 ≤ Y) :
    (4 * Y) ^ (1 - L ^ (-(3 / 4 : ℝ))) ≤
      4 * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hx0 : 0 < 4 * Y := by positivity
  have hlogs : Real.log Y ≤ Real.log (4 * Y) :=
    Real.log_le_log hY0 (by linarith)
  rw [Real.rpow_def_of_pos hx0]
  have he : Real.log (4 * Y) * (1 - L ^ (-(3 / 4 : ℝ))) =
      Real.log (4 * Y) - L ^ (-(3 / 4 : ℝ)) * Real.log (4 * Y) := by ring
  rw [he, Real.exp_sub, Real.exp_log hx0]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  apply Real.exp_le_exp.mpr
  rw [Real.rpow_neg hL.le]
  have hp := mul_le_mul_of_nonneg_left hlogs
    (inv_nonneg.mpr (Real.rpow_nonneg hL.le (3 / 4 : ℝ)))
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith only [hp]

lemma mrt_sparse_height_choices (T₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 ∧
      T₀ ≤ Real.exp (2 * L) ∧ 2 * Real.exp L ≤ Real.exp (2 * L) / 2 ∧
      (5 * Real.exp (2 * L)) * (Real.exp (2 * L)) ^ (-(3 / 2 : ℝ)) ≤ 1 ∧
      (5 * Real.exp (2 * L)) * L ^ 2 / (Real.exp (2 * L)) ^ 3 ≤ 1 := by
  have hd := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have he := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
    (by norm_num : (0 : ℝ) < 2))).eventually (eventually_ge_atTop T₀)
  have hp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    2 4 (by norm_num)).const_mul 5
  simp only [mul_zero] at hp
  filter_upwards [hd, he, hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 5)] with L hd he hp hL hL5
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hE : 5 ≤ Real.exp L := (Real.log_le_iff_le_exp (by norm_num)).mp hL5
  have hprod : Real.exp (2 * L) = Real.exp L * Real.exp L := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
  refine ⟨hL, hd.le, he, ?_, ?_, ?_⟩
  · rw [hprod]
    nlinarith [Real.exp_pos L]
  · rw [← Real.exp_mul, show 2 * L * (-(3 / 2 : ℝ)) = -3 * L by ring]
    rw [show 5 * Real.exp (2 * L) * Real.exp (-3 * L) =
      5 * Real.exp (-L) by rw [mul_assoc, ← Real.exp_add]; congr 2; ring]
    rw [Real.exp_neg]
    exact (div_le_one (Real.exp_pos L)).mpr hE
  · have hid : 5 * Real.exp (2 * L) * L ^ 2 / Real.exp (2 * L) ^ 3 =
        5 * (L ^ (2 : ℝ) * Real.exp (-4 * L)) := by
      rw [Real.rpow_two, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
      norm_num only [Nat.cast_ofNat]
      rw [show 5 * Real.exp (2 * L) * L ^ 2 * Real.exp (-(3 * (2 * L))) =
        5 * L ^ 2 * (Real.exp (2 * L) * Real.exp (-(3 * (2 * L)))) by ring,
        ← Real.exp_add]
      rw [show 2 * L + -(3 * (2 * L)) = -4 * L by ring]
      ring
    rw [hid]
    exact hp.le

lemma mrt_sparse_frequency_height {L u : ℝ} (hL : 0 ≤ L)
    (hu : |u| ≤ 2 * Real.exp L) : 1 + u ^ 2 ≤ 5 * Real.exp (2 * L) := by
  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by linarith)
  have hh : u ^ 2 ≤ 4 * Real.exp (2 * L) := by
    have hs := sq_le_sq₀ (abs_nonneg u) (by positivity : 0 ≤ 2 * Real.exp L)
    have hp := hs.mpr hu
    rw [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
      ← Real.exp_nat_mul] at hp
    simpa only [Nat.cast_ofNat] using hp
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszEstimate
namespace OAI

/-! The sparse-prime Riesz kernel estimate, with no upper restriction on
the prime cutoff. Far tails are charged to the pole term. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter _root_.Set _root_.Erdos970 _root_.OAI.Erdos970
open scoped _root_.Topology

lemma mrt_riesz_finite_shift_simple {x a b T u B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b) (hb2 : b ≤ 2)
    (hu : |u| < T) (hB : 0 ≤ B)
    (hz : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0)
    (hl : ∀ t ∈ Icc (-T) T,
      ‖-deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B)
    (hs : ∀ σ ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
        4 * x / (1 + u ^ 2) + 2 * B * x ^ a + 4 * B * x ^ b / T ^ 3 := by
  have hh := mrt_zeta_riesz_finite_shift hx ha ha1 hb hu hB hz hl hs
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  have hD : 0 ≤ 4 * B * x ^ b / T ^ 3 := by positivity
  have hside : (4 * B * x ^ b / T ^ 3 * (b - a)) / (2 * Real.pi) ≤
      4 * B * x ^ b / T ^ 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    exact mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hD
  have he : (4 * B * x ^ a * Real.pi) / (2 * Real.pi) = 2 * B * x ^ a := by
    field_simp
    ring
  apply hh.trans
  rw [add_div, he]
  linarith only [hside]

theorem MRTWeakHurwitzGrowthInput.riesz_sparse_kernel_oai (h : MRTWeakHurwitzGrowthInput) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
      ∀ u : ℝ, |u| ≤ 2 * Real.exp L →
      ‖mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
        (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => -Real.log (n : ℝ)) u‖ ≤
          C * Y / (1 + u ^ 2) + C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by
  obtain ⟨K, Lr, hK, hb⟩ := h.riesz_boundary
  obtain ⟨D, Tr, hD, hTr, ht⟩ := h.riesz_far_tail
  have he := (mrt_sparse_height_choices (max 2 Tr)).and (eventually_ge_atTop Lr)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp he
  let C := 1000 * (K + D + 1) * (Real.exp 1 + 1)
  refine ⟨C, L₀, by dsimp [C]; positivity, ?_⟩
  intro L Y hL₀' hL hY u hu
  obtain ⟨⟨_, hδ, hT, hU, htail, hside⟩, hLr⟩ := hL₀ L hL₀'
  let x := 4 * Y
  let a := 1 - L ^ (-(3 / 4 : ℝ))
  let b := 1 + 1 / Real.log x
  let T := Real.exp (2 * L)
  let Z := Y / (1 + u ^ 2)
  let E := Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hx : 8 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hb1, hb2, hxb⟩ := mrt_sparse_right_abscissa hx
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith [Real.rpow_pos_of_pos hL0 (-(3 / 4 : ℝ))]
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by positivity
  have huT : |u| ≤ T / 2 := hu.trans hU
  have huT' : |u| < T := by linarith
  obtain ⟨hz, hl, hs⟩ := hb L hLr hL hδ b T u hb1 hb2 hT2
    (by dsimp [T]; linarith [Real.exp_pos (2 * L)]) huT
  have hf := mrt_riesz_finite_shift_simple (by linarith : 1 ≤ x) ha ha1 hb1 hb2 huT'
    (by positivity : 0 ≤ K * L ^ 2) hz hl hs
  have hfar := ht x b T u hx0 hb1 ((le_max_right _ _).trans hT) huT
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I) : ℂ)‖ ≤ 1 := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
    apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hv : ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤
      4 * x / (1 + u ^ 2) + 2 * (K * L ^ 2) * x ^ a +
        4 * (K * L ^ 2) * x ^ b / T ^ 3 + D * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
    have hi := norm_add_le
      ((1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral (mrtZetaRieszIntegrand x u) b (-T) T)
      ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VerticalIntegral (mrtZetaRieszIntegrand x u) b - VIntegral (mrtZetaRieszIntegrand x u) b (-T) T))
    have hid : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral (mrtZetaRieszIntegrand x u) b (-T) T +
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          (VerticalIntegral (mrtZetaRieszIntegrand x u) b - VIntegral (mrtZetaRieszIntegrand x u) b (-T) T) =
        VerticalIntegral' (mrtZetaRieszIntegrand x u) b := by
      simp only [VerticalIntegral', smul_eq_mul]
      ring
    rw [hid] at hi
    have hn := mul_le_mul hnorm hfar (norm_nonneg _) (by positivity)
    have hn' : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VerticalIntegral (mrtZetaRieszIntegrand x u) b -
          VIntegral (mrtZetaRieszIntegrand x u) b (-T) T)‖ ≤
        D * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul]
      simpa only [one_mul] using hn
    exact hi.trans (add_le_add hf hn')
  have hfreq := mrt_sparse_frequency_height hL0.le hu
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hleft : 2 * (K * L ^ 2) * x ^ a ≤ 8 * K * E := by
    have hh := mul_le_mul_of_nonneg_left (mrt_sparse_left_power hL0 hY)
      (show 0 ≤ 2 * (K * L ^ 2) by positivity)
    exact hh.trans_eq (by dsimp [E]; ring)
  have hhor : 4 * (K * L ^ 2) * x ^ b / T ^ 3 ≤ 16 * K * Real.exp 1 * Z := by
    dsimp only [Z]
    rw [← mul_div_assoc]
    rw [hxb]
    apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).mpr
    have hh := (mul_le_mul_of_nonneg_left hfreq (show 0 ≤ L ^ 2 / T ^ 3 by positivity)).trans
      (by simpa [T, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hside)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16 * K * Real.exp 1 * Y by positivity)
    dsimp [x]
    convert (preTransparency := .instances) hh' using 1 <;> ring
  have hfar' : D * x ^ b * T ^ (-(3 / 2 : ℝ)) ≤ 4 * D * Real.exp 1 * Z := by
    dsimp only [Z]
    rw [← mul_div_assoc]
    rw [hxb]
    apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).mpr
    have hh := (mul_le_mul_of_nonneg_right hfreq (Real.rpow_nonneg hT0.le (-(3 / 2 : ℝ)))).trans htail
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * D * Real.exp 1 * Y by positivity)
    dsimp [x]
    nlinarith only [hh']
  rw [mrt_riesz_prime_kernel_integral (by linarith : 0 < Y) hb1 u, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hp : 4 * x / (1 + u ^ 2) = 16 * Z := by dsimp [x, Z]; ring
  have hv' : ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤
      16 * Z + 8 * K * E + 16 * K * Real.exp 1 * Z + 4 * D * Real.exp 1 * Z :=
    hv.trans (by linarith only [hleft, hhor, hfar', hp])
  have hC1 : 64 + 64 * K * Real.exp 1 + 16 * D * Real.exp 1 ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos 1, mul_nonneg hK.le (Real.exp_pos 1).le,
      mul_nonneg hD.le (Real.exp_pos 1).le]
  have hC2 : 32 * K ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos 1, mul_nonneg hK.le (Real.exp_pos 1).le,
      mul_nonneg hD.le (Real.exp_pos 1).le]
  have hh := add_le_add (mul_le_mul_of_nonneg_right hC1 hZ)
    (mul_le_mul_of_nonneg_right hC2 hE)
  change 4 * ‖VerticalIntegral' (mrtZetaRieszIntegrand x u) b‖ ≤ _
  calc
    _ ≤ 4 * (16 * Z + 8 * K * E + 16 * K * Real.exp 1 * Z +
        4 * D * Real.exp 1 * Z) :=
      mul_le_mul_of_nonneg_left hv' (by norm_num : (0 : ℝ) ≤ 4)
    _ = (64 + 64 * K * Real.exp 1 + 16 * D * Real.exp 1) * Z + 32 * K * E := by ring
    _ ≤ C * Z + C * E := hh
    _ = _ := by dsimp [Z, E]; ring


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_sparse_kernel_oai := @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_sparse_kernel_oai
