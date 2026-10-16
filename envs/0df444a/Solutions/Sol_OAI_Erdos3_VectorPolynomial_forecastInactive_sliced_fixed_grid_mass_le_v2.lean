-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_grid_mass_le_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T00:56:41.079543+00:00
-- url     : https://prove2.me/submissions/ef6175f5-9119-4cc3-a86e-6ce7a4768014

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveGridDensity_approximation
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactiveSlicedFixedPath_joint_law
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_axis_integer_law
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B174
import Definitions.Def_OAIErdos3B175

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_const {α R : Type*} [DecidableEq α] [CommRing R]
    (c : R) (s : Finset α) : booleanCoefficient (fun _ => c) s = if s = ∅ then c else 0 := by
  have h1 := booleanCoefficient_monomial (R := R) ∅ s
  simp only [Finset.empty_subset, ite_true] at h1
  have hc := booleanCoefficient_const_mul s c (fun _ => (1 : R))
  simpa only [mul_one, h1, mul_ite, mul_zero] using hc

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

variable [Fintype H]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

theorem complexMean_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℂ) :
    (pi p).complexMean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).complexMean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, ((p j).weight x : ℂ) * v j x
  simp_rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => ((p j).weight x : ℂ) * v j x)).symm

end Erdos3.FiniteProbabilityWeights

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem cyclicIntegerCharacter_intCast (M : ℕ) [NeZero M] (r z : ℤ) :
    cyclicIntegerCharacter M z (r : ZMod M) =
      character (((r : ℝ) * (z : ℝ) / M : ℝ) : CircleFourier.Circle) := by
  change character (ZMod.toAddCircle ((r : ZMod M) * (z : ZMod M))) = _
  rw [← Int.cast_mul, ZMod.toAddCircle_intCast]
  simp only [Int.cast_mul]

theorem cyclicIntegerCharacter_eq_zero_iff (M : ℕ) [NeZero M] (z : ℤ) :
    cyclicIntegerCharacter M z = 0 ↔ (z : ZMod M) = 0 := by
  constructor
  · intro h
    have he := DFunLike.congr_fun h (1 : ZMod M)
    change character (ZMod.toAddCircle ((1 : ZMod M) * (z : ZMod M))) = 1 at he
    rw [one_mul, character_eq_one_iff, ZMod.toAddCircle_eq_zero] at he
    exact he
  · intro h
    apply AddChar.ext
    intro r
    change character (ZMod.toAddCircle (r * (z : ZMod M))) = 1
    simp only [h, mul_zero, map_zero, character_zero]

theorem cyclicIntegerCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ r : ZMod M, cyclicIntegerCharacter M z r) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  classical
  simpa only [cyclicIntegerCharacter_eq_zero_iff, ZMod.card] using
    AddChar.sum_eq_ite (cyclicIntegerCharacter M z)

theorem integerGridCharacter_eq (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) :
    integerGridCharacter M k z =
      character ((((k.val : ℝ) / M) * z : ℝ) : CircleFourier.Circle) := by
  have h := cyclicIntegerCharacter_intCast M (k.val : ℤ) z
  simpa only [integerGridCharacter, gridResidueEquiv, Equiv.coe_fn_mk,
    Int.cast_natCast, div_mul_eq_mul_div] using h

theorem integerGridCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ k : Fin M, integerGridCharacter M k z) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  rw [← cyclicIntegerCharacter_sum M z]
  exact (Equiv.sum_comp (gridResidueEquiv M) (cyclicIntegerCharacter M z))

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem circle_coe_fintype_sum {J : Type*} [Fintype J] (f : J → ℝ) :
    ((∑ j, f j : ℝ) : CircleFourier.Circle) = ∑ j, (f j : CircleFourier.Circle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ

theorem rectangularGridCharacter_eq {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularGridCharacter M k y =
      character ((∑ j, (((k j).val : ℝ) / M) * (y j : ℝ) : ℝ) : CircleFourier.Circle) := by
  simp only [rectangularGridCharacter, integerGridCharacter_eq, circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_norm {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    ‖rectangularGridCharacter M k y‖ = 1 := by
  rw [rectangularGridCharacter_eq, norm_character]

theorem rectangularGridCharacter_add {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y + z) =
      rectangularGridCharacter M k y * rectangularGridCharacter M k z := by
  simp only [rectangularGridCharacter_eq, Pi.add_apply, Int.cast_add, mul_add,
    Finset.sum_add_distrib, AddCircle.coe_add, character_add]

theorem rectangularGridCharacter_sub {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y - z) =
      rectangularGridCharacter M k y * star (rectangularGridCharacter M k z) := by
  simp only [rectangularGridCharacter_eq, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
  rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]

theorem rectangularGridCharacter_fintype_sum {J B : Type*} [Fintype J] [Fintype B]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : B → J → ℤ) :
    rectangularGridCharacter M k (∑ b, y b) = ∏ b, rectangularGridCharacter M k (y b) := by
  classical
  simp only [rectangularGridCharacter_eq, Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_sum {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y) =
      if integerGridResidue M y = 0 then (M : ℂ) ^ Fintype.card J else 0 := by
  classical
  change (∑ k : J → Fin M, ∏ j, integerGridCharacter M (k j) (y j)) = _
  rw [← Fintype.prod_sum (fun j (k : Fin M) => integerGridCharacter M k (y j))]
  simp only [integerGridCharacter_sum]
  by_cases hy : integerGridResidue M y = 0
  · have hz j : (y j : ZMod M) = 0 := congrFun hy j
    simp only [hz, ite_true, Finset.prod_const, Finset.card_univ, hy]
  · have hz : ∃ j, (y j : ZMod M) ≠ 0 := by
      by_contra! h
      exact hy (funext h)
    obtain ⟨j, hj⟩ := hz
    rw [if_neg hy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem rectangularGridCharacter_orthogonality {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y z : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y * star (rectangularGridCharacter M k z)) =
      if integerGridResidue M y = integerGridResidue M z then
        (M : ℂ) ^ Fintype.card J else 0 := by
  simp only [← rectangularGridCharacter_sub, rectangularGridCharacter_sum]
  have h : integerGridResidue M (y - z) = 0 ↔ integerGridResidue M y = integerGridResidue M z := by
    simp only [funext_iff, integerGridResidue, Pi.sub_apply, Pi.zero_apply, Int.cast_sub, sub_eq_zero]
  simp only [h]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dif_pos S.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerGridFourier_inversion {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (z : J → ℤ) :
    (∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ) ^ Fintype.card J * integerGridMass p Y M z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) *
        (∑ k : J → Fin M, rectangularGridCharacter M k (Y x) * star (rectangularGridCharacter M k z)) := by
      simp only [integerGridCoefficient, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [rectangularGridCharacter_orthogonality, integerGridMass, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : integerGridResidue M (Y x) = integerGridResidue M z <;> simp [hx, mul_comm]

theorem independent_integerGridCoefficient {B J : Type*} [Fintype B] [DecidableEq B] [Fintype J]
    {X : B → Type*} [∀ b, Fintype (X b)] (p : ∀ b, FiniteProbabilityWeights (X b))
    (Y : ∀ b, X b → J → ℤ) (shift : J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi p) (fun x => shift + ∑ b, Y b (x b)) M k =
      rectangularGridCharacter M k shift * ∏ b, integerGridCoefficient (p b) (Y b) M k := by
  simp only [integerGridCoefficient, rectangularGridCharacter_add, rectangularGridCharacter_fintype_sum]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  exact FiniteProbabilityWeights.complexMean_pi_product p
    (fun b x => rectangularGridCharacter M k (Y b x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerGridDensity_fourier {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M] (z : J → ℤ) :
    (integerGridDensity p Y K M z : ℂ) =
      ((K : ℂ) / M) ^ Fintype.card J *
        ∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [integerGridFourier_inversion, div_pow]
  simp only [integerGridDensity, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBooleanBlockValue_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) :
    (integerBooleanBlockValue x t : ℝ) = booleanBlockValue (fun g r => (x g r : ℝ)) t := by
  have hf (r : Option I) : ((booleanFeature r t : ℤ) : ℝ) = (booleanFeature r t : ℝ) := by
    cases r with
    | none => simp only [booleanFeature, Int.cast_one]
    | some i =>
        by_cases hi : i ∈ t <;> simp only [booleanFeature, hi, ite_true, ite_false, Int.cast_one, Int.cast_zero]
  simp only [integerBooleanBlockValue, booleanBlockValue, Int.cast_prod, Int.cast_sum, Int.cast_mul, hf]

theorem integerBooleanBlockJet_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) :
    (integerBooleanBlockJet x S : ℝ) =
      booleanCoefficient (booleanBlockValue (fun g r => (x g r : ℝ))) S := by
  have h := booleanCoefficient_map (Int.castRingHom ℝ) (integerBooleanBlockValue x) S
  change (integerBooleanBlockJet x S : ℝ) =
    booleanCoefficient (fun t => (integerBooleanBlockValue x t : ℝ)) S at h
  simpa only [integerBooleanBlockValue_cast] using h

theorem gridJetFrequency_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (v : Finset I → ℝ) :
    (∑ S, gridJetFrequency M J k S * v S) = ∑ S : J, (((k S).val : ℝ) / M) * v S := by
  classical
  calc
    _ = ∑ S ∈ J, gridJetFrequency M J k S * v S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro S _ hS
      simp only [gridJetFrequency, dif_neg hS, zero_mul]
    _ = ∑ S : J, gridJetFrequency M J k S * v S := (Finset.sum_coe_sort J _).symm
    _ = _ := Finset.sum_congr rfl (fun S _ => by rw [gridJetFrequency_apply])

theorem integerBooleanBlockJet_pairing {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    (∑ S : J, (((k S).val : ℝ) / M) * (integerBooleanBlockJet x S : ℝ)) =
      booleanBlockPhase (gridJetFrequency M J k) (fun g r => (x g r : ℝ)) := by
  simp only [integerBooleanBlockJet_cast, booleanBlockPhase, gridJetFrequency_pairing]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

end IntegerSourceLaw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedModeratePointMass
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ}
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affineWeightedCubeGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (u : Fin (n + 1) → Option I → ℤ)
    (v : Fin (n + 1) → Option I → ℕ) (M : ℕ) [NeZero M] (J : Finset (Finset I)) (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi (fun j => (s j).source))
      (affineWeightedCubeIntegerBlock s u v J) M k =
        affineWeightedCubeGridCoefficient s (fun j i => (u j i : ℝ)) v M J k := by
  unfold integerGridCoefficient affineWeightedCubeGridCoefficient
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  unfold affineWeightedCubeIntegerBlock
  rw [integerBooleanBlockJet_pairing]
  unfold affineIntegerCubeCoordinates affineCubeCoordinates
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

theorem affineWeightedCubeIntegerSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift) M k =
      rectangularGridCharacter M k shift *
        ∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M J k := by
  have h := independent_integerGridCoefficient
    (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))
    (fun b => affineWeightedCubeIntegerBlock (s b) (u b) (v b) J) shift M k
  unfold weightedCubeIntegerSource affineWeightedCubeIntegerSum
  simpa only [affineWeightedCubeGridCoefficient_eq_image] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePrincipalPMF
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1)) (a : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a) =
    PMF.pure (inactivePrincipalCoefficient (basisAxisScale (b j) i)
      (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card))) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ∈
      layerIntegerPrincipalSlots (G := G) B j i := (mem_principalCoefficientSlots _ _ _).mpr ⟨a, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    exact (layerIntegerPrincipalSlots_not_constant B j i) (he ▸ hmem)
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · exact integerAxisPrincipalPMF_inactive (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) i) S.positive (principalProfileSize_pos (hR j) _) (S.gap j i) hsmall
  · exact False.elim (hp hmem)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_unit_block_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF.map
      (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z b v k : ℤ)) t) =
      (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
        integerBooleanBlockJet (fun v k => (y ⟨a,b,v⟩ k : ℤ)) t) := by
  intro sources
  have houter :
      (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF =
        dependentProductPMF (fun b => (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi _
  have hinner (b : B a) : (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF =
      dependentProductPMF (fun v => (sources b v).source.toPMF) := FiniteProbabilityWeights.toPMF_pi _
  rw [houter]
  simp_rw [hinner]
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v => (sources b v).source.toPMF))
    (fun b z v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z v k : ℤ))
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    p.map (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet (z b) t))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize)
  rw [← hm] at hp
  simp only [PMF.map_comp, Function.comp_def] at hp
  exact hp.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedInactiveResidueJetPMF_source
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (hlarge : 2 * inactiveDenominator
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) ≤ basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r ⟨j,Sum.inr i⟩ hsize
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) => step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedCubeIntegerSource sources).toPMF.map (affineWeightedCubeIntegerSum sources lower strides rows shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  intro sources lower strides
  have hcoeff : (dependentProductPMF (fun a : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a))) =
      PMF.pure (fun _ : B ⟨j, Sum.inr i⟩ => (1 : ℤ)) := by
    ext c
    rw [dependentProductPMF_apply]
    simp_rw [allocatedInactivePrincipalPMF B U basis S j i hR hσ hsmall, inactivePrincipal_large hlarge]
    by_cases hc : c = fun _ => (1 : ℤ)
    · subst c
      simp
    · obtain ⟨a, ha⟩ : ∃ a, c a ≠ 1 := by
        by_contra hn
        apply hc
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hc]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  unfold allocatedSupportedSlicedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  simp only [one_mul]
  exact containedSupportedProgressionLaw_unit_block_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
    hH hsubset q hq r hcell ⟨j,Sum.inr i⟩ hsize rows shift

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerGridPointCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerPointDensity_norm_le_fourier_sum {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (z : J → ℤ) :
    ‖(((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ) : ℂ)‖ ≤
      ((K : ℝ) / M) ^ Fintype.card J * ∑ k, ‖integerGridCoefficient p Y M k‖ := by
  have hmass : finiteImageMass p Y z ≤ integerGridMass p Y M z := by
    apply p.mean_mono
    intro x
    by_cases hx : Y x = z
    · simp only [hx, ite_true, le_refl]
    · simp only [if_neg hx]
      split_ifs <;> norm_num
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg)]
  rw [← finiteImageMass_eq_toPMF]
  calc
    _ ≤ integerGridDensity p Y K M z :=
      mul_le_mul_of_nonneg_left hmass (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ‖(integerGridDensity p Y K M z : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ _ := by
      rw [integerGridDensity_fourier, norm_mul, norm_pow, norm_div,
        Complex.norm_natCast, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, norm_star, rectangularGridCharacter_norm, mul_one, le_refl]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveFixedCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq hsize in

theorem allocatedSupportedSlicedInactiveResidueJetPMF_norm_le
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val rows.card t P V W := by
  intro V t W
  let M := torus * height
  have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  let _ : NeZero M := ⟨hM.ne'⟩
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [M, Nat.cast_mul, le_refl]
  have hKM : height ≤ M := Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨_,hcap,_⟩ := allocatedSupportedSlicedInactiveGridDensity_approximation B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride
    (Nat.cast_nonneg torus) hMK rows hrows hB zero_lt_one le_rfl
  have hcap0 : 0 ≤ uniformSpectrumAbsoluteCap j.val rows.card t P V W :=
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr hKM))
  have hp := integerPointDensity_norm_le_fourier_sum (weightedCubeIntegerSource sources)
    (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z
  rw [allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
    j i hsmall hlarge hsize rows shift] at hp
  have heq (k : rows → Fin M) := affineWeightedCubeIntegerSum_coefficient
    sources lower strides M rows shift k
  simp_rw [heq, norm_mul, rectangularGridCharacter_norm, one_mul] at hp
  simp only [Fintype.card_coe] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left hcap (by positivity)).trans
    (mul_le_of_le_one_left hcap0 hscale))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) (q d T : ℕ)
local notation "degree" => j.val + 1
local notation "b" => Fintype.card (B (Sigma.mk j (Sum.inr i)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "cost" => (inactiveDenominator gamma : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor q degree b (4 * gamma)
local notation "torusI" => blockTorusFactor q degree b 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedAxisCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    R j
local notation "scale" => basisAxisScale (b j) i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in

theorem forecastInactive_sliced_fixed_zero_axis_norm_le
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (c0 z : ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    ‖(((height : ℝ) *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
        (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val 1 degree P V V := by
  intro V
  have hsize' : ∀ b v, (Fintype.card Empty + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    simpa using hsize
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) : t.card ≤ degree := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val (Finset.univ : Finset (Finset Empty)).card
      (degree * (Finset.univ : Finset (Finset Empty)).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩) := by
    simpa using hB
  have hc := allocatedSupportedSlicedInactiveResidueJetPMF_norm_le
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize' hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride Finset.univ hrows hB' (fun _ => c0) (fun _ => z)
  simpa only [Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one, mul_one, V] using hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => j.val + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card α) degree
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem allocatedInactiveGrid_height_le_of_small_original_side
    (hsmall : height ≤ S.value ^ degree) (Hchild : ℕ)
    (b0 : B ⟨j, Sum.inr i⟩) (v0 : Fin degree)
    (hshort : allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) :
    height ≤ denom * 2 ^ degree * Hchild ^ degree + 2 * denom := by
  by_cases hlarge : 2 * denom ≤ height
  · have hside : inactiveSideLength degree height denom ≤ Hchild := by
      rw [allocatedPrincipalSides_inactive B U basis S j i hsmall b0 v0] at hshort
      exact hshort.le
    have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val)
      (inactiveDenominator_pos _) hlarge).le
    exact (hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree)
      (Nat.pow_le_pow_left hside degree))).trans (Nat.le_add_right _ _)
  · omega

variable (δ P ε : ℝ) (rows : Finset (Finset α))

local notation "V" => (torus : ℝ) * cost / δ ^ degree
local notation "t" => degree * rows.card
local notation "W" => ((torus : ℝ) * cost) ^ rows.card / δ ^ t
local notation "bias" => uniformBlockRetainedBias j.val rows.card t P V W ε
local notation "freq" => Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V bias)
local notation "cap" => uniformSpectrumAbsoluteCap j.val rows.card t P V W
local notation "sizeBound" => uniformSpectrumSizeConstant j.val rows.card t P V W /
  ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)
local notation "periodBound" => uniformScaledRetainedDenominatorBound j.val rows.card t P V W bias
local notation "cutoff" => allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i
  (Nat.ceil (((((Fintype.card α + 1) * q) : ℕ) : ℝ) / δ))

variable (Hchild : ℕ)
local notation "fixedCutoff" => (denom * 2 ^ degree * Hchild ^ degree + 2 * denom : ℕ)
local notation "combinedCutoff" => (max cutoff fixedCutoff : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq in
theorem forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense
    (δ P : ℝ) (Hchild : ℕ)
    (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (hsmall : height ≤ S.value ^ degree)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (c0 z : ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    ‖(((height : ℝ) *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
        (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      max (cutoff : ℝ) (uniformSpectrumAbsoluteCap j.val 1 degree P V V) := by
  intro V cutoff
  have htrivial :
      ‖(((height : ℝ) *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
          (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤ height := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) ((ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one)
  rcases hreg with ⟨b0, v0, hshort⟩ | ⟨hdense, hstep⟩
  · have hk : height ≤ cutoff :=
      (allocatedInactiveGrid_height_le_of_small_original_side B U basis S j i
        hsmall Hchild b0 v0 hshort).trans (le_max_right _ _)
    exact (htrivial.trans (Nat.cast_le.mpr hk)).trans (le_max_left _ _)
  · rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
        q (Nat.ceil ((q : ℝ) / δ)) (Nat.le_ceil _) with hbounded | ⟨hsize, hcases⟩
    · have hk : height ≤ cutoff := hbounded.trans (le_max_left _ _)
      exact (htrivial.trans (Nat.cast_le.mpr hk)).trans (le_max_left _ _)
    · rcases hcases with ⟨hactive, _⟩ | ⟨_, hlarge, hlength⟩
      · exact False.elim ((Nat.not_lt.mpr hsmall) hactive)
      · exact (forecastInactive_sliced_fixed_zero_axis_norm_le
          B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hsmall hlarge
          hδ hlength hstep A hA P hP hsP hstride hB c0 z).trans (le_max_right _ _)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

theorem forecastInactive_sliced_fixed_grid_mass_le_v2_oai
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P)
    (hstride : ∀ a b v, (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual : ℝ) (_hCactual : 0 ≤ Cactual) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    (∏ a, (height a : ℝ)) * law.fiberMean
      (forecastInactiveFixedOutput B U basis S selected coefficients x)
      (fun a _ => z a) (fun _ => 1) ≤ Cactual ^ Fintype.card A := by
  intro degree height denom torus V cap cutoff hactual x z p map law
  let r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod 1 := 0
  let cell : Finset (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty H) :=
    Finset.univ.filter (fun y => principalResidueLabel 1 y = r₀)
  have hcellEq : cell = Finset.univ := by
    ext y
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Subsingleton.elim _ _)
  have hcellMass : p.mass cell = 1 := by
    rw [hcellEq]
    exact p.total
  have hcell : 0 < p.mass cell := by rw [hcellMass]; exact zero_lt_one
  let c₀ (a : A) := coefficients a (constantCoefficientSlot _ _)
  let μ (a : A) := allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S 1 r₀ H step c hH
    hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a)
  let F := forecastInactiveFixedOutput B U basis S selected coefficients x
  have hjoint : ((p.condition cell hcell).fiberLaw map).toPMF.map F = dependentProductPMF μ := by
    have hj := forecastInactiveSlicedFixedPath_joint_law B U basis hR hσ S 1 r₀ H step c hH hsubset hcell
      selected hselected hsmall coefficients hcoefficients x (fun _ => (Finset.univ : Finset (Finset Empty)))
    have hconst (v : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => v) t = v := by
      simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
    unfold F forecastInactiveFixedOutput
    simpa only [hconst, containedSupportedProgressionLaw, p, map, cell, c₀, μ] using hj
  have hmass : law.fiberMean F (fun a _ => z a) (fun _ => 1) =
      (dependentProductPMF μ (fun a _ => z a)).toReal := by
    rw [← hjoint, FiniteProbabilityWeights.toPMF_map_toReal,
      FiniteProbabilityWeights.fiberLaw_mean, FiniteProbabilityWeights.condition_mean,
      hcellMass, hcellEq]
    simp only [Finset.mem_univ, ite_true, div_one]
    simp only [FiniteProbabilityWeights.fiberMean, law, FiniteProbabilityWeights.fiberLaw_mean]
    congr 1
    funext y
    split_ifs <;> rfl
  have haxis (a : A) : (height a : ℝ) * (μ a (fun _ => z a)).toReal ≤ Cactual := by
    have ha := forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense
      B U basis hR hσ S 1 zero_lt_one r₀ H step c hH hsubset hcell (selected a).1 (selected a).2
      δ P Hchild hδ (hreg a) (hsmall a) (hgrid a) L hL hP hsP
      (by simpa only [mul_one] using hstride a) (hB a) (c₀ a) (z a)
    have hab : (height a : ℝ) * (μ a (fun _ => z a)).toReal ≤ max (cutoff a : ℝ) (cap a) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg), Nat.cast_one] using ha
    exact hab.trans (hactual a)
  change (∏ a, (height a : ℝ)) * law.fiberMean F (fun a _ => z a) (fun _ => 1) ≤ _
  rw [hmass, dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _a : A, Cactual :=
      Finset.prod_le_prod (fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
        (fun a _ => haxis a)
    _ = Cactual ^ Fintype.card A := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_grid_mass_le_v2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_grid_mass_le_v2_oai.{u_1, u_2, u_3, u_4, u_5}
