-- Prove2me | solution 1 for OAI.Erdos3.affine_weightedCube_grid_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T13:38:23.034168+00:00
-- url     : https://prove2.me/submissions/6e7a1490-c405-47ea-b55e-880b9eb8ff31

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088
import Theorems.Thm_OAI_Erdos3_affine_weightedCube_uniform_spectrum

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_series_truncation_le {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (c ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k‖ ≤ spectrumTail S (fun k => ‖c k‖) := by
  have hid : (∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k =
      ∑ k, if k ∈ S then 0 else c k * ψ k := by
    calc
      _ = ∑ k, (c k * ψ k - if k ∈ S then c k * ψ k else 0) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, sub_self, sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp only [hk, ite_true, norm_zero, le_refl]
  · simp only [hk, ite_false, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

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

theorem integerGridDensity_truncation {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ℤ) :
    ‖(integerGridDensity p Y K M z : ℂ) - ((K : ℂ) / M) ^ Fintype.card J *
        ∑ k ∈ S, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)‖ ≤
      ((K : ℝ) / M) ^ Fintype.card J * spectrumTail S (fun k => ‖integerGridCoefficient p Y M k‖) := by
  rw [integerGridDensity_fourier, ← mul_sub, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_series_truncation_le S _ _
    (fun k => by rw [norm_star, rectangularGridCharacter_norm])

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_grid_density {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    ∀ shift z, ‖(integerGridDensity (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
      K M z : ℂ) - integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
        K M S z‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  dsimp only
  have ht := (affine_weightedCube_uniform_spectrum s (fun b j i => (u b j i : ℝ)) v A hA hU hV hW hL hε
    h hlen hv hstride M t (Nat.pos_of_ne_zero (NeZero.ne M)) J hJ hB hsize hscale).1
  intro shift z
  have he := integerGridDensity_truncation (weightedCubeIntegerSource s)
    (affineWeightedCubeIntegerSum s u v J shift) K M
      (uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n J.card t U V W ε)) z
  have htail : spectrumTail (uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n J.card t U V W ε))
      (fun k => ‖integerGridCoefficient (weightedCubeIntegerSource s)
        (affineWeightedCubeIntegerSum s u v J shift) M k‖) ≤ ε := by
    simpa only [affineWeightedCubeIntegerSum_coefficient, norm_mul, rectangularGridCharacter_norm, one_mul] using ht
  simpa only [integerGridApproximation, Fintype.card_coe] using
    he.trans (mul_le_mul_of_nonneg_left htail (by positivity))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
variable (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)

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

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.affine_weightedCube_grid_density.{u_1, u_2} := @OAI.Erdos3.affine_weightedCube_grid_density.{u_1, u_2}
