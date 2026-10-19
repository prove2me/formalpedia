-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:41:18.810389+00:00
-- url     : https://prove2.me/submissions/2053517c-f279-460b-b51b-660d7d627a8f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveResidueJetPMF_source_s2
import Theorems.Thm_OAI_Erdos3_affine_weightedCube_uniform_spectrum_s2
import Theorems.Thm_OAI_Erdos3_uniformBlockSpectrumCover_polynomial_card_s2

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

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

end Erdos3.FiniteProbabilityWeights

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

theorem ScalarCubePrimitiveBudget.mono {I : Type*} [Fintype I] [DecidableEq I]
    {s : NormalizedScalarCubeSource I} {A : ℝ≥0} {U V : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hUV : U ≤ V) : ScalarCubePrimitiveBudget s A V :=
  ⟨h.one_le.trans hUV, h.dimension_le.trans hUV, h.modulus_le.trans hUV,
    h.weight_le.trans hUV, h.weightLipschitz_le.trans hUV, h.boundary_le.trans hUV,
    h.grid_le.trans hUV, h.derivative_le.trans hUV, h.density_le.trans hUV⟩

theorem scalarCubePrimitiveBudget_of_raw_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (scalarCubePrimitiveEnvelope I A B T M) := by
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  let X := 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2
  let Y := 2 * scalarCubeGridBoundaryConstant I * V
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X, V]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, V, scalarCubeGridBoundaryConstant]; positivity
  have hZ : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator; positivity
  have hP : 0 ≤ paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap; positivity
  have hparts :
      1 ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      q ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (M : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (B : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (T : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      X ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      Y ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      paddedResidueDensityCap I M ≤ scalarCubePrimitiveEnvelope I A B T M := by
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧ _
    dsimp only [scalarCubePrimitiveEnvelope]
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      q ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (M : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (B : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (T : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      X ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      Y ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      paddedResidueDensityCap I M ≤ 1 + q + M + B + T + X + Y + _ + _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hq, hX, hY, hZ, hP, Nat.cast_nonneg (α := ℝ) M, B.coe_nonneg, T.coe_nonneg]
  obtain ⟨h1, hq', hM', hB', hT', hX', hY', hZ', hP'⟩ := hparts
  have hvol : scalarCubeDomainDensity I ≤ V := scalarCubeDomainDensity_le_power I
  have hboundary : scalarCubeBoundaryConstant I ≤ X := by
    unfold scalarCubeBoundaryConstant
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num)) (by positivity)
  have hgrid : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hvol
      (show 0 ≤ 2 * scalarCubeGridBoundaryConstant I by unfold scalarCubeGridBoundaryConstant; positivity)
    simpa only [scalarCubeDomainDensity, div_eq_mul_inv, Y] using hh
  refine ⟨h1, hq', ?_, ?_, ?_, hboundary.trans hX', hgrid.trans hY', hZ', ?_⟩
  · exact (by exact_mod_cast hM : (s.modulusBound : ℝ) ≤ M).trans hM'
  · exact (by exact_mod_cast hB : (s.weightBound : ℝ) ≤ B).trans hB'
  · exact (by exact_mod_cast hT : (s.weightLipschitz : ℝ) ≤ T).trans hT'
  · exact (paddedResidueDensityCap_mono I hM).trans hP'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalizedUniformCubeSource_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedUniformCubeSource I L M hL m r hm hmM hsize) A
      (scalarCubePrimitiveEnvelope I A 1 0 M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 M le_rfl le_rfl le_rfl

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

open scoped BigOperators NNReal Classical
open CircleFourier

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dif_pos S.property]

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

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

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
  have ht := (affine_weightedCube_uniform_spectrum_s2 s (fun b j i => (u b j i : ℝ)) v A hA hU hV hW hL hε
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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem principalSupportedAxisSources_primitive (b : B a) (v : Fin (h a)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q)
    (r ⟨a, b, v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize b v) A

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_product_ratio {n : ℕ} {δ S C M V : ℝ} (H : Fin n → ℝ)
    (hδ : 0 < δ) (hS : 0 < S) (hC : 0 < C) (hM : 0 ≤ M)
    (hH : ∀ j, δ * S ≤ H j)
    (hbase : M / (C * S ^ n) ≤ V) :
    M / (C * ∏ j, H j) ≤ V / δ ^ n := by
  have hp : δ ^ n * S ^ n ≤ ∏ j, H j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using
      Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => δ * S) (g := H)
        (fun _ _ => (mul_pos hδ hS).le) (fun j _ => hH j)
  have hd : 0 < δ ^ n * (C * S ^ n) := by positivity
  have hden : δ ^ n * (C * S ^ n) ≤ C * ∏ j, H j := by
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  calc
    M / (C * ∏ j, H j) ≤ M / (δ ^ n * (C * S ^ n)) :=
      div_le_div_of_nonneg_left hM hd hden
    _ = (M / (C * S ^ n)) / δ ^ n := by ring
    _ ≤ V / δ ^ n := div_le_div_of_nonneg_right hbase (pow_pos hδ _).le

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedSupportedSlicedInactiveSpectrum
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

theorem allocatedSupportedSlicedInactiveGridDensity_approximation_s2_oai
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C) (hMK : (M : ℝ) ≤ C * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := C * cost / δ ^ degree
    let t := degree * rows.card
    let W := (C * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ shift z : rows → ℤ,
      ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ((height : ℝ) / M) ^ rows.card * ε := by
  intro V t W ζ F
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ (C * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hC)
  have hratio : (M : ℝ) / (1 * (side : ℝ) ^ degree) ≤ C * cost := by
    rw [one_mul]
    exact (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hside) _)).mpr hbound
  have hscale (b : B ⟨j,Sum.inr i⟩) : (M : ℝ) / ∏ v, (((sources) b v).length : ℝ) ≤ V := by
    change (M : ℝ) / ∏ v : Fin degree, (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ) ≤ C * cost / δ ^ degree
    simpa only [one_mul, layerSamplerDegree] using dense_slice_product_ratio (n := j.val + 1)
      (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ (Nat.cast_pos.mpr hside)
      zero_lt_one (Nat.cast_nonneg M) (hlength b) hratio
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card_s2 rows M j.val t
      hP hV hW hL hε hε1 (by simpa only [Fintype.card_coe] using hcard)
  · exact (affine_weightedCube_uniform_spectrum_s2 sources (fun b v a => (lower b v a : ℝ)) strides
      A hA hP hV hW hL hε hs hlength (fun b v _ => hstep b v) (fun b v _ => hstride b v)
      M t (Nat.pos_of_ne_zero (NeZero.ne M)) rows hrows hB hcard hscale).2
  · intro shift z
    have he := affine_weightedCube_grid_density sources lower strides A hA hP hV hW hL hε hs hlength
      (fun b v _ => hstep b v) (fun b v _ => hstride b v) height M t rows hrows hB hcard hscale shift z
    have hlaw := allocatedSupportedSlicedInactiveResidueJetPMF_source_s2 B U basis hR hσ S q hq r H step c
      hH hsubset hcell j i hsmall hlarge hsize rows shift
    have hd := integerGridDensity_eq_of_pmf_image (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) _ hlaw height M z
    have hd' : integerGridDensity (weightedCubeIntegerSource sources)
        (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
      simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
    rw [← hd']
    exact he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation_s2_oai.{u_1, u_2, u_3, u_4, u_5}
