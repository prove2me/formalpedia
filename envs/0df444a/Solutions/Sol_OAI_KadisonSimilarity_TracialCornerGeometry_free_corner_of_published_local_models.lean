-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:47:51.287415+00:00
-- url     : https://prove2.me/submissions/9ced6e0d-0dc9-43f8-8509-1e23ff6b4b67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_estimate_of_published_words
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_norm_spectral_arc_compression

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Hankel test in the similarity manuscript

The coefficients here are the actual Fourier coefficients of the narrow-arc
function in Section `hankel`: `sin (l θ) / (π l)`, with `θ = 1/(2N)`.
The lower bound uses the constant vector in the first `N` coordinates.
No assertion about the free-product construction is assumed here.
-/

noncomputable section

namespace KadisonSimilarity

open Finset

theorem arcWidth_pos {N : ℕ} (hN : 0 < N) : 0 < arcWidth N := by
  unfold arcWidth
  positivity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

private theorem intervalIntegrable_indicator_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem integral_indicator_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    (∫ x in a..b, (Ioc c d).indicator f x) = ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset, ← intervalIntegral.integral_of_le hcd]
  exact Ioc_subset_Ioc hac hdb

theorem centeredArc_integral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (∫ x in -Real.pi..Real.pi, centeredArc θ x) = 0 := by
  simp only [centeredArc]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of intervalIntegrable_const measurableSet_Ioc)
    intervalIntegrable_const,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Nonzero frequency integration over a symmetric arc. -/
theorem integral_arc_exponential (θ r : ℝ) (hr : r ≠ 0) :
    (∫ x in -θ..θ, Complex.exp ((r * x : ℝ) * Complex.I)) =
      (2 * Real.sin (r * θ) / r : ℝ) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (x * Complex.I)) (a := -θ) (b := θ) hr
  rw [mul_neg, integral_exp_mul_I_eq_sin] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, Complex.real_smul, div_eq_mul_inv, mul_comm] using h

@[simp] theorem arcFourierIntegral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    arcFourierIntegral θ 0 = 0 := by
  simp only [arcFourierIntegral, Int.cast_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, centeredArc_integral_zero hθ hπ]
  simp

theorem arcFourierIntegral_ne_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) (hl : l ≠ 0) :
    arcFourierIntegral θ l = (Real.sin (l * θ) / (Real.pi * l) : ℝ) := by
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  let g : ℝ → ℂ := fun x => Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)
  have hg : IntervalIntegrable g volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hid : (fun x => (centeredArc θ x : ℂ) * g x) =
      fun x => (Ioc (-θ) θ).indicator g x - (θ / Real.pi : ℝ) • g x := by
    funext x
    by_cases hx : x ∈ Ioc (-θ) θ <;>
      simp [centeredArc, hx, Complex.real_smul, sub_mul]
  unfold arcFourierIntegral
  change ((2 * Real.pi)⁻¹ : ℝ) • (∫ x in -Real.pi..Real.pi,
    (centeredArc θ x : ℂ) * g x) = _
  have hsg : IntervalIntegrable (fun x => (θ / Real.pi) • g x)
      volume (-Real.pi) Real.pi := hg.smul (θ / Real.pi)
  rw [hid, intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of hg measurableSet_Ioc) hsg,
    intervalIntegral.integral_smul,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  dsimp [g]
  rw [integral_arc_exponential _ _ hlr, integral_arc_exponential _ _ hlr,
    Real.sin_int_mul_pi]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, sub_zero, ← Complex.ofReal_mul]
  congr 1
  field_simp

theorem arcFourierIntegral_eq_real {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) : arcFourierIntegral θ l = (realArcFourierCoefficient θ l : ℂ) := by
  by_cases hl : l = 0
  · subst l
    simp [hθ, hπ, realArcFourierCoefficient]
  · rw [arcFourierIntegral_ne_zero hθ hπ l hl, realArcFourierCoefficient, ite_eq_right hl]

theorem realArcFourierCoefficient_pos_index {N : ℕ} {l : ℕ} (hl : 0 < l) :
    realArcFourierCoefficient (arcWidth N) l = arcCoefficient N l := by
  have h : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  simp only [realArcFourierCoefficient, ite_eq_right h, arcCoefficient, Int.cast_natCast]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dihedral word identity and the finite Fourier matrix entries. -/

noncomputable section
namespace KadisonSimilarity

section Group
variable {G : Type*} [Group G]

/-- The reflection relation fixes the sum-index in the Hankel term. -/
theorem dihedral_word_identity (w d : G) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    w ^ j * d * w ^ (-k) = w ^ (j + k + 1) * (w⁻¹ * d) := by
  have hmove : d * w ^ (-k) = w ^ k * d := by
    have h := (show SemiconjBy d w w⁻¹ from hd).zpow_right (-k)
    simpa only [inv_zpow, zpow_neg, inv_inv] using h.eq
  calc
    _ = w ^ j * (d * w ^ (-k)) := mul_assoc _ _ _
    _ = w ^ j * (w ^ k * d) := by rw [hmove]
    _ = w ^ (j + k) * d := by rw [← mul_assoc, ← zpow_add]
    _ = w ^ (j + k + 1) * (w⁻¹ * d) := by
      rw [← mul_assoc, ← zpow_neg_one, ← zpow_add]
      congr 2
      omega

end Group

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Exact rotation-plus-reflection decomposition of the corner word. -/
theorem dihedral_corner_word (w d : Rˣ) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    (↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R) =
      (1 / 2 : ℂ) • ((↑(w ^ (j - k)) : R) +
        (↑(w ^ (j + k + 1)) : R) * (↑(w⁻¹ * d) : R)) := by
  have hrot : (↑(w ^ j) : R) * (↑(w ^ (-k)) : R) = (↑(w ^ (j - k)) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 1
  have href := congrArg (fun a : Rˣ => (a : R)) (dihedral_word_identity w d hd j k)
  simp only [Units.val_mul] at href
  simp only [dihedralHalfProjection, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_one, smul_add, Units.val_mul]
  rw [hrot, href]

/-- Once the two Fourier coefficient identities hold, the corner entry has
both its Toeplitz difference index and its Hankel sum-plus-one index. -/
theorem dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f : R) (E : R →ₗ[ℂ] R)
    (γ : ℤ → ℂ)
    (hrot : ∀ l : ℤ, E (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E (f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R))) =
      (1 / 2 : ℂ) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [dihedral_corner_word w d hd, mul_smul_comm, mul_add, ← mul_assoc,
    map_smul, map_add, hrot, href]

/-- The two coefficients of `x` and `xs` exchange when `s²=1`. -/
theorem symmetryExpectation_mul_symmetry
    (τ : R →ₗ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (s x : R) (hs : s * s = 1) (hcoset : τ (s * x) = 0) :
    symmetryExpectation τ s x = τ x • 1 ∧
      symmetryExpectation τ s (x * s) = τ x • s := by
  constructor
  · simp only [symmetryExpectation_apply, hcoset, zero_smul, add_zero]
  · have hxs : τ (x * s) = 0 := (htr x s).trans hcoset
    have hconj : τ (s * (x * s)) = τ x := by
      rw [← mul_assoc, htr (s * x) s, ← mul_assoc, hs, one_mul]
    simp only [symmetryExpectation_apply, hxs, hconj, zero_smul, zero_add]

/-- Bimodularity and the tower identity transfer the free-compression
expectation to a dihedral Fourier entry. -/
theorem compressed_dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f h : R)
    (EC E₀ : R →ₗ[ℂ] R) (γ : ℤ → ℂ) (u : ℂ)
    (hEC : EC h = u ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E₀ ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (u ^ 2 / 2) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [← htower j k, hbimod, hEC, mul_smul_comm, smul_mul_assoc, map_smul]
  have hproduct : (↑(w ^ j) : R) * (f * dihedralHalfProjection d) *
      (↑(w ^ (-k)) : R) =
      f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R)) := by
    rw [← mul_assoc (↑(w ^ j) : R) f, hcomm j]
    simp only [mul_assoc]
  rw [hproduct, dihedral_fourier_entry w d hd f E₀ γ hrot href, smul_smul]
  congr 1
  ring

/-- The normalized corner coefficient is exactly `u` when `u = 2t`. -/
theorem normalized_corner_scalar (t : ℂ) (ht : t ≠ 0) :
    t⁻¹ * ((2 * t) ^ 2 / 2) = 2 * t := by field_simp

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense tracial vectors determine the word-level operator compression.
In particular the matrix-entry identity is proved from the trace and the
two-sided expectation identity, rather than supplied as an operator hypothesis. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [CompleteSpace K] in
/-- Matrix coefficients on any dense family determine a bounded operator. -/
theorem operator_eq_of_dense_coefficients {ι : Type*} (v : ι → K)
    (hv : DenseRange v) (A B : K →L[ℂ] K)
    (h : ∀ i j, inner ℂ (v i) (A (v j)) = inner ℂ (v i) (B (v j))) : A = B := by
  have hvec (j : ι) : A (v j) = B (v j) := by
    apply ext_inner_left ℂ
    have heq := hv.equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      (funext (fun i => h i j))
    exact congrFun heq
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer A.continuous B.continuous (funext hvec))

variable {R : Type*} [Ring R] [StarRing R]

/-- Removing the supporting corner in a tracial word leaves precisely the
two Fourier powers around the test operator. -/
theorem tracial_corner_word (w : Rˣ) (hw : star w = w⁻¹)
    (e h a b : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (j k : ℤ) :
    star (e * (↑(w ^ (-j)) : R) * a) *
        (h * (e * (↑(w ^ (-k)) : R) * b)) =
      star a * ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) * b := by
  rw [star_mul, star_mul, star_unitary_zpow w hw, neg_neg, he]
  calc
    _ = star a * (↑(w ^ j) : R) * (e * h * e) * (↑(w ^ (-k)) : R) * b := by
      simp only [mul_assoc]
    _ = _ := by rw [heh, hhe]; simp only [mul_assoc]

variable [Algebra ℂ R] [StarModule ℂ R]

/-- A trace-preserving bimodule projection preserves all matrix coefficients
against its range algebra. -/
theorem tracial_expectation_test (A : StarSubalgebra ℂ R)
    (τ : R →ₗ[ℂ] ℂ) (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R)) (a b : A) (x : R) :
    τ (star (a : R) * x * (b : R)) = τ (star (a : R) * E x * (b : R)) := by
  have h := htrace (star (a : R) * x * (b : R))
  have he : E (star (a : R) * x * (b : R)) = star (a : R) * E x * (b : R) :=
    hbimod (star a) b x
  rw [he] at h
  exact h.symm

/-- Word-level compression computed from dense tracial vectors. `ρ` is the
compression of the left action to the base Hilbert space; it need only be
linear on the full algebra. -/
theorem tracial_word_compression_entry
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R))
    (w : Rˣ) (hw : star w = w⁻¹) (e h : R)
    (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (c q : ℂ) (hc : star c * c = q) (j k : ℤ)
    (Uj Uk : K →L[ℂ] H)
    (hUj : ∀ a : A, Uj (v a) = c • V (e * (↑(w ^ (-j)) : R) * (a : R)))
    (hUk : ∀ a : A, Uk (v a) = c • V (e * (↑(w ^ (-k)) : R) * (a : R))) :
    Uj.adjoint.comp ((L h).comp Uk) =
      q • ρ (E ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R))) := by
  apply operator_eq_of_dense_coefficients v hv
  intro a b
  change inner ℂ (v a) (Uj.adjoint (L h (Uk (v b)))) =
    inner ℂ (v a) (q • ρ (E _) (v b))
  change (starRingEnd ℂ) c * c = q at hc
  rw [ContinuousLinearMap.adjoint_inner_right, hUj, hUk, map_smul,
    inner_smul_left, inner_smul_right, hleft, hinner,
    tracial_corner_word w hw e h (a : R) (b : R) he heh hhe j k,
    tracial_expectation_test A τ E htrace hbimod a b,
    inner_smul_right, hρ, ← mul_assoc, hc]

omit [StarRing R] [StarModule ℂ R] in
/-- Once the algebraic entry calculation is known, linearity and the exact
corner normalization give the whole finite Toeplitz-plus-Hankel matrix. -/
theorem finite_dihedral_compression
    {N : ℕ} (U : Fin N → K →L[ℂ] H) (T : H →L[ℂ] H)
    (ρ : R →ₗ[ℂ] (K →L[ℂ] K)) (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (s : R) (γ : ℤ → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hentry : ∀ i j,
      (U i).adjoint.comp (T.comp (U j)) =
        t⁻¹ • ρ (((2 * t) ^ 2 / 2) •
          (γ ((i : ℕ) - (j : ℤ)) • (1 : R) +
            γ ((i : ℕ) + (j : ℤ) + 1) • s))) :
    (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      (2 * t) • matrixOperator (fun i j =>
        γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
          γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
  have he : (fun i j => (U i).adjoint.comp (T.comp (U j))) =
      fun (i j : Fin N) => (2 * t) • (γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
        γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
    funext i j
    rw [hentry, map_smul, map_add, map_smul, map_smul, hρone,
      smul_smul, normalized_corner_scalar t ht]
  rw [sumColumns_compression, he]
  ext x i
  simp [matrixOperator, Finset.smul_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite narrow-arc compression, assembled from the trace calculation,
the dihedral expectation, and the actual Fourier integral. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite operator matrix identity used by the Hankel test. Every entry
comes from tracial vectors and the two expectation identities. -/
theorem narrow_arc_tracial_compression
    {N : ℕ} (hN : 0 < N)
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (E₀ EC : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E₀ x) = τ x)
    (hbase : ∀ (a b : A) x, E₀ ((a : R) * x * (b : R)) =
      (a : R) * E₀ x * (b : R))
    (w d : Rˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (e f h : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (t : ℝ) (ht : 0 < t) (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → K →L[ℂ] H)
    (hU : ∀ i (a : A), U i (v a) =
      c • V (e * (↑(w ^ (-(i.val : ℤ))) : R) * (a : R)))
    (hEC : EC h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) =
      arcFourierIntegral (arcWidth N) l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      arcFourierIntegral (arcWidth N) l • (↑(w⁻¹ * d) : R)) :
    (sumColumns U).adjoint.comp ((L h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ K +
        (arcHankelMatrix N i j : ℂ) • ρ (↑(w⁻¹ * d) : R)) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hentry : ∀ i j : Fin N,
      (U i).adjoint.comp ((L h).comp (U j)) =
        (t : ℂ)⁻¹ • ρ (((2 * (t : ℂ)) ^ 2 / 2) •
          (arcFourierIntegral (arcWidth N) ((i.val : ℤ) - j.val) • (1 : R) +
            arcFourierIntegral (arcWidth N) ((i.val : ℤ) + j.val + 1) •
              (↑(w⁻¹ * d) : R))) := by
    intro i j
    rw [tracial_word_compression_entry A τ V L hinner hleft v hv ρ hρ E₀ htrace hbase
      w hw e h he heh hhe c (t : ℂ)⁻¹ hc i.val j.val (U i) (U j) (hU i) (hU j),
      compressed_dihedral_fourier_entry w d hd f h EC E₀
        (arcFourierIntegral (arcWidth N)) (2 * (t : ℂ)) hEC hbimod htower hcomm hrot href]
  have hmatrix := finite_dihedral_compression U (L h) ρ hρone
    (↑(w⁻¹ * d) : R) (arcFourierIntegral (arcWidth N)) (t : ℂ) htc hentry
  have hθ : 0 ≤ arcWidth N := (arcWidth_pos hN).le
  have hπ : arcWidth N ≤ Real.pi := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwidth : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have hcoeff : ∀ i j : Fin N,
      realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) + j.val + 1) =
        arcHankelMatrix N i j := by
    intro i j
    have h := realArcFourierCoefficient_pos_index (N := N)
      (l := i.val + j.val + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, arcHankelMatrix] using h
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat,
    arcFourierIntegral_eq_real hθ hπ, hcoeff] using hmatrix

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The expectation of a free compression

Scalar tracial freeness is expressed by vanishing alternating centered words.
The formula `E(e b e) = τ(e)^2 b` is derived by testing against the second
algebra, rather than included among the free-product input data.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

namespace ScalarFree

variable {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)

include hf in
theorem trace_pair {a b : R} (ha : a ∈ P) (hb : b ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) : τ (a * b) = 0 := by
  have h := hf true a [b] (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.nil true)))
  simpa using h

include hf in
theorem trace_triple {a b c : R} (ha : a ∈ Q) (hb : b ∈ P) (hc : c ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) : τ (a * b * c) = 0 := by
  have h := hf false a [b, c]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.cons (by simpa) hc0 (.nil true))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

include hf in
theorem trace_quadruple {a b c d : R} (ha : a ∈ Q) (hb : b ∈ P)
    (hc : c ∈ Q) (hd : d ∈ P)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) (hd0 : τ d = 0) :
    τ (a * b * c * d) = 0 := by
  have h := hf false a [b, c, d]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0
      (.cons (by simpa) hc0 (.cons (by simpa) hd0 (.nil false)))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end ScalarFree

/-- A centered letter is orthogonal, for the trace pairing, to the other algebra. -/
theorem trace_centered_mul_of_free
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {a b : R} (ha : a ∈ P) (ha0 : τ a = 0) (hb : b ∈ Q) :
    τ (a * b) = 0 := by
  have hpair := hf.trace_pair ha (traceCentered_mem τ Q hb) ha0 (traceCentered_trace τ hτ b)
  calc
    τ (a * b) = τ (a * traceCentered τ b + τ b • a) := by
      apply congrArg τ
      calc
        a * b = a * (traceCentered τ b + τ b • 1) :=
          congrArg (fun z : R => a * z) (traceCentered_add τ b).symm
        _ = _ := by rw [mul_add, mul_smul_comm, mul_one]
    _ = 0 := by rw [map_add, map_smul, hpair, ha0]; simp

/-- Orthogonality against the second algebra removes all three mixed terms
in the free-compression expansion. -/
theorem trace_test_free_compression_errors
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {a b c : R} (ha : a ∈ P) (ha0 : τ a = 0)
    (hb : b ∈ Q) (hb0 : τ b = 0) (hc : c ∈ Q) :
    τ (c * (a * b)) = 0 ∧ τ (c * (b * a)) = 0 ∧ τ (c * (a * b * a)) = 0 := by
  have hc0 := traceCentered_trace τ hτ c
  have hcm := traceCentered_mem τ Q hc
  have hab := hf.trace_pair ha hb ha0 hb0
  have hcab := hf.trace_triple hcm ha hb hc0 ha0 hb0
  have hcaba := hf.trace_quadruple hcm ha hb ha hc0 ha0 hb0 ha0
  have hba2 : τ (b * (a * a)) = 0 := by
    rw [htr]
    -- The product a² need not be centered; center it before pairing with b.
    have hp := hf.trace_pair (traceCentered_mem τ P (P.mul_mem ha ha)) hb
      (traceCentered_trace τ hτ _) hb0
    have heq : τ ((a * a) * b) = τ (traceCentered τ (a * a) * b) := by
      rw [traceCentered, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, hb0]
      simp
    exact heq.trans hp
  have haba : τ (a * b * a) = 0 := by
    rw [htr (a * b) a]
    have ha2b : τ ((a * a) * b) = 0 := by rw [htr]; exact hba2
    simpa only [mul_assoc] using ha2b
  have hfirst : τ (c * (a * b)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcab' : τ (traceCentered τ c * (a * b)) = 0 := by
      simpa only [mul_assoc] using hcab
    rw [hcab', hab, smul_zero, add_zero]
  have hsecond : τ (c * (b * a)) = 0 := by
    rw [← mul_assoc, htr]
    exact trace_centered_mul_of_free τ hτ hf ha ha0 (Q.mul_mem hc hb)
  have hthird : τ (c * (a * b * a)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcaba' : τ (traceCentered τ c * (a * b * a)) = 0 := by
      simpa only [mul_assoc] using hcaba
    rw [hcaba', haba, smul_zero, add_zero]
  exact ⟨hfirst, hsecond, hthird⟩

/-- The expectation formula in `lem:free-compression`, proved from scalar
freeness and the defining trace-pairing property of conditional expectation.
The projection condition on `e` is not needed for this algebraic identity. -/
theorem expectation_free_compression
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hfaithful : ∀ z, τ (star z * z) = 0 → z = 0)
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    (E : R →ₗ[ℂ] R) (hE : ∀ x, E x ∈ Q)
    (htrace : ∀ x c, c ∈ Q → τ (c * E x) = τ (c * x))
    {e b : R} (he : e ∈ P) (hb : b ∈ Q) (hb0 : τ b = 0) :
    E (e * b * e) = (τ e) ^ 2 • b := by
  let a := traceCentered τ e
  have ha : a ∈ P := traceCentered_mem τ P he
  have ha0 : τ a = 0 := traceCentered_trace τ hτ e
  have hexpand : e * b * e = (τ e) ^ 2 • b +
      τ e • (a * b) + τ e • (b * a) + a * b * a := by
    calc
      _ = (a + τ e • 1) * b * (a + τ e • 1) := by
        dsimp [a]
        rw [traceCentered_add]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, smul_add, smul_smul, pow_two]
        abel
  apply expectation_eq_of_trace_pairings τ Q hfaithful E hE htrace _ _ (Q.smul_mem hb _)
  intro c hc
  obtain ⟨h1, h2, h3⟩ := trace_test_free_compression_errors τ hτ htr hf ha ha0 hb hb0 hc
  rw [hexpand]
  simp only [mul_add, mul_smul_comm, map_add, map_smul, h1, h2, h3,
    smul_zero, add_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeDihedral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar and reflection-coset moments of two free centered symmetries,
derived directly from alternating-centered-word freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

private theorem pairedWord_append_alternating
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0) (n : ℕ) :
    AlternatingCenteredWord τ P Q true (pairedWord d s n ++ [d]) := by
  induction n with
  | zero => exact .cons (by simpa using hd) hd0 (.nil false)
  | succ n ih => exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

/-- The odd alternating words, which form the reflection coset, also vanish. -/
theorem ScalarFree.trace_pair_power_mul_first
    {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)
    (n : ℕ) : τ ((d * s) ^ n * d) = 0 := by
  have ha := pairedWord_append_alternating τ P Q hd hs hd0 hs0 n
  have hnonempty : pairedWord d s n ++ [d] ≠ [] := by simp
  obtain ⟨x, xs, heq⟩ := List.exists_cons_of_ne_nil hnonempty
  rw [heq] at ha
  have ht := hf true x xs ha
  rw [← heq, List.prod_append, pairedWord_prod] at ht
  simpa using ht

/-- Two free centered symmetries have a product whose nonzero integer
moments vanish. -/
theorem free_symmetry_haar_moments
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ (↑((d * s) ^ l) : R) = if l = 0 then 1 else 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hτ
    | succ n =>
      change τ (↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) =
        if ((n + 1 : ℕ) : ℤ) = 0 then 1 else 0
      rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul, ite_eq_right (by omega)]
      exact hf.trace_pair_power hd hs hd0 hs0 (Nat.succ_pos n)
  | negSucc n =>
    simp only [Int.negSucc_ne_zero, zpow_negSucc]
    rw [← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power hs hd hs0 hd0 (Nat.succ_pos _)

/-- Every reflection-coset word has zero trace. -/
theorem free_symmetry_coset_moments
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ ((↑((d * s) ^ l) : R) * (s : R)) = 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hs0
    | succ n =>
      have hss : s * s = 1 := by simpa only [hsinv] using inv_mul_cancel s
      have hword : (d * s) ^ (n + 1) * s = (d * s) ^ n * d := by
        rw [pow_succ]
        simp only [mul_assoc, hss, mul_one]
      change τ ((↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) * (s : R)) = 0
      rw [zpow_natCast, ← Units.val_mul, hword, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_mul]
      exact hf.trace_pair_power_mul_first hd hs hd0 hs0 n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power_mul_first hs hd hs0 hd0 (n + 1)

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- The product of two selfadjoint involutions is unitary. -/
theorem free_symmetry_product_star (d s : Rˣ)
    (hd : star d = d) (hs : star s = s) (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) :
    star (d * s) = (d * s)⁻¹ := by
  rw [star_mul, hd, hs, mul_inv_rev, hdi, hsi]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ActualArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow-arc finite Fourier compression with actual normalized tracial
dihedral word inclusions. Their formulas and orthogonality are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
theorem dihedral_reflection_relation (d s : Rˣ) (hd : d⁻¹ = d) (hs : s⁻¹ = s) :
    d * (d * s) = (d * s)⁻¹ * d := by
  have hdd : d * d = 1 := by simpa only [hd] using inv_mul_cancel d
  rw [← mul_assoc, hdd, one_mul, mul_inv_rev, hd, hs, mul_assoc, hdd, mul_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem baseInclusion_adjoint_self :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
      (G.baseInclusion A).toContinuousLinearMap = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  have h := (G.baseInclusion A).adjoint_comp_self
  exact h

theorem baseCompression_one : G.baseCompression A 1 = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.left 1).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    G.baseInclusion_adjoint_self]

/-- The coefficient formula required by the tracial Fourier compression. -/
theorem baseCompression_inner (a b : A) (x : P) :
    inner ℂ (G.baseVector A a) (G.baseCompression A x (G.baseVector A b)) =
      G.trace (star (a : P) * x * (b : P)) := by
  change inner ℂ (G.baseVector A a)
    ((G.baseInclusion A).toContinuousLinearMap.adjoint
      (G.left x ((G.baseInclusion A).toContinuousLinearMap (G.baseVector A b)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.left x (G.vector (b : P))) = _
  rw [G.left_vector, G.inner_vector, mul_assoc]

theorem baseInclusion_intertwines (a : A) :
    (G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseRepresentation A a) := rfl

theorem baseCompression_subalgebra (a : A) :
    G.baseCompression A (a : P) = G.baseRepresentation A a := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [G.baseInclusion_intertwines, ← ContinuousLinearMap.comp_assoc,
    G.baseInclusion_adjoint_self, ContinuousLinearMap.id_comp]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseCommutatorCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of commutators with base-algebra elements needs no invariance
hypothesis on the other operator. This also restores the original operator
after the free-product symmetrization. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The faithful tracial representation preserves the C-star norm. -/
theorem norm_left (hfaithful : Function.Injective G.vector) (a : P) :
    ‖G.left a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map G.left (G.left_injective hfaithful) a

/-- The adjoint base inclusion intertwines every base-algebra element. -/
theorem baseInclusion_adjoint_intertwines (a : A) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp (G.left (a : P)) =
      (G.baseRepresentation A a).comp (G.baseInclusion A).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.baseInclusion_intertwines A (star a))
  have hleft : (G.left ((star a : A) : P)).adjoint = G.left (a : P) := by
    change (G.left (star (a : P))).adjoint = G.left (a : P)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have hbase : (G.baseRepresentation A (star a)).adjoint = G.baseRepresentation A a := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  simpa only [ContinuousLinearMap.adjoint_comp, hleft, hbase] using h


/-- Compression commutes with the commutator against a base element. -/
theorem baseOperator_commutator_subalgebra (Y : H →L[ℂ] H) (a : A) :
    G.baseOperator A (commutator Y (G.left (a : P))) =
      commutator (G.baseOperator A Y) (G.baseRepresentation A a) := by
  unfold baseOperator commutator
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_intertwines A a]
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_adjoint_intertwines A a]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_operatorOfForm_le (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) :
    ‖operatorOfForm f hf R hb‖ ≤ R := by
  apply norm_le_of_matrix_coefficients _ hR
  intro x y
  rw [← norm_inner_symm, operatorOfForm_inner]
  convert hb x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompleteSpace H] in
private theorem isClosed_operatorForms : IsClosed {f : H → H → ℂ | IsOperatorForm f} := by
  have hc (x y : H) : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  unfold IsOperatorForm
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc (x + y) z) ((hc x z).add (hc y z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc (c • x) y) (continuous_const.mul (hc x y))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc x (y + z)) ((hc x y).add (hc x z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc x (c • y)) (continuous_const.mul (hc x y))

omit [CompleteSpace H] in
private theorem isCompact_boundedOperatorForms (R : ℝ) :
    IsCompact (boundedOperatorForms (H := H) R) := by
  have hd : IsCompact {f : H → H → ℂ | ∀ x y, f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} :=
    isCompact_pi_infinite fun x => isCompact_pi_infinite fun y => isCompact_closedBall _ _
  have he : boundedOperatorForms (H := H) R =
      {f | IsOperatorForm f} ∩ {f : H → H → ℂ | ∀ x y,
        f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} := by
    ext f
    simp [boundedOperatorForms, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact hd.inter_left isClosed_operatorForms

private theorem continuous_boundedFormOperator (R : ℝ) :
    Continuous (boundedFormOperator (H := H) R) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun f : boundedOperatorForms (H := H) R =>
      inner ℂ y (boundedFormOperator R f x)) =
      fun f => star (f.val x y) := by
    funext f
    change inner ℂ y (operatorOfForm f.val f.property.1 R f.property.2 x) = _
    rw [← inner_conj_symm, operatorOfForm_inner]
    rfl
  rw [he]
  have hc : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  exact (hc.comp continuous_subtype_val).star

/-- The closed norm ball in bounded operators on a Hilbert space is compact
in the weak-operator topology. -/
theorem isCompact_weakOperator_ball (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
  let : CompactSpace (boundedOperatorForms (H := H) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedOperatorForms R)
  have himage : Set.range (boundedFormOperator (H := H) R) =
      {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact norm_operatorOfForm_le f.val f.property.1 R hR f.property.2
    · intro hT
      let f : H → H → ℂ := fun x y => inner ℂ (T x) y
      have hf : IsOperatorForm f := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x y z; simp [f, inner_add_left]
        · intro c x y; simp [f, inner_smul_left, mul_comm]
        · intro x y z; simp [f, inner_add_right]
        · intro c x y; simp [f, inner_smul_right]
      have hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖ := by
        intro x y
        calc
          ‖f x y‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖toCLM T‖ * ‖x‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right ((toCLM T).le_opNorm x) (norm_nonneg y)
          _ ≤ R * ‖x‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hT (norm_nonneg x)) (norm_nonneg y)
      refine ⟨⟨f, hf, hb⟩, ?_⟩
      apply ContinuousLinearMapWOT.ext_inner
      intro x y
      change inner ℂ y (operatorOfForm f hf R hb x) = inner ℂ y (T x)
      rw [← inner_conj_symm, operatorOfForm_inner]
      exact inner_conj_symm _ _
  rw [← himage]
  exact isCompact_range (continuous_boundedFormOperator R)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite unitary averaging and weak-operator cluster points. These are the
analytic and algebraic symmetrization steps, before identifying the matrix
unitaries of the free-product model. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open Filter ContinuousLinearMapWOT

variable {Γ V H : Type*} [Fintype Γ] [Nonempty Γ]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

variable [CompleteSpace H]

/-- Every bounded sequence of operators has a weak-operator cluster point,
without a separability assumption on the Hilbert space. -/
theorem exists_weakOperator_cluster (T : ℕ → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ n, ‖T n‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)) := by
  have hev : ∀ᶠ n : ℕ in atTop, ofCLM (T n) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

/-- Eventual commutator bounds pass to weak cluster points. -/
theorem norm_commutator_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖commutator (T n) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem norm_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ g, ‖A g‖ ≤ R) :
    ‖weakOperatorIntegral μ A hA R hbound‖ ≤ R :=
  norm_operatorOfForm_le _ _ R hR _

/-- Left and right multiplication may be passed through the weak integral. -/
theorem weakOperatorIntegral_sandwich_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B C : H →L[ℂ] H) (x y : H) :
    inner ℂ ((B * weakOperatorIntegral μ A hA R hbound * C) x) y =
      ∫ g, inner ℂ ((B * A g * C) x) y ∂μ := by
  change inner ℂ (B (weakOperatorIntegral μ A hA R hbound (C x))) y = _
  rw [← adjoint_inner_right, weakOperatorIntegral_inner]
  apply integral_congr_ae
  filter_upwards with g
  exact adjoint_inner_right B (A g (C x)) y

/-- A commutator with a fixed operator may be passed through the weak integral. -/
theorem weakOperatorIntegral_commutator_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) (x y : H) :
    inner ℂ (commutator (weakOperatorIntegral μ A hA R hbound) B x) y =
      ∫ g, inner ℂ (commutator (A g) B x) y ∂μ := by
  simp only [commutator, sub_apply, ContinuousLinearMap.mul_def, comp_apply, inner_sub_left]
  rw [weakOperatorIntegral_inner, ← adjoint_inner_right, weakOperatorIntegral_inner,
    ← integral_sub (hA (B x) y) (hA x (B.adjoint y))]
  apply integral_congr_ae
  filter_upwards with g
  rw [adjoint_inner_right]

/-- Uniform commutator bounds are preserved by weak integration. -/
theorem norm_commutator_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ g, ‖commutator (A g) B‖ ≤ c) :
    ‖commutator (weakOperatorIntegral μ A hA R hbound) B‖ ≤ c := by
  apply norm_le_of_matrix_coefficients _ hc
  intro x y
  rw [← norm_inner_symm, weakOperatorIntegral_commutator_inner]
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ (commutator (A g) B x) y‖ ≤ c * ‖x‖ * ‖y‖ :=
    Filter.Eventually.of_forall fun g => calc
      _ ≤ ‖commutator (A g) B x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖commutator (A g) B‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((commutator (A g) B).le_opNorm x) (norm_nonneg y)
      _ ≤ c * ‖x‖ * ‖y‖ := by gcongr; exact hcomm g
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [probReal_univ, mul_one] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Haar averaging is contractive in operator norm. -/
theorem norm_haarTwirl_le (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) :
    ‖haarTwirl μ U hU T hI‖ ≤ ‖T‖ :=
  norm_weakOperatorIntegral_le μ _ _ _ (norm_nonneg _) _

/-- Left invariance of Haar measure gives invariance of the operator average. -/
theorem haarTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    U g * haarTwirl μ U hU T hI * U g⁻¹ = haarTwirl μ U hU T hI := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [haarTwirl, weakOperatorIntegral_sandwich_inner, weakOperatorIntegral_inner]
  calc
    _ = ∫ h, inner ℂ (unitaryConjugate U T (g * h) x) y ∂μ := by
      apply integral_congr_ae
      filter_upwards with h
      congr 2
      simp only [unitaryConjugate, mul_inv_rev, map_mul, mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => inner ℂ (unitaryConjugate U T h x) y) g

/-- Thus the Haar average commutes with the whole compact group. -/
theorem haarTwirl_commute (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    commutator (haarTwirl μ U hU T hI) (U g) = 0 := by
  have hc := congrArg (fun B : H →L[ℂ] H => B * U g) (haarTwirl_conjugate μ U hU T hI g)
  have hi : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc, hi, mul_one] at hc
  exact sub_eq_zero.mpr hc.symm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Every common commutator estimate for the orbit survives Haar averaging. -/
theorem norm_commutator_haarTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H)
    (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (B : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcomm : ∀ g, ‖commutator (unitaryConjugate U T g) B‖ ≤ c) :
    ‖commutator (haarTwirl μ U hU T hI) B‖ ≤ c :=
  norm_commutator_weakOperatorIntegral_le μ _ _ _ _ B hc hcomm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- On a subspace fixed pointwise by the group, compression is exactly
preserved by averaging. -/
theorem haarTwirl_compression (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T))
    (J : K →L[ℂ] H) (hfix : ∀ g, (U g).comp J = J) :
    J.adjoint.comp ((haarTwirl μ U hU T hI).comp J) = J.adjoint.comp (T.comp J) := by
  have happly (g : Γ) (x : K) : U g (J x) = J x :=
    congrArg (fun B : K →L[ℂ] H => B x) (hfix g)
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (J.adjoint (haarTwirl μ U hU T hI (J x))) y =
    inner ℂ (J.adjoint (T (J x))) y
  rw [adjoint_inner_left, adjoint_inner_left, haarTwirl, weakOperatorIntegral_inner]
  apply integral_eq_const
  filter_upwards with g
  change inner ℂ (U g (T (U g⁻¹ (J x)))) (J y) = _
  rw [happly, ← adjoint_inner_right, hstar, happly]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SimultaneousSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous symmetry for an increasing family of compact groups, using
actual Haar averages and a weak-operator cluster point. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT MeasureTheory
open scoped Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A fixed rectangular compression is weak-operator continuous, so an exact
compression identity survives a weak-operator cluster point. -/
theorem compression_eq_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S : H →L[ℂ] H) (A : K →L[ℂ] H) (B : H →L[ℂ] K) (C : K →L[ℂ] K)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    (heq : ∀ᶠ n in atTop, B.comp ((T n).comp A) = C) : B.comp (S.comp A) = C := by
  have hcont : Continuous (fun R : H →WOT[ℂ] H =>
      (ofCLM B).comp (R.comp (ofCLM A))) :=
    (continuous_postcomp (ofCLM B)).comp (continuous_precomp (ofCLM A))
  have hclosed : IsClosed {R : H →WOT[ℂ] H |
      (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} :=
    isClosed_eq hcont continuous_const
  have heq' : ∀ᶠ n in atTop, ofCLM (T n) ∈
      {R : H →WOT[ℂ] H | (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} := by
    filter_upwards [heq] with n hn
    exact congrArg ofCLM hn
  have he := hclosed.mem_of_mapClusterPt hcluster heq'
  exact congrArg toCLM he

variable {Γ : ℕ → Type*} [∀ n, Group (Γ n)] [∀ n, MeasurableSpace (Γ n)]
  [∀ n, MeasurableMul (Γ n)]
  (μ : ∀ n, Measure (Γ n)) [∀ n, IsProbabilityMeasure (μ n)]
  [∀ n, (μ n).IsMulLeftInvariant]

/-- A single cluster point has every finite-stage symmetry, all common
commutator bounds, and the original compression to the fixed subspace.
The stage maps are ordinary group-element inclusions; no limiting invariant
operator is assumed among the data. -/
theorem exists_simultaneously_symmetrized
    (U : ∀ n, Γ n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (hstar : ∀ n g, (U n g).adjoint = U n g⁻¹)
    (embedding : ∀ n m, n ≤ m → Γ n → Γ m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (μ n) (unitaryConjugate (U n) T))
    (J : K →L[ℂ] H) (hfix : ∀ n g, (U n g).comp J = J)
    {ι : Type*} (test : ι → H →L[ℂ] H) (bound : ι → ℝ) (hbound : ∀ i, 0 ≤ bound i)
    (htest : ∀ n g i, ‖commutator (unitaryConjugate (U n) T g) (test i)‖ ≤ bound i) :
    ∃ S : H →L[ℂ] H,
      ‖S‖ ≤ ‖T‖ ∧
      (∀ n g, commutator S (U n g) = 0) ∧
      (∀ i, ‖commutator S (test i)‖ ≤ bound i) ∧
      J.adjoint.comp (S.comp J) = J.adjoint.comp (T.comp J) := by
  let averages : ℕ → H →L[ℂ] H := fun n => haarTwirl (μ n) (U n) (hU n) T (hI n)
  obtain ⟨S, hS, hcluster⟩ := exists_weakOperator_cluster averages (norm_nonneg T)
    (fun n => norm_haarTwirl_le (μ n) (U n) (hU n) T (hI n))
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro n g
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_cluster averages S (U n g) hcluster (le_refl 0)
    filter_upwards [eventually_ge_atTop n] with m hm
    have he := haarTwirl_commute (μ m) (U m) (hU m) T (hI m) (embedding n m hm g)
    rw [hcompat] at he
    simp only [averages, he, norm_zero, le_refl]
  · intro i
    apply norm_commutator_le_of_weakOperator_cluster averages S (test i) hcluster (hbound i)
    exact Eventually.of_forall fun n =>
      norm_commutator_haarTwirl_le (μ n) (U n) (hU n) T (hI n) (test i)
        (hbound i) (fun g => htest n g i)
  · apply compression_eq_of_weakOperator_cluster averages S J J.adjoint
      (J.adjoint.comp (T.comp J)) hcluster
    exact Eventually.of_forall fun n =>
      haarTwirl_compression (μ n) (U n) (hU n) (hstar n) T (hI n) J (hfix n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompactHaarIntegrability
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of a unitary action gives every weak Haar integral
used in symmetrization. No continuity in operator norm is required. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
/-- Moving the left unitary to the second inner-product slot makes matrix
coefficients of its conjugation action continuous in the strong topology. -/
theorem continuous_unitaryConjugate_coefficient
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) (x y : H) :
    Continuous (fun g => inner ℂ (unitaryConjugate U T g x) y) := by
  have he : (fun g => inner ℂ (unitaryConjugate U T g x) y) =
      fun g => inner ℂ (T (U g⁻¹ x)) (U g⁻¹ y) := by
    funext g
    change inner ℂ (U g (T (U g⁻¹ x))) y = _
    rw [← adjoint_inner_right, hstar]
  rw [he]
  exact (T.continuous.comp ((hcont x).comp continuous_inv)).inner
    ((hcont y).comp continuous_inv)

/-- On a compact group these continuous scalar coefficients are integrable
against Haar probability measure. -/
theorem weaklyIntegrable_unitaryConjugate (μ : Measure Γ) [IsFiniteMeasure μ]
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) :
    WeaklyIntegrable μ (unitaryConjugate U T) := by
  intro x y
  exact (continuous_unitaryConjugate_coefficient U hstar hcont T x y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCornerWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The algebraic even-word step in the dihedral corner argument.
Corner letters absorb the reflection on the right, leaving an explicitly
alternating centered word in the original free factors. -/

noncomputable section
namespace KadisonSimilarity
namespace DihedralCornerWords

variable {R : Type*}

section Products
variable [Monoid R]

/-- The corner relation `a*d=a` is exactly what removes the first `d`. -/
theorem blockLetters_prod (d s a : R) {l : ℕ} (hl : 0 < l) (had : a * d = a) :
    (blockLetters d s a l).prod = a * (d * s) ^ l := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  simp only [blockLetters, Nat.succ_sub_one, List.prod_cons, pairLetters_prod,
    pow_succ', ← mul_assoc, had]

/-- The concatenated centered word has precisely the original ordered
product of corner letters and positive rotation powers. -/
theorem productLetters_prod (d s : R) (blocks : List (R × ℕ))
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1) :
    (productLetters d s blocks).prod = (blocks.map fun b => b.1 * (d * s) ^ b.2).prod := by
  induction blocks with
  | nil => simp [productLetters]
  | cons b bs ih =>
    simp only [productLetters, List.flatMap_cons, List.prod_append,
      List.map_cons, List.prod_cons]
    rw [blockLetters_prod d s b.1 (hpositive b List.mem_cons_self)
      (habsorb b List.mem_cons_self)]
    congr 1
    exact ih (fun b hb => hpositive b (List.mem_cons_of_mem _ hb))
      (fun b hb => habsorb b (List.mem_cons_of_mem _ hb))

/-- Intermediate right support factors disappear because each subsequent
letter is left supported on the same idempotent. No idempotence is needed
for this purely multiplicative identity. -/
theorem product_insert_right_support (p : R) (xs : List R) (hne : xs ≠ [])
    (hleft : ∀ x ∈ xs, p * x = x) :
    (xs.map fun x => x * p).prod = xs.prod * p := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.map_cons, List.prod_cons,
        ih (List.cons_ne_nil _ _) (fun z hz => hleft z (List.mem_cons_of_mem _ hz))]
      simp only [List.prod_cons]
      calc
        (x * p) * ((y * ys.prod) * p) = (x * (p * y)) * ys.prod * p := by
          simp only [mul_assoc]
        _ = (x * (y * ys.prod)) * p := by
          rw [hleft y (by simp)]
          simp only [mul_assoc]

end Products

section Freeness
variable [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  (τ : R →ₗ[ℂ] ℂ) (D A : StarSubalgebra ℂ R)
  {d s : R} (hd : d ∈ D) (hs : s ∈ A) (hd0 : τ d = 0) (hs0 : τ s = 0)

include hd hs hd0 hs0 in
/-- Prepending any number of `d,s` pairs preserves the alternating starting
side because each such pair has even length. -/
theorem pairLetters_prepend (n : ℕ) (tail : List R)
    (htail : AlternatingCenteredWord τ D A true tail) :
    AlternatingCenteredWord τ D A true (pairLetters d s n ++ tail) := by
  induction n with
  | zero => simpa only [pairLetters, List.nil_append] using htail
  | succ n ih =>
    change AlternatingCenteredWord τ D A true (d :: s :: (pairLetters d s n ++ tail))
    exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

include hd hs hd0 hs0 in
/-- A centered corner letter followed by `s` and rotation pairs is an
alternating centered word, ready to concatenate with another block. -/
theorem blockLetters_prepend (a : R) (ha : a ∈ D) (ha0 : τ a = 0)
    (l : ℕ) (tail : List R) (htail : AlternatingCenteredWord τ D A true tail) :
    AlternatingCenteredWord τ D A true (blockLetters d s a l ++ tail) := by
  change AlternatingCenteredWord τ D A true (a :: s :: (pairLetters d s (l - 1) ++ tail))
  exact .cons (by simpa using ha) ha0 (.cons (by simpa using hs) hs0
    (pairLetters_prepend τ D A hd hs hd0 hs0 (l - 1) tail htail))

include hd hs hd0 hs0 in
/-- The entire expanded corner product is alternating and centered in the
original two free algebras. -/
theorem productLetters_alternating (blocks : List (R × ℕ))
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0) :
    AlternatingCenteredWord τ D A true (productLetters d s blocks) := by
  induction blocks with
  | nil => exact .nil true
  | cons b bs ih =>
    change AlternatingCenteredWord τ D A true
      (blockLetters d s b.1 b.2 ++ productLetters d s bs)
    exact blockLetters_prepend τ D A hd hs hd0 hs0 b.1 (hmem b List.mem_cons_self)
      (hzero b List.mem_cons_self) b.2 _
      (ih (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
        (fun b hb => hzero b (List.mem_cons_of_mem _ hb)))

omit [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
/-- A nonempty list of corner blocks produces a nonempty centered word. -/
theorem productLetters_ne_nil {blocks : List (R × ℕ)} (hblocks : blocks ≠ []) :
    productLetters d s blocks ≠ [] := by
  cases blocks with
  | nil => exact (hblocks rfl).elim
  | cons b bs => simp [productLetters, blockLetters]

include hd hs hd0 hs0 in
/-- The original algebraic corner-freeness step: every cyclic product of
centered corner letters and positive rotation powers has trace zero. -/
theorem trace_product_eq_zero (hf : ScalarFree τ D A)
    (blocks : List (R × ℕ)) (hblocks : blocks ≠ [])
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0)
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1) :
    τ ((blocks.map fun b => b.1 * (d * s) ^ b.2).prod) = 0 := by
  have hw := productLetters_alternating τ D A hd hs hd0 hs0 blocks hmem hzero
  have hne := productLetters_ne_nil (d := d) (s := s) hblocks
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  rw [hx] at hw
  rw [← productLetters_prod d s blocks hpositive habsorb, hx]
  exact hf true x xs hw

omit [StarRing R] [StarModule ℂ R] in
/-- For a tracial functional, inserting the common corner support after
each letter does not change the trace of a nonempty product. -/
theorem trace_product_insert_right_support
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (p : R)
    (xs : List R) (hne : xs ≠ []) (hleft : ∀ x ∈ xs, p * x = x) :
    τ ((xs.map fun x => x * p).prod) = τ xs.prod := by
  rw [product_insert_right_support p xs hne hleft, htr]
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    simp only [List.prod_cons, ← mul_assoc, hleft x List.mem_cons_self]

include hd hs hd0 hs0 in
/-- The even cyclic trace vanishing remains true with all the actual corner
supports inserted. -/
theorem trace_corner_product_eq_zero (hf : ScalarFree τ D A)
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (p : R)
    (blocks : List (R × ℕ)) (hblocks : blocks ≠ [])
    (hmem : ∀ b ∈ blocks, b.1 ∈ D) (hzero : ∀ b ∈ blocks, τ b.1 = 0)
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (habsorb : ∀ b ∈ blocks, b.1 * d = b.1)
    (hleft : ∀ b ∈ blocks, p * b.1 = b.1) :
    τ ((blocks.map fun b => b.1 * (d * s) ^ b.2 * p).prod) = 0 := by
  let xs := blocks.map fun b => b.1 * (d * s) ^ b.2
  have hne : xs ≠ [] := by simpa only [xs, ne_eq, List.map_eq_nil_iff] using hblocks
  have hsupp : ∀ x ∈ xs, p * x = x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [← mul_assoc, hleft b hb]
  have h := trace_product_insert_right_support τ htr p xs hne hsupp
  simp only [xs, List.map_map, Function.comp_def] at h
  rw [h]
  exact trace_product_eq_zero τ D A hd hs hd0 hs0 hf blocks hblocks hmem hzero
    hpositive habsorb

end Freeness
end DihedralCornerWords
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace-pairing description of conditional expectation. Its uniqueness,
bimodule law, tower law, and Hilbert projection formula are derived here. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

/-- Faithfulness of the algebra-vector realization implies faithfulness of
its positive trace pairing. -/
theorem trace_faithful (G : TracialCornerGeometry P H)
    (hfaithful : Function.Injective G.vector) (x : P)
    (hx : G.trace (star x * x) = 0) : x = 0 := by
  apply hfaithful
  rw [map_zero]
  exact inner_self_eq_zero.mp (by rw [G.inner_vector, hx])

end TracialCornerGeometry

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {A : StarSubalgebra ℂ P}
  (E : TracialExpectation τ A)

/-- Expectation preserves the trace by testing its pairing with the unit. -/
theorem trace_map (x : P) : τ (E.map x) = τ x := by
  simpa only [one_mul] using E.pairing x 1 A.one_mem

variable (hf : ∀ x, τ (star x * x) = 0 → x = 0)

include hf

theorem map_of_mem {x : P} (hx : x ∈ A) : E.map x = x :=
  E.eq_of_pairings hf x x hx (fun _ _ => rfl)

@[simp] theorem map_one : E.map 1 = 1 := E.map_of_mem hf A.one_mem

@[simp] theorem map_map (x : P) : E.map (E.map x) = E.map x :=
  E.map_of_mem hf (E.range x)

theorem bimodule (htr : ∀ x y, τ (x * y) = τ (y * x))
    (a b x : P) (ha : a ∈ A) (hb : b ∈ A) :
    E.map (a * x * b) = a * E.map x * b := by
  rw [E.map_mul_right hf htr _ b hb, E.map_mul_left hf a x ha]

/-- Scalar freeness now gives the free-compression expectation formula for
this actual expectation map. -/
theorem free_compression (hτ : τ 1 = 1)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    {D : StarSubalgebra ℂ P} (hfree : ScalarFree τ D A)
    {e b : P} (he : e ∈ D) (hb : b ∈ A) (hb0 : τ b = 0) :
    E.map (e * b * e) = (τ e) ^ 2 • b :=
  expectation_free_compression τ hτ htr hf hfree E.map E.range E.pairing he hb hb0

end TracialExpectation

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (E : TracialExpectation G.trace A)

/-- Conditional expectation on algebra vectors is exactly orthogonal
projection onto the actual closed base Hilbert space. -/
theorem expectation_base_projection (x : P) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector x) =
      G.baseVector A ⟨E.map x, E.range x⟩ := by
  apply ext_inner_left ℂ
  intro y
  refine (G.baseVector_dense A).induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.vector x) =
    inner ℂ (G.vector (a : P)) (G.vector (E.map x))
  rw [G.inner_vector, G.inner_vector]
  exact (E.pairing x (star (a : P)) (star_mem a.property)).symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a tracial expectation to a corner. The normalized corner
trace and the restricted expectation are constructed from the ambient ones. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CStarCorner

variable (p : P) (hp : IsStarProjection p)

theorem normalizedTrace_one (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0) :
    normalizedTrace p hp τ 1 = 1 := by
  rw [normalizedTrace_apply, coe_one, inv_mul_cancel₀ ht]

theorem normalizedTrace_faithful (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0)
    (hf : ∀ x, τ (star x * x) = 0 → x = 0)
    (x : CStarCorner p hp) (hx : normalizedTrace p hp τ (star x * x) = 0) :
    x = 0 := by
  apply Subtype.ext
  apply hf
  change (τ p)⁻¹ * τ (star (x : P) * (x : P)) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero ht)

end CStarCorner

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P}
  (E : TracialExpectation τ C)
  (hf : ∀ x, τ (star x * x) = 0 → x = 0)
  (htr : ∀ x y, τ (x * y) = τ (y * x))
  (p : P) (hp : IsStarProjection p) (hpC : p ∈ C)

include hf htr in
/-- The ambient expectation formula used in the dihedral corner follows
from freeness in the normalized corner, rather than being extra data. -/
theorem free_corner_compression (ht : τ p ≠ 0)
    (D : StarSubalgebra ℂ P) (hpD : p ∈ D)
    (hfree : ScalarFree (CStarCorner.normalizedTrace p hp τ)
      (CStarCorner.subalgebra p hp D hpD) (CStarCorner.subalgebra p hp C hpC))
    (e b : CStarCorner p hp) (he : (e : P) ∈ D) (hb : (b : P) ∈ C)
    (hb0 : τ (b : P) = 0) :
    E.map ((e : P) * (b : P) * (e : P)) =
      ((τ p)⁻¹ * τ (e : P)) ^ 2 • (b : P) := by
  have h := (E.corner hf htr p hp hpC).free_compression
    (CStarCorner.normalizedTrace_faithful p hp τ ht hf)
    (CStarCorner.normalizedTrace_one p hp τ ht)
    (CStarCorner.normalizedTrace_tracial p hp τ htr) hfree (e := e) (b := b) he hb
    (by simp only [CStarCorner.normalizedTrace_apply, hb0, mul_zero])
  exact congrArg (fun x : CStarCorner p hp => (x : P)) h

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCornerDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate L²-continuity extends the positive-power corner trace tests.
Only density of their linear span in the centered corner is needed;
no uniform bound on approximants is imposed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

/-- The trace with fixed left and right factors is a continuous functional
of the middle L²-vector, by traciality and the inner-product identity. -/
theorem trace_middle_eq_inner (a x b : P) :
    G.trace (a * x * b) = inner ℂ (G.vector (star (b * a))) (G.vector x) := by
  rw [G.inner_vector, star_star]
  calc
    G.trace (a * x * b) = G.trace (b * (a * x)) := G.tracial _ _
    _ = G.trace ((b * a) * x) := by rw [mul_assoc]

/-- A middle-factor trace test that vanishes on generators vanishes on the
closed linear span of their L²-vectors. -/
theorem trace_middle_zero_of_mem_closed_span (S : Set P) (a x b : P)
    (hx : G.vector x ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure)
    (hzero : ∀ y ∈ S, G.trace (a * y * b) = 0) :
    G.trace (a * x * b) = 0 := by
  let L : H →L[ℂ] ℂ := innerSL ℂ (G.vector (star (b * a)))
  have hspan : Submodule.span ℂ (G.vector '' S) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    change inner ℂ (G.vector (star (b * a))) (G.vector y) = 0
    rw [← G.trace_middle_eq_inner]
    exact hzero y hy
  have hclosure := (Submodule.span ℂ (G.vector '' S)).topologicalClosure_minimal
    hspan L.isClosed_ker
  have h := hclosure hx
  change inner ℂ (G.vector (star (b * a))) (G.vector x) = 0 at h
  rw [G.trace_middle_eq_inner]
  exact h

end TracialCornerGeometry

namespace DihedralCornerWords

/-- Extending one variable at a time requires only L²-density. The fixed
factors may have arbitrary operator norms. -/
theorem trace_alternatingProduct_zero_of_dense
    (G : TracialCornerGeometry P H) (S : Set P) (as : List P) (a : P)
    (hzero : ∀ xs : List P, xs.length = as.length → (∀ x ∈ xs, x ∈ S) →
      G.trace (a * alternatingProduct as xs) = 0)
    (xs : List P) (hlen : xs.length = as.length)
    (hmem : ∀ x ∈ xs,
      G.vector x ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure) :
    G.trace (a * alternatingProduct as xs) = 0 := by
  induction as generalizing a xs with
  | nil =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp hlen
    subst xs
    exact hzero [] rfl (by simp)
  | cons b bs ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      have hlen' : xs.length = bs.length := Nat.succ.inj hlen
      have htail : ∀ y ∈ xs,
          G.vector y ∈ (Submodule.span ℂ (G.vector '' S)).topologicalClosure :=
        fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      have htest : ∀ y ∈ S,
          G.trace ((a * b) * y * alternatingProduct bs xs) = 0 := by
        intro y hy
        apply ih (a := a * b * y)
        · intro ys hys hysmem
          have h := hzero (y :: ys) (by simp [hys]) (by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hysmem z hz)
          simpa only [alternatingProduct_cons, mul_assoc] using h
        · exact hlen'
        · exact htail
      have h := G.trace_middle_zero_of_mem_closed_span S (a * b) x
        (alternatingProduct bs xs) (hmem x List.mem_cons_self) htest
      simpa only [alternatingProduct_cons, mul_assoc] using h

section Splitting
variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τR : R →ₗ[ℂ] ℂ} {AR BR : StarSubalgebra ℂ R}

/-- Split an even alternating word into its two ordered lists of letters.
The product identity is valid after applying any map into the ambient algebra. -/
theorem split_even_alternating_word (f : R → P) (w : List R)
    (hw : AlternatingCenteredWord τR AR BR true w) (heven : w.length % 2 = 0) :
    ∃ as bs : List R, as.length = bs.length ∧ w.length = 2 * as.length ∧
      (∀ a ∈ as, a ∈ AR ∧ τR a = 0) ∧ (∀ b ∈ bs, b ∈ BR ∧ τR b = 0) ∧
      (w.map f).prod = alternatingProduct (as.map f) (bs.map f) := by
  induction w using List.twoStepInduction with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp, rfl⟩
  | singleton a => simp at heven
  | cons_cons a b w ih _ =>
    cases hw with
    | cons ha ha0 ht =>
      cases ht with
      | cons hb hb0 ht' =>
        have htail : AlternatingCenteredWord τR AR BR true w := by
          simpa only [Bool.not_not] using ht'
        have ht_even : w.length % 2 = 0 := by
          simp only [List.length_cons] at heven
          omega
        obtain ⟨as, bs, hlen, hwlen, hA, hB, hprod⟩ := ih htail ht_even
        refine ⟨a :: as, b :: bs, by simp only [List.length_cons, hlen], ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by simpa using ha, ha0⟩
          · exact hA x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by simpa using hb, hb0⟩
          · exact hB x hx
        · simp only [List.map_cons, List.prod_cons, alternatingProduct_cons, hprod,
            mul_assoc]

end Splitting

/-- Choosing a positive exponent for each generator converts the alternating
product to the concrete list of corner blocks. -/
theorem alternatingProduct_eq_positive_blocks (p w : P) (as xs : List P)
    (hlen : xs.length = as.length) (hsupport : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, x ∈ positiveCornerPowers p w) :
    ∃ bs : List (P × ℕ), bs.map Prod.fst = as ∧
      (∀ b ∈ bs, 0 < b.2) ∧
      alternatingProduct as xs = (bs.map fun b => b.1 * w ^ b.2 * p).prod := by
  induction as generalizing xs with
  | nil =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp hlen
    subst xs
    exact ⟨[], rfl, by simp, rfl⟩
  | cons a as ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨n, rfl⟩ := hmem x List.mem_cons_self
      obtain ⟨bs, hbs, hpos, heq⟩ := ih xs (Nat.succ.inj hlen)
        (fun b hb => hsupport b (List.mem_cons_of_mem _ hb))
        (fun y hy => hmem y (List.mem_cons_of_mem _ hy))
      refine ⟨(a, n.val) :: bs, ?_, ?_, ?_⟩
      · simp only [List.map_cons, hbs]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact n.property
        · exact hpos b hb
      · simp only [alternatingProduct_cons, List.map_cons, List.prod_cons, heq]
        have h := congrArg (fun z : P => z * w ^ n.val * p *
          (bs.map fun b => b.1 * w ^ b.2 * p).prod) (hsupport a List.mem_cons_self)
        simpa only [mul_assoc] using h

/-- The original scalar freeness supplies every positive-generator test,
with the support factors and exponent choices constructed explicitly. -/
theorem trace_positive_corner_generators_zero
    (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (as xs : List P) (hne : as ≠ []) (hlen : xs.length = as.length)
    (hD : ∀ a ∈ as, a ∈ D) (hzero : ∀ a ∈ as, G.trace a = 0)
    (habsorb : ∀ a ∈ as, a * d = a)
    (hleft : ∀ a ∈ as, p * a = a) (hright : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, x ∈ positiveCornerPowers p (d * s)) :
    G.trace (alternatingProduct as xs) = 0 := by
  obtain ⟨bs, hbs, hpos, heq⟩ :=
    alternatingProduct_eq_positive_blocks p (d * s) as xs hlen hright hmem
  have hbsne : bs ≠ [] := by
    intro hb
    apply hne
    simpa only [hb, List.map_nil] using hbs.symm
  have hfirst : ∀ b ∈ bs, b.1 ∈ as := by
    intro b hb
    rw [← hbs]
    exact List.mem_map_of_mem hb
  rw [heq]
  exact trace_corner_product_eq_zero G.trace D A hd hs hd0 hs0 hf G.tracial p bs
    hbsne (fun b hb => hD _ (hfirst b hb)) (fun b hb => hzero _ (hfirst b hb))
    hpos (fun b hb => habsorb _ (hfirst b hb)) (fun b hb => hleft _ (hfirst b hb))

/-- Every even cyclic product of centered corner letters vanishes once the
positive compressed powers have dense span in the centered second corner. -/
theorem trace_corner_alternating_zero_of_dense
    (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (as xs : List P) (hne : as ≠ []) (hlen : xs.length = as.length)
    (hD : ∀ a ∈ as, a ∈ D) (hzero : ∀ a ∈ as, G.trace a = 0)
    (habsorb : ∀ a ∈ as, a * d = a)
    (hleft : ∀ a ∈ as, p * a = a) (hright : ∀ a ∈ as, a * p = a)
    (hmem : ∀ x ∈ xs, G.vector x ∈
      (Submodule.span ℂ (G.vector '' positiveCornerPowers p (d * s))).topologicalClosure) :
    G.trace (alternatingProduct as xs) = 0 := by
  have h := trace_alternatingProduct_zero_of_dense G (positiveCornerPowers p (d * s))
    as 1 (fun ys hys hymem => by
      simp only [one_mul]
      exact trace_positive_corner_generators_zero G D A hf hd hs hd0 hs0 p as ys
        hne hys hD hzero habsorb hleft hright hymem) xs hlen hmem
  simpa only [one_mul] using h

/-- Coercing a corner product inserts the corner identity at its right end. -/
theorem coe_corner_list_prod (p : P) (hp : IsStarProjection p)
    (w : List (CStarCorner p hp)) :
    (w.prod : P) = (List.map (fun x : CStarCorner p hp => (x : P)) w).prod * p := by
  induction w with
  | nil => simp only [List.prod_nil, CStarCorner.coe_one, List.map_nil, one_mul]
  | cons x xs ih =>
    change (x : P) * (xs.prod : P) =
      (x : P) * (List.map (fun y : CStarCorner p hp => (y : P)) xs).prod * p
    rw [ih, mul_assoc]

/-- Actual corner freeness follows from the original scalar freeness and
density of the centered positive compressed rotation powers. The density
input is a geometric word-span statement, not a freeness assumption. -/
theorem scalarFree_corner_of_positive_power_density
    (G : TracialCornerGeometry P H) (D A C : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) {d s : P}
    (hd : d ∈ D) (hs : s ∈ A) (hd0 : G.trace d = 0) (hs0 : G.trace s = 0)
    (p : P) (hp : IsStarProjection p) (hpD : p ∈ D) (hpC : p ∈ C)
    (hpd : p * d = p) (ht : G.trace p ≠ 0)
    (hdense : ∀ x : CStarCorner p hp, (x : P) ∈ C → G.trace (x : P) = 0 →
      G.vector (x : P) ∈
        (Submodule.span ℂ (G.vector '' positiveCornerPowers p (d * s))).topologicalClosure) :
    ScalarFree (CStarCorner.normalizedTrace p hp G.trace)
      (CStarCorner.subalgebra p hp D hpD) (CStarCorner.subalgebra p hp C hpC) := by
  apply scalarFree_of_even_cyclic
    (CStarCorner.normalizedTrace_one p hp G.trace ht)
    (CStarCorner.normalizedTrace_tracial p hp G.trace G.tracial)
  intro x xs hw heven
  obtain ⟨as, bs, hlen, hwlen, hA, hB, hprod⟩ :=
    split_even_alternating_word (fun y : CStarCorner p hp => (y : P)) (x :: xs) hw heven
  have has : as ≠ [] := by
    intro heq
    simp only [heq, List.length_nil, mul_zero, List.length_cons] at hwlen
    omega
  have hzeroA : ∀ a ∈ as, G.trace (a : P) = 0 := by
    intro a ha
    exact (mul_eq_zero.mp (hA a ha).2).resolve_left (inv_ne_zero ht)
  have hzeroB : ∀ b ∈ bs, G.trace (b : P) = 0 := by
    intro b hb
    exact (mul_eq_zero.mp (hB b hb).2).resolve_left (inv_ne_zero ht)
  have htest := trace_corner_alternating_zero_of_dense G D A hf hd hs hd0 hs0 p
    (List.map (fun a : CStarCorner p hp => (a : P)) as) (List.map (fun b : CStarCorner p hp => (b : P)) bs)
    (by simpa only [ne_eq, List.map_eq_nil_iff] using has)
    (by simpa only [List.length_map] using hlen.symm)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact (hA a ha').1)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact hzeroA a ha')
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      calc
        (a : P) * d = ((a : P) * p) * d := by rw [a.property.2]
        _ = (a : P) * (p * d) := mul_assoc _ _ _
        _ = (a : P) := by rw [hpd, a.property.2])
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact a.property.1)
    (by
      intro a ha
      obtain ⟨a, ha', rfl⟩ := (List.mem_map (f := fun a : CStarCorner p hp => (a : P))).mp ha
      exact a.property.2)
    (by
      intro b hb
      obtain ⟨b, hb', rfl⟩ := (List.mem_map (f := fun b : CStarCorner p hp => (b : P))).mp hb
      exact hdense b (hB b hb').1 (hzeroB b hb'))
  rw [← hprod] at htest
  rw [CStarCorner.normalizedTrace_apply, coe_corner_list_prod]
  apply mul_eq_zero_of_right
  rw [G.tracial _ p]
  simpa only [List.map_cons, List.prod_cons, ← mul_assoc, x.property.1] using htest

end DihedralCornerWords
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralPositiveDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered dihedral corner is generated in L² by the positive
compressed rotation powers. Apply the bounded centered corner map to the
ordinary rotation/reflection word span; no bounded approximation theorem
or corner-freeness hypothesis is needed. -/

noncomputable section
namespace KadisonSimilarity

section Algebra
variable {P : Type*} [Ring P] [Algebra ℂ P]

/-- Both sides of the half projection absorb its reflection. -/
theorem halfProjection_absorbs_reflection (d : Pˣ) (hd : d * d = 1) :
    dihedralHalfProjection d * (d : P) = dihedralHalfProjection d ∧
      (d : P) * dihedralHalfProjection d = dihedralHalfProjection d := by
  have hd' : (d : P) * (d : P) = 1 := by rw [← Units.val_mul, hd, Units.val_one]
  constructor
  · simp only [dihedralHalfProjection, smul_mul_assoc, add_mul, one_mul, hd']
    congr 1
    abel
  · simp only [dihedralHalfProjection, mul_smul_comm, mul_add, mul_one, hd']
    congr 1
    abel

/-- Reflection conjugation makes opposite rotation powers equal after
compression to the half projection. -/
theorem halfProjection_compressed_neg (d w : Pˣ) (hd : d * d = 1)
    (hconj : d * w = w⁻¹ * d) (l : ℤ) :
    dihedralHalfProjection d * (↑(w ^ (-l)) : P) * dihedralHalfProjection d =
      dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d := by
  obtain ⟨hpd, hdp⟩ := halfProjection_absorbs_reflection d hd
  have hm := (show SemiconjBy d w w⁻¹ from hconj).zpow_right l
  have hm' : (d : P) * (↑(w ^ l) : P) = (↑(w ^ (-l)) : P) * (d : P) := by
    have h := congrArg (fun a : Pˣ => (a : P)) hm.eq
    simpa only [Units.val_mul, inv_zpow, zpow_neg] using h
  calc
    _ = dihedralHalfProjection d * (↑(w ^ (-l)) : P) *
        ((d : P) * dihedralHalfProjection d) := by rw [hdp]
    _ = dihedralHalfProjection d * ((↑(w ^ (-l)) : P) * (d : P)) *
        dihedralHalfProjection d := by simp only [mul_assoc]
    _ = dihedralHalfProjection d * ((d : P) * (↑(w ^ l) : P)) *
        dihedralHalfProjection d := by rw [← hm']
    _ = _ := by rw [← mul_assoc (dihedralHalfProjection d) (d : P), hpd]

/-- Every compressed nonzero integer power is a positive compressed power. -/
theorem halfProjection_compressed_natAbs (d w : Pˣ) (hd : d * d = 1)
    (hconj : d * w = w⁻¹ * d) (l : ℤ) :
    dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d =
      dihedralHalfProjection d * (w : P) ^ l.natAbs * dihedralHalfProjection d := by
  cases l with
  | ofNat n => rfl
  | negSucc n =>
    have h := halfProjection_compressed_neg d w hd hconj ((n + 1 : ℕ) : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at h
    have heq : -((n + 1 : ℕ) : ℤ) = Int.negSucc n := by omega
    rw [heq] at h
    exact h

/-- Reflection-coset words have the same corner compression as rotations. -/
theorem halfProjection_compressed_coset (d w : Pˣ) (hd : d * d = 1) (l : ℤ) :
    dihedralHalfProjection d * ((↑(w ^ l) : P) * (d : P)) * dihedralHalfProjection d =
      dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d := by
  rw [mul_assoc, mul_assoc, (halfProjection_absorbs_reflection d hd).2]
  rw [← mul_assoc]

end Algebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H)

/-- Its value on algebra vectors is the centered corner compression. -/
theorem centeredCornerProjection_vector (p : P) (hp : IsStarProjection p) (x : P) :
    G.centeredCornerProjection p (G.vector x) =
      G.vector (p * x * p) - ((G.trace p)⁻¹ * G.trace (p * x)) • G.vector p := by
  simp only [centeredCornerProjection, sub_apply,
    smul_apply, G.cornerProjection_vector, InnerProductSpace.rankOne_apply,
    G.inner_vector, hp.isSelfAdjoint.star_eq, smul_smul]

/-- Every centered corner vector is fixed by the bounded centered compression. -/
theorem centeredCornerProjection_fixed (p : P) (hp : IsStarProjection p)
    (x : CStarCorner p hp) (hx : G.trace (x : P) = 0) :
    G.centeredCornerProjection p (G.vector (x : P)) = G.vector (x : P) := by
  rw [G.centeredCornerProjection_vector p hp, x.property.1, x.property.2, hx]
  simp

/-- The identity contributes only the scalar part of the corner. -/
theorem centeredCornerProjection_one (p : P) (hp : IsStarProjection p)
    (ht : G.trace p ≠ 0) :
    G.centeredCornerProjection p (G.vector 1) = 0 := by
  rw [G.centeredCornerProjection_vector p hp]
  simp only [mul_one, hp.isIdempotentElem.eq, inv_mul_cancel₀ ht, one_smul, sub_self]

/-- The normalized Haar and coset moments kill the scalar coefficient of
every nonidentity compressed rotation. -/
theorem trace_halfProjection_rotation (d w : Pˣ)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    (l : ℤ) (hl : l ≠ 0) :
    G.trace (dihedralHalfProjection d * (↑(w ^ l) : P)) = 0 := by
  simp only [dihedralHalfProjection, smul_mul_assoc, add_mul, one_mul,
    map_smul, map_add, G.tracial (d : P), hhaar, ite_eq_right hl, hcoset,
    add_zero, smul_zero]

/-- Reflection does not change the trace coefficient in the corner. -/
theorem trace_halfProjection_coset (d w : Pˣ) (hd : d * d = 1) (l : ℤ) :
    G.trace (dihedralHalfProjection d * ((↑(w ^ l) : P) * (d : P))) =
      G.trace (dihedralHalfProjection d * (↑(w ^ l) : P)) := by
  rw [← mul_assoc, G.tracial _ (d : P), ← mul_assoc,
    (halfProjection_absorbs_reflection d hd).2]

/-- Centered compression sends every group word into the closed span of
positive compressed rotation powers. -/
theorem centeredCornerProjection_group_word_mem
    (d w : Pˣ) (hd : d * d = 1) (hconj : d * w = w⁻¹ * d)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : G.trace (dihedralHalfProjection d) ≠ 0)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    {z : H} (hz : z ∈ G.dihedralGroupWordVectors d w) :
    G.centeredCornerProjection (dihedralHalfProjection d) z ∈
      (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
        (dihedralHalfProjection d) (w : P))).topologicalClosure := by
  let M := Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
    (dihedralHalfProjection d) (w : P))
  have hrot : ∀ l : ℤ,
      G.centeredCornerProjection (dihedralHalfProjection d) (G.vector (↑(w ^ l) : P)) ∈
        M.topologicalClosure := by
    intro l
    by_cases hl : l = 0
    · subst l
      simpa only [zpow_zero, Units.val_one] using
        (show G.centeredCornerProjection (dihedralHalfProjection d) (G.vector 1) ∈
          M.topologicalClosure by rw [G.centeredCornerProjection_one _ hp ht]; exact Submodule.zero_mem _)
    · rw [G.centeredCornerProjection_vector _ hp,
        G.trace_halfProjection_rotation d w hhaar hcoset l hl, mul_zero, zero_smul, sub_zero,
        halfProjection_compressed_natAbs d w hd hconj]
      apply M.le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      exact ⟨⟨l.natAbs, Int.natAbs_pos.mpr hl⟩, rfl⟩
  rcases hz with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exact hrot l
  · have heq : G.centeredCornerProjection (dihedralHalfProjection d)
        (G.vector ((↑(w ^ l) : P) * (d : P))) =
      G.centeredCornerProjection (dihedralHalfProjection d) (G.vector (↑(w ^ l) : P)) := by
      rw [G.centeredCornerProjection_vector _ hp, G.centeredCornerProjection_vector _ hp,
        halfProjection_compressed_coset d w hd,
        G.trace_halfProjection_coset d w hd]
    rw [heq]
    exact hrot l

/-- Applying the centered corner map to the raw group-word L²-span gives
the desired positive-power density for each centered corner vector. -/
theorem positive_corner_density_of_group_word_density
    (d w : Pˣ) (hd : d * d = 1) (hconj : d * w = w⁻¹ * d)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : G.trace (dihedralHalfProjection d) ≠ 0)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    (x : CStarCorner (dihedralHalfProjection d) hp) (hx : G.trace (x : P) = 0)
    (hspan : G.vector (x : P) ∈
      (Submodule.span ℂ (G.dihedralGroupWordVectors d w)).topologicalClosure) :
    G.vector (x : P) ∈
      (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
        (dihedralHalfProjection d) (w : P))).topologicalClosure := by
  let M := (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
    (dihedralHalfProjection d) (w : P))).topologicalClosure
  let Q := G.centeredCornerProjection (dihedralHalfProjection d)
  have hmap : Submodule.span ℂ (G.dihedralGroupWordVectors d w) ≤ M.comap Q.toLinearMap := by
    apply Submodule.span_le.mpr
    intro z hz
    exact G.centeredCornerProjection_group_word_mem d w hd hconj hp ht hhaar hcoset hz
  have hM : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  have hclosed : IsClosed (M.comap Q.toLinearMap : Set H) :=
    hM.preimage Q.continuous
  have h := ((Submodule.span ℂ (G.dihedralGroupWordVectors d w)).topologicalClosure_minimal
    hmap hclosed) hspan
  change Q (G.vector (x : P)) ∈ M at h
  dsimp only [Q] at h
  rw [G.centeredCornerProjection_fixed _ hp x hx] at h
  exact h

/-- For two involutions, the first one reverses their product. -/
theorem free_symmetry_rotation_conjugation (d s : Pˣ)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) : d * (d * s) = (d * s)⁻¹ * d := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  calc
    d * (d * s) = s := by rw [← mul_assoc, hdd, one_mul]
    _ = (d * s)⁻¹ * d := by
      rw [mul_inv_rev, hdi, hsi, mul_assoc, hdd, mul_one]

/-- The reflection-coset moments used by the centered corner map follow
from the scalar-freeness moments. -/
theorem free_symmetry_first_coset_moments
    (D A : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) (l : ℤ) :
    G.trace ((↑((d * s) ^ l) : P) * (d : P)) = 0 := by
  have hss : s * s = 1 := by simpa only [hsi] using inv_mul_cancel s
  have heq : (d * s) ^ (l + 1) * s = (d * s) ^ l * d := by
    rw [zpow_add, zpow_one, mul_assoc, mul_assoc, hss, mul_one]
  have hval := congrArg (fun u : Pˣ => (u : P)) heq
  simp only [Units.val_mul] at hval
  rw [← hval]
  exact free_symmetry_coset_moments G.trace D A hf d s hd hs hd0 hs0 hdi hsi (l + 1)

/-- The full normalized-corner freeness theorem requires only the raw
L²-span of the dihedral group words, in addition to the original free factors. -/
theorem scalarFree_corner_of_dihedral_word_density
    (D A C : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (hspan : ∀ x : CStarCorner (dihedralHalfProjection d) hp, (x : P) ∈ C →
      G.vector (x : P) ∈
        (Submodule.span ℂ (G.dihedralGroupWordVectors d (d * s))).topologicalClosure) :
    ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D
        (D.smul_mem (D.add_mem D.one_mem hd) (1 / 2 : ℂ)))
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC) := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  have htval : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ) := by
    simp only [dihedralHalfProjection, map_smul, map_add, hτ, hd0, add_zero,
      smul_eq_mul, mul_one]
  have ht : G.trace (dihedralHalfProjection d) ≠ 0 := by rw [htval]; norm_num
  apply DihedralCornerWords.scalarFree_corner_of_positive_power_density G D A C hf hd hs hd0 hs0
    (dihedralHalfProjection d) hp _ hpC
    (halfProjection_absorbs_reflection d hdd).1 ht
  intro x hx hx0
  exact G.positive_corner_density_of_group_word_density d (d * s) hdd
    (free_symmetry_rotation_conjugation d s hdi hsi) hp ht
    (free_symmetry_haar_moments G.trace hτ D A hf d s hd hs hd0 hs0 hdi hsi)
    (G.free_symmetry_first_coset_moments D A hf d s hd hs hd0 hs0 hdi hsi)
    x hx0 (hspan x hx)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary dihedral word span is a unital star subalgebra. This
reduces its L²-density to density of the algebra generated by the two
symmetries, without assuming a normal-form density statement. -/

noncomputable section
namespace KadisonSimilarity
namespace DihedralWordAlgebra

variable {P : Type*} [CStarAlgebra P]

/-- The normal-form span contains the reflection. -/
theorem reflection_mem (d w : Pˣ) (hd : d * d = 1) (hc : d * w = w⁻¹ * d)
    (hdstar : star d = d) (hwstar : star w = w⁻¹) :
    (d : P) ∈ spanStarAlgebra d w hd hc hdstar hwstar :=
  Submodule.subset_span (Or.inr ⟨0, by simp⟩)

/-- The normal-form span contains the rotation. -/
theorem rotation_mem (d w : Pˣ) (hd : d * d = 1) (hc : d * w = w⁻¹ * d)
    (hdstar : star d = d) (hwstar : star w = w⁻¹) :
    (w : P) ∈ spanStarAlgebra d w hd hc hdstar hwstar :=
  Submodule.subset_span (Or.inl ⟨1, by simp⟩)

/-- The other symmetry is the reflection times the rotation. -/
theorem second_symmetry_mem (d s : Pˣ) (hd : d * d = 1)
    (hc : d * (d * s) = (d * s)⁻¹ * d)
    (hdstar : star d = d) (hwstar : star (d * s) = (d * s)⁻¹) :
    (s : P) ∈ spanStarAlgebra d (d * s) hd hc hdstar hwstar := by
  have h := (spanStarAlgebra d (d * s) hd hc hdstar hwstar).mul_mem
    (reflection_mem d (d * s) hd hc hdstar hwstar)
    (rotation_mem d (d * s) hd hc hdstar hwstar)
  have heq : d * (d * s) = s := by rw [← mul_assoc, hd, one_mul]
  have hval := congrArg (fun u : Pˣ => (u : P)) heq
  simp only [Units.val_mul] at hval
  change (s : P) ∈ (spanStarAlgebra d (d * s) hd hc hdstar hwstar).toSubalgebra
  simpa only [Units.val_mul, hval] using h

/-- Thus every finite algebraic star word in the two symmetries belongs to
the linear span of dihedral normal forms. -/
theorem generated_le_span (d s : Pˣ) (hd : d * d = 1)
    (hc : d * (d * s) = (d * s)⁻¹ * d)
    (hdstar : star d = d) (hwstar : star (d * s) = (d * s)⁻¹) :
    StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) ≤
      spanStarAlgebra d (d * s) hd hc hdstar hwstar := by
  apply StarAlgebra.adjoin_le
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact reflection_mem d (d * s) hd hc hdstar hwstar
  · exact second_symmetry_mem d s hd hc hdstar hwstar

/-- A linear map takes the ordinary word span into the span of its word vectors. -/
theorem map_mem_word_span {H : Type*} [AddCommGroup H] [Module ℂ H]
    (V : P →ₗ[ℂ] H) (d w : Pˣ) {a : P}
    (ha : a ∈ Submodule.span ℂ (wordSet d w)) :
    V a ∈ Submodule.span ℂ (V '' wordSet d w) := by
  let M := Submodule.span ℂ (V '' wordSet d w)
  induction ha using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => simpa only [map_zero] using M.zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using M.add_mem ha hb
  | smul c a _ ha => simpa only [map_smul] using M.smul_mem c ha

end DihedralWordAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The algebraic and Hilbert-space versions of the normal-form set agree. -/
theorem image_dihedralWordSet (d w : Pˣ) :
    G.vector '' DihedralWordAlgebra.wordSet d w = G.dihedralGroupWordVectors d w := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inl ⟨l, rfl⟩
    · exact Or.inr ⟨l, rfl⟩
  · rintro (⟨l, rfl⟩ | ⟨l, rfl⟩)
    · exact ⟨_, Or.inl ⟨l, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr ⟨l, rfl⟩, rfl⟩

/-- Density of the ordinary generated star algebra supplies exactly the
dihedral group-word span used by the centered corner argument. -/
theorem group_word_density_of_generated_density
    (d s : Pˣ) (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hdstar : star d = d) (hsstar : star s = s) (x : P)
    (hspan : G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure) :
    G.vector x ∈ (Submodule.span ℂ (G.dihedralGroupWordVectors d (d * s))).topologicalClosure := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  have hinc : Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P)) ≤
        Submodule.span ℂ (G.dihedralGroupWordVectors d (d * s)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨a, ha, rfl⟩
    rw [← G.image_dihedralWordSet]
    exact DihedralWordAlgebra.map_mem_word_span G.vector d (d * s)
      (DihedralWordAlgebra.generated_le_span d s hdd
        (free_symmetry_rotation_conjugation d s hdi hsi) hdstar
        (free_symmetry_product_star d s hdstar hsstar hdi hsi) ha)
  exact Submodule.topologicalClosure_mono hinc hspan

/-- Corner freeness reduces to ordinary L²-density of the algebra
generated by the two centered symmetries. -/
theorem scalarFree_corner_of_generated_word_density
    (D A C : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) (hdstar : star d = d) (hsstar : star s = s)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (hspan : ∀ x : CStarCorner (dihedralHalfProjection d) hp, (x : P) ∈ C →
      G.vector (x : P) ∈ (Submodule.span ℂ
        (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure) :
    ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D
        (D.smul_mem (D.add_mem D.one_mem hd) (1 / 2 : ℂ)))
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC) := by
  apply G.scalarFree_corner_of_dihedral_word_density D A C hf hτ d s hd hs hd0 hs0 hdi hsi hp hpC
  intro x hx
  exact G.group_word_density_of_generated_density d s hdi hsi hdstar hsstar (x : P) (hspan x hx)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ExpectationWordClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending the two-dimensional expectation range from word vectors to
their tracial Hilbert closure. Orthogonal projection supplies continuity. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The expectation of a Hilbert limit of word vectors still lies in the
span of the unit and the specified base element. -/
theorem expectation_span_of_word_closure (E : TracialExpectation G.trace A)
    (hfaithful : Function.Injective G.vector) (s : P) (words : Set P)
    (hword : ∀ x ∈ words, ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (x : P) (hx : G.vector x ∈
      (Submodule.span ℂ (G.vector '' words)).topologicalClosure) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  let F : H →L[ℂ] H := (G.baseInclusion A).toContinuousLinearMap.comp
    (G.baseInclusion A).toContinuousLinearMap.adjoint
  have hF (y : P) : F (G.vector y) = G.vector (E.map y) := by
    change (G.baseInclusion A)
      ((G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector y)) = _
    rw [G.expectation_base_projection A E]
    rfl
  let B : Submodule ℂ H := Submodule.span ℂ {G.vector 1, G.vector s}
  have : FiniteDimensional ℂ B := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hclosed : IsClosed (B : Set H) := B.closed_of_finiteDimensional
  have hspan : Submodule.span ℂ (G.vector '' words) ≤ B.comap F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    change F (G.vector y) ∈ B
    rw [hF]
    obtain ⟨α, β, h⟩ := hword y hy
    rw [h, map_add, map_smul, map_smul]
    exact B.add_mem (B.smul_mem α (Submodule.subset_span (by simp)))
      (B.smul_mem β (Submodule.subset_span (by simp)))
  have hmem := (Submodule.span ℂ (G.vector '' words)).topologicalClosure_minimal
    hspan (hclosed.preimage F.continuous) hx
  change F (G.vector x) ∈ B at hmem
  rw [hF] at hmem
  obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨α, β, ?_⟩
  apply hfaithful
  simpa only [map_add, map_smul] using h.symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space implementation of trace-preserving automorphisms. The
implementation and its covariance are constructed from dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (θ : P ≃⋆ₐ[ℂ] P)
  (hθ : ∀ a, G.trace (θ a) = G.trace a)

/-- Multiplication covariance extends from the algebra to the whole Hilbert space. -/
theorem automorphismUnitary_left (a : P) (x : H) :
    G.automorphismUnitary θ hθ (G.left a x) =
      G.left (θ a) (G.automorphismUnitary θ hθ x) := by
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [G.left_vector, automorphismUnitary_vector, map_mul]

theorem automorphismUnitary_fixes_base (A : StarSubalgebra ℂ P)
    (hA : ∀ a : A, θ (a : P) = (a : P)) (x : G.baseSpace A) :
    G.automorphismUnitary θ hθ (x : H) = (x : H) := by
  refine (G.baseVector_dense A).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change G.automorphismUnitary θ hθ (G.vector (a : P)) = G.vector (a : P)
  rw [G.automorphismUnitary_vector, hA]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D)
  (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- The constructed matrix action fixes the whole completed base space,
by the algebraic fixation of its dense bounded vectors. -/
theorem matrixExtensionUnitaryRepresentation_base
    (u : Matrix.unitaryGroup α ℂ) (x : G.baseSpace A) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (x : H) = (x : H) := by
  exact G.automorphismUnitary_fixes_base
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a)
    A (fun a => G.matrixExtensionAutomorphism_base A D ι hgen hfaithful hext u a) x

/-- The represented ambient left action transforms under the actual
matrix-conjugation automorphism on all Hilbert vectors. -/
theorem matrixExtensionUnitaryRepresentation_left
    (u : Matrix.unitaryGroup α ℂ) (a : P) (x : H) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (G.left a x) =
    G.left (G.chosenMatrixExtension A D ι hext u a)
      ((G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H) x) := by
  exact G.automorphismUnitary_left
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a) a x

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of the constructed finite matrix action follows from
ordinary factor-algebra density and the isometry bound; it is not an extra
free-product or Haar-averaging hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

section ContinuousOrbits
variable {Γ H : Type*} [TopologicalSpace Γ]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (U : Γ → H →L[ℂ] H)

/-- A common contraction bound makes the continuous-orbit subspace closed. -/
theorem continuousOrbitSubmodule_isClosed (hU : ∀ g, ‖U g‖ ≤ 1) :
    IsClosed (continuousOrbitSubmodule U : Set H) := by
  apply isSeqClosed_iff_isClosed.mp
  intro x y hx hy
  have hu : TendstoUniformly (fun n g => U g (x n)) (fun g => U g y) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hy ε hε] with n hn
    intro g
    have hbound : dist (U g y) (U g (x n)) ≤ dist (x n) y := by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm, norm_sub_rev]
      calc
        ‖U g (y - x n)‖ ≤ ‖U g‖ * ‖y - x n‖ := (U g).le_opNorm _
        _ ≤ 1 * ‖y - x n‖ := mul_le_mul_of_nonneg_right (hU g) (norm_nonneg _)
        _ = ‖y - x n‖ := one_mul _
    exact hbound.trans_lt hn
  exact hu.continuous (Filter.Eventually.of_forall hx).frequently

end ContinuousOrbits

namespace TracialCornerGeometry
variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The tracial vector map is continuous because it is left multiplication
on its fixed vacuum vector. -/
theorem continuous_vector : Continuous G.vector := by
  have he : (G.vector : P → H) = fun a => G.left a (G.vector 1) := by
    funext a
    simpa only [mul_one] using (G.left_vector a 1).symm
  rw [he]
  exact (map_continuous G.left).clm_apply continuous_const

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- Conjugation of a fixed factor element depends continuously on the matrix
unitary, directly from finite-dimensional continuity and multiplication. -/
theorem continuous_matrixConjugateLetter (d : D) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => (matrixConjugateLetter D ι u d : P)) := by
  have hι : Continuous (D.subtype.comp ι : Matrix α α ℂ →⋆ₐ[ℂ] P) :=
    (D.subtype.comp ι).toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hc : Continuous (fun u : Matrix.unitaryGroup α ℂ => (ι (u : Matrix α α ℂ) : P)) :=
    hι.comp continuous_subtype_val
  simpa only [matrixConjugateLetter, MulMemClass.coe_mul, StarMemClass.coe_star] using
    (hc.fun_mul continuous_const).fun_mul hc.star

/-- Every element of the algebra generated by the two factors has a
continuous orbit in the original operator norm. -/
theorem continuous_chosenMatrixExtension (a : factorAlgebra A D) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => G.chosenMatrixExtension A D ι hext u (a : P)) := by
  let S : StarSubalgebra ℂ P :=
    { carrier := {a | Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u a)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => (0 : P)))
      one_mem' := by simpa only [Set.mem_ofPred_eq, map_one] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => (1 : P)))
      add_mem' := by intro a b ha hb; simpa only [Set.mem_ofPred_eq, map_add] using ha.fun_add hb
      mul_mem' := by intro a b ha hb; simpa only [Set.mem_ofPred_eq, map_mul] using ha.fun_mul hb
      algebraMap_mem' := by
        intro c
        have he : (fun u : Matrix.unitaryGroup α ℂ =>
            G.chosenMatrixExtension A D ι hext u (algebraMap ℂ P c)) =
            fun _ => algebraMap ℂ P c :=
          funext (fun u => (G.chosenMatrixExtension A D ι hext u).commutes c)
        change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
          G.chosenMatrixExtension A D ι hext u (algebraMap ℂ P c))
        rw [he]
        exact continuous_const
      star_mem' := by intro a ha; simpa only [Set.mem_ofPred_eq, map_star] using ha.star }
  have hs : factorAlgebra A D ≤ S := by
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u x)
      simpa only [G.chosenMatrixExtension_base A D ι hext _ (⟨x, hx⟩ : A)] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => x))
    · change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u x)
      simpa only [G.chosenMatrixExtension_other A D ι hext _ (⟨x, hx⟩ : D)] using
        continuous_matrixConjugateLetter D ι (⟨x, hx⟩ : D)
  exact hs a.property

/-- The actual free-product matrix representation is strongly continuous;
only the ordinary tracial generation and published factor extension are used. -/
theorem matrixExtensionUnitaryRepresentation_stronglyContinuous (x : H) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ =>
      (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H) x) := by
  let U : Matrix.unitaryGroup α ℂ → H →L[ℂ] H := fun u =>
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
  have hclosed : IsClosed (continuousOrbitSubmodule U : Set H) :=
    continuousOrbitSubmodule_isClosed U (fun u =>
      (Unitary.linearIsometryEquiv
        (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u)).toLinearIsometry.norm_toContinuousLinearMap_le)
  refine hgen.induction_on x hclosed ?_
  intro a
  change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (G.vector (a : P)))
  simpa only [G.matrixExtensionUnitaryRepresentation_vector, Function.comp_def] using
    G.continuous_vector.comp (G.continuous_chosenMatrixExtension A D ι hext a)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation kills every reduced word starting in the other
free factor. This is derived from scalar freeness by trace tests. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {τ : P →ₗ[ℂ] ℂ}
  {A D : StarSubalgebra ℂ P}

namespace TracialExpectation

/-- A reduced word beginning in the other factor has zero base expectation,
including when its final letter belongs to the base algebra. -/
theorem map_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (x : P) (xs : List P) (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map ((x :: xs).prod) = 0 := by
  apply E.eq_of_pairings hfaithful _ 0 A.zero_mem
  intro c hc
  have hzero := hfree true x xs hword
  have htest : τ (traceCentered τ c * (x :: xs).prod) = 0 := by
    have h := hfree false (traceCentered τ c) (x :: xs)
      (.cons (by simpa using traceCentered_mem τ A hc)
        (traceCentered_trace τ hτ c) hword)
    exact h
  rw [mul_zero, map_zero]
  calc
    τ (c * (x :: xs).prod) =
        τ ((traceCentered τ c + τ c • 1) * (x :: xs).prod) := by
      rw [traceCentered_add]
    _ = 0 := by
      rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul, htest, hzero]
      simp

/-- A base letter at the front of such a word is removed by bimodularity. -/
theorem map_base_mul_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (a : P) (ha : a ∈ A) (x : P) (xs : List P)
    (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map (a * (x :: xs).prod) = 0 := by
  rw [E.map_mul_left hfaithful a _ ha, E.map_reduced_word hfaithful hτ hfree x xs hword,
    mul_zero]

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace DihedralSpectralArc

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P} {w d : Pˣ} {θ : ℝ}
  (F : DihedralSpectralArc τ C w d θ)

theorem trace_zero (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ F.element = 0 := by
  have h := F.rotation_moment 0
  simpa only [zpow_zero, Units.val_one, mul_one, arcFourierIntegral_zero hθ hπ] using h

theorem rotation_commutes (l : ℤ) :
    (↑(w ^ l) : P) * F.element = F.element * (↑(w ^ l) : P) :=
  (F.commute_rotation.units_zpow_right l).eq.symm

/-- The reflection used in the Hankel term is `w⁻¹d`, rather than `d`.
Traciality shifts the Fourier index and supplies its zero mixed moment. -/
theorem shifted_reflection_moment (htr : ∀ x y, τ (x * y) = τ (y * x)) (l : ℤ) :
    τ ((↑(w⁻¹ * d) : P) * (F.element * (↑(w ^ l) : P))) = 0 := by
  have hpow : w ^ l * w⁻¹ = w ^ (l - 1) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
  rw [htr]
  have hid : (F.element * (↑(w ^ l) : P)) * (↑(w⁻¹ * d) : P) =
      (F.element * (↑(w ^ (l - 1)) : P)) * (d : P) := by
    have hval : (↑(w ^ l) : P) * (↑w⁻¹ : P) = (↑(w ^ (l - 1)) : P) := by
      rw [← Units.val_mul, hpow]
    calc
      _ = F.element * ((↑(w ^ l) : P) * (↑w⁻¹ : P)) * (d : P) := by
        simp only [Units.val_mul, mul_assoc]
      _ = _ := by rw [hval]
  rw [hid, F.reflection_moment]

theorem corner_mem (hp : IsStarProjection (dihedralHalfProjection d))
    (hdC : (d : P) ∈ C) : (F.corner hp : P) ∈ C :=
  C.mul_mem F.mem (C.smul_mem (C.add_mem C.one_mem hdC) _)

theorem corner_trace_zero (hp : IsStarProjection (dihedralHalfProjection d))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ (F.corner hp : P) = 0 := by
  have hd0 : τ (F.element * (d : P)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using F.reflection_moment 0
  simp only [corner_coe, dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.trace_zero hθ hπ, hd0, add_zero, smul_zero]

/-- The trace-pairing expectation of the actual compressed arc is derived
from normalized corner freeness. The factor `2t` is not an extra hypothesis. -/
theorem compressed_expectation
    (E : TracialExpectation τ C)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (D : StarSubalgebra ℂ P) (hpD : dihedralHalfProjection d ∈ D)
    (htp : τ (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
    (e : CStarCorner (dihedralHalfProjection d) hp) (heD : (e : P) ∈ D)
    (hdC : (d : P) ∈ C) {t : ℝ} (hte : τ (e : P) = (t : ℂ))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    E.map ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (2 * (t : ℂ)) ^ 2 • (F.element * dihedralHalfProjection d) := by
  have htne : τ (dihedralHalfProjection d) ≠ 0 := by rw [htp]; norm_num
  have h := E.free_corner_compression hfaithful htr (dihedralHalfProjection d) hp hpC
    htne D hpD hfree e (F.corner hp) heD (F.corner_mem hp hdC)
    (F.corner_trace_zero hp hθ hπ)
  simpa only [F.corner_coe, htp, hte, one_div, inv_inv] using h

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying a tracial expectation whose range lies in the two-dimensional
algebra generated by a centered symmetry. The Fourier identities then require
only scalar trace moments, not operator-valued moment assumptions. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {τ : P →ₗ[ℂ] ℂ}
  {A : StarSubalgebra ℂ P}

namespace TracialExpectation

/-- Trace preservation and the trace pairing with s determine both
coefficients of the conditional expectation. -/
theorem map_eq_symmetryExpectation (E : TracialExpectation τ A)
    (hτ : τ 1 = 1) (s : P) (hsA : s ∈ A) (hs0 : τ s = 0) (hs2 : s * s = 1)
    (x : P) (hspan : ∃ α β : ℂ, E.map x = α • (1 : P) + β • s) :
    E.map x = symmetryExpectation τ s x := by
  obtain ⟨α, β, he⟩ := hspan
  have hα : τ x = α := by
    rw [← E.trace_map x, he, map_add, map_smul, map_smul, hτ, hs0]
    simp
  have hβ : τ (s * x) = β := by
    rw [← E.pairing x s hsA, he, mul_add, mul_smul_comm, mul_smul_comm,
      mul_one, hs2, map_add, map_smul, map_smul, hs0, hτ]
    simp
  rw [he, symmetryExpectation_apply, hα, hβ]

/-- The rotation and reflection expectation identities follow from scalar
Fourier moments once the free-word calculation puts these expectations in
span{1,s}. -/
theorem rotation_reflection_of_scalar_moments (E : TracialExpectation τ A)
    (hτ : τ 1 = 1) (htr : ∀ x y, τ (x * y) = τ (y * x))
    (s : P) (hsA : s ∈ A) (hs0 : τ s = 0) (hs2 : s * s = 1)
    (x : P) (γ : ℂ) (hcoef : τ x = γ) (hcoset : τ (s * x) = 0)
    (hspan : ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (hspan' : ∃ α β : ℂ, E.map (x * s) = α • (1 : P) + β • s) :
    E.map x = γ • (1 : P) ∧ E.map (x * s) = γ • s := by
  rw [E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 x hspan,
    E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 (x * s) hspan']
  simpa only [hcoef] using symmetryExpectation_mul_symmetry τ htr s x hs2 hcoset

/-- On the word algebra, a two-dimensional base expectation factors through
any intermediate algebra containing the symmetry. No global tower inclusion
of the entire base algebra is required. -/
theorem restricted_tower_of_symmetry_span (E : TracialExpectation τ A)
    {C S : StarSubalgebra ℂ P} (EC : TracialExpectation τ C) (hCS : C ≤ S)
    (hτ : τ 1 = 1) (s : P) (hsA : s ∈ A) (hsC : s ∈ C)
    (hs0 : τ s = 0) (hs2 : s * s = 1)
    (hspan : ∀ x, x ∈ S → ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (x : P) (hx : x ∈ S) : E.map (EC.map x) = E.map x := by
  rw [E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 _ (hspan _ (hCS (EC.range x))),
    E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 x (hspan x hx)]
  simp only [symmetryExpectation_apply, EC.trace_map, EC.pairing x s hsC]

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation on the algebra generated by the other free factor
and one centered symmetry. The only density datum is the ordinary reduced
word span; the two-dimensional expectation range is proved. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CenteredSymmetryWord

variable {τ : P →ₗ[ℂ] ℂ} {D A : StarSubalgebra ℂ P} {s : P}

theorem alternating (hs : s ∈ A) (hs0 : τ s = 0)
    {side : Bool} {xs : List P} (h : CenteredSymmetryWord τ D s side xs) :
    AlternatingCenteredWord τ D A side xs := by
  induction h with
  | nil side => exact .nil side
  | other hd hz _ ih => exact .cons (by simpa using hd) hz ih
  | symmetry _ ih => exact .cons (by simpa using hs) hs0 ih

/-- The expectation of a reduced word is either zero, the unit, or the
specified symmetry. This follows from freeness and bimodularity. -/
theorem expectation_span
    (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (hs : s ∈ A) (hs0 : τ s = 0)
    {side : Bool} {xs : List P} (h : CenteredSymmetryWord τ D s side xs) :
    ∃ α β : ℂ, E.map xs.prod = α • (1 : P) + β • s := by
  cases h with
  | nil side =>
    refine ⟨1, 0, ?_⟩
    simp only [List.prod_nil, E.map_one hfaithful, one_smul, zero_smul, add_zero]
  | @other d xs hd hz tail =>
    refine ⟨0, 0, ?_⟩
    have hw : AlternatingCenteredWord τ D A true (d :: xs) :=
      .cons (by simpa using hd) hz (tail.alternating hs hs0)
    rw [E.map_reduced_word hfaithful hτ hfree d xs hw]
    simp
  | @symmetry xs tail =>
    cases tail with
    | nil =>
      refine ⟨0, 1, ?_⟩
      simp only [List.prod_cons, List.prod_nil, mul_one,
        E.map_of_mem hfaithful hs, zero_smul, one_smul, zero_add]
    | @other d ys hd hz tail =>
      refine ⟨0, 0, ?_⟩
      have hw : AlternatingCenteredWord τ D A true (d :: ys) :=
        .cons (by simpa using hd) hz (tail.alternating hs hs0)
      change E.map (s * (d :: ys).prod) = _
      rw [E.map_base_mul_reduced_word hfaithful hτ hfree s hs d ys hw]
      simp

end CenteredSymmetryWord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D S : StarSubalgebra ℂ P)

/-- Passage from the actual reduced words to their L² closure supplies the
word-algebra range hypothesis of the Fourier compression. -/
theorem expectation_span_of_symmetry_word_density
    (E : TracialExpectation G.trace A) (hfaithful : Function.Injective G.vector)
    (hτ : G.trace 1 = 1) (hfree : ScalarFree G.trace D A)
    (s : P) (hs : s ∈ A) (hs0 : G.trace s = 0)
    (hdense : ∀ x, x ∈ S → G.vector x ∈
      (Submodule.span ℂ (G.vector '' centeredSymmetryWordProducts G.trace D s)).topologicalClosure)
    (x : P) (hx : x ∈ S) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  apply G.expectation_span_of_word_closure A E hfaithful s
    (centeredSymmetryWordProducts G.trace D s) _ x (hdense x hx)
  rintro y ⟨side, xs, hw, rfl⟩
  exact hw.expectation_span E (G.trace_faithful hfaithful) hτ hfree hs hs0

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic normal forms for the algebra generated by a star subalgebra
and a symmetry. Centering the other-factor letters and cancelling adjacent
symmetries proves the reduced-word density used by the base expectation. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace SymmetryWordAlgebra

variable (τ : P →ₗ[ℂ] ℂ) (D : StarSubalgebra ℂ P) (s : P)

variable (hτ : τ 1 = 1)

variable (hsq : s * s = 1)

variable (hstar : star s = s)

theorem generated_le_span :
    StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) ≤ spanStarAlgebra τ D s hτ hsq hstar := by
  apply StarAlgebra.adjoin_le
  rintro x (hx | hx)
  · exact other_mem τ D s hτ x hx
  · exact Set.mem_singleton_iff.mp hx ▸ symmetry_mem τ D s

end SymmetryWordAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem symmetry_word_density_of_generated_density
    (D : StarSubalgebra ℂ P) (s : P) (hτ : G.trace 1 = 1)
    (hsq : s * s = 1) (hstar : star s = s) (x : P)
    (hx : G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))).topologicalClosure) :
    G.vector x ∈ (Submodule.span ℂ
      (G.vector '' centeredSymmetryWordProducts G.trace D s)).topologicalClosure := by
  apply Submodule.topologicalClosure_mono (s := Submodule.span ℂ
    (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))) _ hx
  apply Submodule.span_le.mpr
  rintro y ⟨a, ha, rfl⟩
  have hmem := SymmetryWordAlgebra.generated_le_span G.trace D s hτ hsq hstar ha
  change a ∈ Submodule.span ℂ (centeredSymmetryWordProducts G.trace D s) at hmem
  clear ha
  induction hmem using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

/-- The base expectation of the actual generated von Neumann algebra has
the range needed in the Fourier argument. Only ordinary generated-algebra
L² density remains, rather than an assumed range formula. -/
theorem expectation_span_of_generated_symmetry_algebra
    (A D S : StarSubalgebra ℂ P) (E : TracialExpectation G.trace A)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfree : ScalarFree G.trace D A) (s : P) (hs : s ∈ A)
    (hs0 : G.trace s = 0) (hsq : s * s = 1) (hstar : star s = s)
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))).topologicalClosure)
    (x : P) (hx : x ∈ S) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  apply G.expectation_span_of_symmetry_word_density A D S E hf hτ hfree s hs hs0 _ x hx
  intro y hy
  exact G.symmetry_word_density_of_generated_density D s hτ hsq hstar y (hdense y hy)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier matrix with the actual base compression and actual
trace-pairing expectations. Only scalar moments of the arc remain as data. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Scalar Fourier moments and the expectation range on the tested word
algebra determine the finite operator matrix on the actual tracial base. -/
theorem arc_compression_of_scalar_moments
    (E : TracialExpectation G.trace A) {C S : StarSubalgebra ℂ P}
    (EC : TracialExpectation G.trace C) (hCS : C ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hspan : ∀ x, x ∈ S → ∃ α β : ℂ,
      E.map x = α • (1 : P) + β • (↑(w⁻¹ * d) : P))
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (e f h : P) (hestar : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (hfC : f ∈ C) (hhS : h ∈ S)
    {N : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 < t) (c : ℂ)
    (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector (e * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P)))
    (hEC : EC.map h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : P) * f = f * (↑(w ^ j) : P))
    (hcoef : ∀ l : ℤ, G.trace (f * (↑(w ^ l) : P)) =
      arcFourierIntegral (arcWidth N) l)
    (hcoset : ∀ l : ℤ,
      G.trace ((↑(w⁻¹ * d) : P) * (f * (↑(w ^ l) : P))) = 0) :
    (sumColumns U).adjoint.comp ((G.left h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hfaithful := G.trace_faithful hf
  have hrotref (l : ℤ) := E.rotation_reflection_of_scalar_moments hτ G.tracial
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 (f * (↑(w ^ l) : P))
    (arcFourierIntegral (arcWidth N) l) (hcoef l) (hcoset l)
    (hspan _ (hCS (C.mul_mem hfC (hpower l))))
    (hspan _ (hCS (C.mul_mem (C.mul_mem hfC (hpower l)) hsC)))
  apply narrow_arc_tracial_compression hN A G.trace G.vector G.left.toLinearMap
    G.inner_vector G.left_vector (G.baseVector A) (G.baseVector_dense A)
    (G.baseCompression A) (G.baseCompression_inner A) (G.baseCompression_one A)
    E.map EC.map E.trace_map (fun a b x => E.bimodule hfaithful G.tracial
      (a : P) (b : P) x a.property b.property)
    w d hw hd e f h hestar heh hhe t ht c hc U hU hEC
  · intro j k
    exact EC.bimodule hfaithful G.tracial _ _ h (hpower j) (hpower (-k))
  · intro j k
    exact E.restricted_tower_of_symmetry_span EC hCS hτ _ hsA hsC hs0 hs2 hspan _
      (S.mul_mem (S.mul_mem (hCS (hpower j)) hhS) (hCS (hpower (-k))))
  · exact hcomm
  · exact fun l => (hrotref l).1
  · exact fun l => (hrotref l).2

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

section Algebra
variable {P : Type*} [Ring P] [StarRing P]

omit [StarRing P] in
/-- The reflected rotation appearing in the Hankel entry is the second
involution itself. -/
theorem dihedral_inverse_mul_reflection (d s : Pˣ) (hs : s⁻¹ = s) :
    ((d * s)⁻¹ * d : Pˣ) = s := by
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, hs]

end Algebra

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact groups in free-product symmetrization are the actual matrix
unitary groups. Their compatibility follows from the nested matrix embeddings
and uniqueness of the trace-preserving extension on the two factors. -/

noncomputable section
namespace KadisonSimilarity

section Conjugation

variable {H Γ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Group Γ]

omit [CompleteSpace H] in
/-- Conjugation transports a commutator through its actual covariance. -/
theorem commutator_unitaryConjugate_of_covariance
    (U : Γ →* (H →L[ℂ] H)) (T B C : H →L[ℂ] H) (g : Γ)
    (hcov : U g⁻¹ * B = C * U g⁻¹) :
    commutator (unitaryConjugate U T g) B =
      unitaryConjugate U (commutator T C) g := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hi' : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcov' : B * U g = U g * C := by
    calc
      B * U g = (U g * U g⁻¹) * B * U g := by rw [hi, one_mul]
      _ = U g * (U g⁻¹ * B) * U g := by simp only [mul_assoc]
      _ = U g * (C * U g⁻¹) * U g := by rw [hcov]
      _ = U g * C := by simp only [mul_assoc, hi', mul_one]
  change U g * T * U g⁻¹ * B - B * (U g * T * U g⁻¹) =
    U g * (T * C - C * T) * U g⁻¹
  rw [mul_sub, sub_mul]
  congr 1
  · calc
      U g * T * U g⁻¹ * B = U g * T * (U g⁻¹ * B) := mul_assoc _ _ _
      _ = U g * T * (C * U g⁻¹) := by rw [hcov]
      _ = U g * (T * C) * U g⁻¹ := by simp only [mul_assoc]
  · calc
      B * (U g * T * U g⁻¹) = (B * U g) * (T * U g⁻¹) := by simp only [mul_assoc]
      _ = (U g * C) * (T * U g⁻¹) := by rw [hcov']
      _ = U g * (C * T) * U g⁻¹ := by simp only [mul_assoc]

end Conjugation

namespace TracialCornerGeometry

open MeasureTheory TopologicalSpace
open scoped Topology CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)

omit [∀ j, Nonempty (I j)] in
theorem matrixStageUnitaryInclusion_embedding (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    M.embedding j (G.matrixStageUnitaryInclusion D M i j h u : Matrix (I j) (I j) ℂ) =
      M.embedding i (u : Matrix (I i) (I i) ℂ) :=
  M.compatible i j h u

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- The ambient extension does not depend on the matrix stage used to
represent the same unitary in the factor. -/
theorem chosenMatrixExtension_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.chosenMatrixExtension A D (M.embedding j) (hext j)
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.chosenMatrixExtension A D (M.embedding i) (hext i) u := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · intro a
    rw [G.chosenMatrixExtension_base, G.chosenMatrixExtension_base]
  · intro d
    rw [G.chosenMatrixExtension_other, G.chosenMatrixExtension_other]
    congr 1
    simp only [matrixConjugateLetter, G.matrixStageUnitaryInclusion_embedding]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- Compatibility of the actual Hilbert-space representations is proved
on dense algebra vectors. -/
theorem tracialMatrixUnitaryRepresentation_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext i u := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp only [tracialMatrixUnitaryRepresentation, G.matrixExtensionUnitaryRepresentation_vector]
  rw [G.chosenMatrixExtension_compatible A D M hgen hfaithful hext i j h u]

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_star (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).adjoint =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u⁻¹ := by
  change (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u :
    H →L[ℂ] H).adjoint =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ : H →L[ℂ] H)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star]
  have hs : star (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ := by
    rw [Unitary.star_eq_inv, map_inv]
  exact congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H)) hs

omit [∀ j, Nonempty (I j)] in
theorem norm_tracialMatrixUnitaryOperator_le (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    ‖G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖G.automorphismUnitary
    (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u)
    (fun a => G.matrixExtensionAutomorphism_trace A D (M.embedding j) hgen hfaithful
      (hext j) u a) x‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, one_mul]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext i u := by
  exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H))
    (G.tracialMatrixUnitaryRepresentation_compatible A D M hgen hfaithful hext i j h u)

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_fixes_base (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).comp
        (G.baseInclusion A).toContinuousLinearMap = (G.baseInclusion A).toContinuousLinearMap := by
  ext x
  exact G.matrixExtensionUnitaryRepresentation_base A D (M.embedding j) hgen hfaithful
    (hext j) u x

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_stronglyContinuous (j : ℕ) (x : H) :
    Continuous (fun u => G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u x) :=
  G.matrixExtensionUnitaryRepresentation_stronglyContinuous A D (M.embedding j)
    hgen hfaithful (hext j) x

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryCompactSpace
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryMeasurableSpace
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryBorelSpace
/-- The weak integrability needed for the actual Haar average is a
consequence of the proved strong continuity. -/
theorem weaklyIntegrable_tracialMatrixUnitaryConjugate (j : ℕ)
    (μ : Measure (Matrix.unitaryGroup (I j) ℂ)) [IsFiniteMeasure μ] (T : H →L[ℂ] H) :
    WeaklyIntegrable μ
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T) :=
  weaklyIntegrable_unitaryConjugate μ _
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext j)
    (G.tracialMatrixUnitaryOperator_stronglyContinuous A D M hgen hfaithful hext j) T

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutator (T : H →L[ℂ] H)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (x : P) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left x) =
    unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      (commutator T (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ x)))
      u := by
  apply commutator_unitaryConjugate_of_covariance
  ext v
  exact G.matrixExtensionUnitaryRepresentation_left A D (M.embedding j) hgen hfaithful
    (hext j) u⁻¹ x v

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutes_factor (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (d : D) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left (d : P)) = 0 := by
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  have hd : G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P) ∈ D := by
    rw [G.chosenMatrixExtension_other]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ d).property
  have hz : commutator T
      (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P))) = 0 :=
    sub_eq_zero.mpr (hTD ⟨_, hd⟩)
  rw [hz]
  simp only [unitaryConjugate, mul_zero, zero_mul]

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_cornerBound (T : H →L[ℂ] H) {t ε : ℝ}
    (hT : G.TraceCornerBound D T t ε) (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    G.TraceCornerBound D
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T u) t ε := by
  intro e he heD het x
  let Φ := G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹
  have he' : IsStarProjection (Φ e) := by
    constructor
    · change Φ e * Φ e = Φ e
      rw [← map_mul, he.isIdempotentElem.eq]
    · change star (Φ e) = Φ e
      rw [← map_star, he.isSelfAdjoint.star_eq]
  have heD' : Φ e ∈ D := by
    dsimp only [Φ]
    rw [G.chosenMatrixExtension_other A D (M.embedding j) (hext j) u⁻¹ ⟨e, heD⟩]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ ⟨e, heD⟩).property
  have het' : G.trace (Φ e) = (t : ℂ) :=
    (G.chosenMatrixExtension_trace A D (M.embedding j) (hext j) u⁻¹ e).trans het
  let x' : CStarCorner (Φ e) he' := ⟨Φ (x : P), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  have hn : ‖x'‖ = ‖x‖ :=
    StarAlgEquiv.norm_map
      (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u⁻¹) (x : P)
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  apply (norm_unitaryConjugate_le _
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext j) _ u).trans
  simpa only [hn] using hT (Φ e) he' heD' het' x'

include hgen hfaithful in
/-- Simultaneous compact averaging produces the exact additional symmetries
used by word classification. It preserves the original base compression and
the uniform corner bound. No invariant limiting operator is an input. -/
theorem exists_tracially_symmetrized (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    {t ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ∃ Y : H →L[ℂ] H,
      ‖Y‖ ≤ ‖T‖ ∧
      (∀ d : D, Y.comp (G.left (d : P)) = (G.left (d : P)).comp Y) ∧
      (∀ j w, Y.comp
          (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y) ∧
      G.TraceCornerBound D Y t ε ∧ G.baseOperator A Y = G.baseOperator A T := by
  let U := G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext
  let Test := D ⊕ G.traceCornerElements D t
  let test : Test → H →L[ℂ] H := Sum.elim (fun d => G.left (d : P)) (fun x => G.left (x : P))
  let bound : Test → ℝ := Sum.elim (fun _ => 0) (fun x => ε * ‖(x : P)‖)
  have hbound : ∀ x, 0 ≤ bound x := by
    intro x
    cases x with
    | inl d => exact le_refl 0
    | inr x => exact mul_nonneg hε (norm_nonneg _)
  have htest : ∀ j w x, ‖commutator (unitaryConjugate (U j) T w) (test x)‖ ≤ bound x := by
    intro j w x
    cases x with
    | inl d =>
      change ‖commutator (unitaryConjugate (U j) T w) (G.left (d : P))‖ ≤ 0
      rw [G.tracialMatrixUnitaryConjugate_commutes_factor A D M hgen hfaithful hext T hTD]
      simp only [norm_zero, le_refl]
    | inr x =>
      obtain ⟨e, he, heD, het, hxleft, hxright⟩ := x.property
      exact G.tracialMatrixUnitaryConjugate_cornerBound A D M hgen hfaithful hext T hcorner
        j w e he heD het ⟨x, hxleft, hxright⟩
  obtain ⟨Y, hYnorm, hYW, hYtest, hbase⟩ := exists_simultaneously_symmetrized
    (tracialMatrixHaarProbability (I := I)) U
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext)
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext)
    (fun i j h u => G.matrixStageUnitaryInclusion D M i j h u)
    (G.tracialMatrixUnitaryOperator_compatible A D M hgen hfaithful hext) T
    (fun j => G.weaklyIntegrable_tracialMatrixUnitaryConjugate A D M hgen hfaithful hext j _ T)
    (G.baseInclusion A).toContinuousLinearMap
    (G.tracialMatrixUnitaryOperator_fixes_base A D M hgen hfaithful hext)
    test bound hbound htest
  refine ⟨Y, hYnorm, ?_, ?_, ?_, ?_⟩
  · intro d
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (hYtest (.inl d)) (norm_nonneg _)
  · intro j w
    exact sub_eq_zero.mp (hYW j w)
  · intro e he heD het x
    exact hYtest (.inr ⟨(x : P), e, he, heD, het, x.property.1, x.property.2⟩)
  · exact hbase

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSpectralCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-arc compression matrix. The normalized corner
expectation and the shifted reflection moment are derived here, leaving no
operator-valued Fourier identity among the hypotheses. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem spectral_arc_compression
    (A C D S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfreeDA : ScalarFree G.trace D A)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hdC : (d : P) ∈ C)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hsstar : star (↑(w⁻¹ * d) : P) = (↑(w⁻¹ * d) : P))
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(↑(w⁻¹ * d) : P)}):
        Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpD : dihedralHalfProjection d ∈ D)
    (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (e : CStarCorner (dihedralHalfProjection d) hp)
    (he : IsStarProjection (e : P)) (heD : (e : P) ∈ D)
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C w d (arcWidth N))
    (t : ℝ) (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector ((e : P) * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P))) :
    (sumColumns U).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))).comp
        (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hpC : dihedralHalfProjection d ∈ C :=
    C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2)
  have hspan := G.expectation_span_of_generated_symmetry_algebra A D S E hf hτ hfreeDA
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 hsstar hdense
  have hwidth : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsmall : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have heh : (e : P) * ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    simp only [← mul_assoc, he.isIdempotentElem.eq]
  have hhe : ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) * (e : P) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    rw [mul_assoc, he.isIdempotentElem.eq]
  exact G.arc_compression_of_scalar_moments A E EC hCS hf hτ w d hw hd hsA hsC hs0 hs2
    hspan hpower (e : P) F.element
    ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))
    he.isSelfAdjoint.star_eq heh hhe F.mem
    (S.mul_mem (S.mul_mem (hDS heD) (hCS (C.mul_mem F.mem hpC))) (hDS heD))
    hN t ht c hc U hU
    (F.compressed_expectation EC (G.trace_faithful hf) G.tracial hp hpC D hpD htp
      hfree e heD hdC hte (arcWidth_pos hN).le hwidth)
    F.rotation_commutes F.rotation_moment (F.shifted_reflection_moment G.tracial)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSpectralColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized dihedral columns have the rotation-power formula
needed by the spectral Fourier computation. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- The repeated product column is exactly the normalized negative rotation
power column; the identity is proved on its actual bounded algebra vectors. -/
theorem tracialDihedralColumns_rotation_formula (N : ℕ) (i : Fin N) (a : A) :
    G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N i (G.baseVector A a) =
      dihedralNormalization t • G.vector
        ((e : P) * (↑((dU * sU) ^ (-(i.val : ℤ))) : P) * (a : P)) := by
  change G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
    he ht hte i.val (G.baseVector A a) = _
  rw [G.tracialDihedralInclusion_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, mul_inv_rev,
    symmetryUnit_inv, Units.val_pow_eq_pow_val, Units.val_mul, symmetryUnit_coe]

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- The Fourier compression theorem, on the actual normalized columns.
The bounded column formula and reflected base compression are derived here. -/
theorem spectral_arc_actual_columns
    (C S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S) (hfaithful : Function.Injective G.vector)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑((dU * sU) ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection dU))
    (hpD : dihedralHalfProjection dU ∈ D)
    (htp : G.trace (dihedralHalfProjection dU) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection dU) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection dU) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection dU) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (hep : dihedralHalfProjection dU * (e : P) = (e : P))
    (hpe : (e : P) * dihedralHalfProjection dU = (e : P))
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C (dU * sU) dU (arcWidth N)) :
    let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N
    (sumColumns V).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection dU) * (e : P))).comp
        (sumColumns V)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s) := by
  have hshift : (dU * sU)⁻¹ * dU = sU :=
    dihedral_inverse_mul_reflection dU sU (symmetryUnit_inv _ _)
  let eC : CStarCorner (dihedralHalfProjection dU) hp := ⟨e, hep, hpe⟩
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  have h := G.spectral_arc_compression A C D S E EC hCS hDS hfaithful hτ hf
    (dU * sU) dU
    (free_symmetry_product_star dU sU
      (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
      (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
      (symmetryUnit_inv _ _) (symmetryUnit_inv _ _))
    (dihedral_reflection_relation dU sU (symmetryUnit_inv _ _) (symmetryUnit_inv _ _))
    hdC (by simpa only [hshift, symmetryUnit_coe] using s.property)
    (by simpa only [hshift, symmetryUnit_coe] using hsC)
    (by simpa only [hshift, symmetryUnit_coe] using hs0)
    (by simpa only [hshift, symmetryUnit_coe, MulMemClass.coe_mul, OneMemClass.coe_one] using
      congrArg (fun x : A => (x : P)) hssq)
    (by simpa only [hshift, symmetryUnit_coe, StarMemClass.coe_star] using
      congrArg (fun x : A => (x : P)) hsstar)
    (by simpa only [hshift, symmetryUnit_coe] using hdense)
    hpower hp hpD htp hfree eC heP e.property hN F t ht hte
    (dihedralNormalization t) (dihedralNormalization_sq ht)
    (G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte N)
    (G.tracialDihedralColumns_rotation_formula A D hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N)
  simpa only [hshift, symmetryUnit_coe, G.baseCompression_subalgebra] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSpectralTest
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the actual operator tested by the free-corner argument.
Its norm and Fourier matrix are conclusions from the elementary published
creation model and the local spectral arc, rather than input estimates. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D C R : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)] [IsClosed (C : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

variable
  (hp : IsStarProjection (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))))
  (hpD : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ D)
  (hpC : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C)
  (htp : G.trace (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (1 / 2 : ℂ))

local notation "DA" => CStarCorner.subalgebra p hp D hpD
local notation "CA" => CStarCorner.subalgebra p hp C hpC

omit [IsClosed (A : Set P)] in
/-- A spectral arc supplies an actual small corner operator with the precise
finite Hankel compression required by propagation. -/
theorem exists_actual_spectral_test
    (K : StarSubalgebra ℂ (CStarCorner p hp))
    [IsClosed (K : Set (CStarCorner p hp))]
    (hK : (factorAlgebra DA CA).topologicalClosure = K)
    (compression : RicardXuCompressionInput ((G.halfCornerGeometry dU hp htp).baseGeometry K)
      ((DA).comap K.subtype) ((CA).comap K.subtype))
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCR : C ≤ R) (hDR : D ≤ R) (hfaithful : Function.Injective G.vector)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (hdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑((dU * sU) ^ j) : P) ∈ C)
    (hfree : ScalarFree (CStarCorner.normalizedTrace p hp G.trace) DA CA)
    (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C (dU * sU) dU (arcWidth N))
    (hwidth : 4 * arcWidth N ≤ 2 * t)
    (Y : H →L[ℂ] H) {ε : ℝ}
    (hcorner : ∀ x : CStarCorner (e : P)
      ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
        congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 3 * (2 * t) ∧
      ‖commutator Y T‖ ≤ ε * ‖T‖ ∧
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
          (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
            ContinuousLinearMap.id ℂ (G.baseSpace A) +
          (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s) := by
  let h := (e : P) * (F.element * p) * (e : P)
  let T := G.left h
  have hπ : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  let eC : CStarCorner p hp := ⟨e, hep, hpe⟩
  have heC : IsStarProjection eC :=
    ⟨Subtype.ext heP.isIdempotentElem.eq, Subtype.ext heP.isSelfAdjoint.star_eq⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · change ‖G.left h‖ ≤ _
    rw [G.norm_left hfaithful]
    exact G.norm_spectral_arc_compression C D (dU * sU) dU hp hpC hpD htp K hK compression
      hfaithful hfree hdC F (arcWidth_pos hN).le hπ eC heC e.property ht.le hte hwidth
  · have hc := hcorner (CStarCorner.compress (e : P) heP (F.element * p))
    change ‖commutator Y (G.left h)‖ ≤ ε * ‖h‖ at hc
    change ‖commutator Y (G.left h)‖ ≤ ε * ‖G.left h‖
    rwa [G.norm_left hfaithful]
  · exact G.spectral_arc_actual_columns A D hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte C R E EC hCR hDR hfaithful hdC hsC hdense hpower hp hpD htp
      hfree hep hpe hN F

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerTheorem
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.amplifiedScalarRepresentation_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_adjoint_apply _root_.OAI.KadisonSimilarity.firstCopiesInclusion_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.hilbertArrayFlatten_apply _root_.OAI.KadisonSimilarity.hilbertFourfoldFlatten_apply _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.hilbertTripleFlatten_apply _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.matrixLeftArray_apply _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tracial free-corner argument assembled from the actual word model,
matrix symmetrization, and spectral test. All propagation, Fourier-matrix,
operator-norm, and averaging conclusions are derived from the local inputs.
Only the underlying local model and the specified published inputs remain. -/

noncomputable section
namespace KadisonSimilarity

universe u v

/-- An arbitrarily small positive spectral arc is available by choosing
the finite compression size. -/
theorem exists_arcWidth_le {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, 0 < N ∧ 4 * arcWidth N ≤ 2 * t := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  have heq : 4 * arcWidth (n + 1) = 2 * (1 / (n + 1 : ℝ)) := by
    have hnne : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold arcWidth
    push_cast
    field_simp [hnne]
    ring
  rw [heq]
  linarith

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
  (hdense : ReducedWordGenerated G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

variable (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P) (show IsStarProjection (e : P) from ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq, congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩)))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]
  (hp : IsStarProjection (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))))
  (hpD : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ D)
  (hpC : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C)
  (htp : G.trace (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (1 / 2 : ℂ))

variable (K : StarSubalgebra ℂ (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))
  [IsClosed (K : Set (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))]
  (hK : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC)).topologicalClosure = K)
  (compression : RicardXuCompressionInput ((G.halfCornerGeometry (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) hp htp).baseGeometry K)
    ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD).comap K.subtype) ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC).comap K.subtype))
  (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
  (hCR : C ≤ R) (hDR : D ≤ R)
  (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
  (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
    (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
  (hpower : ∀ j : ℤ, (↑(((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) ^ j) : P) ∈ C)
  (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp G.trace) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC))
  (hep : (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) * (e : P) = (e : P)) (hpe : (e : P) * (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (e : P))
  (spectral : DihedralSpectralArcInput G.trace C ((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)))

include hgen hext S hsize hword hτ creation hf hdense ha htrace hhaar support comparison
  hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation
  hK compression E EC hCR hDR hfaithful hdC hsC hRdense hpower hfree hep hpe spectral in
/-- For an operator with the finite matrix symmetries, the actual spectral
test and the proved propagation give the uniform free-corner bound. -/
theorem free_corner_from_local_models (Y : H →L[ℂ] H)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (hYU : ∀ j w, Y.comp
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D Y t ε) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨N, hN, hwidth⟩ := exists_arcWidth_le ht
  have hπ : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  obtain ⟨F⟩ := spectral (arcWidth N) (arcWidth_pos hN).le hπ
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  have hcorner_e := hcorner (e : P) heP e.property hte
  obtain ⟨T, hT, hcomm, hFourier⟩ :=
    G.exists_actual_spectral_test A D C R hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte hp hpD hpC htp K hK compression E EC hCR hDR hfaithful hdC hsC
      hRdense hpower hfree hep hpe hN F hwidth Y hcorner_e
  exact G.free_corner_estimate_of_published_words A D M hgen hfaithful hext S hsize U hword hτ
    Y hYD hYU creation hf hdense z ha htrace hhaar τ support (e : P) heP e.property
    hqe comparison hN₀ frame hframe hsum hε hcorner_e published commutation d s e
    hdstar hdsq hd0 hsstar hssq hs0 he ht hte T hN
    (fun i j => realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)))
    (mul_pos (by norm_num) ht) hT hcomm hFourier

include hgen hext S hsize hword hτ creation hf hdense ha htrace hhaar support comparison
  hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation
  hK compression E EC hCR hDR hfaithful hdC hsC hRdense hpower hfree hep hpe spectral in
/-- The original operator satisfies the free-corner estimate. The extra
matrix symmetries are constructed by actual normalized Haar averaging, and
its exact base compression is restored at the end. -/
theorem free_corner_original_operator (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  obtain ⟨Y, _hYnorm, hYD, hYU, hYcorner, hbase⟩ :=
    G.exists_tracially_symmetrized A D M hgen hfaithful hext T hTD hε hcorner
  rw [G.baseOperator_commutator_subalgebra A T s, ← hbase]
  exact G.free_corner_from_local_models A D M hgen hfaithful hext S hsize U hword hτ
    creation hf hdense z ha htrace hhaar τ support comparison d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte hqe hN₀ frame hframe hsum published commutation C R hp hpD hpC
    htp K hK compression E EC hCR hDR hdC hsC hRdense hpower hfree hep hpe spectral
    Y hYD hYU hε hYcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerModel
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining word and reflection data in the free-corner argument are
constructed from the local published reduced-product model and ordinary
generated-algebra density. In particular neither an invariant word
decomposition nor freeness of the compressed factors is an input. -/

noncomputable section
namespace KadisonSimilarity

universe u v

variable {P : Type u} [CStarAlgebra P]

/-- All integer rotations lie in a star subalgebra containing both
involutions. The inverse is the product in reverse order. -/
theorem symmetryRotation_zpow_mem (C : StarSubalgebra ℂ P)
    {D A : StarSubalgebra ℂ P} (d : D) (s : A)
    (hdsq : d * d = 1) (hssq : s * s = 1)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C) (j : ℤ) :
    (↑((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq) *
      symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) ^ j) : P) ∈ C := by
  cases j with
  | ofNat n =>
    have h : ((d : P) * (s : P)) ^ n ∈ C := C.pow_mem (C.mul_mem hdC hsC) n
    simpa only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul,
      symmetryUnit_coe] using h
  | negSucc n =>
    have h : ((s : P) * (d : P)) ^ (n + 1) ∈ C := C.pow_mem (C.mul_mem hsC hdC) (n + 1)
    simpa only [zpow_negSucc, ← inv_pow, mul_inv_rev, symmetryUnit_inv,
      Units.val_pow_eq_pow_val, Units.val_mul, symmetryUnit_coe] using h

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (words : RicardXuWordDecompositionInput G A D)
  (creation : RicardXuCreationInput G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
  (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P)
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

include hgen hfaithful hext S hsize hτ hf words creation ha htrace hhaar support
  comparison hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation in
/-- The free-corner estimate from the local reduced-product model. Word
coordinates, reduced density, the half projection, rotation membership and
compressed freeness are all derived. -/
theorem free_corner_of_published_local_models_oai
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (K : StarSubalgebra ℂ (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))
    [IsClosed (K : Set (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))]
    (hK : (factorAlgebra
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property))
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC))).topologicalClosure = K)
    (compression : RicardXuCompressionInput
      ((G.halfCornerGeometry dU (symmetryHalfProjectionProof d hdstar hdsq)
        (trace_dihedralHalfProjection G.trace hτ dU hd0)).baseGeometry K)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property)).comap K.subtype)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC)).comap K.subtype))
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCR : C ≤ R) (hDR : D ≤ R)
    (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hCdense : ∀ x, x ∈ C → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure)
    (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
    (spectral : DihedralSpectralArcInput G.trace C (dU * sU) dU)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  have hdense := G.reducedWordGenerated_of_factorsTraciallyGenerate A D hτ hgen
  obtain ⟨U, hword⟩ := words hτ hfaithful hf hdense
  have hfree := G.scalarFree_corner_of_generated_word_density D A C hf hτ dU sU
    d.property s.property hd0 hs0 (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
    (symmetryHalfProjectionProof d hdstar hdsq)
    (symmetryHalfProjection_mem C d hdsq hdC) (fun x hx => hCdense (x : P) hx)
  exact G.free_corner_original_operator A D M hgen hfaithful hext S hsize U hword hτ
    creation hf hdense z ha htrace hhaar τ support comparison d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte hqe hN₀ frame hframe hsum published commutation C R
    (symmetryHalfProjectionProof d hdstar hdsq)
    (symmetryHalfProjection_mem D d hdsq d.property)
    (symmetryHalfProjection_mem C d hdsq hdC)
    (trace_dihedralHalfProjection G.trace hτ dU hd0) K hK compression E EC hCR hDR
    hdC hsC hRdense (symmetryRotation_zpow_mem C d s hdsq hssq hdC hsC)
    hfree hep hpe spectral T hTD hε hcorner

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models_oai.{u, v, u_1} := @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models_oai.{u, v, u_1}
