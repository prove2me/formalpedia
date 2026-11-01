-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:49:42.799965+00:00
-- url     : https://prove2.me/submissions/66aa3bbd-d894-4d3f-8749-1144ae4d3956

import Mathlib
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The normalized second moment is the Bernoulli variance of the arc. -/
theorem centeredArc_second_moment {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (2 * Real.pi)⁻¹ * (∫ x in -Real.pi..Real.pi, centeredArc θ x ^ 2) =
      (θ / Real.pi) * (1 - θ / Real.pi) := by
  have hid : (fun x => centeredArc θ x ^ 2) =
      fun x => (1 - 2 * (θ / Real.pi)) *
        (Ioc (-θ) θ).indicator (fun _ => (1 : ℝ)) x + (θ / Real.pi) ^ 2 := by
    funext x
    by_cases hx : x ∈ Ioc (-θ) θ
    · simp only [centeredArc, indicator_of_mem hx]
      ring
    · simp only [centeredArc, indicator_of_notMem hx]
      ring
  rw [hid, intervalIntegral.integral_add
    ((intervalIntegrable_indicator_of intervalIntegrable_const
      measurableSet_Ioc).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem centeredArc_second_moment_le {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (2 * Real.pi)⁻¹ * (∫ x in -Real.pi..Real.pi, centeredArc θ x ^ 2) ≤ 4 * θ := by
  rw [centeredArc_second_moment hθ hπ]
  have hratio : θ / Real.pi ≤ 4 * θ := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (θ / Real.pi)]

@[simp] theorem arcFourierIntegral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    arcFourierIntegral θ 0 = 0 := by
  simp only [arcFourierIntegral, Int.cast_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, centeredArc_integral_zero hθ hπ]
  simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The three-block free-compression norm estimate

The reduced-word construction in `lem:free-compression` supplies a projection
`p` with a zero fourth block, a small overlap with the corner `e`, and `L²`
bounds on the two off-diagonal blocks. These bounds imply the compressed
operator norm estimate.
-/

noncomputable section

namespace KadisonSimilarity

variable {R : Type*} [NormedRing R]

/-- The creation, annihilation, and diagonal blocks exhaust an operator when
its fourth block is zero. -/
theorem three_block_decomposition (p T : R) (hzero : (1 - p) * T * (1 - p) = 0) :
    T = p * T * (1 - p) + (1 - p) * T * p + p * T * p := by
  have hid : p * T * (1 - p) + (1 - p) * T * p + p * T * p =
      T - (1 - p) * T * (1 - p) := by noncomm_ring
  rw [hid, hzero, sub_zero]

/-- Abstract form of the free-compression bound. The parameter `b₂` is the
tracial `L²` norm in the intended application. -/
theorem norm_free_compression_le (e p T : R) (hp : p * p = p)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hb₂ : 0 ≤ b₂)
    (he : ‖e‖ ≤ 1) (hep : ‖e * p‖ ≤ Real.sqrt u) (hpe : ‖p * e‖ ≤ Real.sqrt u)
    (hzero : (1 - p) * T * (1 - p) = 0)
    (hcreate : ‖p * T * (1 - p)‖ ≤ b₂)
    (hannihilate : ‖(1 - p) * T * p‖ ≤ b₂) :
    ‖e * T * e‖ ≤ 2 * Real.sqrt u * b₂ + u * ‖T‖ := by
  have hleft : ‖e * (p * T * (1 - p)) * e‖ ≤ Real.sqrt u * b₂ := by
    have hid : e * (p * T * (1 - p)) * e =
        (e * p) * (p * T * (1 - p)) * e := by
      symm
      calc
        (e * p) * (p * T * (1 - p)) * e = e * (p * p) * T * (1 - p) * e := by
          noncomm_ring
        _ = e * (p * T * (1 - p)) * e := by rw [hp]; noncomm_ring
    rw [hid]
    calc
      _ ≤ (‖e * p‖ * ‖p * T * (1 - p)‖) * ‖e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (Real.sqrt u * b₂) * 1 := by gcongr
      _ = Real.sqrt u * b₂ := mul_one _
  have hright : ‖e * ((1 - p) * T * p) * e‖ ≤ Real.sqrt u * b₂ := by
    have hid : e * ((1 - p) * T * p) * e =
        e * ((1 - p) * T * p) * (p * e) := by
      symm
      calc
        e * ((1 - p) * T * p) * (p * e) = e * ((1 - p) * T * (p * p)) * e := by
          noncomm_ring
        _ = e * ((1 - p) * T * p) * e := by rw [hp]
    rw [hid]
    calc
      _ ≤ (‖e‖ * ‖(1 - p) * T * p‖) * ‖p * e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * b₂) * Real.sqrt u := by gcongr
      _ = Real.sqrt u * b₂ := by ring
  have hdiag : ‖e * (p * T * p) * e‖ ≤ u * ‖T‖ := by
    have hid : e * (p * T * p) * e = (e * p) * T * (p * e) := by
      simp only [mul_assoc]
    rw [hid]
    calc
      _ ≤ (‖e * p‖ * ‖T‖) * ‖p * e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (Real.sqrt u * ‖T‖) * Real.sqrt u := by gcongr
      _ = (Real.sqrt u) ^ 2 * ‖T‖ := by ring
      _ = u * ‖T‖ := by rw [Real.sq_sqrt hu]
  have hsplit : e * T * e = e * (p * T * (1 - p)) * e +
      e * ((1 - p) * T * p) * e + e * (p * T * p) * e := by
    conv_lhs => rw [three_block_decomposition p T hzero]
    simp only [mul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤ (‖e * (p * T * (1 - p)) * e‖ + ‖e * ((1 - p) * T * p) * e‖) +
        ‖e * (p * T * p) * e‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Real.sqrt u * b₂ + Real.sqrt u * b₂) + u * ‖T‖ :=
      add_le_add (add_le_add hleft hright) hdiag
    _ = 2 * Real.sqrt u * b₂ + u * ‖T‖ := by ring

/-- For the narrow arc used in the paper, the compression has norm at most
three times the corner trace. -/
theorem norm_narrow_arc_compression_le (e p T : R) (hp : p * p = p)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hb₂ : 0 ≤ b₂)
    (he : ‖e‖ ≤ 1) (hep : ‖e * p‖ ≤ Real.sqrt u) (hpe : ‖p * e‖ ≤ Real.sqrt u)
    (hzero : (1 - p) * T * (1 - p) = 0)
    (hcreate : ‖p * T * (1 - p)‖ ≤ b₂)
    (hannihilate : ‖(1 - p) * T * p‖ ≤ b₂)
    (h₂ : b₂ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) : ‖e * T * e‖ ≤ 3 * u := by
  have hs := Real.sqrt_nonneg u
  have hsq := Real.sq_sqrt hu
  have hb : b₂ ≤ Real.sqrt u := by nlinarith
  calc
    ‖e * T * e‖ ≤ 2 * Real.sqrt u * b₂ + u * ‖T‖ :=
      norm_free_compression_le e p T hp hu hb₂ he hep hpe hzero hcreate hannihilate
    _ ≤ 2 * Real.sqrt u * Real.sqrt u + u * 1 := by gcongr
    _ = 3 * u := by nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompressionGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The overlap of a small corner with words starting in the other free
factor. The estimate follows from the displayed tensor geometry. -/

noncomputable section
namespace KadisonSimilarity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_hilbertTensorInsert_le (Ω : E) :
    ‖hilbertTensorInsert (H := F) Ω‖ ≤ ‖Ω‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Ω)
  intro x
  rw [norm_hilbertTensorInsert]

/-- The unit vector insertion is an isometry, expressed by its adjoint. -/
theorem hilbertTensorInsert_adjoint_comp (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (hilbertTensorInsert (H := F) Ω).adjoint.comp (hilbertTensorInsert Ω) =
      ContinuousLinearMap.id ℂ F := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hilbertTensorInsert Ω).adjoint (hilbertTensorInsert Ω x)) =
    inner ℂ y x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_hilbertTensorInsert,
    inner_self_eq_norm_sq_to_K, hΩ]
  simp

theorem firstLetterProjection_idempotent (Ω : E) (hΩ : ‖Ω‖ = 1)
    (Q : F →L[ℂ] F) (hQ : Q * Q = Q) :
    firstLetterProjection Ω Q * firstLetterProjection Ω Q = firstLetterProjection Ω Q := by
  let J := hilbertTensorInsert (H := F) Ω
  have hJ : J.adjoint.comp J = ContinuousLinearMap.id ℂ F :=
    hilbertTensorInsert_adjoint_comp Ω hΩ
  change (J.comp (Q.comp J.adjoint)).comp (J.comp (Q.comp J.adjoint)) =
    J.comp (Q.comp J.adjoint)
  have heq : (J.comp (Q.comp J.adjoint)).comp (J.comp (Q.comp J.adjoint)) =
      J.comp ((Q.comp (J.adjoint.comp J)).comp (Q.comp J.adjoint)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq, hJ, ContinuousLinearMap.comp_id, ← ContinuousLinearMap.comp_assoc Q Q]
  change J.comp ((Q * Q).comp J.adjoint) = _
  rw [hQ]

theorem firstLetterProjection_adjoint (Ω : E) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) :
    (firstLetterProjection Ω Q).adjoint = firstLetterProjection Ω Q := by
  simp only [firstLetterProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hQ, ContinuousLinearMap.comp_assoc]

/-- Multiplication in the first factor only sees the small vector `eΩ` on
the range of the first-letter projection. -/
theorem norm_corner_firstLetterProjection_le
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F) (hQ : ‖Q‖ ≤ 1)
    (e : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x) :
    ‖e * firstLetterProjection Ω Q‖ ≤ ‖eΩ‖ := by
  let J := hilbertTensorInsert (H := F) Ω
  have hJ : ‖J‖ ≤ 1 := by simpa only [J, hΩ] using norm_hilbertTensorInsert_le (F := F) Ω
  have hEJ : ‖e.comp J‖ ≤ ‖eΩ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg eΩ)
    intro x
    change ‖e (hilbertTensorInsert Ω x)‖ ≤ _
    rw [hact, norm_hilbertTensorInsert]
  change ‖e.comp (J.comp (Q.comp J.adjoint))‖ ≤ _
  rw [← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖e.comp J‖ * ‖Q.comp J.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖eΩ‖ * (‖Q‖ * ‖J.adjoint‖) :=
      mul_le_mul hEJ (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖eΩ‖ * (1 * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
    _ = ‖eΩ‖ := by ring

/-- The tracial vector identity gives the square-root overlap in both orders. -/
theorem norm_corner_overlap_le
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e : HilbertTensor E F →L[ℂ] HilbertTensor E F) (he : e.adjoint = e)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {u : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u) :
    ‖e * firstLetterProjection Ω Q‖ ≤ Real.sqrt u ∧
      ‖firstLetterProjection Ω Q * e‖ ≤ Real.sqrt u := by
  have hn : ‖eΩ‖ ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u, norm_nonneg eΩ]
  have hleft := (norm_corner_firstLetterProjection_le Ω eΩ hΩ Q hQnorm e hact).trans hn
  refine ⟨hleft, ?_⟩
  have hadj : (e * firstLetterProjection Ω Q).adjoint = firstLetterProjection Ω Q * e := by
    change (e.comp (firstLetterProjection Ω Q)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, firstLetterProjection_adjoint Ω Q hQ, he]
    rfl
  rw [← hadj, ContinuousLinearMap.adjoint.norm_map]
  exact hleft

omit [CompleteSpace F] in
/-- For a selfadjoint free letter the annihilation block is adjoint to the
creation block, so only the latter needs to be estimated. -/
theorem norm_annihilation_eq_creation
    (P T : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (hP : P.adjoint = P) (hT : T.adjoint = T) :
    ‖(1 - P) * T * P‖ = ‖P * T * (1 - P)‖ := by
  have hs : (P * T * (1 - P)).adjoint = (1 - P) * T * P := by
    change ((P.comp T).comp (1 - P)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      map_sub, hP, hT]
    rw [ContinuousLinearMap.adjoint_one]
    rfl
  rw [← hs, ContinuousLinearMap.adjoint.norm_map]

/-- The narrow arc has an order-`u` compression solely from the tensor
geometry, the standard creation block, and its scalar moment bounds. -/
theorem norm_narrow_arc_from_tensor_geometry
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e T : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (he : e.adjoint = e) (hesq : e * e = e) (hT : T.adjoint = T)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u) (hb₂ : 0 ≤ b₂)
    (hzero : (1 - firstLetterProjection Ω Q) * T * (1 - firstLetterProjection Ω Q) = 0)
    (hcreate : ‖firstLetterProjection Ω Q * T * (1 - firstLetterProjection Ω Q)‖ ≤ b₂)
    (h₂ : b₂ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) :
    ‖e * T * e‖ ≤ 3 * u := by
  have hov := norm_corner_overlap_le Ω eΩ hΩ Q hQ hQnorm e he hact hu hsq
  have hann : ‖(1 - firstLetterProjection Ω Q) * T * firstLetterProjection Ω Q‖ ≤ b₂ := by
    rw [norm_annihilation_eq_creation _ T (firstLetterProjection_adjoint Ω Q hQ) hT]
    exact hcreate
  exact norm_narrow_arc_compression_le e (firstLetterProjection Ω Q) T
    (firstLetterProjection_idempotent Ω hΩ Q hQsq) hu hb₂
    (norm_projection_le_one e he hesq) hov.1 hov.2 hzero hcreate hann h₂ hnorm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed base algebra has its actual tracial Hilbert representation
inside the ambient one. Its left, right, and conjugation actions are compatible
with the canonical base inclusion. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

variable [IsClosed (A : Set P)]

/-- Faithfulness of the represented algebra vectors passes to the base. -/
theorem baseGeometry_vector_injective (hfaithful : Function.Injective G.vector) :
    Function.Injective (G.baseGeometry A).vector := by
  intro a b hab
  apply Subtype.ext
  apply hfaithful
  exact congrArg (fun x : G.baseSpace A => (x : H)) hab

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ReducedCreationBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The creation and zero-block consequences of the reduced-word action.
Only its action on elementary words is needed; the operator block bounds are
derived by the isometric word coordinates and density. -/

noncomputable section
namespace KadisonSimilarity

variable {E K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace K] [CompleteSpace H] in
theorem norm_reducedCreator_le (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) :
    ‖reducedCreator C b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖C (hilbertTensorInsert b x)‖ ≤ ‖b‖ * ‖x‖
  rw [LinearIsometry.norm_map, norm_hilbertTensorInsert]

/-- The reduced-word formula on words not beginning in the chosen free factor
implies both the vanishing diagonal block and the L² creation bound. -/
theorem reduced_word_creation_blocks
    (J : K →ₗᵢ[ℂ] H) (C : HilbertTensor E K →ₗᵢ[ℂ] H)
    (P T : H →L[ℂ] H) (b : E)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint = 1 - P)
    (hcreator : ∀ x, P (C (hilbertTensorInsert b x)) = C (hilbertTensorInsert b x))
    (hword : ∀ x, T (J x) = C (hilbertTensorInsert b x)) :
    (1 - P) * T * (1 - P) = 0 ∧ ‖P * T * (1 - P)‖ ≤ ‖b‖ := by
  let J₀ := J.toContinuousLinearMap
  have hQ (x : H) : (1 - P) x = J (J₀.adjoint x) := by
    exact congrArg (fun B : H →L[ℂ] H => B x) hcomplement.symm
  have hzero : (1 - P) * T * (1 - P) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change (1 - P) (T ((1 - P) x)) = 0
    rw [hQ x, hword]
    change C (hilbertTensorInsert b (J₀.adjoint x)) -
      P (C (hilbertTensorInsert b (J₀.adjoint x))) = 0
    rw [hcreator, sub_self]
  have hblock : P * T * (1 - P) = (reducedCreator C b).comp J₀.adjoint := by
    apply ContinuousLinearMap.ext
    intro x
    change P (T ((1 - P) x)) = _
    rw [hQ, hword, hcreator]
    rfl
  refine ⟨hzero, ?_⟩
  rw [hblock]
  calc
    _ ≤ ‖reducedCreator C b‖ * ‖J₀.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖b‖ * 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul (norm_reducedCreator_le C b) J.norm_toContinuousLinearMap_le
        (norm_nonneg _) (norm_nonneg _)
    _ = ‖b‖ := mul_one _

/-- The elementary reduced-word action is sufficient for the narrow-arc
compression estimate. The creation bound and zero block are conclusions. -/
theorem norm_narrow_arc_of_reduced_word_action
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : K →L[ℂ] K)
    (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e T : HilbertTensor E K →L[ℂ] HilbertTensor E K)
    (he : e.adjoint = e) (hesq : e * e = e) (hT : T.adjoint = T)
    (heword : ∀ x, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (J : L →ₗᵢ[ℂ] HilbertTensor E K) (C : HilbertTensor B L →ₗᵢ[ℂ] HilbertTensor E K)
    (b : B)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint =
      1 - firstLetterProjection Ω Q)
    (hcreator : ∀ x, firstLetterProjection Ω Q (C (hilbertTensorInsert b x)) =
      C (hilbertTensorInsert b x))
    (hword : ∀ x, T (J x) = C (hilbertTensorInsert b x))
    {u : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u)
    (h₂ : ‖b‖ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) :
    ‖e * T * e‖ ≤ 3 * u := by
  obtain ⟨hzero, hcreate⟩ := reduced_word_creation_blocks J C
    (firstLetterProjection Ω Q) T b hcomplement hcreator hword
  exact norm_narrow_arc_from_tensor_geometry Ω eΩ hΩ Q hQ hQsq hQnorm e T he hesq hT
    heword hu hsq (norm_nonneg b) hzero hcreate h₂ hnorm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free-compression norm bound in the faithful tracial representation.
The hypotheses describe only the elementary reduced-word coordinates; their
zero block, creation bound, and the small-corner norm bound are conclusions. -/

noncomputable section
namespace KadisonSimilarity

variable {P H F K : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A Z : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (Z : Set P)]

omit [IsClosed (A : Set P)] in
/-- The faithful tracial norm and the elementary creation action give the
order-`u` bound used for the narrow spectral arc. -/
theorem norm_narrow_compression_of_reduced_words
    (hfaithful : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (W : H ≃ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) F)
    (hhead : ∀ (a : A) x, W (G.left (a : P) x) =
      tensorHeadAction (G.baseRepresentation A a) (W x))
    (Q : F →L[ℂ] F) (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (J : K →ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) F)
    (C : HilbertTensor (centeredSubspace (G.baseVector Z 1)) K →ₗᵢ[ℂ]
      HilbertTensor (G.baseSpace A) F)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint =
      1 - firstLetterProjection (G.baseVector A 1) Q)
    (e : A) (he : IsStarProjection (e : P))
    (b : Z) (hbself : star b = b) (hb0 : G.trace (b : P) = 0)
    (hcreator : ∀ x, firstLetterProjection (G.baseVector A 1) Q
      (C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x)) =
        C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x))
    (hword : ∀ x, W (G.left (b : P) (W.symm (J x))) =
      C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x))
    {u : ℝ} (hu : 0 ≤ u) (hetrace : G.trace (e : P) = (u : ℂ))
    (hb₂ : (G.trace (star (b : P) * (b : P))).re ≤ u) (hbnorm : ‖(b : P)‖ ≤ 1) :
    ‖(e : P) * (b : P) * (e : P)‖ ≤ 3 * u := by
  let ρ := W.conjStarAlgEquiv.toStarAlgHom.comp G.left
  have hρinjective : Function.Injective ρ := by
    intro a b hab
    apply G.left_injective hfaithful
    apply W.conjStarAlgEquiv.injective
    exact hab
  have hρnorm (x : P) : ‖ρ x‖ = ‖x‖ := by
    exact NonUnitalStarAlgHom.norm_map ρ hρinjective x
  have hΩ : ‖G.baseVector A 1‖ = 1 := by
    have hsq : ‖G.baseVector A 1‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
      change (G.trace (star (1 : P) * 1)).re = 1
      simp only [star_one, one_mul, hτ, Complex.one_re]
    nlinarith [norm_nonneg (G.baseVector A 1)]
  have heΩ : ‖G.baseVector A e‖ ^ 2 = u := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner,
      he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, hetrace]
    rfl
  have heword (x : F) : ρ (e : P) (hilbertTensorInsert (G.baseVector A 1) x) =
      hilbertTensorInsert (G.baseVector A e) x := by
    change W (G.left (e : P) (W.symm _)) = _
    rw [hhead, W.apply_symm_apply, tensorHeadAction_insert]
    have hv : G.baseRepresentation A e (G.baseVector A 1) = G.baseVector A e := by
      apply Subtype.ext
      change G.left (e : P) (G.vector 1) = G.vector (e : P)
      rw [G.left_vector, mul_one]
    rw [hv]
  have hestar : (ρ (e : P)).adjoint = ρ (e : P) := by
    change star (ρ (e : P)) = ρ (e : P)
    exact (map_star ρ (e : P)).symm.trans (congrArg ρ he.isSelfAdjoint.star_eq)
  have hesq : ρ (e : P) * ρ (e : P) = ρ (e : P) := by
    rw [← map_mul, he.isIdempotentElem.eq]
  have hbstar : (ρ (b : P)).adjoint = ρ (b : P) := by
    change star (ρ (b : P)) = ρ (b : P)
    exact (map_star ρ (b : P)).symm.trans
      (congrArg ρ (congrArg (fun z : Z => (z : P)) hbself))
  have hbvec : ‖G.baseSymmetryLetter Z b hb0‖ ^ 2 ≤ u := by
    change ‖G.baseVector Z b‖ ^ 2 ≤ u
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    exact hb₂
  have hbound := norm_narrow_arc_of_reduced_word_action
    (G.baseVector A 1) (G.baseVector A e) hΩ Q hQ hQsq hQnorm
    (ρ (e : P)) (ρ (b : P)) hestar hesq hbstar heword J C
    (G.baseSymmetryLetter Z b hb0) hcomplement hcreator hword hu heΩ hbvec
    (by rw [hρnorm]; exact hbnorm)
  rw [← map_mul, ← map_mul, hρnorm] at hbound
  exact hbound

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_PublishedWordCreation
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary creation part of the published reduced free-product model.

Ricard--Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2--3,
and Lemma 2.3: prepending a centered letter to a word from the opposite
factor is the Hilbert tensor insertion. This interface has only those raw
word maps; prefix isometry and propagation are derived separately. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- The narrow-arc norm estimate follows from the published elementary
creation model and the proved three-block estimate. -/
theorem norm_narrow_compression_of_published_words
    (published : RicardXuCompressionInput G A D)
    (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (hfree : ScalarFree G.trace D A) (hdense : ReducedWordGenerated G A D)
    (e : A) (he : IsStarProjection (e : P))
    (b : D) (hbself : star b = b) (hb0 : G.trace (b : P) = 0)
    {u : ℝ} (hu : 0 ≤ u) (hetrace : G.trace (e : P) = (u : ℂ))
    (hb₂ : (G.trace (star (b : P) * (b : P))).re ≤ u) (hbnorm : ‖(b : P)‖ ≤ 1) :
    ‖(e : P) * (b : P) * (e : P)‖ ≤ 3 * u := by
  obtain ⟨W⟩ := published hτ hfaithful hfree hdense
  exact G.norm_narrow_compression_of_reduced_words A D hfaithful hτ
    W.head.unitary W.head.left_head W.tailProjection W.projection_adjoint
    W.projection_sq W.projection_norm W.includeBefore W.create W.complement
    e he b hbself hb0 (W.create_range b hb0) (W.create_word b hb0) hu hetrace hb₂ hbnorm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedCompression
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction to the C-star algebra generated by the two free factors.
The compression model is used on this cyclic generated representation,
and faithfulness transfers its norm estimate to the ambient algebra. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

/-- Norm generation implies generation of the actual tracial Hilbert space. -/
theorem factorsTraciallyGenerate_of_norm_generation
    (hgen : (factorAlgebra A D).topologicalClosure = ⊤) :
    G.FactorsTraciallyGenerate A D := by
  let M := (G.vector.comp (factorAlgebra A D).subtype.toLinearMap).range.topologicalClosure
  have ha (a : P) : G.vector a ∈ M := by
    have hc : IsClosed (G.vector ⁻¹' (M : Set H)) :=
      (Submodule.isClosed_topologicalClosure _).preimage G.continuous_vector
    have hs : (factorAlgebra A D : Set P) ⊆ G.vector ⁻¹' (M : Set H) := by
      intro x hx
      exact Submodule.le_topologicalClosure _ ⟨⟨x, hx⟩, rfl⟩
    have ha : a ∈ closure (factorAlgebra A D : Set P) := by
      change a ∈ (factorAlgebra A D).topologicalClosure
      rw [hgen]
      trivial
    exact hc.closure_subset_iff.mpr hs ha
  have hM : M = ⊤ := by
    apply top_unique
    intro x _
    exact G.dense_vector.induction_on x (Submodule.isClosed_topologicalClosure _) ha
  apply dense_iff_closure_eq.mpr
  change (M : Set H) = Set.univ
  rw [hM]
  rfl

end TracialCornerGeometry

/-- Pulling the two factors into their closed generated algebra preserves
their ordinary norm-generation property. -/
theorem factorAlgebra_comap_generates (A D S : StarSubalgebra ℂ P)
    (hA : A ≤ S) (hD : D ≤ S) (hS : (factorAlgebra A D).topologicalClosure = S)
    [IsClosed (S : Set P)] :
    (factorAlgebra (A.comap S.subtype) (D.comap S.subtype)).topologicalClosure = ⊤ := by
  have himage (B : StarSubalgebra ℂ P) (hB : B ≤ S) :
      S.subtype '' (B.comap S.subtype : Set S) = (B : Set P) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hB hx⟩, hx, rfl⟩
  have hm : (factorAlgebra (A.comap S.subtype) (D.comap S.subtype)).map S.subtype =
      factorAlgebra A D := by
    simp only [factorAlgebra, StarAlgHom.map_adjoin, Set.image_union, himage A hA, himage D hD]
  have hclosed : IsClosedMap S.subtype :=
    (show IsClosed (S : Set P) from inferInstance).isClosedMap_subtype_val
  have hmap := StarSubalgebra.topologicalClosure_map
    (factorAlgebra (A.comap S.subtype) (D.comap S.subtype)) S.subtype hclosed
      continuous_subtype_val
  rw [hm, hS] at hmap
  apply top_unique
  intro x _
  have hx : (x : P) ∈ ((factorAlgebra (A.comap S.subtype)
      (D.comap S.subtype)).topologicalClosure).map S.subtype := by
    rw [← hmap]
    exact x.property
  obtain ⟨y, hy, heq⟩ := hx
  exact (Subtype.ext heq : y = x) ▸ hy

theorem alternatingCenteredWord_subtype (τ : P →ₗ[ℂ] ℂ)
    (A D S : StarSubalgebra ℂ P) {side : Bool} {xs : List S}
    (h : AlternatingCenteredWord (τ.comp S.subtype.toLinearMap)
      (A.comap S.subtype) (D.comap S.subtype) side xs) :
    AlternatingCenteredWord τ A D side (xs.map (fun x : S => (x : P))) := by
  induction h with
  | nil side => exact .nil side
  | @cons side x xs hm hz _ ih =>
    change AlternatingCenteredWord τ A D side ((x : P) :: xs.map (fun x : S => (x : P)))
    apply AlternatingCenteredWord.cons ?_ (show τ (x : P) = 0 from hz) ih
    cases side <;> exact hm

theorem scalarFree_subtype (τ : P →ₗ[ℂ] ℂ) (A D S : StarSubalgebra ℂ P)
    (hf : ScalarFree τ A D) :
    ScalarFree (τ.comp S.subtype.toLinearMap) (A.comap S.subtype) (D.comap S.subtype) := by
  intro side x xs h
  have ht := hf side (x : P) (xs.map (fun y : S => (y : P)))
    (alternatingCenteredWord_subtype τ A D S h)
  exact (congrArg τ (map_list_prod S.subtype (x :: xs))).trans ht

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D S : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)] [IsClosed (S : Set P)]

/-- The narrow compression bound is proved in the cyclic Hilbert space of
the generated algebra, then read in the ambient C-star norm. -/
theorem norm_narrow_compression_on_generated_algebra
    (hA : A ≤ S) (hD : D ≤ S) (hS : (factorAlgebra A D).topologicalClosure = S)
    (published : RicardXuCompressionInput (G.baseGeometry S)
      (A.comap S.subtype) (D.comap S.subtype))
    (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (hfree : ScalarFree G.trace D A)
    (e : A) (he : IsStarProjection (e : P))
    (b : D) (hbself : star b = b) (hb0 : G.trace (b : P) = 0)
    {u : ℝ} (hu : 0 ≤ u) (hetrace : G.trace (e : P) = (u : ℂ))
    (hb₂ : (G.trace (star (b : P) * (b : P))).re ≤ u) (hbnorm : ‖(b : P)‖ ≤ 1) :
    ‖(e : P) * (b : P) * (e : P)‖ ≤ 3 * u := by
  let eS : A.comap S.subtype := ⟨⟨e, hA e.property⟩, e.property⟩
  let bS : D.comap S.subtype := ⟨⟨b, hD b.property⟩, b.property⟩
  have heS : IsStarProjection (eS : S) := by
    constructor
    · exact Subtype.ext he.isIdempotentElem.eq
    · exact Subtype.ext he.isSelfAdjoint.star_eq
  have hbS : star bS = bS := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : D => (x : P)) hbself
  have hτS := G.baseGeometry_trace_one S hτ
  have hgen := factorAlgebra_comap_generates A D S hA hD hS
  have hdense := (G.baseGeometry S).reducedWordGenerated_of_factorsTraciallyGenerate
    (A.comap S.subtype) (D.comap S.subtype) hτS
    ((G.baseGeometry S).factorsTraciallyGenerate_of_norm_generation
      (A.comap S.subtype) (D.comap S.subtype) hgen)
  exact norm_narrow_compression_of_published_words (G.baseGeometry S)
    (A.comap S.subtype) (D.comap S.subtype) published hτS
    (G.baseGeometry_vector_injective S hfaithful) (scalarFree_subtype G.trace D A S hfree)
    hdense eS heS bS hbS hb0 hu hetrace hb₂ hbnorm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

end CStarCorner

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tracial Hilbert representation of an actual C-star corner.
Its density and action are inherited from the ambient tracial representation. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (p : P) (hp : IsStarProjection p)

theorem cornerGeometry_vector_injective (c : ℂ) (hc : c ≠ 0)
    (hcτ : star c * c = (G.trace p)⁻¹) (hf : Function.Injective G.vector) :
    Function.Injective (G.cornerGeometry p hp c hc hcτ).vector := by
  intro a b hab
  apply Subtype.ext
  apply hf
  have h := congrArg (fun x : G.corner p p => (x : H)) hab
  change c • G.vector (a : P) = c • G.vector (b : P) at h
  exact (smul_right_injective H hc) h

theorem normalizedCornerGeometry_trace_one {t : ℝ} (ht : 0 < t)
    (htp : G.trace p = (t : ℂ)) : (G.normalizedCornerGeometry p hp ht htp).trace 1 = 1 := by
  apply CStarCorner.normalizedTrace_one
  rw [htp]
  exact_mod_cast ht.ne'

theorem normalizedCornerGeometry_vector_injective {t : ℝ} (ht : 0 < t)
    (htp : G.trace p = (t : ℂ)) (hf : Function.Injective G.vector) :
    Function.Injective (G.normalizedCornerGeometry p hp ht htp).vector :=
  G.cornerGeometry_vector_injective p hp _ _ _ hf

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

theorem corner_mem (hp : IsStarProjection (dihedralHalfProjection d))
    (hdC : (d : P) ∈ C) : (F.corner hp : P) ∈ C :=
  C.mul_mem F.mem (C.smul_mem (C.add_mem C.one_mem hdC) _)

theorem corner_selfAdjoint (hp : IsStarProjection (dihedralHalfProjection d)) :
    star (F.corner hp) = F.corner hp := by
  apply Subtype.ext
  change star (F.element * dihedralHalfProjection d) = _
  rw [star_mul, hp.isSelfAdjoint.star_eq, F.selfAdjoint,
    ← F.halfProjection_commutes.eq]
  rfl

theorem corner_norm_le (hp : IsStarProjection (dihedralHalfProjection d)) :
    ‖F.corner hp‖ ≤ 1 := by
  change ‖F.element * dihedralHalfProjection d‖ ≤ 1
  exact (norm_mul_le _ _).trans
    ((mul_le_mul F.norm_le hp.norm_le (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))

theorem corner_trace_zero (hp : IsStarProjection (dihedralHalfProjection d))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ (F.corner hp : P) = 0 := by
  have hd0 : τ (F.element * (d : P)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using F.reflection_moment 0
  simp only [corner_coe, dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.trace_zero hθ hπ, hd0, add_zero, smul_zero]

theorem corner_square (hp : IsStarProjection (dihedralHalfProjection d)) :
    ((F.corner hp * F.corner hp : CStarCorner (dihedralHalfProjection d) hp) : P) =
      (F.element * F.element) * dihedralHalfProjection d := by
  change (F.element * dihedralHalfProjection d) *
    (F.element * dihedralHalfProjection d) = _
  calc
    _ = F.element * (dihedralHalfProjection d * F.element) *
        dihedralHalfProjection d := by simp only [mul_assoc]
    _ = F.element * (F.element * dihedralHalfProjection d) *
        dihedralHalfProjection d := by rw [← F.halfProjection_commutes.eq]
    _ = _ := by simp only [mul_assoc, hp.isIdempotentElem.eq]

/-- Normalization cancels the half-corner trace, leaving the arc variance. -/
theorem corner_second_moment (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : τ (dihedralHalfProjection d) = (1 / 2 : ℂ)) :
    CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ
      (star (F.corner hp) * F.corner hp) = ((θ / Real.pi) * (1 - θ / Real.pi) : ℝ) := by
  rw [F.corner_selfAdjoint hp, CStarCorner.normalizedTrace_apply, F.corner_square hp, ht]
  simp only [dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.square_moment, F.square_reflection_moment, add_zero,
    smul_eq_mul]
  ring

theorem corner_second_moment_le (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : τ (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ
      (star (F.corner hp) * F.corner hp)).re ≤ 4 * θ := by
  rw [F.corner_second_moment hp ht, Complex.ofReal_re,
    ← centeredArc_second_moment hθ hπ]
  exact centeredArc_second_moment_le hθ hπ

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSpectralNorm
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow spectral arc has the required small norm in the original
algebra. Its creation model is applied on the closed algebra generated by
the two corner factors, with the normalized restricted trace. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (C D : StarSubalgebra ℂ P)
  [IsClosed (C : Set P)] [IsClosed (D : Set P)]
  (w d : Pˣ) (hp : IsStarProjection (dihedralHalfProjection d))
  (hpC : dihedralHalfProjection d ∈ C) (hpD : dihedralHalfProjection d ∈ D)
  (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))

variable
  (S : StarSubalgebra ℂ (CStarCorner (dihedralHalfProjection d) hp))
  [IsClosed (S : Set (CStarCorner (dihedralHalfProjection d) hp))]

/-- The published elementary creation model yields the actual `3u` norm
bound for the spectral test, with `u = 2t`. -/
theorem norm_spectral_arc_compression_oai
    (hS : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC)).topologicalClosure = S)
    (published : RicardXuCompressionInput
      ((G.halfCornerGeometry d hp htp).baseGeometry S)
      ((CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD).comap S.subtype)
      ((CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC).comap S.subtype))
    (hfaithful : Function.Injective G.vector)
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
    (hdC : (d : P) ∈ C)
    {θ : ℝ} (F : DihedralSpectralArc G.trace C w d θ)
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (e : CStarCorner (dihedralHalfProjection d) hp) (he : IsStarProjection e)
    (heD : (e : P) ∈ D) {t : ℝ} (ht : 0 ≤ t) (hte : G.trace (e : P) = (t : ℂ))
    (hwidth : 4 * θ ≤ 2 * t) :
    ‖(e : P) * (F.element * dihedralHalfProjection d) * (e : P)‖ ≤ 3 * (2 * t) := by
  let DA := CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD
  let CA := CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC
  have hDA : DA ≤ S := by
    rw [← hS]
    exact fun x hx => (StarSubalgebra.le_topologicalClosure _)
      (StarAlgebra.subset_adjoin ℂ _ (Or.inl hx))
  have hCA : CA ≤ S := by
    rw [← hS]
    exact fun x hx => (StarSubalgebra.le_topologicalClosure _)
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr hx))
  let ee : DA := ⟨e, heD⟩
  let bb : CA := ⟨F.corner hp, F.corner_mem hp hdC⟩
  have hbself : star bb = bb := Subtype.ext (F.corner_selfAdjoint hp)
  have hb0 : (G.halfCornerGeometry d hp htp).trace (bb : CStarCorner _ hp) = 0 := by
    change (G.trace (dihedralHalfProjection d))⁻¹ * G.trace (F.corner hp : P) = 0
    rw [F.corner_trace_zero hp hθ hπ, mul_zero]
  have hetrace : (G.halfCornerGeometry d hp htp).trace (ee : CStarCorner _ hp) =
      ((2 * t : ℝ) : ℂ) := by
    change (G.trace (dihedralHalfProjection d))⁻¹ * G.trace (e : P) = _
    rw [htp, hte]
    push_cast
    ring
  have hb₂ : ((G.halfCornerGeometry d hp htp).trace
      (star (bb : CStarCorner _ hp) * (bb : CStarCorner _ hp))).re ≤ 2 * t :=
    (F.corner_second_moment_le hp htp hθ hπ).trans hwidth
  exact (G.halfCornerGeometry d hp htp).norm_narrow_compression_on_generated_algebra
    DA CA S hDA hCA hS published
    (G.normalizedCornerGeometry_trace_one _ hp (by norm_num : 0 < (1 / 2 : ℝ))
      (by simpa using htp))
    (G.normalizedCornerGeometry_vector_injective _ hp (by norm_num : 0 < (1 / 2 : ℝ))
      (by simpa using htp) hfaithful) hfree.symm ee he bb hbself hb0
    (mul_nonneg (by norm_num) ht) hetrace hb₂
    (F.corner_norm_le hp)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression_oai.{u_1, u_2}
