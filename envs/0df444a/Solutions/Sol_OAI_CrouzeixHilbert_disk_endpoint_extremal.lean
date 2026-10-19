-- Prove2me | solution 1 for OAI.CrouzeixHilbert.disk_endpoint_extremal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:53:27.957361+00:00
-- url     : https://prove2.me/submissions/c824b912-31d0-40cf-b50f-0d4f6de933d2

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_matrixHolomorphicEval_matrixRationalFunction

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_le_of_mem_numericalRange (A : Operator H) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (A : Operator H) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_le_of_mem_numericalRange A hz

theorem numericalClosure_subset_closedBall (A : Operator H) :
    numericalClosure A ⊆ Metric.closedBall 0 ‖A‖ :=
  closure_minimal (numericalRange_subset_closedBall A) Metric.isClosed_closedBall

theorem isCompact_numericalClosure (A : Operator H) : IsCompact (numericalClosure A) :=
  (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset isClosed_closure
    (numericalClosure_subset_closedBall A)

theorem numericalRange_nonempty [Nontrivial H] (A : Operator H) :
    (numericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟪x, A x⟫_ℂ, x, hx, rfl⟩

theorem numericalClosure_nonempty [Nontrivial H] (A : Operator H) :
    (numericalClosure A).Nonempty :=
  (numericalRange_nonempty A).mono subset_closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

open scoped Kronecker

theorem norm_matrixAmplificationCoordinates (n m : ℕ)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    ‖matrixAmplificationCoordinates n m v‖ = ‖v‖ := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (matrixAmplificationCoordinates n m).continuous.norm continuous_norm) ?_
  intro a
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map,
    UniformSpace.Completion.norm_coe]

theorem matrixAmplificationCoordinates_tensorOperator {n m : ℕ}
    (M : Coeff n) (B : Coeff m) (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B) (matrixAmplificationCoordinates n m v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((matrixAmplificationCoordinates n m).continuous.comp
      (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).continuous)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B)).continuous.comp
        (matrixAmplificationCoordinates n m).continuous)) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x y =>
    simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
    apply PiLp.ext
    rintro ⟨i, j⟩
    simp only [matrixAmplificationCoordinates_tmul, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

theorem trace_conjTranspose_mul_re {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    (Aᴴ * A).trace.re = ‖toHS A‖ ^ 2 := by
  rw [norm_toHS_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

section MatrixMultipliers

theorem inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℂ = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, toHS,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem real_inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℝ = (Aᴴ * B).trace.re := by
  rw [← inner_toHS]
  simp only [PiLp.inner_apply, toHS, real_inner_eq_re_inner ℂ,
    RCLike.re_to_complex, Complex.re_sum]

@[simp] theorem adjoint_hsLeft {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsLeft A) = hsLeft Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsLeft_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

@[simp] theorem adjoint_hsRight {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsRight A) = hsRight Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsRight_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (V * A)]

end MatrixMultipliers

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SteinMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stein Metric. -/

noncomputable section

open Set Filter

open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Metric

section Stein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem summable_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    Summable (fun j : ℕ => star (T ^ j) * T ^ j) := by
  have hs := summable_norm_pow T hT
  have hsmall : ∀ᶠ j in atTop, ‖T ^ j‖ ≤ 1 := by
    exact (hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun j hj => hj.le)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsmall] with j hj
  calc
    ‖star (T ^ j) * T ^ j‖ ≤ ‖star (T ^ j)‖ * ‖T ^ j‖ := norm_mul_le _ _
    _ = ‖T ^ j‖ * ‖T ^ j‖ := by rw [norm_star]
    _ ≤ ‖T ^ j‖ * 1 := mul_le_mul_of_nonneg_left hj (norm_nonneg _)
    _ = ‖T ^ j‖ := mul_one _

theorem steinSeries_nonneg (T : A) : 0 ≤ steinSeries T :=
  tsum_nonneg (fun _ => star_mul_self_nonneg _)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_eq_one_add (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T = 1 + star T * steinSeries T * T := by
  have hs := summable_steinSeries T hT
  have he : (fun j : ℕ => star (T ^ (j + 1)) * T ^ (j + 1)) =
      (fun j : ℕ => star T * (star (T ^ j) * T ^ j) * T) := by
    funext j
    rw [pow_succ, star_mul]
    simp only [mul_assoc]
  have hz := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, star_one, mul_one] at hz
  rw [he, (hs.mul_left (star T)).tsum_mul_right T, hs.tsum_mul_left (star T)] at hz
  exact hz.symm

theorem one_le_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    1 ≤ steinSeries T := by
  rw [steinSeries_eq_one_add T hT]
  exact le_add_of_nonneg_right (star_left_conjugate_nonneg (steinSeries_nonneg T) T)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_sub (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T - star T * steinSeries T * T = 1 := by
  nth_rw 1 [steinSeries_eq_one_add T hT]
  exact add_sub_cancel_right _ _

end Stein

section Minimization

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Feasible.nonneg {T H : A} {τ : ℝ} (h : Feasible T τ H) : 0 ≤ H :=
  zero_le_one.trans h.lower

theorem Feasible.selfAdjoint {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsSelfAdjoint H := .of_nonneg h.nonneg

theorem Feasible.isStrictlyPositive {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsStrictlyPositive H := isStrictlyPositive_one.of_le h.lower

variable [Nontrivial A]

theorem Feasible.one_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : 1 ≤ τ := by
  have he : algebraMap ℝ A 1 ≤ algebraMap ℝ A τ := by simpa using h.lower.trans h.upper
  exact algebraMap_le_algebraMap.mp he

theorem Feasible.norm_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : ‖H‖ ≤ τ :=
  (CStarAlgebra.norm_le_iff_le_algebraMap H (zero_le_one.trans h.one_le) h.nonneg).mpr h.upper

end Minimization

section Similarity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_le_one_iff_star_mul_self_le (a : A) :
    ‖a‖ ≤ 1 ↔ star a * a ≤ 1 := by
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (star a * a)
    (star_mul_self_nonneg a), CStarRing.norm_star_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg a]

variable [Nontrivial A]

theorem Feasible.sqrt_similarity {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsUnit (CFC.sqrt H) ∧
      ‖CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)‖ ≤ 1 ∧
      ‖CFC.sqrt H‖ * ‖Ring.inverse (CFC.sqrt H)‖ ≤ Real.sqrt τ := by
  let S := CFC.sqrt H
  let R := Ring.inverse S
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg H
  have hS1 : (1 : A) ≤ S := by
    simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt (1 : A) H h.lower
  have hSpos : IsStrictlyPositive S := isStrictlyPositive_one.of_le hS1
  have hu : IsUnit S := hSpos.isUnit
  have hR0 : 0 ≤ R := (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hu).mpr hS0
  have hR1 : R ≤ (1 : A) := by
    simpa only [Ring.inverse_one] using CStarAlgebra.ringInverse_le_ringInverse hS1
  have hRS : R * S = 1 := Ring.inverse_mul_cancel S hu
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hu
  have hRSa : star R = R := (IsSelfAdjoint.of_nonneg hR0).star_eq
  have hSSa : star S = S := (IsSelfAdjoint.of_nonneg hS0).star_eq
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H h.nonneg
  have hconj := star_left_conjugate_le_conjugate h.stein R
  have hright : star R * H * R = 1 := by
    rw [hRSa, ← hSS, ← mul_assoc, hRS, one_mul, hSR]
  have hleft : star R * (star T * H * T) * R =
      star (S * T * R) * (S * T * R) := by
    rw [star_mul, star_mul, hSSa, ← hSS]
    noncomm_ring
  rw [hleft, hright] at hconj
  refine ⟨hu, (norm_le_one_iff_star_mul_self_le _).mpr hconj, ?_⟩
  have hRn : ‖R‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg R hR0).mpr hR1
  change ‖S‖ * ‖R‖ ≤ Real.sqrt τ
  calc
    ‖S‖ * ‖R‖ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hRn (norm_nonneg _)
    _ = Real.sqrt ‖H‖ := by simpa only [S, mul_one] using CFC.norm_sqrt H h.nonneg
    _ ≤ Real.sqrt τ := Real.sqrt_le_sqrt h.norm_le

theorem Feasible.sqrt_spectrum {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    spectrum ℂ (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) = spectrum ℂ T := by
  obtain ⟨u, hu⟩ := h.sqrt_similarity.1
  rw [← hu]
  simpa only [Ring.inverse_unit] using spectrum.units_conjugate (R := ℂ) (a := T) (u := u)

end Similarity

end CrouzeixHilbert.Metric

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint. -/

noncomputable section

open Set Filter

open scoped Topology MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Endpoint

section Cone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
theorem unit_mem_strictCone : (unit : Herm A) ∈ strictCone :=
  ⟨1, zero_lt_one, by simp⟩

theorem strictCone_nonneg {H : Herm A} (h : H ∈ strictCone) : 0 ≤ H := by
  obtain ⟨ε, hε, hH⟩ := h
  apply le_trans _ hH
  change 0 ≤ ε • (1 : A)
  exact smul_nonneg hε.le zero_le_one

theorem strictCone_add_nonneg {H P : Herm A} (hH : H ∈ strictCone)
    (hP : 0 ≤ P) : H + P ∈ strictCone := by
  obtain ⟨ε, hε, hH⟩ := hH
  exact ⟨ε, hε, hH.trans (le_add_of_nonneg_right hP)⟩

theorem strictCone_smul {H : Herm A} (hH : H ∈ strictCone) {r : ℝ}
    (hr : 0 < r) : r • H ∈ strictCone := by
  obtain ⟨ε, hε, hH⟩ := hH
  refine ⟨r * ε, mul_pos hr hε, ?_⟩
  rw [mul_smul]
  exact smul_le_smul_of_nonneg_left hH hr.le

theorem convex_strictCone : Convex ℝ (strictCone : Set (Herm A)) := by
  intro H hH J hJ a b ha hb hab
  obtain ⟨ε, hε, hH⟩ := hH
  obtain ⟨δ, hδ, hJ⟩ := hJ
  refine ⟨a * ε + b * δ, ?_, ?_⟩
  · have hs : 0 ≤ a * ε := mul_nonneg ha hε.le
    have ht : 0 ≤ b * δ := mul_nonneg hb hδ.le
    by_cases h : a = 0
    · have : b = 1 := by linarith
      simp [h, this, hδ]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hε) ht
  · rw [add_smul, mul_smul, mul_smul]
    exact add_le_add (smul_le_smul_of_nonneg_left hH ha)
      (smul_le_smul_of_nonneg_left hJ hb)

theorem isOpen_strictCone : IsOpen (strictCone : Set (Herm A)) := by
  rw [Metric.isOpen_iff]
  intro H hH
  obtain ⟨ε, hε, hlower⟩ := hH
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro J hJ
  have hd : ‖(J - H : Herm A)‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hJ
  have hlo : -(‖(J - H : Herm A)‖) • (unit : Herm A) ≤ J - H := by
    change -(‖((J - H : Herm A) : A)‖) • (1 : A) ≤ ((J - H : Herm A) : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      (J - H).property.neg_algebraMap_norm_le_self
  refine ⟨ε / 2, half_pos hε, ?_⟩
  have hh := add_le_add hlower hlo
  rw [← add_smul, add_sub_cancel] at hh
  apply le_trans _ hh
  change (ε / 2) • (1 : A) ≤ (ε + -‖(J - H : Herm A)‖) • (1 : A)
  exact smul_le_smul_of_nonneg_right (by linarith) zero_le_one

theorem orderUnit_bounds (H : Herm A) :
    -(‖H‖) • (unit : Herm A) ≤ H ∧ H ≤ ‖H‖ • (unit : Herm A) := by
  constructor
  · change -(‖(H : A)‖) • (1 : A) ≤ (H : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      H.property.neg_algebraMap_norm_le_self
  · change (H : A) ≤ ‖(H : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using H.property.le_algebraMap_norm_self

theorem positive_mono (f : (Herm A) →L[ℝ] ℝ)
    (hf : ∀ H, 0 ≤ H → 0 ≤ f H) : Monotone f := by
  intro H J hHJ
  have h := hf (J - H) (sub_nonneg.mpr hHJ)
  rw [map_sub] at h
  linarith

theorem positive_eq_zero (f : (Herm A) →L[ℝ] ℝ)
    (hf : ∀ H, 0 ≤ H → 0 ≤ f H) (h1 : f unit = 0) : f = 0 := by
  ext H
  have hl := positive_mono f hf (orderUnit_bounds H).1
  have hu := positive_mono f hf (orderUnit_bounds H).2
  simp only [map_smul, smul_eq_mul, h1, mul_zero, zero_apply] at *
  exact le_antisymm hu hl

end Cone

lemma slope_nonpos {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ t → b + a * t ≤ c) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  have hb := h 0 le_rfl
  simp only [mul_zero, add_zero] at hb
  have ht : 0 ≤ (c - b + 1) / a := div_nonneg (by linarith) ha.le
  have hh := h ((c - b + 1) / a) ht
  rw [mul_div_cancel₀ _ ha.ne'] at hh
  linarith

lemma slope_zero {a b c : ℝ} (h : ∀ t : ℝ, c ≤ b + a * t) : a = 0 := by
  have hn : a ≤ 0 := slope_nonpos (b := -b) (c := -c) (fun t ht => by
    have := h (-t)
    linarith)
  have hp : -a ≤ 0 := slope_nonpos (b := -b) (c := -c) (fun t ht => by
    have := h t
    linarith)
  linarith

section Separation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem convex_lowerOpen (τ : ℝ) : Convex ℝ (lowerOpen (A := A) τ) :=
  (convex_Iio τ).prod (convex_strictCone.prod (convex_strictCone.prod convex_strictCone))

theorem isOpen_lowerOpen (τ : ℝ) : IsOpen (lowerOpen (A := A) τ) :=
  isOpen_Iio.prod (isOpen_strictCone.prod (isOpen_strictCone.prod isOpen_strictCone))

omit [PartialOrder A] [StarOrderedRing A] in
theorem convex_slacks (T : A) : Convex ℝ {p : SlackSpace A | ∃ s H, p = slacks T s H} := by
  rintro x ⟨s, H, rfl⟩ y ⟨t, J, rfl⟩ a b ha hb hab
  refine ⟨a * s + b * t, a • H + b • J, ?_⟩
  dsimp only [slacks]
  ext1
  · rfl
  · ext1
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub]
      have he : a • (unit : Herm A) + b • unit = unit := by rw [← add_smul, hab, one_smul]
      calc
        a • H - a • unit + (b • J - b • unit) =
            a • H + b • J - (a • unit + b • unit) := by abel
        _ = _ := by rw [he]
    · ext1
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub, add_smul, mul_smul]
        module
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub, map_add, map_smul]
        module

omit [PartialOrder A] [StarOrderedRing A] in
theorem functional_decomposition (f : SlackSpace A →L[ℝ] ℝ)
    (s : ℝ) (U V W : Herm A) :
    f (s,U,V,W) = scalarPart f * s - firstPart f U - secondPart f V - thirdPart f W := by
  have he : (s,U,V,W) = s • ((1,0,0,0) : SlackSpace A) + (0,U,0,0) + (0,0,V,0) + (0,0,0,W) := by
    ext <;> simp
  rw [he, map_add, map_add, map_add, map_smul]
  simp [scalarPart, firstPart, secondPart, thirdPart, mul_comm]
  rfl

theorem lowerOpen_disjoint_slacks (T : A) {τ : ℝ}
    (hmin : ∀ s H, Metric.Feasible T s H → τ ≤ s) :
    Disjoint (lowerOpen (A := A) τ) {p : SlackSpace A | ∃ s H, p = slacks T s H} := by
  rw [Set.disjoint_left]
  rintro p hp ⟨s, H, rfl⟩
  obtain ⟨hs, hU, hV, hW⟩ := hp
  have hH : Metric.Feasible T s (H : A) := by
    constructor
    · exact sub_nonneg.mp (strictCone_nonneg hU)
    · have hv := strictCone_nonneg hV
      change 0 ≤ s • (1 : A) - (H : A) at hv
      simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mp hv
    · exact sub_nonneg.mp (strictCone_nonneg hW)
  exact hs.not_ge (hmin s H hH)

theorem separating_parts_nonneg (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ p ∈ lowerOpen τ, f p ≤ c) :
    0 ≤ scalarPart f ∧
      (∀ H, 0 ≤ H → 0 ≤ firstPart f H) ∧
      (∀ H, 0 ≤ H → 0 ≤ secondPart f H) ∧
      (∀ H, 0 ≤ H → 0 ≤ thirdPart f H) := by
  have h1 := unit_mem_strictCone (A := A)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := slope_nonpos (a := -scalarPart f)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1 - t, unit, unit, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 - t < τ; linarith, h1, h1, h1⟩
        have h := hf _ hp
        rw [functional_decomposition] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -firstPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit + t • H, unit, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, strictCone_add_nonneg h1 (smul_nonneg ht hH), h1, h1⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -secondPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit, unit + t • H, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, h1, strictCone_add_nonneg h1 (smul_nonneg ht hH), h1⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -thirdPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit, unit, unit + t • H) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, h1, h1, strictCone_add_nonneg h1 (smul_nonneg ht hH)⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith

theorem separating_value_lower (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ p ∈ lowerOpen τ, f p ≤ c) : scalarPart f * τ ≤ c := by
  let q : ℝ → ℝ := fun ε => scalarPart f * (τ - ε) - ε * firstPart f unit -
    ε * secondPart f unit - ε * thirdPart f unit
  have hcq : Continuous q := by dsimp [q]; fun_prop
  have ht : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (scalarPart f * τ)) := by
    simpa only [q, sub_zero, zero_mul] using hcq.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  have hp : (τ - ε, ε • unit, ε • unit, ε • unit) ∈ lowerOpen (A := A) τ := by
    have hs := strictCone_smul (unit_mem_strictCone (A := A)) hε
    exact ⟨by change τ - ε < τ; linarith, hs, hs, hs⟩
  have h := hf _ hp
  simpa only [q, functional_decomposition, map_smul, smul_eq_mul] using h

omit [PartialOrder A] [StarOrderedRing A] in
theorem separating_affine_balance (T : A) (c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ s H, c ≤ f (slacks T s H)) :
    secondPart f unit = scalarPart f ∧
      (∀ H, secondPart f H - firstPart f H = thirdPart f H - thirdPart f (congruence T H)) ∧
      c ≤ firstPart f unit := by
  have he (s : ℝ) (H : Herm A) :
      f (slacks T s H) = firstPart f unit +
        (scalarPart f - secondPart f unit) * s +
          (secondPart f H - firstPart f H - thirdPart f H + thirdPart f (congruence T H)) := by
    simp only [slacks, functional_decomposition, map_sub, map_smul, smul_eq_mul]
    ring
  have hscalar := slope_zero (a := scalarPart f - secondPart f unit)
    (b := firstPart f unit) (c := c) (fun t => by
      have h := hf t 0
      simpa only [he, map_zero, sub_zero, add_zero, zero_sub] using h)
  have hscalar : secondPart f unit = scalarPart f := by linarith
  refine ⟨hscalar, ?_, ?_⟩
  · intro H
    have h := slope_zero
      (a := secondPart f H - firstPart f H - thirdPart f H + thirdPart f (congruence T H))
      (b := firstPart f unit) (c := c) (fun t => by
        have h := hf 0 (t • H)
        simp only [he, mul_zero, add_zero, map_smul, smul_eq_mul] at h
        linarith)
    linarith
  · have h := hf 0 0
    simpa only [he, mul_zero, add_zero, map_zero, sub_zero, zero_sub] using h

theorem exists_unit_slacks (T : A) (hT : spectralRadius ℂ T < 1) :
    ∃ (s : ℝ) (H : Herm A), unit ≤ H - unit ∧
      unit ≤ s • unit - H ∧ unit ≤ H - congruence T H := by
  let H₀ := Metric.steinSeries T
  have h₀ : (1 : A) ≤ H₀ := Metric.one_le_steinSeries T hT
  have h0 : 0 ≤ H₀ := Metric.steinSeries_nonneg T
  let H : Herm A := ⟨H₀ + H₀, IsSelfAdjoint.of_nonneg (add_nonneg h0 h0)⟩
  have hup : (H : A) ≤ algebraMap ℝ A ‖(H : A)‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) (add_nonneg h0 h0)).mp le_rfl
  refine ⟨‖(H : A)‖ + 1, H, ?_, ?_, ?_⟩
  · change (1 : A) ≤ H₀ + H₀ - 1
    exact le_sub_iff_add_le.mpr (add_le_add h₀ h₀)
  · change (1 : A) ≤ (‖(H : A)‖ + 1) • (1 : A) - (H : A)
    rw [add_smul, one_smul]
    apply le_sub_iff_add_le.mpr
    simpa only [Algebra.algebraMap_eq_smul_one, add_comm] using add_le_add_right hup 1
  · change (1 : A) ≤ H₀ + H₀ - star T * (H₀ + H₀) * T
    rw [mul_add, add_mul, add_sub_add_comm, Metric.steinSeries_sub T hT]
    exact le_add_of_nonneg_right zero_le_one

theorem separating_scalar_pos (T : A) (hT : spectralRadius ℂ T < 1)
    (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (ho : ∀ p ∈ lowerOpen τ, f p < c)
    (ha : ∀ s H, c ≤ f (slacks T s H)) : 0 < scalarPart f := by
  have ho' : ∀ p ∈ lowerOpen τ, f p ≤ c := fun p hp => (ho p hp).le
  obtain ⟨hlam, hY, hX, hZ⟩ := separating_parts_nonneg τ c f ho'
  have hc := separating_value_lower τ c f ho'
  by_contra hn
  have hlam0 : scalarPart f = 0 := le_antisymm (le_of_not_gt hn) hlam
  obtain ⟨s, H, hU, hV, hW⟩ := exists_unit_slacks T hT
  have hs := ha s H
  rw [slacks, functional_decomposition, hlam0, zero_mul] at hs
  rw [hlam0, zero_mul] at hc
  have he : (0 : Herm A) ≤ unit := (by change (0 : A) ≤ 1; exact zero_le_one)
  have hYe := hY unit he
  have hXe := hX unit he
  have hZe := hZ unit he
  have hYu := positive_mono (firstPart f) hY hU
  have hXv := positive_mono (secondPart f) hX hV
  have hZw := positive_mono (thirdPart f) hZ hW
  have hY0 : firstPart f = 0 := positive_eq_zero _ hY (by linarith)
  have hX0 : secondPart f = 0 := positive_eq_zero _ hX (by linarith)
  have hZ0 : thirdPart f = 0 := positive_eq_zero _ hZ (by linarith)
  have hf0 : f = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨r,U,V,W⟩
    simp only [functional_decomposition, hlam0, hY0, hX0, hZ0, zero_apply,
      zero_mul, sub_zero]
  have h1 := unit_mem_strictCone (A := A)
  have hp : (τ - 1, unit, unit, unit) ∈ lowerOpen (A := A) τ :=
    ⟨by change τ - 1 < τ; linarith, h1, h1, h1⟩
  have hg := ho _ hp
  have ha0 := ha 0 0
  simp only [hf0, zero_apply] at hg ha0
  linarith

theorem exists_dualCertificate (T : A) (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} (H : Herm A) (hH : Metric.Feasible T τ (H : A))
    (hmin : ∀ s J, Metric.Feasible T s J → τ ≤ s) :
    Nonempty (DualCertificate T τ H) := by
  obtain ⟨f,c,ho,ha'⟩ := geometric_hahn_banach_open
    (convex_lowerOpen (A := A) τ) (isOpen_lowerOpen τ) (convex_slacks T)
    (lowerOpen_disjoint_slacks T hmin)
  have ha : ∀ s J, c ≤ f (slacks T s J) := fun s J => ha' _ ⟨s,J,rfl⟩
  have ho' : ∀ p ∈ lowerOpen τ, f p ≤ c := fun p hp => (ho p hp).le
  have hlam := separating_scalar_pos T hT τ c f ho ha
  obtain ⟨_, hY, hX, hZ⟩ := separating_parts_nonneg τ c f ho'
  obtain ⟨he, hbal, hval⟩ := separating_affine_balance T c f ha
  have hc := separating_value_lower τ c f ho'
  have hunit : (0 : Herm A) ≤ unit := (by change (0 : A) ≤ 1; exact zero_le_one)
  have hU : (0 : Herm A) ≤ H - unit := sub_nonneg.mpr hH.lower
  have hV : (0 : Herm A) ≤ τ • unit - H := by
    change 0 ≤ τ • (1 : A) - (H : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hH.upper
  have hW : (0 : Herm A) ≤ H - congruence T H := sub_nonneg.mpr hH.stein
  have hab : f (slacks T τ H) = firstPart f unit := by
    simp only [slacks, functional_decomposition, map_sub, map_smul, smul_eq_mul]
    have hb := hbal H
    rw [he]
    linarith
  have hvalue : firstPart f unit = scalarPart f * τ - firstPart f (H - unit) -
      secondPart f (τ • unit - H) - thirdPart f (H - congruence T H) := by
    rw [← hab, slacks, functional_decomposition]
  have hYu := hY _ hU
  have hXv := hX _ hV
  have hZw := hZ _ hW
  have hYE : firstPart f unit = scalarPart f * τ := by linarith
  have hYS : firstPart f (H - unit) = 0 := by linarith
  have hXS : secondPart f (τ • unit - H) = 0 := by linarith
  have hZS : thirdPart f (H - congruence T H) = 0 := by linarith
  let r := (scalarPart f)⁻¹
  have hr : 0 ≤ r := (inv_pos.mpr hlam).le
  refine ⟨{
    X := r • secondPart f
    Y := r • firstPart f
    Z := r • thirdPart f
    X_positive := ?_
    Y_positive := ?_
    Z_positive := ?_
    X_unit := ?_
    Y_unit := ?_
    balance := ?_
    Y_slack := ?_
    X_slack := ?_
    Z_slack := ?_ }⟩
  · intro J hJ
    exact mul_nonneg hr (hX J hJ)
  · intro J hJ
    exact mul_nonneg hr (hY J hJ)
  · intro J hJ
    exact mul_nonneg hr (hZ J hJ)
  · simp only [smul_apply, smul_eq_mul, he, r, inv_mul_cancel₀ hlam.ne']
  · simp only [smul_apply, smul_eq_mul, hYE, r, ← mul_assoc,
      inv_mul_cancel₀ hlam.ne', one_mul]
  · intro J
    simpa only [smul_apply, smul_eq_mul, mul_sub] using congrArg (r * ·) (hbal J)
  · simp only [smul_apply, smul_eq_mul, hYS, mul_zero]
  · simp only [smul_apply, smul_eq_mul, hXS, mul_zero]
  · simp only [smul_apply, smul_eq_mul, hZS, mul_zero]

end Separation

section Riesz

open scoped InnerProductSpace ComplexOrder

open Boundary

theorem exists_trace_representative {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X.IsHermitian ∧
      ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re := by
  let F := f.comp (hermHSCoordinate n).toContinuousLinearMap
  let u := (InnerProductSpace.toDual ℝ (hermHS n)).symm F
  refine ⟨ofHS u.val, (mem_hermHS _).mp u.property, ?_⟩
  intro J
  let v : hermHS n := ⟨toHS J.val, (mem_hermHS _).mpr J.property⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v) (y := F)
  have he : hermHSCoordinate n v = J := by apply Subtype.ext; rfl
  change ⟪u, v⟫_ℝ = f (hermHSCoordinate n v) at h
  rw [he] at h
  rw [← h]
  change ⟪u.val, toHS J.val⟫_ℝ = _
  nth_rw 1 [← toHS_ofHS u.val]
  rw [real_inner_toHS, ((mem_hermHS _).mp u.property).eq]

theorem trace_representative_posSemidef {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ)
    (hf : ∀ J, 0 ≤ J → 0 ≤ f J)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (hrep : ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re) :
    X.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hX
  intro x
  let J : Herm (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨Matrix.vecMulVec x (star x), (Matrix.posSemidef_vecMulVec_self_star x).isHermitian⟩
  have hJ : (0 : Herm (Matrix (Fin n) (Fin n) ℂ)) ≤ J :=
    (Matrix.posSemidef_vecMulVec_self_star x).nonneg
  have h := hf J hJ
  rw [hrep] at h
  change 0 ≤ (X * Matrix.vecMulVec x (star x)).trace.re at h
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at h
  exact Complex.nonneg_iff.mpr ⟨h, (hX.im_star_dotProduct_mulVec_self x).symm⟩

theorem exists_positive_trace_representative {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ)
    (hf : ∀ J, 0 ≤ J → 0 ≤ f J) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef ∧
      ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re := by
  obtain ⟨X,hX,hrep⟩ := exists_trace_representative f
  exact ⟨X, trace_representative_posSemidef f hf X hX hrep, hrep⟩

end Riesz

end CrouzeixHilbert.Endpoint

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realization. -/

noncomputable section

open Set Filter

open scoped Topology InnerProductSpace

namespace CrouzeixHilbert.Realization

section Gram

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_isometryEquiv_of_norm_eq (A B : E →ₗ[ℂ] V)
    (h : ∀ x, ‖A x‖ = ‖B x‖) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (A x) = B x := by
  have hk : A.ker ≤ B.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [← h x, LinearMap.mem_ker.mp hx, norm_zero]
  let l : A.range →ₗ[ℂ] V := (A.ker.liftQ B hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hl (x : E) : l ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    simp [l]
  let L : A.range →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl]
        exact (h x).symm }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, ?_⟩
  intro x
  change L.extend (A x) = B x
  rw [show A x = (⟨A x, LinearMap.mem_range_self A x⟩ : A.range) from rfl,
    LinearIsometry.extend_apply]
  exact hl x

end Gram

section Pair

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace E] [CompleteSpace H]

theorem adjoint_pairL (A B : E →L[ℂ] H) :
    ContinuousLinearMap.adjoint (pairL A B) =
      rowL (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint B) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro y x
  simp only [rowL_apply, pairL_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply]
  rfl

end Pair

section Colligation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

theorem exists_colligation (D L X Y : H →L[ℂ] H)
    (h : L * star L + Y * star Y = (D * L) * star (D * L) + X * star X) :
    ∃ U : SumSpace H ≃ₗᵢ[ℂ] SumSpace H,
      ∀ v, rowL L Y v = rowL (D * L) X (U v) := by
  let A := pairL (star (D * L)) (star X)
  let B := pairL (star L) (star Y)
  have hg : (ContinuousLinearMap.adjoint A).comp A =
      (ContinuousLinearMap.adjoint B).comp B := by
    simp only [A, B, adjoint_pairL]
    ext x
    simpa only [ContinuousLinearMap.comp_apply, pairL_apply, WithLp.toLp_fst,
      WithLp.toLp_snd, rowL_apply, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.star_eq_adjoint, add_apply,
      mul_apply_eq_comp] using (DFunLike.congr_fun h x).symm
  obtain ⟨U, hU⟩ := exists_isometryEquiv_of_norm_eq A.toLinearMap B.toLinearMap (fun x => by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖A x‖ ^ 2 = ‖B x‖ ^ 2
    rw [A.apply_norm_sq_eq_inner_adjoint_left, B.apply_norm_sq_eq_inner_adjoint_left, hg])
  use U.symm
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp A = B := by
    ext x
    exact hU x
  have he' := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp, U.adjoint_eq_symm] at he'
  have he'' : (rowL (D * L) X).comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      rowL L Y := by
    simpa only [A, B, adjoint_pairL, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using he'
  intro v
  exact (DFunLike.congr_fun he'' v).symm

end Colligation

section Transfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace Colligation

theorem apply_pair (C : Colligation H) (v e : H) :
    C.unitary (WithLp.toLp 2 (v,e)) =
      WithLp.toLp 2 (C.a v + C.b e, C.c v + C.d e) := by
  have he : WithLp.toLp 2 (v,e) = pairL (1 : H →L[ℂ] H) 0 v + pairL 0 1 e := by
    apply WithLp.equiv 2 (H × H) |>.injective
    simp only [pairL_apply, one_apply_eq_self, zero_apply, WithLp.equiv_apply,
      WithLp.ofLp_add]
    ext <;> simp
  rw [he, map_add]
  apply WithLp.equiv 2 (H × H) |>.injective
  rfl

theorem energy (C : Colligation H) (v e : H) :
    ‖C.a v + C.b e‖ ^ 2 + ‖C.c v + C.d e‖ ^ 2 = ‖v‖ ^ 2 + ‖e‖ ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2) (C.unitary.norm_map (WithLp.toLp 2 (v,e)))
  rw [C.apply_pair, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2] at h
  exact h

theorem norm_a_le (C : Colligation H) : ‖C.a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := C.energy v 0
  simp only [map_zero, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  simp only [one_mul]
  nlinarith [norm_nonneg v, norm_nonneg (C.a v), sq_nonneg ‖C.c v‖]

variable [CompleteSpace H]

theorem one_sub_isUnit (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit (1 - z • C.a) := by
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left C.norm_a_le (norm_nonneg z)).trans_lt
    (by simpa only [mul_one] using hz)

theorem transfer_energy (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) (e : H) :
    ‖e‖ ^ 2 - ‖C.transfer z e‖ ^ 2 = (1 - ‖z‖ ^ 2) *
      ‖Ring.inverse (1 - z • C.a) (C.b e)‖ ^ 2 := by
  let v := Ring.inverse (1 - z • C.a) (C.b e)
  have hv : v - z • C.a v = C.b e := by
    have h := DFunLike.congr_fun
      (Ring.mul_inverse_cancel (1 - z • C.a) (C.one_sub_isUnit hz)) (C.b e)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] using h
  have ht : C.c (z • v) + C.d e = C.transfer z e := by
    simp only [transfer, add_apply, smul_apply, mul_apply_eq_comp, map_smul, v, add_comm]
  have h := C.energy (z • v) e
  rw [ht, map_smul, show z • C.a v + C.b e = v by rw [← hv]; abel,
    norm_smul, mul_pow] at h
  nlinarith

theorem norm_transfer_le (C : Colligation H) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖C.transfer z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro e
  have h := C.transfer_energy hz e
  have hz' : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpos := mul_nonneg hz' (sq_nonneg ‖Ring.inverse (1 - z • C.a) (C.b e)‖)
  simp only [one_mul]
  nlinarith [norm_nonneg e, norm_nonneg (C.transfer z e)]

end Colligation

variable [FiniteDimensional ℂ H]

theorem exists_colligation_data (D L X Y : H →L[ℂ] H)
    (h : L * star L + Y * star Y = (D * L) * star (D * L) + X * star X) :
    ∃ C : Colligation H, L = D * L * C.a + X * C.c ∧
      Y = D * L * C.b + X * C.d := by
  obtain ⟨U, hU⟩ := exists_colligation D L X Y h
  refine ⟨⟨U⟩, ?_, ?_⟩
  · ext v
    have h := hU (WithLp.toLp 2 (v,0))
    simpa only [rowL_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, add_zero, add_apply, mul_apply_eq_comp, Colligation.a, Colligation.c,
      ContinuousLinearMap.comp_apply, pairL_apply, one_apply_eq_self, zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h
  · ext v
    have h := hU (WithLp.toLp 2 (0,v))
    simpa only [rowL_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, zero_add, add_apply, mul_apply_eq_comp, Colligation.b, Colligation.d,
      ContinuousLinearMap.comp_apply, pairL_apply, one_apply_eq_self, zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h

end Transfer

end CrouzeixHilbert.Realization

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MatrixEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix Endpoint. -/

noncomputable section

open Set Filter

open scoped InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace CrouzeixHilbert.Endpoint

open Boundary

theorem eq_zero_of_trace_pair_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian)
    (h : ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), (X * J.val).trace.re = 0) : X = 0 := by
  have hh := h ⟨X, hX⟩
  change (X * X).trace.re = 0 at hh
  nth_rw 1 [← hX.eq] at hh
  rw [trace_conjTranspose_mul_re] at hh
  have hn : ‖toHS X‖ = 0 := (sq_eq_zero_iff).mp hh
  have hz := norm_eq_zero.mp hn
  exact congrArg ofHS hz

theorem exists_matrixCertificate {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : spectralRadius ℂ T < 1) {τ : ℝ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Metric.Feasible T τ H)
    (hmin : ∀ s J, Metric.Feasible T s J → τ ≤ s) :
    Nonempty (MatrixCertificate T τ H) := by
  obtain ⟨C⟩ := exists_dualCertificate T hT ⟨H, hH.selfAdjoint⟩ hH hmin
  obtain ⟨X, hX, hx⟩ := exists_positive_trace_representative C.X C.X_positive
  obtain ⟨Y, hY, hy⟩ := exists_positive_trace_representative C.Y C.Y_positive
  obtain ⟨Z, hZ, hz⟩ := exists_positive_trace_representative C.Z C.Z_positive
  refine ⟨⟨X,Y,Z,hX,hY,hZ,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa only [hx, unit_val, mul_one] using C.X_unit
  · simpa only [hy, unit_val, mul_one] using C.Y_unit
  · apply sub_eq_zero.mp
    apply eq_zero_of_trace_pair_zero _
      ((hX.isHermitian.sub hY.isHermitian).sub
      (hZ.isHermitian.sub (hZ.mul_mul_conjTranspose_same T).isHermitian))
    intro J
    have h := C.balance J
    rw [hx, hy, hz, hz] at h
    change (X * J.val).trace.re - (Y * J.val).trace.re =
      (Z * J.val).trace.re - (Z * (Tᴴ * J.val * T)).trace.re at h
    have he : (Z * (Tᴴ * J.val * T)).trace = (T * Z * Tᴴ * J.val).trace := by
      rw [Matrix.trace_mul_cycle', ← mul_assoc, ← mul_assoc]
    rw [he] at h
    simp only [sub_mul, Matrix.trace_sub, Complex.sub_re]
    linarith
  · have h := C.Y_slack
    rw [hy] at h
    exact h
  · have h := C.X_slack
    rw [hx] at h
    exact h
  · have h := C.Z_slack
    rw [hz] at h
    exact h

theorem trace_mul_eq_norm_sqrt_sq {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (B * C).trace.re = ‖toHS (CFC.sqrt C * CFC.sqrt B)‖ ^ 2 := by
  have hBS : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).isHermitian.eq
  have hCS : (CFC.sqrt C)ᴴ = CFC.sqrt C :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C)).isHermitian.eq
  rw [← trace_conjTranspose_mul_re, Matrix.conjTranspose_mul, hBS, hCS]
  have he : CFC.sqrt B * CFC.sqrt C * (CFC.sqrt C * CFC.sqrt B) =
      CFC.sqrt B * C * CFC.sqrt B := by
    calc
      _ = CFC.sqrt B * (CFC.sqrt C * CFC.sqrt C) * CFC.sqrt B := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [he, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self B hB.nonneg]

theorem mul_sqrt_eq_zero_of_trace_mul_eq_zero {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (h : (B * C).trace.re = 0) : C * CFC.sqrt B = 0 := by
  rw [trace_mul_eq_norm_sqrt_sq B C hB hC] at h
  have hz : CFC.sqrt C * CFC.sqrt B = 0 := by
    have hn : ‖toHS (CFC.sqrt C * CFC.sqrt B)‖ = 0 := sq_eq_zero_iff.mp h
    exact congrArg ofHS (norm_eq_zero.mp hn)
  rw [← CFC.sqrt_mul_sqrt_self C hC.nonneg, mul_assoc, hz, mul_zero]

theorem sqrt_mul_eigen {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H X : A) (hH : 0 ≤ H) {t : ℝ} (ht : 0 < t) (hX : H * X = (t ^ 2) • X) :
    CFC.sqrt H * X = t • X := by
  have hu : IsUnit (CFC.sqrt H + t • (1 : A)) :=
    (IsStrictlyPositive.nonneg_add (CFC.sqrt_nonneg H)
      (IsStrictlyPositive.smul ht isStrictlyPositive_one)).isUnit
  have hz : (CFC.sqrt H + t • (1 : A)) * (CFC.sqrt H * X - t • X) = 0 := by
    calc
      _ = CFC.sqrt H * CFC.sqrt H * X - (t * t) • X := by
        simp only [add_mul, mul_sub, mul_smul_comm, smul_mul_assoc, one_mul, mul_assoc]
        module
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self H hH, ← sq, hX, sub_self]
  have he := congrArg (Ring.inverse (CFC.sqrt H + t • (1 : A)) * ·) hz
  rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, mul_zero] at he
  exact sub_eq_zero.mp he

theorem gram_congruence {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) {t : ℝ} (hX : S * X = t • X) :
    S * (X * Xᴴ) * S = (t ^ 2) • (X * Xᴴ) := by
  have hXR : Xᴴ * S = t • Xᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hS.eq] using
      congrArg Matrix.conjTranspose hX
  calc
    _ = (S * X) * (Xᴴ * S) := by simp only [mul_assoc]
    _ = _ := by rw [hX, hXR, smul_mul_assoc, mul_smul_comm, smul_smul, sq]

theorem exists_endpointFactors {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    {κ : ℝ} (hκ : 1 < κ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Metric.Feasible T (κ ^ 2) H) (C : MatrixCertificate T (κ ^ 2) H) :
    Nonempty (EndpointFactors T κ H) := by
  let S := CFC.sqrt H
  let R := Ring.inverse S
  let X := CFC.sqrt C.X
  let Y₀ := CFC.sqrt C.Y
  let Y := κ⁻¹ • Y₀
  let Q := (κ⁻¹ ^ 2) • (S * C.Z * S)
  have hk : 0 < κ := zero_lt_one.trans hκ
  have hS : S.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg H)).isHermitian
  have hX : X.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C.X)).isHermitian
  have hY : Y₀.IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C.Y)).isHermitian
  have hXX : X * Xᴴ = C.X := by rw [hX.eq]; exact CFC.sqrt_mul_sqrt_self _ C.X_positive.nonneg
  have hYY : Y₀ * Y₀ᴴ = C.Y := by rw [hY.eq]; exact CFC.sqrt_mul_sqrt_self _ C.Y_positive.nonneg
  have hHX : H * X = κ ^ 2 • X := by
    have hp : (κ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℂ) - H).PosSemidef := by
      apply Matrix.nonneg_iff_posSemidef.mp
      apply sub_nonneg.mpr
      simpa only [Algebra.algebraMap_eq_smul_one] using hH.upper
    have h := mul_sqrt_eq_zero_of_trace_mul_eq_zero _ _ C.X_positive hp C.X_slack
    rw [sub_mul, smul_mul_assoc, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hHY : H * Y₀ = Y₀ := by
    have hp : (H - 1).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hH.lower)
    have h := mul_sqrt_eq_zero_of_trace_mul_eq_zero _ _ C.Y_positive hp C.Y_slack
    rw [sub_mul, one_mul] at h
    exact sub_eq_zero.mp h
  have hSX : S * X = κ • X := sqrt_mul_eigen H X hH.nonneg hk hHX
  have hSY : S * Y₀ = Y₀ := by
    simpa only [one_smul] using sqrt_mul_eigen H Y₀ hH.nonneg zero_lt_one
      (by simpa only [one_pow, one_smul] using hHY)
  have hnormX : ‖toHS X‖ ^ 2 = 1 := by
    rw [← trace_conjTranspose_mul_re, hX.eq]
    nth_rw 2 [← hX.eq]
    rw [hXX, C.X_trace]
  have hnormY₀ : ‖toHS Y₀‖ ^ 2 = κ ^ 2 := by
    rw [← trace_conjTranspose_mul_re, hY.eq]
    nth_rw 2 [← hY.eq]
    rw [hYY, C.Y_trace]
  have hnormY : ‖toHS Y‖ ^ 2 = 1 := by
    change ‖hsEquiv n (κ⁻¹ • Y₀)‖ ^ 2 = 1
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le),
      mul_pow, hsEquiv_apply, hnormY₀]
    field_simp
  have hGramX : X * Xᴴ = (κ⁻¹ ^ 2) • (S * C.X * S) := by
    rw [← hXX, gram_congruence S X hS hSX, smul_smul]
    simp [hk.ne']
  have hGramY : Y * Yᴴ = (κ⁻¹ ^ 2) • (S * C.Y * S) := by
    have hs : S * (Y₀ * Y₀ᴴ) * S = Y₀ * Y₀ᴴ := by
      simpa only [one_smul, one_pow] using gram_congruence S Y₀ hS
        (show S * Y₀ = (1 : ℝ) • Y₀ by simpa only [one_smul])
    rw [← hYY, hs]
    simp only [Y, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc,
      mul_smul_comm, smul_smul, sq]
  have hQ : Q.PosSemidef := by
    have hs := C.Z_positive.mul_mul_conjTranspose_same S
    rw [hS.eq] at hs
    exact Matrix.nonneg_iff_posSemidef.mp (smul_nonneg (sq_nonneg (κ⁻¹)) hs.nonneg)
  have hu : IsUnit S := hH.isStrictlyPositive.isUnit_cfcSqrt H
  have hRS : R * S = 1 := Ring.inverse_mul_cancel S hu
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hu
  have hR : R.IsHermitian := (IsSelfAdjoint.of_nonneg
    ((CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hu).mpr (CFC.sqrt_nonneg H))).isHermitian
  have hconj : (S * T * R) * (S * C.Z * S) * (S * T * R)ᴴ = S * (T * C.Z * Tᴴ) * S := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hR.eq]
    calc
      _ = (S * T) * (R * S) * C.Z * (S * R) * (Tᴴ * S) := by noncomm_ring
      _ = _ := by rw [hRS, hSR, mul_one, mul_one]; simp only [mul_assoc]
  refine ⟨⟨X,Y,Q,?_,?_,hSX,?_,?_,hQ,?_⟩⟩
  · nlinarith [norm_nonneg (toHS X)]
  · nlinarith [norm_nonneg (toHS Y)]
  · change S * Y = Y
    simp only [Y, mul_smul_comm, hSY]
  · have hXR : Xᴴ * S = κ • Xᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hS.eq] using
        congrArg Matrix.conjTranspose hSX
    have he : (κ - 1) • (Xᴴ * Y) = 0 := by
      rw [sub_smul, one_smul, ← smul_mul_assoc, ← hXR, mul_assoc]
      simp only [Y, mul_smul_comm, hSY, sub_self]
    exact (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hκ.ne')
  · change X * Xᴴ - Y * Yᴴ = Q - (S * T * R) * Q * (S * T * R)ᴴ
    rw [hGramX, hGramY, ← smul_sub, ← sub_mul, ← mul_sub, C.balance]
    simp only [mul_sub, sub_mul, smul_sub, Q, mul_smul_comm, smul_mul_assoc, hconj]

theorem endpointFactors_of_minimum {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : spectralRadius ℂ T < 1) {κ : ℝ} (hκ : 1 < κ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : Metric.Feasible T (κ ^ 2) H)
    (hmin : ∀ s J, Metric.Feasible T s J → κ ^ 2 ≤ s) :
    Nonempty (EndpointFactors T κ H) := by
  obtain ⟨C⟩ := exists_matrixCertificate T hT H hH hmin
  exact exists_endpointFactors T hκ H hH C

end CrouzeixHilbert.Endpoint

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic continuity, pole-free rational evaluation, and tensor norm bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rational_holomorphic_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : ∀ z ∈ U, ∀ i j, (R i j).denom.eval z ≠ 0 := by
    intro z hz i j
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn
      (fun z hz => hne z hz i j)

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Transfer. -/

noncomputable section

open Set Filter

open scoped Topology Matrix Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Realization

theorem ratFunc_denom_ne_zero_on_closedDisk (r : RatFunc ℂ) (C : ℝ)
    (h : ∀ z : ℂ, ‖z‖ < 1 → ‖RatFunc.eval (RingHom.id ℂ) z r‖ ≤ C) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → r.denom.eval z ≠ 0 := by
  let Z : Set ℂ := {z | r.denom.eval z = 0}
  have hf : Z.Finite := Polynomial.finite_setOfPred_isRoot r.denom_ne_zero
  have hd : Dense (Zᶜ) := by
    exact ((dense_univ (X := ℂ)).sdiff_finite hf).mono (fun _ hz => hz.2)
  let S : Set ℂ := {z | ‖r.num.eval z‖ ≤ C * ‖r.denom.eval z‖}
  have hS : IsClosed S := isClosed_le r.num.continuous.norm (r.denom.continuous.norm.const_mul C)
  have hs : Zᶜ ∩ Metric.ball (0 : ℂ) 1 ⊆ S := by
    rintro z ⟨hz, hz'⟩
    have hn : r.denom.eval z ≠ 0 := hz
    have hh := h z (by simpa only [Metric.mem_ball, dist_zero_right] using hz')
    simpa only [S, mem_ofPred_eq, RatFunc.eval, Polynomial.eval₂_id, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hn)] using hh
  have hb : Metric.ball (0 : ℂ) 1 ⊆ S := by
    intro z hz
    apply closure_minimal hs hS
    exact Metric.isOpen_ball.closure_inter ⟨hd z, hz⟩
  have hc : Metric.closedBall (0 : ℂ) 1 ⊆ S := by
    simpa only [closure_ball (0 : ℂ) one_ne_zero] using closure_minimal hb hS
  intro z hz hn
  have hp := hc (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  change ‖r.num.eval z‖ ≤ C * ‖r.denom.eval z‖ at hp
  rw [hn, norm_zero, mul_zero] at hp
  have hp' : r.num.eval z = 0 := norm_le_zero_iff.mp hp
  have he := Polynomial.aeval_ne_zero_of_isCoprime r.isCoprime_num_denom z
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, hp', hn, ne_eq,
    not_true_eq_false, or_self] at he

theorem ratFunc_eval_quotient (p q : Polynomial ℂ) {z : ℂ} (hq : q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z ((algebraMap _ (RatFunc ℂ)) p /
      (algebraMap _ (RatFunc ℂ)) q) = p.eval z / q.eval z := by
  let r : RatFunc ℂ := (algebraMap _ _) p / (algebraMap _ _) q
  have hq' : q ≠ 0 := by rintro rfl; simp at hq
  have hd : r.denom.eval z ≠ 0 := by
    intro hd
    obtain ⟨b, hb⟩ := RatFunc.denom_div_dvd p q
    apply hq
    rw [hb, Polynomial.eval_mul, hd, zero_mul]
  have he := congrArg (Polynomial.eval z)
    ((RatFunc.num_mul_eq_mul_denom_iff hq').mpr (show r = _ from rfl))
  simp only [Polynomial.eval_mul] at he
  change r.num.eval z / r.denom.eval z = _
  exact (div_eq_div_iff hd hq).mpr he

theorem map_ringInverse_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  calc
    _ = (f (Ring.inverse x) * f x) * Ring.inverse (f x) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ (hx.map f), mul_one]
    _ = _ := by rw [← map_mul, Ring.inverse_mul_cancel _ hx, map_one, one_mul]

section RationalMatrices

variable {n : ℕ}

lemma mapMatrix_scalar {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (M : Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (r • M) = f r • f.mapMatrix M := by
  ext i j
  exact map_mul f r (M i j)

lemma eval_constantMatrix (z : ℂ) (M : Coeff n) :
    (Polynomial.evalRingHom z).mapMatrix (M.map Polynomial.C) = M := by
  ext i j
  exact Polynomial.eval_C

lemma eval_pencil (z : ℂ) (a : Coeff n) :
    (Polynomial.evalRingHom z).mapMatrix (pencil a) = 1 - z • a := by
  rw [pencil, map_sub, map_one, mapMatrix_scalar, eval_constantMatrix]
  simp

lemma eval_transferDenominator (a : Coeff n) (z : ℂ) :
    (transferDenominator a).eval z = (1 - z • a).det := by
  exact ((Polynomial.evalRingHom z).map_det (pencil a)).trans
    (congrArg Matrix.det (eval_pencil z a))

lemma eval_transferNumerator (a b c d : Coeff n) (z : ℂ) :
    (Polynomial.evalRingHom z).mapMatrix (transferNumerator a b c d) =
      (1 - z • a).det • d + z • (c * (1 - z • a).adjugate * b) := by
  simp only [transferNumerator, map_add, mapMatrix_scalar, map_mul,
    eval_constantMatrix, RingHom.map_adjugate, eval_pencil]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, eval_transferDenominator]

lemma matrix_inverse_adjugate (M : Coeff n) :
    Ring.inverse M = M.det⁻¹ • M.adjugate := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def, Ring.inverse_eq_inv]

theorem transferRational_eq (a b c d : Coeff n) {z : ℂ}
    (hz : IsUnit (1 - z • a)) :
    matrixRationalFunction (transferRational a b c d) z =
      d + z • (c * Ring.inverse (1 - z • a) * b) := by
  have hdet : (1 - z • a).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hz)
  have hq : (transferDenominator a).eval z ≠ 0 := by
    rwa [eval_transferDenominator]
  ext i j
  rw [matrixRationalFunction, transferRational, ratFunc_eval_quotient _ _ hq]
  have he := congrArg (fun M : Coeff n => M i j) (eval_transferNumerator a b c d z)
  change (transferNumerator a b c d i j).eval z = _ at he
  rw [he, eval_transferDenominator, matrix_inverse_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    mul_smul_comm, smul_mul_assoc]
  field_simp

end RationalMatrices

namespace Colligation

variable {n : ℕ}

theorem rational_eq_transfer (C : Colligation (EuclideanSpace ℂ (Fin n)))
    {z : ℂ} (hz : ‖z‖ < 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (matrixRationalFunction C.rational z) = C.transfer z := by
  have hu : IsUnit (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a) := by
    simpa only [map_sub, map_one, map_smul] using
      (C.one_sub_isUnit hz).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
  rw [rational, transferRational_eq _ _ _ _ hu]
  simp only [map_add, map_smul, map_mul, StarAlgEquiv.apply_symm_apply]
  have hi : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
      (Ring.inverse (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a)) =
        Ring.inverse ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
          (1 - z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a)) :=
    map_ringInverse_of_isUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toRingHom hu
  rw [hi]
  simp only [map_sub, map_one, map_smul, StarAlgEquiv.apply_symm_apply, transfer]

theorem norm_rational_le_openDisk (C : Colligation (EuclideanSpace ℂ (Fin n)))
    {z : ℂ} (hz : ‖z‖ < 1) : ‖matrixRationalFunction C.rational z‖ ≤ 1 := by
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (matrixRationalFunction C.rational z)‖ ≤ 1
  rw [C.rational_eq_transfer hz]
  exact C.norm_transfer_le hz

theorem rational_polesOutside (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    PolesOutside (Metric.closedBall (0 : ℂ) 1) C.rational := by
  intro i j z hz
  apply ratFunc_denom_ne_zero_on_closedDisk (C.rational i j) ‖entryMap i j‖ ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  intro w hw
  change ‖entryMap i j (matrixRationalFunction C.rational w)‖ ≤ _
  calc
    _ ≤ ‖entryMap i j‖ * ‖matrixRationalFunction C.rational w‖ :=
      (entryMap i j).le_opNorm _
    _ ≤ ‖entryMap i j‖ * 1 :=
      mul_le_mul_of_nonneg_left (C.norm_rational_le_openDisk hw) (norm_nonneg _)
    _ = _ := mul_one _

theorem rational_extension (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction C.rational)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction C.rational z‖ ≤ 1) := by
  obtain ⟨U, hU, hK, hF⟩ := rational_holomorphic_neighborhood C.rational C.rational_polesOutside
  refine ⟨⟨U,hU,hK,hF⟩, ?_⟩
  have hc : ContinuousOn (fun z => ‖matrixRationalFunction C.rational z‖)
      (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact (hF.continuousOn.mono hK).norm
  intro z hz
  apply le_on_closure (s := Metric.ball (0 : ℂ) 1)
    (fun w hw => C.norm_rational_le_openDisk
      (by simpa only [Metric.mem_ball, dist_zero_right] using hw)) hc continuousOn_const
  simpa only [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right] using hz

end Colligation

section Transpose

variable {n : ℕ}

lemma norm_conjugateVector (x : EuclideanSpace ℂ (Fin n)) :
    ‖conjugateVector x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, conjugateVector, norm_star]

lemma conjugate_apply (M : Coeff n) (x : EuclideanSpace ℂ (Fin n)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (M.map star) x =
      conjugateVector ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M (conjugateVector x)) := by
  apply WithLp.equiv 2 (Fin n → ℂ) |>.injective
  ext i
  simp only [WithLp.equiv_apply, Matrix.ofLp_toEuclideanCLM, conjugateVector,
    Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma norm_conjugateMatrix_le (M : Coeff n) : ‖M.map star‖ ≤ ‖M‖ := by
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (M.map star)‖ ≤ ‖M‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
  intro x
  rw [conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector, ← Matrix.cstar_norm_def] using
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) M).le_opNorm (conjugateVector x)

theorem norm_matrix_transpose (M : Coeff n) : ‖Mᵀ‖ = ‖M‖ := by
  have h (N : Coeff n) : ‖N.map star‖ = ‖N‖ := by
    apply le_antisymm (norm_conjugateMatrix_le N)
    have hh := norm_conjugateMatrix_le (N.map star)
    have he : (N.map star).map star = N := by ext i j; exact star_star _
    rwa [he] at hh
  rw [← h Mᵀ]
  exact Matrix.l2_opNorm_conjTranspose M

namespace Colligation

theorem diskExtremal_function (C : Colligation (EuclideanSpace ℂ (Fin n))) (z : ℂ) :
    matrixRationalFunction C.diskExtremal z = (matrixRationalFunction C.rational z)ᵀ := rfl

theorem diskExtremal_polesOutside (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    PolesOutside (Metric.closedBall (0 : ℂ) 1) C.diskExtremal :=
  fun i j => C.rational_polesOutside j i

theorem diskExtremal_extension (C : Colligation (EuclideanSpace ℂ (Fin n))) :
    (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction C.diskExtremal)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction C.diskExtremal z‖ ≤ 1) := by
  refine ⟨rational_holomorphic_neighborhood C.diskExtremal C.diskExtremal_polesOutside, ?_⟩
  intro z hz
  rw [C.diskExtremal_function, norm_matrix_transpose]
  exact C.rational_extension.2 z hz

end Colligation

end Transpose

end CrouzeixHilbert.Realization

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Vectorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vectorization. -/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Realization

@[simp] theorem norm_vectorization {n : ℕ} (X : Coeff n) :
    ‖vectorization X‖ = ‖Boundary.toHS X‖ := by
  rw [← norm_matrixAmplificationCoordinates n n, vectorization_coordinates]

theorem kronecker_toHS {n : ℕ} (A B X : Coeff n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ B)) (Boundary.toHS X) =
      Boundary.toHS (A * X * Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Boundary.toHS,
    WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorOperator_vectorization {n : ℕ} (A B X : Coeff n) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) A) B (vectorization X) =
      vectorization (A * X * Bᵀ) := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_tensorOperator, vectorization_coordinates,
    vectorization_coordinates, kronecker_toHS]

namespace Endpoint

open Boundary

theorem EndpointFactors.exists_colligation {n : ℕ} {T H : Coeff n} {κ : ℝ}
    (E : EndpointFactors T κ H) :
    ∃ C : Realization.Colligation (EuclideanSpace ℂ (Fin n)),
      CFC.sqrt E.Q =
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * CFC.sqrt E.Q *
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a +
            E.X * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.c ∧
      E.Y = (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * CFC.sqrt E.Q *
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.b +
          E.X * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.d := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let D := CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)
  let L := CFC.sqrt E.Q
  have hL : L * Lᴴ = E.Q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg E.Q)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self E.Q E.Q_positive.nonneg
  have hbal : L * Lᴴ + E.Y * E.Yᴴ = (D * L) * (D * L)ᴴ + E.X * E.Xᴴ := by
    rw [Matrix.conjTranspose_mul]
    have he : (D * L) * (Lᴴ * Dᴴ) = D * E.Q * Dᴴ := by
      rw [mul_assoc D L, ← mul_assoc L, hL, ← mul_assoc]
    rw [he, hL]
    have h := E.balance
    change E.X * E.Xᴴ - E.Y * E.Yᴴ = E.Q - D * E.Q * Dᴴ at h
    apply sub_eq_sub_iff_add_eq_add.mp at h
    rw [add_comm] at h
    exact h.symm
  obtain ⟨C, hC, hY⟩ := Realization.exists_colligation_data (e D) (e L) (e E.X) (e E.Y)
    (by simpa only [← map_mul, ← map_star, ← map_add, Matrix.star_eq_conjTranspose]
        using congrArg e hbal)
  refine ⟨C, ?_, ?_⟩
  · simpa only [map_add, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm hC
  · simpa only [map_add, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm hY

end Endpoint

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BlockPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block Polynomial. -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker TensorProduct

namespace CrouzeixHilbert

theorem blockPolynomialEval_smul_constant {n m : ℕ} (D : Coeff n)
    (p : Polynomial ℂ) (B : Coeff m) :
    blockPolynomialEval D (p • B.map Polynomial.C) = Polynomial.aeval D p ⊗ₖ B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [blockPolynomialEval_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_mul, Polynomial.aeval_C, Matrix.kronecker_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, Matrix.smul_apply]
  exact mul_comm _ _

@[simp] theorem blockPolynomialEval_constant {n m : ℕ} (D : Coeff n) (B : Coeff m) :
    blockPolynomialEval D (B.map Polynomial.C) = 1 ⊗ₖ B := by
  simpa only [one_smul, map_one] using blockPolynomialEval_smul_constant D 1 B

theorem blockPolynomialEval_scalar {n m : ℕ} (D : Coeff n) (p : Polynomial ℂ) :
    blockPolynomialEval (m := m) D (p • 1) = Polynomial.aeval D p ⊗ₖ 1 := by
  have he : (1 : Coeff m).map Polynomial.C = 1 :=
    (Polynomial.C.mapMatrix).map_one
  rw [← he, blockPolynomialEval_smul_constant]

theorem blockPolynomialEval_commute {n m : ℕ} (D : Coeff n) (p : Polynomial ℂ)
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) :
    Commute (Polynomial.aeval D p ⊗ₖ (1 : Coeff m)) (blockPolynomialEval D M) := by
  rw [← blockPolynomialEval_scalar]
  apply Commute.map _ (blockPolynomialEval D)
  show (p • (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ))) * M = M * (p • 1)
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem blockPolynomialEval_expansion {n m : ℕ} (D : Coeff n)
    (P : Matrix (Fin m) (Fin m) (Polynomial ℂ)) :
    blockPolynomialEval D P =
      ∑ i, ∑ j, Polynomial.aeval D (P i j) ⊗ₖ Matrix.single i j 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

namespace Realization

theorem aeval_reduced_denom_isUnit {A : Type*} [Ring A] [Algebra ℂ A]
    (D : A) (p q : Polynomial ℂ) (hq : IsUnit (Polynomial.aeval D q)) :
    IsUnit (Polynomial.aeval D
      ((algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q).denom) := by
  let r := (algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q
  obtain ⟨b, hb⟩ := RatFunc.denom_div_dvd p q
  have hc := (Commute.all r.denom b).map (Polynomial.aeval D)
  apply (hc.isUnit_mul_iff.mp ?_).1
  rw [← map_mul]
  exact hb ▸ hq

theorem aeval_quotient_cancel {A : Type*} [Ring A] [Algebra ℂ A]
    (D : A) (p q : Polynomial ℂ) (hq0 : q ≠ 0) (hq : IsUnit (Polynomial.aeval D q)) :
    Polynomial.aeval D q *
      (Polynomial.aeval D ((algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q).num *
        Ring.inverse (Polynomial.aeval D ((algebraMap _ (RatFunc ℂ)) p /
          (algebraMap _ (RatFunc ℂ)) q).denom)) = Polynomial.aeval D p := by
  let r := (algebraMap _ (RatFunc ℂ)) p / (algebraMap _ (RatFunc ℂ)) q
  have hd := aeval_reduced_denom_isUnit D p q hq
  have he := congrArg (Polynomial.aeval D)
    ((RatFunc.num_mul_eq_mul_denom_iff hq0).mpr (show r = _ from rfl))
  simp only [map_mul] at he
  change Polynomial.aeval D q * (Polynomial.aeval D r.num * Ring.inverse _) = _
  rw [← mul_assoc, ((Commute.all q r.num).map (Polynomial.aeval D)).eq,
    he, mul_assoc, Ring.mul_inverse_cancel _ hd, mul_one]

theorem map_ringInverse_equiv {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (x : A) : e (Ring.inverse x) = Ring.inverse (e x) := by
  by_cases hx : IsUnit x
  · exact map_ringInverse_of_isUnit e.toRingHom hx
  · have hy : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa only [RingEquiv.symm_apply_apply] using h.map e.symm
    rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ hy, map_zero]

end Realization

@[simp] theorem rationalEval_matrix {n : ℕ} (D : Coeff n) (r : RatFunc ℂ) :
    rationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D) r =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (rationalBaseMatrix D r) := by
  simp only [rationalEval, rationalBaseMatrix, map_mul,
    Polynomial.aeval_algHom_apply]
  congr 1
  exact (Realization.map_ringInverse_equiv
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toRingEquiv _).symm

theorem matrixAmplificationCoordinates_rationalEval {n m : ℕ}
    (D : Coeff n) (R : RationalMatrix m)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m
      (matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D) R v) =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (blockRationalEval D R)
          (matrixAmplificationCoordinates n m v) := by
  simp only [matrixRationalEval, blockRationalEval, sum_apply, map_sum,
    rationalEval_matrix, matrixAmplificationCoordinates_tensorOperator]

theorem blockRationalEval_denom_cancel {n m : ℕ} (D : Coeff n)
    (P : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (q : Polynomial ℂ)
    (hq0 : q ≠ 0) (hq : IsUnit (Polynomial.aeval D q)) :
    (Polynomial.aeval D q ⊗ₖ (1 : Coeff m)) *
      blockRationalEval D (fun i j => (algebraMap _ (RatFunc ℂ)) (P i j) /
        (algebraMap _ (RatFunc ℂ)) q) = blockPolynomialEval D P := by
  unfold blockRationalEval
  rw [Finset.mul_sum, blockPolynomialEval_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [rationalBaseMatrix, Realization.aeval_quotient_cancel D (P i j) q hq0 hq]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

theorem sub_div_sub_mem_slitPlane {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    (w - a) / (w - b) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hwb : w - b ≠ 0 := by
    intro he
    exact hw ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  let r : ℝ := ((w - a) / (w - b)).re
  have hr : r ≤ 0 := h.1
  have hrc : (r : ℂ) = (w - a) / (w - b) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using h.2.symm
  have hmul : (r : ℂ) * (w - b) = w - a := by rw [hrc, div_mul_cancel₀ _ hwb]
  have hp : 0 < 1 - r := by linarith
  have hpn : (1 - (r : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  apply hw
  refine ⟨(1 - r)⁻¹, -r / (1 - r), inv_nonneg.mpr hp.le,
    div_nonneg (neg_nonneg.mpr hr) hp.le, ?_, ?_⟩
  · field_simp
    ring
  · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    apply (mul_right_cancel₀ hpn)
    field_simp
    linear_combination hmul

theorem SmoothContour.intervalIntegrable_indexIntegrand (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.path '' Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => deriv Γ.path t / (Γ.path t - a))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  apply Γ.smooth.continuous_deriv_one.continuousOn.div
    (Γ.smooth.continuous.sub continuous_const).continuousOn
  intro t ht he
  exact ha ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.index_eq_of_segment_avoids (Γ : SmoothContour) {a b : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Γ.path t ∉ segment ℝ a b) :
    Γ.index a = Γ.index b := by
  have hnza (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ left_mem_segment ℝ a b)
  have hnzb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - b ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnza t ht (sub_eq_zero.mpr he)
  have hb : b ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnzb t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log ((Γ.path t - a) / (Γ.path t - b)))
        (deriv Γ.path t / (Γ.path t - a) - deriv Γ.path t / (Γ.path t - b)) t := by
    have hg := (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
    have he := ((hg.sub_const a).div (hg.sub_const b) (hnzb t ht)).clog_real
      (sub_div_sub_mem_slitPlane (h t ht))
    simp only [Pi.div_apply] at he
    convert! he using 1
    field_simp [hnza t ht, hnzb t ht]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    ((Γ.intervalIntegrable_indexIntegrand ha).sub (Γ.intervalIntegrable_indexIntegrand hb))
  rw [Γ.closed, sub_self, intervalIntegral.integral_sub
    (Γ.intervalIntegrable_indexIntegrand ha) (Γ.intervalIntegrable_indexIntegrand hb)] at he
  unfold SmoothContour.index
  rw [sub_eq_zero.mp he]

theorem SmoothContour.index_eq_zero_of_re_pos (Γ : SmoothContour) {a c : ℂ}
    (hc : c ≠ 0) (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (Γ.path t - a)).re) :
    Γ.index a = 0 := by
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    simpa only [he, mul_zero, Complex.zero_re, lt_self_iff_false] using h t ht
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnz t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log (c * (Γ.path t - a)))
        (deriv Γ.path t / (Γ.path t - a)) t := by
    have he := (((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).const_mul c).clog_real
      (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    simpa only [mul_div_mul_left _ _ hc] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (Γ.intervalIntegrable_indexIntegrand ha)
  rw [Γ.closed, sub_self] at he
  simp only [SmoothContour.index, he, mul_zero]

theorem SmoothContour.index_eq_zero_of_convex (Γ : SmoothContour) {V : Set ℂ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hΓ : Γ.path '' Icc (0 : ℝ) 1 ⊆ V)
    {a : ℂ} (ha : a ∉ V) :
    Γ.index a = 0 := by
  obtain ⟨l, r, hla, hlV⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hV hVc ha
  have hl (z : ℂ) : l z = l 1 * z := by
    calc
      l z = l (z • (1 : ℂ)) := by simp
      _ = z • l 1 := l.map_smul z 1
      _ = l 1 * z := by simp [mul_comm]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (l 1 * (Γ.path t - a)).re := by
    rw [← hl, map_sub, Complex.sub_re]
    exact sub_pos.mpr (hla.trans (hlV _ (hΓ ⟨t, ht, rfl⟩)))
  apply Γ.index_eq_zero_of_re_pos ?_ hp
  intro he
  have := hp 0 ⟨le_rfl, zero_le_one⟩
  simp only [he, zero_mul, Complex.zero_re, lt_self_iff_false] at this

theorem exists_smooth_radial_frontier_approx {V : Set ℂ}
    (hV : Convex ℝ V) (hV0 : V ∈ 𝓝 (0 : ℂ)) (hVb : Bornology.IsBounded V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ → ℝ, ContDiff ℝ 1 q ∧ (∀ z, 0 < q z) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ∃ w ∈ frontier V, dist (q z • z) w < ε := by
  obtain ⟨R, hR, hVR⟩ := hVb.subset_closedBall_lt 0 0
  let r : ℂ → ℝ := fun z => (max R⁻¹ (gauge V z))⁻¹
  have hrp (z : ℂ) : 0 < r z := inv_pos.mpr ((inv_pos.mpr hR).trans_le (le_max_left _ _))
  have hrc : Continuous r :=
    (continuous_const.max (continuous_gauge hV hV0)).inv₀ (fun z => ((inv_pos.mpr hR).trans_le (le_max_left _ _)).ne')
  obtain ⟨q, hq, hqr, -⟩ := hrc.exists_contDiff_approx 1
    (continuous_const.min (hrc.div_const 2)) (fun z => lt_min hε (half_pos (hrp z)))
  refine ⟨q, by simpa using hq, ?_, ?_⟩
  · intro z
    have he := (abs_lt.mp (hqr z)).1
    have := min_le_right ε (r z / 2)
    linarith [hrp z]
  · intro z hz
    have hg : R⁻¹ ≤ gauge V z := by
      simpa only [hz, one_div] using
        (le_gauge_of_subset_closedBall (absorbent_nhds_zero hV0) hR.le hVR (x := z))
    have hr : r z = (gauge V z)⁻¹ := inv_inj.mpr (max_eq_right hg)
    have hgz : gauge V z ≠ 0 := ne_of_gt ((inv_pos.mpr hR).trans_le hg)
    refine ⟨r z • z, (gauge_eq_one_iff_mem_frontier hV hV0).mp ?_, ?_⟩
    · rw [gauge_smul_of_nonneg (hrp z).le, smul_eq_mul, hr, inv_mul_cancel₀ hgz]
    · calc
        dist (q z • z) (r z • z) = |q z - r z| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, hz, mul_one, Real.norm_eq_abs]
        _ < min ε (r z / 2) := hqr z
        _ ≤ ε := min_le_left _ _

theorem unitCirclePath_ne_zero (t : ℝ) : unitCirclePath t ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [unitCirclePath_norm]
  norm_num

theorem hasDerivAt_unitCirclePath (t : ℝ) :
    HasDerivAt unitCirclePath (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  convert! (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi)) using 1
  simp only [unitCirclePath, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem radialContour_index_center (a : ℂ) (q : ℂ → ℝ) (hq : ContDiff ℝ 1 q)
    (hqp : ∀ z, 0 < q z) : (radialContour a q hq).index a = 1 := by
  let f : ℝ → ℝ := fun t => q (unitCirclePath t)
  have hf : ContDiff ℝ 1 f := hq.comp unitCirclePath_smooth
  have hfp (t : ℝ) : f t ≠ 0 := (hqp _).ne'
  have hfc : f 0 = f 1 := by dsimp [f]; rw [unitCirclePath_closed]
  have hdiff (t : ℝ) : HasDerivAt f (deriv f t) t :=
    (hf.differentiable (by norm_num) t).hasDerivAt
  have hd (t : ℝ) : deriv (radialContour a q hq).path t =
      f t • (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
        deriv f t • unitCirclePath t :=
    ((hdiff t).smul (hasDerivAt_unitCirclePath t)).const_add a |>.deriv
  have hi : IntervalIntegrable (fun t => deriv f t / f t) MeasureTheory.volume (0 : ℝ) 1 :=
    (hf.continuous_deriv_one.div hf.continuous hfp).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => (hdiff t).log (hfp t)) hi
  rw [← hfc, sub_self] at he
  have heq (t : ℝ) : deriv (radialContour a q hq).path t /
      ((radialContour a q hq).path t - a) =
        ((deriv f t / f t : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hd]
    change ((f t : ℂ) * (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
      ((deriv f t : ℝ) : ℂ) * unitCirclePath t) /
      (a + (f t : ℂ) * unitCirclePath t - a) = _
    rw [add_sub_cancel_left, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr (hfp t), unitCirclePath_ne_zero t]
    ring
  have hic : IntervalIntegrable (fun t => ((deriv f t / f t : ℝ) : ℂ))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Complex.continuous_ofReal.comp (hf.continuous_deriv_one.div hf.continuous hfp)).intervalIntegrable 0 1
  simp only [SmoothContour.index, heq]
  rw [intervalIntegral.integral_add hic intervalIntegrable_const,
    intervalIntegral.integral_ofReal, he, Complex.ofReal_zero, zero_add,
    intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  apply inv_mul_cancel₀
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem exists_calculusContour {K U : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U) :
    Nonempty (CalculusContour K U) := by
  obtain ⟨a, ha⟩ := hKne
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  let e : ℂ ≃ₜ ℂ := Homeomorph.addLeft a
  let V : Set ℂ := e ⁻¹' (cthickening (ε / 2) K)
  have hV : Convex ℝ V := by
    convert! (hKc.cthickening (ε / 2)).translate (-a) using 1
    ext z
    constructor
    · intro hz
      exact ⟨a + z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      change a + (-a + w) ∈ cthickening (ε / 2) K
      simpa using hw
  have hV0 : V ∈ 𝓝 (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    change 0 ∈ interior (e ⁻¹' (cthickening (ε / 2) K))
    rw [← e.preimage_interior]
    change a + 0 ∈ interior (cthickening (ε / 2) K)
    rw [add_zero]
    exact thickening_subset_interior_cthickening _ _ (self_subset_thickening (half_pos hε) _ ha)
  have hVb : Bornology.IsBounded V := (e.isCompact_preimage.mpr hK.cthickening).isBounded
  obtain ⟨q, hq, hqp, hqV⟩ := exists_smooth_radial_frontier_approx hV hV0 hVb
    (div_pos hε (by norm_num : (0 : ℝ) < 4))
  let Γ : SmoothContour := radialContour a q hq
  have hΓ (t : ℝ) : Γ.path t ∈ cthickening ε K ∧ Γ.path t ∉ K := by
    obtain ⟨w, hw, hd⟩ := hqV (unitCirclePath t) (unitCirclePath_norm t)
    have hw' : a + w ∈ frontier (cthickening (ε / 2) K) := by
      change w ∈ e ⁻¹' frontier (cthickening (ε / 2) K)
      rw [e.preimage_frontier]
      exact hw
    have hiw : infDist (a + w) K = ε / 2 := by
      unfold infDist
      rw [frontier_cthickening_subset K hw', ENNReal.toReal_ofReal (half_pos hε).le]
    have hd' : dist (Γ.path t) (a + w) < ε / 4 := by
      simpa only [Γ, radialContour, dist_add_left] using hd
    have hi : infDist (Γ.path t) K < ε := by
      have hle := infDist_le_infDist_add_dist (s := K) (x := Γ.path t) (y := a + w)
      rw [hiw] at hle
      linarith
    refine ⟨thickening_subset_cthickening ε K ((mem_thickening_iff_infDist_lt ⟨a, ha⟩).mpr hi), ?_⟩
    intro htK
    have hle := infDist_le_infDist_add_dist (s := K) (x := a + w) (y := Γ.path t)
    rw [hiw, infDist_zero_of_mem htK, zero_add, dist_comm] at hle
    linarith
  refine ⟨{ toSmoothContour := Γ, avoids := ?_, index_inside := ?_, index_outside := ?_ }⟩
  · intro t _ht
    exact ⟨hεU (hΓ t).1, (hΓ t).2⟩
  · intro z hz
    calc
      Γ.index z = Γ.index a := Γ.index_eq_of_segment_avoids (fun t _ht htz =>
        (hΓ t).2 (hKc.segment_subset hz ha htz))
      _ = 1 := radialContour_index_center a q hq hqp
  · intro z hz
    exact Γ.index_eq_zero_of_convex (hKc.cthickening ε) isClosed_cthickening
      (by rintro _ ⟨t, _ht, rfl⟩; exact (hΓ t).1) (fun he => hz (hεU he))

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Convexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the numerical range and its closure. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem phase_real (u v : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * u + star c * v).im = 0 := by
  let d : ℂ := u - star v
  have him (c : ℂ) : (c * u + star c * v).im = (c * d).im := by
    simp only [d, mul_sub, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  by_cases hd : d = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [him, hd, mul_zero, Complex.zero_im]
  · refine ⟨(‖d‖ : ℂ)⁻¹ * star d, ?_, ?_⟩
    · simp [hd]
    · rw [him, mul_assoc]
      simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_inv,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem unit_interval_of_quadratic_endpoints (B : Operator H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hBx : ⟪x, B x⟫_ℂ = 0) (hBy : ⟪y, B y⟫_ℂ = 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ w : H, ‖w‖ = 1 ∧ ⟪w, B w⟫_ℂ = (t : ℂ) := by
  obtain ⟨c, hc, hcross⟩ := phase_real ⟪x, B y⟫_ℂ ⟪y, B x⟫_ℂ
  let y' : H := c • y
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hc, hy]
  have hy'B : ⟪y', B y'⟫_ℂ = 1 := by
    simp only [y', map_smul, inner_smul_left, inner_smul_right, hBy, mul_one,
      Complex.mul_conj', hc, Complex.ofReal_one, one_pow]
  have hc' : (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ).im = 0 := by
    simpa only [y', map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply] using hcross
  let q : ℝ → H := fun s => ((1 - s : ℝ) : ℂ) • x + (s : ℂ) • y'
  have hq0 (s : ℝ) : q s ≠ 0 := by
    intro hz
    have heq : (((1 - s : ℝ) : ℂ) • x) = -(s : ℂ) • y' := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz
    have hq := congrArg (fun z : H => ⟪z, B z⟫_ℂ) heq
    simp only [map_smul, inner_smul_left, inner_smul_right, hBx, hy'B, mul_zero,
      mul_one, map_neg, Complex.conj_ofReal, neg_mul_neg] at hq
    have hs : s = 0 := by
      have hh := congrArg Complex.re hq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.zero_re] at hh
      nlinarith
    simp [q, hs] at hz
    rw [hz] at hx
    norm_num at hx
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hqi (s : ℝ) : (⟪q s, B (q s)⟫_ℂ).im = 0 := by
    have heq : ⟪q s, B (q s)⟫_ℂ = (s : ℂ) ^ 2 +
        (s : ℂ) * (1 - (s : ℂ)) * (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ) := by
      simp only [q, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal, hBx, hy'B, map_sub, map_one,
        mul_zero, mul_one, zero_add, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [heq]
    simp [Complex.add_im, Complex.mul_im, hc', pow_two]
  let g : ℝ → H := fun s => (‖q s‖ : ℂ)⁻¹ • q s
  have hg (s : ℝ) : ‖g s‖ = 1 := by
    simp [g, norm_smul, hq0 s]
  have hgc : Continuous g := by
    apply Continuous.smul _ hq
    apply Continuous.inv₀ (Complex.continuous_ofReal.comp hq.norm)
    intro s
    change (‖q s‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (hq0 s)
  have hgi (s : ℝ) : (⟪g s, B (g s)⟫_ℂ).im = 0 := by
    simp only [g, map_smul, inner_smul_left, inner_smul_right, ← Complex.ofReal_inv,
      Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hqi s]
    ring
  let f : ℝ → ℝ := fun s => (⟪g s, B (g s)⟫_ℂ).re
  have hfc : Continuous f := Complex.continuous_re.comp (hgc.inner (𝕜 := ℂ) (B.continuous.comp hgc))
  have hf0 : f 0 = 0 := by simp [f, g, q, hx, hBx]
  have hf1 : f 1 = 1 := by simp [f, g, q, hy', hy'B]
  have hmem : t ∈ Icc (f 0) (f 1) := by simpa only [hf0, hf1] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfc.continuousOn hmem
  refine ⟨g s, hg s, ?_⟩
  apply Complex.ext
  · exact hs
  · exact hgi s

theorem convex_numericalRange (A : Operator H) : Convex ℝ (numericalRange A) := by
  intro a ha b hb α β hα hβ hsum
  by_cases hab : a = b
  · subst b
    rw [← add_smul, hsum, one_smul]
    exact ha
  obtain ⟨x, hx, hAx⟩ := ha
  obtain ⟨y, hy, hAy⟩ := hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let B : Operator H := (b - a)⁻¹ • (A - a • 1)
  have hform (v : H) (hv : ‖v‖ = 1) :
      ⟪v, B v⟫_ℂ = (b - a)⁻¹ * (⟪v, A v⟫_ℂ - a) := by
    simp [B, inner_self_eq_norm_sq_to_K, hv]
  have hBx : ⟪x, B x⟫_ℂ = 0 := by rw [hform x hx, hAx, sub_self, mul_zero]
  have hBy : ⟪y, B y⟫_ℂ = 1 := by rw [hform y hy, hAy, inv_mul_cancel₀ hba]
  obtain ⟨w, hw, hwB⟩ := unit_interval_of_quadratic_endpoints B x y hx hy hBx hBy
    β ⟨hβ, by linarith⟩
  refine ⟨w, hw, ?_⟩
  rw [hform w hw] at hwB
  have hid := congrArg (fun z : ℂ => (b - a) * z) hwB
  simp only [← mul_assoc, mul_inv_cancel₀ hba, one_mul] at hid
  have hsumC : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hsum
  calc
    ⟪w, A w⟫_ℂ = (⟪w, A w⟫_ℂ - a) + a := by ring
    _ = (b - a) * (β : ℂ) + a := by rw [hid]
    _ = α • a + β • b := by
      simp only [Complex.real_smul]
      linear_combination -a * hsumC

theorem convex_numericalClosure (A : Operator H) : Convex ℝ (numericalClosure A) :=
  (convex_numericalRange A).closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.EndpointInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Interpolation. -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker TensorProduct ENNReal

namespace CrouzeixHilbert

open Realization Boundary

theorem aeval_transferDenominator_isUnit {n : ℕ} (D a : Coeff n)
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1) :
    IsUnit (Polynomial.aeval D (transferDenominator a)) := by
  nontriviality (Coeff n)
  rw [← spectrum.zero_notMem_iff (R := ℂ), spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, he⟩
  have hn : ‖z‖ < 1 := by
    rw [spectralRadius] at hD
    have hi : (‖z‖₊ : ℝ≥0∞) < 1 := (le_iSup₂ (α := ℝ≥0∞) z hz).trans_lt hD
    exact_mod_cast hi
  have hu : IsUnit (1 - z • a) := by
    apply isUnit_one_sub_of_norm_lt_one
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt (by simpa using hn)
  have hh := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← eval_transferDenominator] at hh
  exact isUnit_iff_ne_zero.mp hh he

@[simp] theorem transferDenominator_ne_zero {n : ℕ} (a : Coeff n) :
    transferDenominator a ≠ 0 := by
  intro h
  have he := eval_transferDenominator a 0
  rw [h, Polynomial.eval_zero, zero_smul, sub_zero, Matrix.det_one] at he
  exact zero_ne_one he

theorem leftTensor_isUnit {n m : ℕ} (A : Coeff n) (hA : IsUnit A) :
    IsUnit (A ⊗ₖ (1 : Coeff m)) := by
  refine ⟨⟨A ⊗ₖ (1 : Coeff m), Ring.inverse A ⊗ₖ 1, ?_, ?_⟩, rfl⟩
  · rw [← Matrix.mul_kronecker_mul, mul_one, Ring.mul_inverse_cancel _ hA]
    exact Matrix.one_kronecker_one
  · rw [← Matrix.mul_kronecker_mul, mul_one, Ring.inverse_mul_cancel _ hA]
    exact Matrix.one_kronecker_one

theorem blockPolynomialEval_pencil_transpose {n : ℕ} (D a : Coeff n) :
    blockPolynomialEval D (pencil a)ᵀ = 1 - D ⊗ₖ aᵀ := by
  rw [pencil, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    ← Matrix.transpose_map, map_sub, map_one, blockPolynomialEval_smul_constant]
  simp only [Polynomial.aeval_X]

theorem blockPolynomialEval_adjugate_pencil {n : ℕ} (D a : Coeff n) :
    blockPolynomialEval D (pencil a).adjugateᵀ *
        blockPolynomialEval D (pencil a)ᵀ =
      Polynomial.aeval D (transferDenominator a) ⊗ₖ (1 : Coeff n) := by
  rw [← map_mul, ← Matrix.transpose_mul, Matrix.mul_adjugate,
    Matrix.transpose_smul, Matrix.transpose_one, blockPolynomialEval_scalar]
  rfl

theorem blockPolynomialEval_transferNumerator_transpose {n : ℕ} (D a b c d : Coeff n) :
    blockPolynomialEval D (transferNumerator a b c d)ᵀ =
      Polynomial.aeval D (transferDenominator a) ⊗ₖ dᵀ +
      (D ⊗ₖ bᵀ) * blockPolynomialEval D (pencil a).adjugateᵀ * (1 ⊗ₖ cᵀ) := by
  simp only [transferNumerator, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_mul, ← Matrix.transpose_map, map_add]
  rw [← mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, map_mul, map_mul,
    blockPolynomialEval_smul_constant, blockPolynomialEval_smul_constant,
    blockPolynomialEval_constant, Polynomial.aeval_X]

theorem rational_transfer_interpolates {n : ℕ} (D a b c d L X Y : Coeff n)
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1)
    (hL : L = D * L * a + X * c) (hY : Y = D * L * b + X * d) :
    matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D)
      (transferRational a b c d)ᵀ (vectorization X) = vectorization Y := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n × Fin n)
  let E := blockPolynomialEval D (pencil a)ᵀ
  let M := blockPolynomialEval D (pencil a).adjugateᵀ
  let Q := Polynomial.aeval D (transferDenominator a) ⊗ₖ (1 : Coeff n)
  have hME : M * E = Q := blockPolynomialEval_adjugate_pencil D a
  have hrec : e E (toHS L) = e (1 ⊗ₖ cᵀ) (toHS X) := by
    rw [show E = 1 - D ⊗ₖ aᵀ from blockPolynomialEval_pencil_transpose D a,
      map_sub, map_one, sub_apply, one_apply_eq_self,
      kronecker_toHS, kronecker_toHS, Matrix.transpose_transpose, Matrix.transpose_transpose, one_mul]
    change hsEquiv n L - hsEquiv n (D * L * a) = hsEquiv n (X * c)
    rw [← map_sub]
    exact congrArg (hsEquiv n) (sub_eq_iff_eq_add.mpr (hL.trans (add_comm _ _)))
  have hQc : Commute Q (D ⊗ₖ bᵀ) := by
    simpa only [blockPolynomialEval_smul_constant, Polynomial.aeval_X] using
      blockPolynomialEval_commute D (transferDenominator a)
        ((Polynomial.X : Polynomial ℂ) • bᵀ.map Polynomial.C)
  have hNX : e (blockPolynomialEval D (transferNumerator a b c d)ᵀ) (toHS X) =
      e Q (toHS Y) := by
    rw [blockPolynomialEval_transferNumerator_transpose, map_add, add_apply]
    have hd : Polynomial.aeval D (transferDenominator a) ⊗ₖ dᵀ = Q * (1 ⊗ₖ dᵀ) := by
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    have hdX : e (1 ⊗ₖ dᵀ) (toHS X) = toHS (X * d) := by
      rw [kronecker_toHS, Matrix.transpose_transpose, one_mul]
    have hbL : e (D ⊗ₖ bᵀ) (toHS L) = toHS (D * L * b) := by
      rw [kronecker_toHS, Matrix.transpose_transpose]
    rw [hd, map_mul, mul_apply_eq_comp, hdX,
      map_mul, mul_apply_eq_comp, ← hrec, ← mul_apply_eq_comp, ← map_mul,
      mul_assoc, hME, ← hQc.eq, map_mul, mul_apply_eq_comp, hbL, ← map_add]
    congr 1
    change hsEquiv n (X * d) + hsEquiv n (D * L * b) = hsEquiv n Y
    rw [← map_add]
    exact congrArg (hsEquiv n) ((add_comm _ _).trans hY.symm)
  have hq := aeval_transferDenominator_isUnit D a hD ha
  have hQR : Q * blockRationalEval D (transferRational a b c d)ᵀ =
      blockPolynomialEval D (transferNumerator a b c d)ᵀ :=
    blockRationalEval_denom_cancel D (transferNumerator a b c d)ᵀ _
      (transferDenominator_ne_zero a) hq
  let coords : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply coords.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_rationalEval, vectorization_coordinates, vectorization_coordinates]
  have h0 : e Q (e (blockRationalEval D (transferRational a b c d)ᵀ) (toHS X)) =
      e Q (toHS Y) := by
    rw [← mul_apply_eq_comp, ← map_mul, hQR]
    exact hNX
  obtain ⟨u, hu⟩ := (leftTensor_isUnit (m := n) _ hq).map e
  rw [← hu] at h0
  have hi := congrArg (fun v => (↑(u⁻¹) : EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n × Fin n)) v) h0
  simpa only [← mul_apply_eq_comp, ← mul_assoc, Units.inv_mul, one_mul, one_apply_eq_self] using hi

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Contours. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rational_poleFree_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : PolesOutside U R := by
    intro i j z hz
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, hne, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn (hne i j)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Endpoint. -/

noncomputable section

open Set

open scoped TensorProduct Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace CrouzeixHilbert

open Boundary Realization Endpoint

@[simp] theorem vectorization_smul {n : ℕ} (c : ℂ) (X : Coeff n) :
    vectorization (c • X) = c • vectorization X := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [map_smul, vectorization_coordinates, vectorization_coordinates]
  apply PiLp.ext
  intro ij
  rfl

theorem tensor_endpoint_of_matrix_endpoint {n : ℕ} (S X : Coeff n)
    (t : ℝ) (h : S * X = t • X) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) S) (1 : Coeff n)
      (vectorization X) = (t : ℂ) • vectorization X := by
  rw [tensorOperator_vectorization, Matrix.transpose_one, mul_one, h]
  rw [← vectorization_smul]
  congr 1

theorem trace_gram_eq_norm_vectorization_sq {n : ℕ} (X : Coeff n) :
    (X * Xᴴ).trace = (‖vectorization X‖ : ℂ) ^ 2 := by
  rw [Matrix.trace_mul_comm, ← inner_toHS, inner_self_eq_norm_sq_to_K, norm_vectorization]
  norm_cast

theorem disk_endpoint_extremal_oai {n : ℕ} (hn : 0 < n) (T : Coeff n)
    (hT : spectralRadius ℂ T < 1) {κ : ℝ} (hκ : 1 < κ)
    (H : Coeff n) (hH : Metric.Feasible T (κ ^ 2) H)
    (hmin : ∀ s J, Metric.Feasible T s J → κ ^ 2 ≤ s) :
    ∃ (X Y : Coeff n) (R : RationalMatrix n) (U : Set ℂ),
      (X * Xᴴ).trace = 1 ∧ (Y * Yᴴ).trace = 1 ∧
      CFC.sqrt H * X = κ • X ∧ CFC.sqrt H * Y = Y ∧ Xᴴ * Y = 0 ∧
      ‖vectorization X‖ = 1 ∧ ‖vectorization Y‖ = 1 ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization X) = (κ : ℂ) • vectorization X ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization Y) = vectorization Y ∧
      IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction R z‖ ≤ 1) ∧
      matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) R
          (vectorization X) = vectorization Y ∧
      matrixHolomorphicEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) U
          (matrixRationalFunction R) (vectorization X) = vectorization Y := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨E⟩ := endpointFactors_of_minimum T hT hκ H hH hmin
  obtain ⟨C, hL, hY⟩ := E.exists_colligation
  let D := CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  have hD : spectralRadius ℂ D < 1 := by
    simpa only [D, spectralRadius, hH.sqrt_spectrum] using hT
  have ha : ‖e.symm C.a‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, StarAlgEquiv.apply_symm_apply]
    exact C.norm_a_le
  have hi : matrixRationalEval (e D) C.diskExtremal (vectorization E.X) =
      vectorization E.Y :=
    rational_transfer_interpolates D (e.symm C.a) (e.symm C.b) (e.symm C.c) (e.symm C.d)
      (CFC.sqrt E.Q) E.X E.Y hD ha hL hY
  obtain ⟨U, hU, hKU, hRU, hFU⟩ := rational_poleFree_neighborhood C.diskExtremal
    C.diskExtremal_polesOutside
  have hKD : numericalClosure (e D) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    (numericalClosure_subset_closedBall (e D)).trans
      (Metric.closedBall_subset_closedBall (by
        have hnD := hH.sqrt_similarity.2.1
        rwa [← Matrix.cstar_norm_def]))
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure (e D))
    (convex_numericalClosure (e D)) (numericalClosure_nonempty (e D)) hU (hKD.trans hKU)
  have heval := matrixHolomorphicEval_matrixRationalFunction (e D) Γ C.diskExtremal hRU
  have hXn : ‖vectorization E.X‖ = 1 := by rw [norm_vectorization, E.X_norm]
  have hYn : ‖vectorization E.Y‖ = 1 := by rw [norm_vectorization, E.Y_norm]
  refine ⟨E.X, E.Y, C.diskExtremal, U, ?_, ?_, E.X_endpoint, E.Y_endpoint,
    E.perpendicular, hXn, hYn, ?_, ?_, hU, hKU, hRU, hFU,
    C.diskExtremal_extension.2, hi, ?_⟩
  · rw [trace_gram_eq_norm_vectorization_sq, hXn]; norm_num
  · rw [trace_gram_eq_norm_vectorization_sq, hYn]; norm_num
  · exact tensor_endpoint_of_matrix_endpoint (CFC.sqrt H) E.X κ E.X_endpoint
  · simpa only [Complex.ofReal_one, one_smul] using
      tensor_endpoint_of_matrix_endpoint (CFC.sqrt H) E.Y 1
        (by simpa only [one_smul] using E.Y_endpoint)
  · rw [heval]
    exact hi

end CrouzeixHilbert

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.disk_endpoint_extremal_oai := @OAI.CrouzeixHilbert.disk_endpoint_extremal_oai
