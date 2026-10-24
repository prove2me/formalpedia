-- Prove2me | solution 1 for OAI.PosteriorReplicas.replica_klDiv_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:52:25.433986+00:00
-- url     : https://prove2.me/submissions/a010e755-58e2-44d2-8ba8-7b43020b399c

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000
import Theorems.Thm_OAI_PosteriorReplicas_equal_label_tilt_identity

section
-- module Solutions.OAIQW_PosteriorReplicas.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_PiLast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section PiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable
end PiLast

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)

lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]

theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GaussianDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let f : E → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 (fun i => ⟪u i, x⟫)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (stdGaussian E).map f = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    have hi (x : E) : ⟪f x, t⟫ = ⟪x, ∑ i, t i • u i⟫ := by
      simp [f, PiLp.inner_apply, inner_sum, inner_smul_right, real_inner_comm x]
    have hn : ‖∑ i, t i • u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]
    rw [charFun_apply, integral_map hf.aemeasurable (by fun_prop)]
    simp_rw [hi]
    change charFun (stdGaussian E) (∑ i, t i • u i) = _
    rw [charFun_stdGaussian, charFun_stdGaussian]
    congr 2
    exact_mod_cast congrArg Neg.neg hn
  have h := congrArg (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) he
  rw [← map_pi_eq_stdGaussian] at h
  simpa [Measure.map_map (WithLp.measurable_ofLp _ _) hf,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _),
    Function.comp_def, f, WithLp.ofLp_toLp, Measure.map_id] using h

end GaussianDomination

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_AePiLast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.map_eq, MeasurableEmbedding.ae_map_iff (MeasurableEquiv.measurableEmbedding _)]
  have heq : (fun z : E × (Fin n → E) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm z) =
      fun z => Fin.snoc z.2 z.1 := by
    ext z : 1
    change (Fin.last n).insertNth (α := fun _ => E) z.1 z.2 = _
    exact Fin.insertNth_last' z.1 z.2
  have hm : Measurable (fun z : E × (Fin n → E) => Fin.snoc (α := fun _ => E) z.2 z.1) := by
    rw [← heq]
    exact hp.measurable
  change (∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
      P ((fun z => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E)
        (Fin.last n)).symm z) z)) ↔ _
  have hPP : MeasurableSet {z : E × (Fin n → E) | P (Fin.snoc z.2 z.1)} := hP.preimage hm
  rw [heq, Measure.ae_prod_iff_ae_ae hPP]
  exact Measure.ae_ae_comm hPP
end AePiLast

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
section InverseMoments

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma inverse_pow_dyadic_majorant (f : X → ℝ) (m : ℕ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      1 + ∑' k : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
  classical
  by_cases hzero : f x = 0
  · simp only [hzero, inv_zero]
    exact le_add_of_le_left (by cases m <;> simp)
  have hxpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hzero)
  by_cases hxone : 1 ≤ f x
  · apply le_add_of_le_left
    have h : (f x)⁻¹ ^ m ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (hf x)) (inv_le_one_of_one_le₀ hxone)
    simpa using ENNReal.ofReal_le_ofReal h
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hxone) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv : (f x)⁻¹ ≤ (2 : ℝ) ^ (k + 1) := by
    have h := (inv_le_inv₀ hxpos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)).2 hklo.le
    simpa using h
  have hpow : ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := by
    apply ENNReal.ofReal_le_ofReal
    simpa [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (inv_nonneg.mpr (hf x)) hinv m
  calc
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤ ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := hpow
    _ = ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
      rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ (1 / 2 : ℝ) ^ k} from hkhi)]
    _ ≤ ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x :=
      ENNReal.le_tsum (f := fun index : ℕ =>
        ({point | f point ≤ (1 / 2 : ℝ) ^ index}).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (index + 1)))) x) k
    _ ≤ 1 + ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x := le_add_left le_rfl

lemma dyadic_power_cancel (m k : ℕ) :
    (2 : ℝ) ^ (m * (k + 1)) * ((1 / 2 : ℝ) ^ k) ^ (m + 1) =
      (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
  rw [Nat.mul_add, mul_one, pow_add, pow_succ]
  have h : (2 : ℝ) ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m = 1 := by
    rw [Nat.mul_comm m k, pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    2 ^ (m * k) * 2 ^ m * (((1 / 2 : ℝ) ^ k) ^ m * (1 / 2 : ℝ) ^ k) =
      (2 ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m) * (2 ^ m * (1 / 2 : ℝ) ^ k) := by ring
    _ = _ := by rw [h, one_mul]

theorem inverse_moment_of_tube_bound (μ : Measure X) (f : X → ℝ) (m : ℕ)
    (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ {x | f x ≤ r} ≤ C * ENNReal.ofReal (r ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤
      μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
  classical
  let g : ℕ → X → ℝ≥0∞ := fun k =>
    ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
      (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))))
  have hg : ∀ k, Measurable (g k) := fun k =>
    measurable_const.indicator (measurableSet_le hf measurable_const)
  calc
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤ ∫⁻ x, 1 + ∑' k, g k x ∂μ :=
      lintegral_mono (inverse_pow_dyadic_majorant f m hnonneg)
    _ = μ Set.univ + ∑' k, ∫⁻ x, g k x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul, lintegral_tsum (fun k => (hg k).aemeasurable)]
    _ ≤ μ Set.univ + ∑' k, C * ENNReal.ofReal ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro k
      dsimp only [g]
      rw [lintegral_indicator (measurableSet_le hf measurable_const), lintegral_const,
        Measure.restrict_apply_univ]
      calc
        ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) * μ {x | f x ≤ (1 / 2 : ℝ) ^ k} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) *
              (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ (m + 1))) := by
          gcongr
          exact htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
        _ = _ := by
          rw [← mul_assoc, mul_comm _ C, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            dyadic_power_cancel]
    _ = μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num [pow_succ, mul_assoc, ENNReal.ofReal_div_of_pos]

end InverseMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

end GramDistances

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

end ReplicaMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaNondegenerate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ReplicaNondegenerate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

end ReplicaNondegenerate

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace PosteriorReplicas

section GaussianSplitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma charFun_gaussian_starProjection (U : Submodule ℝ E) (t : E) :
    charFun ((stdGaussian E).map U.starProjection) t =
      Complex.exp (- ‖U.starProjection t‖ ^ 2 / 2) := by
  rw [charFun_apply, integral_map U.starProjection.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp_rw [U.inner_starProjection_left_eq_right]
  change charFun (stdGaussian E) (U.starProjection t) = _
  exact charFun_stdGaussian _

lemma gaussian_orthogonal_sum (U : Submodule ℝ E) :
    (((stdGaussian E).map U.starProjection).prod
      ((stdGaussian E).map Uᗮ.starProjection)).map (fun z => z.1 + z.2) =
        stdGaussian E := by
  let : IsProbabilityMeasure ((stdGaussian E).map U.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff
      U.starProjection.continuous.measurable.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure ((stdGaussian E).map Uᗮ.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff
      Uᗮ.starProjection.continuous.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply,
    charFun_gaussian_starProjection, charFun_gaussian_starProjection,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection t U
  have hc : (‖t‖ : ℂ)^2 = (‖U.starProjection t‖ : ℂ)^2 +
      (‖Uᗮ.starProjection t‖ : ℂ)^2 := by exact_mod_cast h
  rw [hc]
  ring

lemma gaussian_orthogonal_pair (U : Submodule ℝ E) :
    (stdGaussian E).map (fun x => (U.starProjection x, Uᗮ.starProjection x)) =
      ((stdGaussian E).map U.starProjection).prod
        ((stdGaussian E).map Uᗮ.starProjection) := by
  have hP : Measurable (fun x : E => (U.starProjection x, Uᗮ.starProjection x)) :=
    U.starProjection.continuous.measurable.prodMk Uᗮ.starProjection.continuous.measurable
  conv_lhs => rw [← gaussian_orthogonal_sum U]
  rw [Measure.map_map hP (by fun_prop)]
  rw [Measure.map_prod_map _ _ U.starProjection.continuous.measurable
    Uᗮ.starProjection.continuous.measurable]
  rw [Measure.map_map (hP.comp (by fun_prop))
    (U.starProjection.continuous.measurable.prodMap
      Uᗮ.starProjection.continuous.measurable)]
  congr 1
  funext z
  dsimp [Function.comp_def]
  simp only [map_add]
  have h₁ : U.starProjection (U.starProjection z.1) = U.starProjection z.1 :=
    U.starProjection_eq_self_iff.mpr (by simp)
  have h₂ : Uᗮ.starProjection (Uᗮ.starProjection z.2) = Uᗮ.starProjection z.2 :=
    Uᗮ.starProjection_eq_self_iff.mpr (by simp)
  have h₃ : Uᗮ.starProjection (U.starProjection z.1) = 0 :=
    U.starProjection_orthogonal_apply_eq_zero (by simp)
  have h₄ : U.starProjection (Uᗮ.starProjection z.2) = 0 := by
    rw [← U.orthogonal_orthogonal]
    exact Uᗮ.starProjection_orthogonal_apply_eq_zero (by simp)
  rw [h₁, h₂, h₃, h₄, add_zero, zero_add]
  rfl

lemma gaussian_orthogonal_indep (U : Submodule ℝ E) :
    IndepFun U.starProjection Uᗮ.starProjection (stdGaussian E) := by
  exact (indepFun_iff_map_prod_eq_prod_map_map
    U.starProjection.continuous.measurable.aemeasurable
    Uᗮ.starProjection.continuous.measurable.aemeasurable).mpr (gaussian_orthogonal_pair U)

omit [MeasurableSpace E] [BorelSpace E] in
lemma pairing_starProjection (U : Submodule ℝ E) {v : E} (hv : v ∈ U) (x : E) :
    ⟪v, U.starProjection x⟫ = ⟪v, x⟫ := by
  rw [← U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hv]

omit [MeasurableSpace E] [BorelSpace E] in
lemma orthonormal_starProjection {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) (x : E) :
    (Submodule.span ℝ (Set.range u)).starProjection x = ∑ i, ⟪u i, x⟫ • u i := by
  let U := Submodule.span ℝ (Set.range u)
  have hmem (i : Fin n) : u i ∈ U := Submodule.subset_span (Set.mem_range_self i)
  apply U.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.sum_mem (fun i _ => U.smul_mem _ (hmem i))
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨i, rfl⟩
      rw [inner_sub_left, hu.inner_left_fintype]
      simp [real_inner_comm x]
    | zero => simp
    | add v w hv hw ihv ihw => simp [inner_add_right, ihv, ihw]
    | smul a v hv ih => simp [inner_smul_right, ih]

lemma gaussian_pairings_residual_indep {n : ℕ} (v : Fin n → E) :
    IndepFun (fun x : E => fun i => ⟪v i, x⟫)
      (Submodule.span ℝ (Set.range v))ᗮ.starProjection (stdGaussian E) := by
  let U := Submodule.span ℝ (Set.range v)
  have h := (gaussian_orthogonal_indep U).comp
    (show Measurable (fun x : E => fun i => ⟪v i, x⟫) by fun_prop) measurable_id
  have heq : (fun x : E => fun i => ⟪v i, x⟫) ∘ U.starProjection =
      (fun x : E => fun i => ⟪v i, x⟫) := by
    funext x i
    apply pairing_starProjection U (Submodule.subset_span (Set.mem_range_self i))
  simpa only [heq, Function.id_comp] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairingLift_mem {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) :
    pairingLift v y ∈ Submodule.span ℝ (Set.range v) := by
  unfold pairingLift
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairings_pairingLift {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (y : Fin n → ℝ) : (fun j => ⟪v j, pairingLift v y⟫) = y := by
  have hd : IsUnit (Matrix.gram ℝ v).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)
  calc
    _ = (Matrix.gram ℝ v) *ᵥ ((Matrix.gram ℝ v)⁻¹ *ᵥ y) := by
      ext j
      simp [pairingLift, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, mul_comm]
    _ = y := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

omit [MeasurableSpace E] [BorelSpace E] in
lemma starProjection_eq_pairingLift {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    (Submodule.span ℝ (Set.range v)).starProjection x =
      pairingLift v (fun i => ⟪v i, x⟫) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (pairingLift_mem _ _)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨i, rfl⟩
    rw [inner_sub_left, real_inner_comm (v i) x, real_inner_comm (v i) (pairingLift _ _)]
    have h := congrFun (pairings_pairingLift hv (fun i => ⟪v i, x⟫)) i
    rw [h, sub_self]
  | zero => simp
  | add v w hv hw ihv ihw => simp [inner_add_right, ihv, ihw]
  | smul a v hv ih => simp [inner_smul_right, ih]

lemma gaussian_pairings_disintegration {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) :
    (((stdGaussian E).map (fun x => fun i => ⟪v i, x⟫)).prod
      ((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)).map
        (fun z => pairingLift v z.1 + z.2) = stdGaussian E := by
  rw [← (gaussian_pairings_residual_indep v).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), Measure.map_map
      (by fun_prop)
      (by fun_prop)]
  convert (Measure.map_id (μ := stdGaussian E)) using 1
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [← starProjection_eq_pairingLift hv x,
    Submodule.starProjection_add_starProjection_orthogonal]
  rfl

lemma gaussian_pairings_integral {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂stdGaussian E =
      ∫⁻ y, ∫⁻ r, g (pairingLift v y + r)
        ∂((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)
        ∂((stdGaussian E).map (fun x => fun i => ⟪v i, x⟫)) := by
  conv_lhs => rw [← gaussian_pairings_disintegration hv]
  rw [lintegral_map hg
    (by fun_prop),
    lintegral_prod _ (by fun_prop)]

end GaussianSplitting
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_DensityTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {T : α → β} (hT : Measurable T) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ T)).map T = (μ.map T).withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hT,
    lintegral_withDensity_eq_lintegral_mul _ (hf.comp hT)
      (show Measurable (fun a => g (T a)) from hg.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hf hg,
    lintegral_map (hf.mul hg) hT]
  rfl

lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hf (show Measurable (fun a => g (e a)) from hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun y => f (e.symm y)) from hf.comp e.symm.measurable) hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => f (e.symm y) * g y) from (hf.comp e.symm.measurable).mul hg) e.measurable]
  simp

lemma lintegral_fin_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E i.succ),
          f 0 x.1 * ∏ i, f i.succ (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp
          (by exact Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i)))]
        simp only [Fin.prod_univ_succ, Fin.zero_succAbove]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        have hg : Measurable (fun x : (i : Fin n) → E i.succ => ∏ i, f i.succ (x i)) :=
          Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
        rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable,
          ih _ _ (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_finite_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp
    (show Measurable (fun x => ∏ i, f i (x i)) from Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i)))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i => hf (e i))

lemma pi_withDensity {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_finite_prod _ _ hf]
  congr 1
  ext i
  rw [withDensity_apply _ (hs i)]

lemma pi_gaussian_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  have h : gaussianReal 0 1 = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← h]
    infer_instance
  rw [h]
  exact pi_withDensity _ _ (fun _ => measurable_gaussianPDF _ _)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

lemma gaussian_linear_image_density {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hd : M.det ≠ 0) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (Matrix.toLin' M) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y =>
        ENNReal.ofReal |M.det⁻¹| * ∏ i, gaussianPDF 0 1 ((M⁻¹ *ᵥ y) i)) := by
  let e := (matrixLinearEquiv M hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = Matrix.toLin' M := rfl
  have hi : (e.symm : (Fin n → ℝ) → (Fin n → ℝ)) = Matrix.toLin' M⁻¹ := rfl
  rw [pi_gaussian_density, ← he, map_withDensity_equiv _ e (by fun_prop), he,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hd, withDensity_smul_measure,
    ← withDensity_smul _ (by fun_prop)]
  rfl

lemma gaussian_density_product {n : ℕ} (z : Fin n → ℝ) :
    (∏ i, gaussianPDF 0 1 (z i)) = ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(∑ i, (z i)^2) / 2)) := by
  have hconst : (Real.sqrt (2 * Real.pi))⁻¹ ^ n =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
    rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    ring
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (z i))]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

section PairingsDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pairingTriangular_expansion [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (j : Fin n) : ∑ i, pairingTriangular v i j • gramSchmidtNormed ℝ v i = v j := by
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  rw [← PosteriorRegression.gsUpper_expansion n v j]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairingTriangular, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
  congr 1
  simp [hn i, mul_comm]

lemma pairingTriangular_det [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (v : Fin n → E) :
    (pairingTriangular v).transpose.det = Real.sqrt (Matrix.gram ℝ v).det := by
  rw [pairingTriangular, Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal,
    PosteriorRegression.gsUpper_det, mul_one, PosteriorRegression.sqrt_det_gram]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma pairingTriangular_det_pos {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    0 < (pairingTriangular v).transpose.det := by
  rw [pairingTriangular_det]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos

lemma pairings_eq_triangular {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' (pairingTriangular v).transpose) ∘
        (fun x => fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) := by
  funext x j
  rw [← pairingTriangular_expansion hv j]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner, inner_smul_left]

lemma gaussian_pairings_density_coordinates {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y =>
        ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
          ∏ i, gaussianPDF 0 1 (((pairingTriangular v).transpose⁻¹ *ᵥ y) i)) := by
  rw [pairings_eq_triangular hv, ← Measure.map_map (by fun_prop) (by fun_prop),
    PosteriorRegression.orthonormal_gaussian_map (gramSchmidtNormed_orthonormal hv),
    gaussian_linear_image_density _ (ne_of_gt (pairingTriangular_det_pos hv)),
    abs_of_pos (inv_pos.mpr (pairingTriangular_det_pos hv)), pairingTriangular_det]

lemma orthonormal_pairings_eq_inverse {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    (fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) =
      (pairingTriangular v).transpose⁻¹ *ᵥ (fun i => ⟪v i, x⟫) := by
  have he := congrFun (pairings_eq_triangular hv) x
  change (fun i => ⟪v i, x⟫) =
    (pairingTriangular v).transpose *ᵥ (fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) at he
  rw [he, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (pairingTriangular_det_pos hv))),
    Matrix.one_mulVec]

lemma pairingLift_energy {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (y : Fin n → ℝ) :
    ‖pairingLift v y‖^2 = ∑ i, (((pairingTriangular v).transpose⁻¹ *ᵥ y) i)^2 := by
  have hu := gramSchmidtNormed_orthonormal hv
  have hs : Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ v)) =
      Submodule.span ℝ (Set.range v) :=
    (span_gramSchmidtNormed_range v).trans (span_gramSchmidt ℝ v)
  have hexp := orthonormal_starProjection hu (pairingLift v y)
  rw [hs, (Submodule.span ℝ (Set.range v)).starProjection_eq_self_iff.mpr
    (pairingLift_mem v y)] at hexp
  have hc := orthonormal_pairings_eq_inverse hv (pairingLift v y)
  rw [pairings_pairingLift hv y] at hc
  simp_rw [congrFun hc] at hexp
  rw [hexp, ← real_inner_self_eq_norm_sq, hu.inner_sum]
  simp [pow_two]

lemma gaussian_pairings_density {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖pairingLift v y‖^2 / 2) /
          Real.sqrt (Matrix.gram ℝ v).det)) := by
  rw [gaussian_pairings_density_coordinates hv]
  congr 1
  funext y
  rw [gaussian_density_product, ← pairingLift_energy hv,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma gaussian_fiber_integral {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂stdGaussian E = ∫⁻ y, ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖pairingLift v y‖^2 / 2) /
        Real.sqrt (Matrix.gram ℝ v).det) *
      ∫⁻ r, g (pairingLift v y + r)
        ∂((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) := by
  rw [gaussian_pairings_integral hv hg, gaussian_pairings_density hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

end PairingsDensity
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_density : stdGaussian E = volume.withDensity
    (fun x : E => gaussianRadialDensity (Module.finrank ℝ E) ‖x‖) := by
  let b := stdOrthonormalBasis ℝ E
  have hp : MeasurePreserving (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i)
      volume volume := by
    have heq : (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) =
        b.repr.symm ∘ WithLp.toLp 2 := by
      funext x
      exact b.sum_repr_symm (WithLp.toLp 2 x)
    rw [heq]
    exact b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp _)
  apply Measure.ext_of_lintegral
  intro g hg
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    lintegral_map hg (by fun_prop), pi_gaussian_density,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg,
    ← hp.lintegral_comp (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  have hnorm : ‖∑ i, x i • b i‖^2 = ∑ i, (x i)^2 := by
    rw [← real_inner_self_eq_norm_sq, b.orthonormal.inner_sum]
    simp [sq]
  rw [gaussian_density_product, gaussianRadialDensity, hnorm]

lemma stdGaussian_absolutelyContinuous_volume : stdGaussian E ≪ volume := by
  rw [stdGaussian_density]
  exact withDensity_absolutelyContinuous _ _

lemma stdGaussian_singleton_eq_zero [Nontrivial E] (x : E) : (stdGaussian E) {x} = 0 :=
  stdGaussian_absolutelyContinuous_volume (measure_singleton x)

lemma gaussian_polar [Nontrivial E] :
    ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      (homeomorphUnitSphereProd E) =
      (volume : Measure E).toSphere.prod (gaussianPolarRadius E) := by
  let e := (homeomorphUnitSphereProd E).toMeasurableEquiv
  let c : ({0}ᶜ : Set E) → E := Subtype.val
  have hc : MeasurableEmbedding c := MeasurableEmbedding.subtype_coe (measurableSet_singleton 0).compl
  have he : ((volume : Measure E).comap c).map e =
      (volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) :=
    (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)).map_eq
  have hcomap : (stdGaussian E).comap c = ((volume : Measure E).comap c).withDensity
      (fun x => gaussianRadialDensity (Module.finrank ℝ E) ‖(x : E)‖) := by
    apply hc.map_injective
    rw [hc.map_comap]
    have hd : (fun x : ({0}ᶜ : Set E) => gaussianRadialDensity (Module.finrank ℝ E) ‖(x : E)‖) =
        (fun x : E => gaussianRadialDensity (Module.finrank ℝ E) ‖x‖) ∘ c := rfl
    rw [hd, map_withDensity_comp _ hc.measurable (by fun_prop)]
    rw [hc.map_comap, stdGaussian_density, restrict_withDensity hc.measurableSet_range]
  change ((stdGaussian E).comap c).map e = _
  rw [hcomap, map_withDensity_equiv _ e (by fun_prop), he]
  have hn (z : sphere (0 : E) 1 × Ioi (0 : ℝ)) : ‖(e.symm z : E)‖ = z.2.1 := by
    change ‖z.2.1 • (z.1 : E)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, mem_sphere_zero_iff_norm.mp z.1.2, mul_one]
  simp_rw [hn]
  rw [gaussianPolarRadius, ← withDensity_one (μ := (volume : Measure E).toSphere),
    prod_withDensity (by fun_prop) (by fun_prop)]
  simp

lemma gaussian_polar_reconstruction [Nontrivial E] :
    (((volume : Measure E).toSphere).prod (gaussianPolarRadius E)).map
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) = stdGaussian E := by
  rw [← gaussian_polar, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) ∘
      homeomorphUnitSphereProd E) = (Subtype.val : ({0}ᶜ : Set E) → E) := by
    funext x
    change ((homeomorphUnitSphereProd E).symm ((homeomorphUnitSphereProd E) x) : E) = _
    simp
  rw [he, (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).map_comap]
  simp only [Subtype.range_coe]
  apply Measure.restrict_eq_self_of_ae_mem
  simpa using (measure_eq_zero_iff_ae_notMem.mp (stdGaussian_singleton_eq_zero (0 : E)))

lemma gaussian_polar_mass [Nontrivial E] :
    (volume : Measure E).toSphere univ * gaussianPolarRadius E univ = 1 := by
  have h := congrArg (fun μ : Measure E => μ univ) (gaussian_polar_reconstruction (E := E))
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at h
  simpa only [preimage_univ, ← univ_prod_univ, Measure.prod_prod, measure_univ] using h

lemma gaussianPolarRadius_mass [Nontrivial E] :
    gaussianPolarRadius E univ = ((volume : Measure E).toSphere univ)⁻¹ := by
  have hs : (volume : Measure E).toSphere univ ≠ 0 :=
    (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume))
  have hf : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.mul_right_inj hs hf).mp
  rw [gaussian_polar_mass, ENNReal.mul_inv_cancel hs hf]

instance instIsFiniteMeasureElemRealIoiOfNatGaussianPolarRadiusOfNontrivial [Nontrivial E] : IsFiniteMeasure (gaussianPolarRadius E) where
  measure_univ_lt_top := by
    rw [gaussianPolarRadius_mass]
    exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
      (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalDirection_smul_sphere [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ = 1) :
    normalDirection (r • x) = x := by
  simp [normalDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, smul_smul, hr.ne']

lemma gaussian_normalDirection [Nontrivial E] :
    (stdGaussian E).map normalDirection = uniformDirection E := by
  rw [← gaussian_polar_reconstruction (E := E), Measure.map_map (by fun_prop) (by fun_prop)]
  have he : normalDirection ∘
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) =
      Subtype.val ∘ Prod.fst := by
    funext z
    exact normalDirection_smul_sphere z.2.2 (mem_sphere_zero_iff_norm.mp z.1.2)
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Subtype.val
    (((volume : Measure E).toSphere).prod (gaussianPolarRadius E)).fst = _
  rw [Measure.fst, Measure.map_fst_prod, gaussianPolarRadius_mass]
  rfl

instance instIsProbabilityMeasureUniformDirectionOfNontrivial [Nontrivial E] : IsProbabilityMeasure (uniformDirection E) := by
  rw [← gaussian_normalDirection]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BaseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

attribute [fun_prop] measurable_labels

lemma rowGram_eq_gram {d k : ℕ} (A : Rows d k) : rowGram A = Matrix.gram ℝ A := rfl

lemma kernelComponent_eq_starProjection {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (x : Vec d) :
    kernelComponent A x = (Submodule.span ℝ (Set.range A))ᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val, starProjection_eq_pairingLift hA]
  rfl

lemma labels_liftLabel {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (y : Labels k) :
    labels A (liftLabel A y) = y := pairings_pairingLift hA y

lemma labels_kernelComponent {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (x : Vec d) :
    labels A (kernelComponent A x) = 0 := by
  unfold kernelComponent
  ext i
  change ⟪A i, x - liftLabel A (labels A x)⟫ = 0
  rw [inner_sub_right]
  change labels A x i - labels A (liftLabel A (labels A x)) i = 0
  rw [labels_liftLabel hA, sub_self]

lemma labels_basePoint {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) (x : Vec d) : labels A (basePoint base A y x) = y := by
  have h₁ := labels_liftLabel hA y
  have h₂ := labels_kernelComponent hA x
  cases base <;> ext i <;>
    simp only [basePoint, labels, inner_add_right, inner_smul_right,
      show ⟪A i, liftLabel A y⟫ = y i from congrFun h₁ i,
      show ⟪A i, kernelComponent A x⟫ = 0 from congrFun h₂ i, mul_zero, add_zero]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_RadialIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma lintegral_pos_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ENNReal.ofReal (r ^ Module.finrank ℝ E) * ∫⁻ x, f (r • x) := by
  have hm : ENNReal.ofReal (r ^ Module.finrank ℝ E) •
      (volume : Measure E).map (fun x => r • x) = volume := by
    rw [Measure.map_addHaar_smul _ hr.ne', smul_smul,
      abs_of_pos (inv_pos.mpr (pow_pos hr _)), ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), ENNReal.ofReal_one, one_smul]
  conv_lhs => rw [← hm]
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop)]
  rfl

lemma lintegral_Ioi_pos_mul {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioi (0 : ℝ), f x = ENNReal.ofReal r * ∫⁻ x in Ioi (0 : ℝ), f (r * x) := by
  have hp : (fun x : ℝ => r * x) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hr]
  have hm : ENNReal.ofReal r •
      ((volume : Measure ℝ).restrict (Ioi 0)).map (fun x => r * x) = volume.restrict (Ioi 0) := by
    rw [← hp, ← Measure.restrict_map (by fun_prop) measurableSet_Ioi,
      Real.map_volume_mul_left hr.ne', Measure.restrict_smul, smul_smul,
      abs_of_pos (inv_pos.mpr hr), ← ENNReal.ofReal_mul hr.le,
      mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_smul]
    rw [hp]
  conv_lhs => rw [← hm]
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop)]
  rfl

lemma radial_lintegral_scale (n : ℕ) {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f (c * r) =
      ENNReal.ofReal ((c⁻¹) ^ (n + 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f r := by
  rw [lintegral_Ioi_pos_mul (inv_pos.mpr hc) (by fun_prop)]
  have he (r : ℝ) : ENNReal.ofReal ((c⁻¹ * r)^n) * f (c * (c⁻¹ * r)) =
      ENNReal.ofReal ((c⁻¹)^n) * (ENNReal.ofReal (r^n) * f r) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
      mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [pow_succ']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianPolarRadius_mass_integral [MeasurableSpace E] [BorelSpace E] :
    gaussianPolarRadius E univ =
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      gaussianRadialDensity (Module.finrank ℝ E) r := by
  rw [gaussianPolarRadius, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, Measure.volumeIoiPow]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1))) by fun_prop)
    (show Measurable (fun r : Ioi (0 : ℝ) => gaussianRadialDensity (Module.finrank ℝ E) r.1) by fun_prop)]
  exact lintegral_subtype_comap (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      gaussianRadialDensity (Module.finrank ℝ E) r)

omit [MeasurableSpace E] [BorelSpace E] in
lemma lintegral_gaussianPolarRadius [MeasurableSpace E] [BorelSpace E]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r : Ioi (0 : ℝ), g r.1 ∂gaussianPolarRadius E =
      ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
          gaussianRadialDensity (Module.finrank ℝ E) r * g r := by
  rw [gaussianPolarRadius, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simpa only [Pi.mul_apply, mul_assoc] using
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        gaussianRadialDensity (Module.finrank ℝ E) r * g r)

lemma gaussianRadialDensity_mul (n q : ℕ) (r s : ℝ) :
    gaussianRadialDensity q r * gaussianRadialDensity n (r * s) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-((n + q : ℕ) : ℝ) / 2) *
        Real.exp (-(1 + s^2) * r^2 / 2)) := by
  unfold gaussianRadialDensity
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_mul_mul_comm, ← Real.rpow_add (by positivity), ← Real.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring

lemma radial_power_gaussian_product {n q d : ℕ} (hq : 1 ≤ q) (hd : n + q = d)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ENNReal.ofReal (r ^ (q - 1)) * gaussianRadialDensity q r *
        (ENNReal.ofReal (r ^ n) * gaussianRadialDensity n (r * s)) =
      ENNReal.ofReal (r ^ (d - 1)) *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
          Real.exp (-(1 + s^2) * r^2 / 2)) := by
  rw [mul_mul_mul_comm, ← ENNReal.ofReal_mul (by positivity), ← pow_add,
    gaussianRadialDensity_mul, hd]
  have hn : q - 1 + n = d - 1 := by omega
  rw [hn]

lemma radial_gaussian_integral [Nontrivial E] {a : ℝ} (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
        Real.exp (-a * r^2 / 2)) =
      ENNReal.ofReal (a ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        ((volume : Measure E).toSphere univ)⁻¹ := by
  have he (r : ℝ) : ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
      Real.exp (-a * r^2 / 2)) = gaussianRadialDensity (Module.finrank ℝ E) (Real.sqrt a * r) := by
    unfold gaussianRadialDensity
    rw [mul_pow, Real.sq_sqrt ha.le]
    ring_nf
  simp_rw [he]
  rw [radial_lintegral_scale _ (Real.sqrt_pos.mpr ha) (by fun_prop),
    ← gaussianPolarRadius_mass_integral, gaussianPolarRadius_mass]
  congr 2
  rw [Nat.sub_add_cancel Module.finrank_pos, Real.sqrt_eq_rpow,
    ← Real.rpow_neg ha.le, ← Real.rpow_natCast,
    ← Real.rpow_mul ha.le]
  congr 1
  ring

lemma sphere_area [Nontrivial E] : (volume : Measure E).toSphere univ =
    ENNReal.ofReal (2 * Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
      Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2)) := by
  have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hp : Real.sqrt Real.pi ^ Module.finrank ℝ E =
      Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [Measure.toSphere_apply_univ, InnerProductSpace.volume_ball, ENNReal.ofReal_one,
    one_pow, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), hp, Real.Gamma_add_one (by positivity)]
  congr 1
  field_simp

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BallJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Determinant
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma det_id_add_smulRight (φ : E →ₗ[ℝ] ℝ) (v : E) :
    (LinearMap.id + φ.smulRight v).det = 1 + φ v := by
  classical
  let b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  have he : Matrix.vecMulVec (fun i => b.repr v i) (fun i => φ (b i)) =
      Matrix.replicateCol Unit (fun i => b.repr v i) *
        Matrix.replicateRow Unit (fun i => φ (b i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec]
  change (1 + Matrix.vecMulVec (fun i => b.repr v i) (fun i => φ (b i))).det = _
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  have hφ := congrArg φ (b.sum_repr v)
  simpa only [dotProduct, map_sum, map_smul, smul_eq_mul, mul_comm] using hφ

end Determinant

section Ball
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma one_sub_norm_sq_pos {x : E} (hx : x ∈ ball (0 : E) 1) : 0 < 1 - ‖x‖^2 := by
  have h := mem_ball_zero_iff.mp hx
  nlinarith [norm_nonneg x]

omit [FiniteDimensional ℝ E] in
lemma ballStretch_eq : EqOn (ballStretch : E → E)
    OpenPartialHomeomorph.univUnitBall.symm (ball 0 1) := by
  intro x hx
  rw [ballStretch, OpenPartialHomeomorph.univUnitBall_symm_apply,
    neg_div, Real.rpow_neg (one_sub_norm_sq_pos hx).le, Real.sqrt_eq_rpow]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_ballStretch {x : E} (hx : x ∈ ball (0 : E) 1) :
    HasFDerivAt ballStretch (ballStretchDeriv x) x := by
  have hb := one_sub_norm_sq_pos hx
  have h := (((hasFDerivAt_id x).norm_sq.const_sub 1).rpow_const
    (p := -(1 : ℝ) / 2) (Or.inl hb.ne')).smul (hasFDerivAt_id x)
  apply h.congr_fderiv
  ext y
  simp only [ballStretchDeriv, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    _root_.neg_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, id_eq]
  rw [Real.rpow_sub hb, Real.rpow_one]
  module

lemma det_ballStretchDeriv {x : E} (hx : x ∈ ball (0 : E) 1) :
    (ballStretchDeriv x).det =
      (1 - ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1) := by
  have hb := one_sub_norm_sq_pos hx
  change ((ballStretchDeriv x).toLinearMap).det = _
  have he : (ballStretchDeriv x).toLinearMap =
      (1 - ‖x‖^2) ^ (-(1 : ℝ) / 2) • (LinearMap.id +
        (((1 - ‖x‖^2)⁻¹ • innerSL ℝ x).toLinearMap).smulRight x) := by
    ext y
    simp [ballStretchDeriv, smul_smul, mul_assoc]
  rw [he, LinearMap.det_smul, det_id_add_smulRight]
  have hi : 1 + (((1 - ‖x‖^2)⁻¹ • innerSL ℝ x).toLinearMap) x = (1 - ‖x‖^2)⁻¹ := by
    simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
    ring
  rw [hi, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
    ← Real.rpow_neg_one, ← Real.rpow_add hb]
  congr 1
  ring

omit [FiniteDimensional ℝ E] in
lemma ballStretch_eq_inv_sqrt {x : E} (hx : x ∈ ball (0 : E) 1) :
    ballStretch x = (Real.sqrt (1 - ‖x‖^2))⁻¹ • x := by
  rw [ballStretch, neg_div, Real.rpow_neg (one_sub_norm_sq_pos hx).le, Real.sqrt_eq_rpow]

omit [FiniteDimensional ℝ E] in
lemma one_add_norm_ballStretch_sq {x : E} (hx : x ∈ ball (0 : E) 1) :
    1 + ‖ballStretch x‖^2 = (1 - ‖x‖^2)⁻¹ := by
  have hb := one_sub_norm_sq_pos hx
  rw [ballStretch_eq_inv_sqrt hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)), mul_pow, inv_pow, Real.sq_sqrt hb.le]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
lemma ballStretch_weight {x : E} (hx : x ∈ ball (0 : E) 1) (q : ℕ) :
    ENNReal.ofReal ((1 - ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1)) *
        ENNReal.ofReal ((1 + ‖ballStretch x‖^2) ^
          (-((Module.finrank ℝ E + q : ℕ) : ℝ) / 2)) =
      ENNReal.ofReal ((1 - ‖x‖^2) ^ (((q : ℝ) - 2) / 2)) := by
  have hb := one_sub_norm_sq_pos hx
  rw [← ENNReal.ofReal_mul (by positivity), one_add_norm_ballStretch_sq hx,
    Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, ← Real.rpow_add hb]
  congr 2
  push_cast
  ring

lemma lintegral_ballStretch [MeasurableSpace E] [BorelSpace E] (g : E → ℝ≥0∞) :
    ∫⁻ x, g x = ∫⁻ y in ball (0 : E) 1,
      ENNReal.ofReal ((1 - ‖y‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1)) *
        g (ballStretch y) := by
  have hi : InjOn (ballStretch : E → E) (ball 0 1) := by
    exact OpenPartialHomeomorph.univUnitBall.symm.injOn.congr ballStretch_eq.symm
  have he : (ballStretch : E → E) '' ball 0 1 = univ := by
    rw [ballStretch_eq.image_eq]
    exact OpenPartialHomeomorph.univUnitBall.symm.image_source_eq_target
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure E)), ← he]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (fun x hx => (hasFDerivAt_ballStretch hx).hasFDerivWithinAt) hi g]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [det_ballStretchDeriv hx, abs_of_pos (Real.rpow_pos_of_pos (one_sub_norm_sq_pos hx) _)]

end Ball
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_SphereSubspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_orthogonalProjectionOnto (U : Submodule ℝ E) :
    (stdGaussian E).map U.orthogonalProjectionOnto = stdGaussian U := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have he (x : E) : ⟪U.orthogonalProjectionOnto x, t⟫ = ⟪x, (t : E)⟫ := by
    change ⟪U.starProjection x, (t : E)⟫ = _
    rw [real_inner_comm, pairing_starProjection U t.2, real_inner_comm]
  simp_rw [he]
  change charFun (stdGaussian E) (t : E) = _
  rw [charFun_stdGaussian, charFun_stdGaussian]
  rfl

lemma gaussian_subspace_map (U : Submodule ℝ E) :
    (stdGaussian U).map (Subtype.val : U → E) = (stdGaussian E).map U.starProjection := by
  rw [← gaussian_orthogonalProjectionOnto U, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma gaussian_subspace_sum (U : Submodule ℝ E) :
    ((stdGaussian U).prod (stdGaussian Uᗮ)).map (fun z => (z.1 : E) + (z.2 : E)) =
      stdGaussian E := by
  rw [← gaussian_orthogonal_sum U, ← gaussian_subspace_map, ← gaussian_subspace_map,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma subspace_sum_norm_sq [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : Submodule ℝ E) (x : U) (z : Uᗮ) :
    ‖(x : E) + (z : E)‖^2 = ‖x‖^2 + ‖z‖^2 := by
  have ho : ⟪(x : E), (z : E)⟫ = 0 :=
    (real_inner_comm _ _).trans ((Submodule.mem_orthogonal' U (z : E)).mp z.2 _ x.2)
  simp [norm_add_sq_real, ho]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalDirection_pos_smul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) (x : E) :
    normalDirection (r • x) = normalDirection x := by
  simp [normalDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    _root_.mul_inv_rev, smul_smul, hr.ne']

lemma sphere_subspace_gaussian_integral (U : Submodule ℝ E) [Nontrivial E]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂uniformDirection E =
      ∫⁻ x : U, ∫⁻ z : Uᗮ, g (normalDirection ((x : E) + (z : E)))
        ∂stdGaussian Uᗮ ∂stdGaussian U := by
  rw [← gaussian_normalDirection, lintegral_map hg (by fun_prop),
    ← gaussian_subspace_sum U, lintegral_map (by fun_prop) (by fun_prop),
    lintegral_prod _ (by fun_prop)]

lemma sphere_subspace_polar_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ r : Ioi (0 : ℝ), ∫⁻ x : U,
        gaussianRadialDensity (Module.finrank ℝ U) ‖x‖ *
          g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E)))
          ∂volume ∂gaussianPolarRadius Uᗮ ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_gaussian_integral U hg]
  have hp (x : U) : (∫⁻ z : Uᗮ, g (normalDirection ((x : E) + (z : E))) ∂stdGaussian Uᗮ) =
      ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ r : Ioi (0 : ℝ),
        g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E)))
          ∂gaussianPolarRadius Uᗮ ∂(volume : Measure Uᗮ).toSphere := by
    rw [← gaussian_polar_reconstruction (E := Uᗮ), lintegral_map (by fun_prop) (by fun_prop),
      lintegral_prod _ (by fun_prop)]
    rfl
  simp_rw [hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro r
  rw [stdGaussian_density, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

lemma radial_subspace_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ] (s : ℝ) :
    ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1 ^ Module.finrank ℝ U) *
        gaussianRadialDensity (Module.finrank ℝ U) (r.1 * s) ∂gaussianPolarRadius Uᗮ =
      ENNReal.ofReal ((1 + s^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        ((volume : Measure E).toSphere univ)⁻¹ := by
  rw [lintegral_gaussianPolarRadius (E := Uᗮ) (g := fun r : ℝ =>
    ENNReal.ofReal (r ^ Module.finrank ℝ U) *
      gaussianRadialDensity (Module.finrank ℝ U) (r * s)) (by fun_prop)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
          Real.exp (-(1 + s^2) * r^2 / 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact radial_power_gaussian_product Module.finrank_pos U.finrank_add_finrank_orthogonal hr.le s
    _ = _ := radial_gaussian_integral (by positivity)

lemma scaled_subspace_integral (U : Submodule ℝ E) (z : sphere (0 : Uᗮ) 1)
    (r : Ioi (0 : ℝ)) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : U, gaussianRadialDensity (Module.finrank ℝ U) ‖x‖ *
        g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E))) =
      ∫⁻ x : U, ENNReal.ofReal (r.1 ^ Module.finrank ℝ U) *
        gaussianRadialDensity (Module.finrank ℝ U) (r.1 * ‖x‖) *
          g (normalDirection ((x : E) + ((z : Uᗮ) : E))) := by
  rw [lintegral_pos_smul r.2 (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2]
  have he : ((r.1 • x : U) : E) + r.1 • ((z : Uᗮ) : E) =
      r.1 • ((x : E) + ((z : Uᗮ) : E)) := by simp [smul_add]
  rw [he, normalDirection_pos_smul r.2, mul_assoc]

lemma sphere_subspace_slope_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ *
        ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ x : U,
          ENNReal.ofReal ((1 + ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
            g (normalDirection ((x : E) + ((z : Uᗮ) : E)))
          ∂volume ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_polar_integral U hg, ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro z
  simp_rw [scaled_subspace_integral U z _ hg]
  rw [lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const _ (by fun_prop), radial_subspace_integral]
  ac_rfl

lemma normalDirection_ballStretch (U : Submodule ℝ E) {x : U}
    (hx : x ∈ ball (0 : U) 1) (z : sphere (0 : Uᗮ) 1) :
    normalDirection (((ballStretch x : U) : E) + ((z : Uᗮ) : E)) =
      (x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E) := by
  have hb := one_sub_norm_sq_pos hx
  have hs := Real.sqrt_pos.mpr hb
  have hz : ‖(z : Uᗮ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hn : ‖(x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)‖ = 1 := by
    have h := subspace_sum_norm_sq U x (Real.sqrt (1 - ‖x‖^2) • (z : Uᗮ))
    simp only [Submodule.coe_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs, hz, mul_one, Real.sq_sqrt hb.le] at h
    nlinarith [norm_nonneg ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E))]
  have he : ((ballStretch x : U) : E) + ((z : Uᗮ) : E) =
      (Real.sqrt (1 - ‖x‖^2))⁻¹ •
        ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)) := by
    rw [ballStretch_eq_inv_sqrt hx]
    change (Real.sqrt (1 - ‖x‖^2))⁻¹ • (x : E) + ((z : Uᗮ) : E) = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [he, normalDirection_smul_sphere (inv_pos.mpr hs) hn]

lemma sphere_subspace_surface_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ *
        ∫⁻ x : U in ball 0 1,
          ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
            ∫⁻ z : sphere (0 : Uᗮ) 1,
              g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E))
              ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_slope_integral U hg]
  congr 1
  have ht (z : sphere (0 : Uᗮ) 1) :
      (∫⁻ x : U, ENNReal.ofReal ((1 + ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        g (normalDirection ((x : E) + ((z : Uᗮ) : E)))) =
      ∫⁻ x : U in ball 0 1,
        ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
          g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)) := by
    rw [lintegral_ballStretch]
    apply setLIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [normalDirection_ballStretch U hx z, ← mul_assoc,
      ← U.finrank_add_finrank_orthogonal, ballStretch_weight hx]
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [lintegral_const_mul _ (by fun_prop)]

lemma surface_lintegral_eq_gaussian [Nontrivial E] {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : sphere (0 : E) 1, g (z : E) ∂(volume : Measure E).toSphere =
      (volume : Measure E).toSphere univ * ∫⁻ x, g (normalDirection x) ∂stdGaussian E := by
  have he : (∫⁻ x, g (normalDirection x) ∂stdGaussian E) = ∫⁻ x, g x ∂uniformDirection E := by
    rw [← gaussian_normalDirection, lintegral_map hg (by fun_prop)]
  rw [he, uniformDirection, lintegral_map hg (by fun_prop), lintegral_smul_measure]
  change _ = (volume : Measure E).toSphere univ *
    (((volume : Measure E).toSphere univ)⁻¹ *
      ∫⁻ z : sphere (0 : E) 1, g (z : E) ∂(volume : Measure E).toSphere)
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)) (measure_ne_top _ _), one_mul]

lemma sphere_subspace_gaussian_fiber_integral (U : Submodule ℝ E)
    [Nontrivial E] [Nontrivial Uᗮ] {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure Uᗮ).toSphere univ *
        ∫⁻ x : U in ball 0 1,
          ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
            ∫⁻ z : E, g ((x : E) + Real.sqrt (1 - ‖x‖^2) •
              normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E := by
  rw [sphere_subspace_surface_integral U hg, mul_assoc]
  congr 1
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [surface_lintegral_eq_gaussian (E := Uᗮ) (g := fun z =>
    g ((x : E) + Real.sqrt (1 - ‖x‖^2) • (z : E))) (by fun_prop)]
  have he : (∫⁻ z : Uᗮ, g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((normalDirection z : Uᗮ) : E))
      ∂stdGaussian Uᗮ) = ∫⁻ z : E, g ((x : E) + Real.sqrt (1 - ‖x‖^2) •
        normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E := by
    rw [← gaussian_orthogonalProjectionOnto Uᗮ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he]
  ac_rfl

lemma sphere_area_ratio (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ] :
    ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure Uᗮ).toSphere univ =
      ENNReal.ofReal (Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
        (Real.pi ^ (((Module.finrank ℝ U : ℕ) : ℝ) / 2) *
          Real.Gamma (((Module.finrank ℝ Uᗮ : ℕ) : ℝ) / 2))) := by
  have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hq : 0 < ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have he : ((Module.finrank ℝ E : ℕ) : ℝ) =
      ((Module.finrank ℝ U : ℕ) : ℝ) + ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) := by
    exact_mod_cast U.finrank_add_finrank_orthogonal.symm
  have hp : Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) =
      Real.pi ^ (((Module.finrank ℝ U : ℕ) : ℝ) / 2) *
        Real.pi ^ (((Module.finrank ℝ Uᗮ : ℕ) : ℝ) / 2) := by
    rw [he, add_div, Real.rpow_add Real.pi_pos]
  rw [sphere_area, sphere_area, ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hp]
  field_simp

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_SphereDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma volume_pairings_on_span {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    let U := Submodule.span ℝ (Set.range v)
    (volume : Measure U).map (fun x : U => fun i => ⟪v i, (x : E)⟫) =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) • volume := by
  let U := Submodule.span ℝ (Set.range v)
  let F : U → Fin n → ℝ := fun x i => ⟪v i, (x : E)⟫
  let h : (Fin n → ℝ) → ℝ≥0∞ := fun y => gaussianRadialDensity n ‖pairingLift v y‖
  have hF : Measurable F := by unfold F; fun_prop
  have hh : Measurable h := by unfold h; fun_prop
  have hj : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
    Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hU : Module.finrank ℝ U = n := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hv
  have hl (x : U) : pairingLift v (F x) = (x : E) := by
    rw [← starProjection_eq_pairingLift hv]
    exact U.starProjection_eq_self_iff.mpr x.2
  have hg : (stdGaussian U).map F = (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) := by
    rw [← gaussian_orthogonalProjectionOnto U, Measure.map_map hF (by fun_prop)]
    congr 1
    funext x i
    exact pairing_starProjection U (Submodule.subset_span (Set.mem_range_self i)) x
  have hd : (stdGaussian U) = (volume : Measure U).withDensity (h ∘ F) := by
    rw [stdGaussian_density, hU]
    congr 1
    funext x
    simp only [Function.comp_apply, h, hl, Submodule.norm_coe]
  have he : ((volume : Measure U).map F).withDensity h =
      (ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) •
        (volume : Measure (Fin n → ℝ))).withDensity h := by
    rw [← map_withDensity_comp _ hF hh, ← hd, hg, gaussian_pairings_density hv,
      withDensity_smul_measure, ← withDensity_smul _ hh]
    congr 1
    funext y
    change ENNReal.ofReal _ = ENNReal.ofReal _ * gaussianRadialDensity n ‖pairingLift v y‖
    rw [gaussianRadialDensity, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hz (y : Fin n → ℝ) : h y ≠ 0 := by
    dsimp [h, gaussianRadialDensity]
    positivity
  have ht (y : Fin n → ℝ) : h y ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv := congrArg (fun μ : Measure (Fin n → ℝ) => μ.withDensity (fun y => (h y)⁻¹)) he
  rw [withDensity_inv_same hh (Filter.Eventually.of_forall hz) (Filter.Eventually.of_forall ht),
    withDensity_inv_same hh (Filter.Eventually.of_forall hz) (Filter.Eventually.of_forall ht)] at hinv
  exact hinv

lemma lintegral_pairingLift {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    let U := Submodule.span ℝ (Set.range v)
    ∫⁻ x : U, g (x : E) ∂volume =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) * ∫⁻ y, g (pairingLift v y) := by
  let U := Submodule.span ℝ (Set.range v)
  have he := congrArg (fun μ : Measure (Fin n → ℝ) => ∫⁻ y, g (pairingLift v y) ∂μ)
    (volume_pairings_on_span hv)
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_smul_measure] at he
  change _ = ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
    ∫⁻ y, g (pairingLift v y) at he
  convert he using 1
  apply lintegral_congr
  intro x
  rw [← starProjection_eq_pairingLift hv, U.starProjection_eq_self_iff.mpr x.2]

lemma sphere_fiber_integral {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hn : n < Module.finrank ℝ E) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂uniformDirection E = ∫⁻ y, sphericalPairingsDensity v y *
      ∫⁻ z, g (pairingLift v y + Real.sqrt (1 - ‖pairingLift v y‖^2) •
        normalDirection ((Submodule.span ℝ (Set.range v))ᗮ.starProjection z)) ∂stdGaussian E := by
  let U := Submodule.span ℝ (Set.range v)
  have hU : Module.finrank ℝ U = n := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hv
  have hV : Module.finrank ℝ Uᗮ = Module.finrank ℝ E - n := by
    have ha := U.finrank_add_finrank_orthogonal
    omega
  have hVr : ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) = ((Module.finrank ℝ E : ℕ) : ℝ) - n := by
    rw [hV, Nat.cast_sub hn.le]
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  let : Nontrivial Uᗮ := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ Uᗮ)
  let C : ℝ := Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
    (Real.pi ^ ((n : ℝ) / 2) * Real.Gamma ((((Module.finrank ℝ E : ℕ) : ℝ) - n) / 2))
  let β : ℝ := (((Module.finrank ℝ E : ℕ) : ℝ) - n - 2) / 2
  let G : E → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 - ‖x‖^2)^β) *
    ∫⁻ z, g (x + Real.sqrt (1 - ‖x‖^2) • normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E
  have hG : Measurable G := by unfold G; fun_prop
  have hJ : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
    Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hC : 0 < C := by
    dsimp [C]
    have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    have hq : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) - n := by
      rw [← hVr]
      exact Nat.cast_pos.mpr Module.finrank_pos
    positivity
  rw [sphere_subspace_gaussian_fiber_integral U hg, sphere_area_ratio, hU, hVr]
  change ENNReal.ofReal C * (∫⁻ x : U in ball 0 1, G (x : E)) = _
  have hi : (∫⁻ x : U in ball 0 1, G (x : E)) =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
        ∫⁻ y, (ball (0 : E) 1).indicator G (pairingLift v y) := by
    have he := lintegral_pairingLift hv (g := (ball (0 : E) 1).indicator G)
      (hG.indicator measurableSet_ball)
    convert he using 1
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro x
    rfl
  have hI : Measurable (fun y => (ball (0 : E) 1).indicator G (pairingLift v y)) :=
    (hG.indicator measurableSet_ball).comp (continuous_pairingLift v).measurable
  rw [hi, ← mul_assoc, ← lintegral_const_mul _ hI]
  apply lintegral_congr
  intro y
  by_cases hy : ‖pairingLift v y‖ < 1
  · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hy)]
    dsimp [G, sphericalPairingsDensity]
    rw [ite_eq_left hy, ← mul_assoc, ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    congr 1
    dsimp [C, β]
    ring
  · rw [Set.indicator_of_notMem (mt mem_ball_zero_iff.mp hy)]
    simp [sphericalPairingsDensity, hy]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_BaseDisintegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma baseDensity_lt_top {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    baseDensity base A y < ∞ := by
  cases base <;> dsimp only [baseDensity] <;> split_ifs <;> simp

lemma baseDensity_spherical {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) : baseDensity .spherical A y = sphericalPairingsDensity A y := by
  simp only [baseDensity, ite_eq_left hA, sphericalPairingsDensity,
    finrank_euclideanSpace, Fintype.card_fin]
  rfl

lemma base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {g : Vec d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂base.measure d = ∫⁻ y, baseDensity base A y *
      ∫⁻ x, g x ∂baseFiber base A y := by
  simp_rw [baseFiber_eq_map, lintegral_map hg (measurable_basePoint_fixed base A _)]
  cases base
  · change (∫⁻ x, g x ∂uniformDirection (Vec d)) = _
    rw [sphere_fiber_integral hA (by simpa using hk) hg]
    apply lintegral_congr
    intro y
    rw [baseDensity_spherical hA]
    congr 1
    apply lintegral_congr
    intro x
    congr 1
    simp only [basePoint, kernelComponent_eq_starProjection hA, normalDirection,
      smul_smul, div_eq_mul_inv]
    rfl
  · change (∫⁻ x, g x ∂stdGaussian (Vec d)) = _
    rw [gaussian_fiber_integral hA hg]
    apply lintegral_congr
    intro y
    rw [baseDensity, ite_eq_left hA]
    congr 1
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    apply lintegral_congr
    intro x
    rw [basePoint, kernelComponent_eq_starProjection hA]
    rfl

lemma weighted_base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f g : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(base.measure d).withDensity f =
      ∫⁻ y, baseDensity base A y * ∫⁻ x, f x * g x ∂baseFiber base A y := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
  exact base_lintegral hA hk base (hf.mul hg)

lemma tiltMass_le {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) : tiltMass base f A y ≤ L := by
  unfold tiltMass
  calc
    _ ≤ ∫⁻ _, L ∂baseFiber base A y := lintegral_mono hL
    _ = L := by simp

lemma tiltMass_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    tiltMass base f A y ≠ ∞ := ne_top_of_le_ne_top hL (tiltMass_le base hfL A y)

lemma projectedDensity_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    projectedDensity base f A y ≠ ∞ :=
  ENNReal.mul_ne_top (baseDensity_lt_top base A y).ne (tiltMass_ne_top base hL hfL A y)

lemma weighted_fiber_labels {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {g : Labels k → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, f x * g (labels A x) ∂baseFiber base A y = tiltMass base f A y * g y := by
  have hfg : Measurable (fun x => f x * g (labels A x)) := by fun_prop
  rw [baseFiber_eq_map, lintegral_map hfg (measurable_basePoint_fixed base A y)]
  simp_rw [labels_basePoint hA]
  rw [lintegral_mul_const _ (show Measurable (fun x => f (basePoint base A y x)) from
    hf.comp (measurable_basePoint_fixed base A y))]
  congr 1
  rw [tiltMass, baseFiber_eq_map, lintegral_map hf (measurable_basePoint_fixed base A y)]

lemma projected_measure {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    ((base.measure d).withDensity f).map (labels A) =
      volume.withDensity (projectedDensity base f A) := by
  have hl : Measurable (labels A) := by unfold labels; fun_prop
  have hp0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hp0
  have hp : Measurable (projectedDensity base f A) := hp0
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hl]
  rw [weighted_base_lintegral hA hk base hf (g := fun x => g (labels A x)) (hg.comp hl)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hp hg]
  simp only [Pi.mul_apply, weighted_fiber_labels hA base _ hf hg, projectedDensity, mul_assoc]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_FrameTubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma baseProjectionConstant_pos {d k : ℕ} (hk : k < d) (base : BaseLaw) :
    0 < baseProjectionConstant base d k := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdk : 0 < (d : ℝ) - k := sub_pos.mpr (by exact_mod_cast hk)
  cases base <;> unfold baseProjectionConstant <;> positivity

lemma baseDensity_le_sup {d k : ℕ} (hk : k + 2 ≤ d) (base : BaseLaw)
    (A : Rows d k) (y : Labels k) : baseDensity base A y ≤
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram A).det) := by
  have hC := (baseProjectionConstant_pos (by omega : k < d) base).le
  by_cases hA : LinearIndependent ℝ A
  · rw [baseDensity.eq_def, ite_eq_left hA]
    cases base
    · dsimp only [baseProjectionConstant] at hC ⊢
      split_ifs with hy
      · apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        have hb : 0 ≤ 1 - ‖liftLabel A y‖^2 := by nlinarith [norm_nonneg (liftLabel A y)]
        have he : 0 ≤ ((d : ℝ) - k - 2) / 2 := by
          have : (k : ℝ) + 2 ≤ d := by exact_mod_cast hk
          linarith
        exact mul_le_of_le_one_right hC (Real.rpow_le_one hb (by nlinarith [sq_nonneg ‖liftLabel A y‖]) he)
      · exact bot_le
    · dsimp only [baseProjectionConstant] at hC ⊢
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)))
  · rw [baseDensity.eq_def, ite_eq_right hA]
    exact bot_le

lemma baseDensity_le_orthonormal {d k : ℕ} (hk : k + 2 ≤ d) (base : BaseLaw)
    {A : Rows d k} (hA : Orthonormal ℝ A) (y : Labels k) :
    baseDensity base A y ≤ ENNReal.ofReal (baseProjectionConstant base d k) := by
  simpa only [rowGram_eq_gram, Matrix.gram_eq_one_iff_orthonormal.mpr hA,
    Matrix.det_one, Real.sqrt_one, div_one] using baseDensity_le_sup hk base A y

lemma projected_base_measure {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) : (base.measure d).map (labels A) =
      volume.withDensity (baseDensity base A) := by
  have h := projected_measure hA hk base (f := fun _ => 1) measurable_const
  have hμ : (base.measure d).withDensity (fun _ => 1) = base.measure d := by
    exact withDensity_one
  have hp : projectedDensity base (fun _ => 1) A = baseDensity base A := by
    funext y
    simp only [projectedDensity, tiltMass, lintegral_one, measure_univ, mul_one]
  rw [hμ, hp] at h
  exact h

lemma orthonormal_in_orthogonal {d q : ℕ} (U : Submodule ℝ (Vec d))
    (hq : q ≤ Module.finrank ℝ Uᗮ) :
    ∃ v : Fin q → Vec d, Orthonormal ℝ v ∧ ∀ i, v i ∈ Uᗮ := by
  let b := stdOrthonormalBasis ℝ Uᗮ
  let v : Fin q → Uᗮ := fun i => b (Fin.castLE hq i)
  refine ⟨fun i => (v i : Vec d), ?_, fun i => (v i).2⟩
  exact (b.orthonormal.comp (Fin.castLE hq) (Fin.castLE_injective hq)).comp_linearIsometry Uᗮ.subtypeₗᵢ

lemma pairing_le_infDist {d : ℕ} (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    {p v : Vec d} (hp : p ∈ L) (hv : v ∈ L.directionᗮ) (hvnorm : ‖v‖ = 1) (x : Vec d) :
    |⟪v, x - p⟫| ≤ Metric.infDist x L := by
  have ho : ⟪v, (orthogonalProjection L x : Vec d) - p⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.vsub_mem_direction (orthogonalProjection_mem x) hp) hv
  have he : ⟪v, x - p⟫ = ⟪v, x - (orthogonalProjection L x : Vec d)⟫ := by
    rw [inner_sub_right] at ho
    simp only [inner_sub_right]
    linarith
  rw [he, ← dist_orthogonalProjection_eq_infDist, dist_eq_norm]
  simpa only [hvnorm, one_mul] using abs_real_inner_le_norm v (x - (orthogonalProjection L x : Vec d))

lemma base_affine_tube {d q : ℕ} (hq : q + 2 ≤ d) (base : BaseLaw)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction + q ≤ d) {r : ℝ} (hr : 0 < r) :
    (base.measure d) {x | Metric.infDist x L ≤ r} ≤
      (ENNReal.ofReal (baseProjectionConstant base d q) * 2^q) * ENNReal.ofReal (r^q) := by
  have hdim : q ≤ Module.finrank ℝ L.directionᗮ := by
    have he := L.direction.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace_fin] at he
    omega
  obtain ⟨v, hv, hvin⟩ := orthonormal_in_orthogonal L.direction hdim
  obtain ⟨p, hp⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty L)
  let c := labels v p
  let s : Set (Labels q) := Set.pi univ (fun i => Icc (c i - r) (c i + r))
  have hs : MeasurableSet s := MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have hsub : {x | Metric.infDist x L ≤ r} ⊆ (labels v) ⁻¹' s := by
    intro x hx
    simp only [Set.mem_preimage, s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have hi := (pairing_le_infDist L hp (hvin i) (hv.norm_eq_one i) x).trans hx
    rw [inner_sub_right, abs_le] at hi
    exact ⟨by dsimp [c, labels]; linarith [hi.1], by dsimp [c, labels]; linarith [hi.2]⟩
  calc
    _ ≤ (base.measure d) ((labels v) ⁻¹' s) := measure_mono hsub
    _ = ((base.measure d).map (labels v)) s :=
      (Measure.map_apply (by unfold labels; fun_prop) hs).symm
    _ = ∫⁻ y in s, baseDensity base v y := by
      rw [projected_base_measure hv.linearIndependent (by omega) base, withDensity_apply _ hs]
    _ ≤ ∫⁻ _y in s, ENNReal.ofReal (baseProjectionConstant base d q) :=
      setLIntegral_mono' hs (fun y _ => baseDensity_le_orthonormal hq base hv y)
    _ = ENNReal.ofReal (baseProjectionConstant base d q) * ENNReal.ofReal (2*r)^q := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      congr 1
      change (Measure.pi (fun _ : Fin q => volume)) s = _
      rw [Measure.pi_pi]
      simp only [Real.volume_Icc, show ∀ i, c i + r - (c i - r) = 2*r from fun _ => by ring]
      simp
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num), mul_pow, ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow hr.le, mul_assoc]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_AffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma replica_integral_of_affine_moment {ν : Measure E} [IsFiniteMeasure ν]
    (m n : ℕ) (p : E) (C : ℝ≥0∞)
    (hmoment : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n →
      ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ C) :
    ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤ C^n := by
  induction n with
  | zero => simp [PosteriorRegression.replicaWeight]
  | succ n ih =>
    have hinner (v : Fin n → E) :
        ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν ≤
          PosteriorRegression.replicaWeight m p v * C := by
      simp_rw [PosteriorRegression.replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply hmoment _ inferInstance
      rw [AffineSubspace.direction_mk']
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [AffineSubspace.direction_mk', Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hdim
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := PosteriorRegression.lintegral_pi_snoc ν _
            (PosteriorRegression.measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v * C
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v
          ∂Measure.pi (fun _ => ν)) * C := lintegral_mul_const _
            (PosteriorRegression.measurable_replicaWeight m p n)
      _ ≤ C^n * C := mul_le_mul' (ih (fun L hL hdim => hmoment L hL (by omega))) le_rfl
      _ = _ := (pow_succ _ _).symm

lemma ae_replica_independent_of_affine_null {ν : Measure E} [IsFiniteMeasure ν]
    (p : E) (n : ℕ)
    (hnull : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n → ν L = 0) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), LinearIndependent ℝ (fun j => v j - p) := by
  suffices h : ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 by
    filter_upwards [h] with v hv
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [PosteriorRegression.det_gram_eq_prod_gramSchmidt]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [PosteriorRegression.ae_pi_snoc ν (PosteriorRegression.measurableSet_gramSchmidt_ne_zero p (n+1))]
    filter_upwards [ih (fun L hL hdim => hnull L hL (by omega))] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : Module.finrank ℝ L.direction < n + 1 := by
      dsimp only [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hh
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      simpa using hnull L inferInstance hdim
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [PosteriorRegression.norm_gramSchmidt_sub_eq_affine_infDist, PosteriorRegression.image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [PosteriorRegression.gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

end Generic

lemma base_affine_null {d : ℕ} (hd : 3 ≤ d) (base : BaseLaw)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction < d) : (base.measure d) L = 0 := by
  let C := ENNReal.ofReal (baseProjectionConstant base d 1) * 2
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hb (n : ℕ) : (base.measure d) L ≤ C * ENNReal.ofReal ((1/2 : ℝ)^n) := by
    calc
      _ ≤ (base.measure d) {x | Metric.infDist x L ≤ (1/2 : ℝ)^n} := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hx]
        positivity
      _ ≤ _ := by simpa [C] using base_affine_tube hd base L (by omega) (r := (1/2 : ℝ)^n) (by positivity)
  have hlim : Tendsto (fun n : ℕ => C * ENNReal.ofReal ((1/2 : ℝ)^n)) atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC)
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le

lemma base_affine_inverse_bound {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hm : 1 ≤ m) (base : BaseLaw) (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction < m) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ k) ∂base.measure d ≤
      1 + (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1)) * 2^(k+1) := by
  let : NeZero d := ⟨by omega⟩
  have h := PosteriorRegression.inverse_moment_of_tube_bound (base.measure d)
    (fun x => Metric.infDist x L) k (Metric.continuous_infDist_pt _).measurable
    (fun _ => Metric.infDist_nonneg)
    (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1))
    (fun r hr _ => base_affine_tube (by omega) base L (by omega) hr)
  simpa only [measure_univ] using h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianLogMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_gramSchmidt_le_norm [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) (i : Fin m) :
    ‖gramSchmidt ℝ v i‖ ≤ ‖v i‖ := by
  rw [PosteriorRegression.gramSchmidt_eq_sub_starProjection,
    ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gramVolume_eq_prod [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) :
    gramVolume v = ∏ i, ‖gramSchmidt ℝ v i‖ := PosteriorRegression.sqrt_det_gram m v

@[fun_prop] lemma measurable_gramVolume {m : ℕ} : Measurable (gramVolume : (Fin m → E) → ℝ) := by
  change Measurable (fun v : Fin m → E => gramVolume v)
  simp_rw [gramVolume_eq_prod]
  exact Finset.measurable_prod _ (fun i _ => (PosteriorRegression.measurable_gramSchmidt i).norm)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_PiTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma lintegral_pi_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => μ) =
      ∫⁻ p, ∫⁻ v : Fin n → E, f (Fin.cons p v) ∂Measure.pi (fun _ => μ) ∂μ := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0).symm
  have he (z : E × (Fin n → E)) : e z = Fin.cons z.1 z.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  rw [← hm.lintegral_comp hf]
  change (∫⁻ z, f (e z) ∂μ.prod (Measure.pi (fun _ : Fin n => μ))) = _
  have hfe : Measurable (fun z => f (e z)) := hf.comp e.measurable
  rw [lintegral_prod _ hfe.aemeasurable]
  simp_rw [he]

lemma ae_pi_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => μ), P v) ↔
      ∀ᵐ p ∂μ, ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => μ), P (Fin.cons p v) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0).symm
  have he (z : E × (Fin n → E)) : e z = Fin.cons z.1 z.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  rw [← hm.map_eq, MeasurableEmbedding.ae_map_iff e.measurableEmbedding]
  have hPe : MeasurableSet {z | P (e z)} := hP.preimage e.measurable
  rw [Measure.ae_prod_iff_ae_ae hPe]
  simp_rw [he]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_TupleMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma measurableSet_row_independent {d k : ℕ} :
    MeasurableSet {A : Rows d k | LinearIndependent ℝ A} := by
  have he : {A : Rows d k | LinearIndependent ℝ A} = {A | (rowGram A).det ≠ 0} := by
    ext A
    exact ⟨fun h => (Matrix.posDef_gram_of_linearIndependent h).det_pos.ne',
      fun h => Matrix.linearIndependent_of_det_gram_ne_zero (show (Matrix.gram ℝ A).det ≠ 0 from h)⟩
  rw [he]
  exact (isClosed_eq continuous_rowGram.matrix_det continuous_const).isOpen_compl.measurableSet

lemma measurableSet_affine_independent {d m : ℕ} :
    MeasurableSet {u : Tuple d m | LinearIndependent ℝ (differences u)} :=
  measurableSet_row_independent.preimage continuous_differences.measurable

lemma ae_base_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => base.measure d),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  rw [ae_pi_cons (base.measure d) measurableSet_affine_independent]
  apply Filter.Eventually.of_forall
  intro p
  simpa only [differences_cons] using
    ae_replica_independent_of_affine_null p m
      (fun L _ hL => base_affine_null hd base L (by omega))

lemma ae_gaussian_rows_full_rank {d k : ℕ} (hd : 3 ≤ d) (hk : k < d) :
    ∀ᵐ A ∂gaussianRows d k, LinearIndependent ℝ A := by
  have h := ae_replica_independent_of_affine_null (ν := stdGaussian (Vec d)) (0 : Vec d) k
    (fun L _ hL => base_affine_null hd .gaussian L (by omega))
  simpa only [sub_zero, gaussianRows] using h

lemma base_tuple_inverse_finite {d k m : ℕ} (hd : k + m + 2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) :
    (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k
      ∂Measure.pi (fun _ => base.measure d)) < ∞ := by
  have : NeZero d := ⟨by omega⟩
  have hrank := ae_base_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base
  have he : (fun u : Tuple d m => (ENNReal.ofReal (affineVolume u))⁻¹ ^ k) =ᵐ[
      Measure.pi (fun _ => base.measure d)]
      (fun u => ENNReal.ofReal ((affineVolume u)⁻¹ ^ k)) := by
    filter_upwards [hrank] with u hu
    have hp : 0 < affineVolume u := Real.sqrt_pos.mpr
      (Matrix.posDef_gram_of_linearIndependent hu).det_pos
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hp]
  rw [lintegral_congr_ae he,
    lintegral_pi_cons (base.measure d) (by fun_prop)]
  let C : ℝ≥0∞ := 1 + (ENNReal.ofReal (baseProjectionConstant base d (k+1)) * 2^(k+1)) * 2^(k+1)
  have hbound (p : Vec d) :
      (∫⁻ v : Fin m → Vec d, ENNReal.ofReal
        ((affineVolume (Fin.cons p v))⁻¹ ^ k) ∂Measure.pi (fun _ => base.measure d)) ≤ C^m := by
    have h := replica_integral_of_affine_moment k m p C
      (fun L _ hL => base_affine_inverse_bound hd hm base L hL)
    simpa only [PosteriorRegression.replicaWeight_eq_det,
      affineVolume, differences_cons] using h
  apply lt_of_le_of_lt (lintegral_mono hbound)
  simp only [lintegral_const, measure_univ, mul_one]
  dsimp only [C]
  finiteness

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualRightMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma constrainedRows_eq_residualRows {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    constrainedRows k u = (gaussianRows d k).map (residualRows u) := by
  unfold constrainedRows residualRows differenceSpan
  simp_rw [kernelComponent_eq_starProjection hu]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_TiltNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma bounded_withDensity_finite {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ≥0∞} {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    IsFiniteMeasure (μ.withDensity f) := by
  apply isFiniteMeasure_withDensity
  exact ne_top_of_le_ne_top (by simpa using ENNReal.mul_ne_top hL (measure_ne_top μ univ))
    (lintegral_mono hfL)

lemma tiltedFiber_probability {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    IsProbabilityMeasure (tiltedFiber base f A y) := by
  unfold tiltedFiber
  split_ifs with ha
  · infer_instance
  · constructor
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (tiltMass base f A y)⁻¹ * tiltMass base f A y = 1
    exact ENNReal.inv_mul_cancel ha (tiltMass_ne_top base hL hfL A y)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualLabelTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma equalConstant_pos (k m : ℕ) : 0 < equalConstant k m := by
  unfold equalConstant
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

lemma ae_tilt_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hL hfL
  rw [pi_withDensity _ _ (fun _ => hf)]
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_base_tuple_full_rank hd hm base] with u hu
  exact fun _ => hu

lemma equalLabelRight_residual {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelRight base f H = equalConstant k m *
      ∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
        ∂Measure.pi (fun _ => (base.measure d).withDensity f) := by
  unfold equalLabelRight equalConstant
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_tilt_tuple_full_rank hd hm base hf hL hfL] with u hu
  rw [constrainedRows_eq_residualRows hu, lintegral_map (by fun_prop) (by unfold residualRows; fun_prop)]

lemma equal_label_transfer {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {g : Rows d k × Labels k → ℝ≥0∞} (hg : Measurable g)
    (hzero : ∀ A, LinearIndependent ℝ A → ∀ᵐ y ∂volume,
      0 < projectedDensity base f A y → g (A,y) = 0) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, g (A, labels A (u 0)) = 0 := by
  have : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hL hfL
  have he : equalLabelLeft (m := m) base f (fun z => g (z.1,z.2.1)) = 0 := by
    unfold equalLabelLeft
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero A hA] with y hy
    by_cases hp : projectedDensity base f A y = 0
    · simp [hp]
    · simp [hy (pos_iff_ne_zero.mpr hp)]
  rw [equal_label_tilt_identity hd hk hm base hf hL hfL (by fun_prop),
    equalLabelRight_residual (by omega) (by omega) base hf hL hfL (by fun_prop)] at he
  have hint : (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
      ∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k
      ∂Measure.pi (fun _ => (base.measure d).withDensity f)) = 0 :=
    (mul_eq_zero.mp he).resolve_left (equalConstant_pos k m).ne'
  have hzg := (lintegral_eq_zero_iff (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k) by
      unfold residualRows; fun_prop)).mp hint
  filter_upwards [hzg, ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base hf hL hfL]
    with u hgu hu
  have hinn : (∫⁻ A, g (residualRows u A, labels (residualRows u A) (u 0)) ∂gaussianRows d k) = 0 :=
    (mul_eq_zero.mp hgu).resolve_left
      (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
  rw [constrainedRows_eq_residualRows hu]
  apply (ae_map_iff ((show Measurable (residualRows u) by unfold residualRows; fun_prop).aemeasurable)
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  exact (lintegral_eq_zero_iff (by unfold residualRows; fun_prop)).mp hinn

lemma equal_label_transfer_prop {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {P : Rows d k → Labels k → Prop} (hP : MeasurableSet {z : Rows d k × Labels k | P z.1 z.2})
    (hgood : ∀ A, LinearIndependent ℝ A → ∀ᵐ y ∂volume,
      0 < projectedDensity base f A y → P A y) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, P A (labels A (u 0)) := by
  classical
  let g : Rows d k × Labels k → ℝ≥0∞ := fun z => if P z.1 z.2 then 0 else 1
  have hg : Measurable g := Measurable.ite hP measurable_const measurable_const
  have h := equal_label_transfer hd hk hm base hf hL hfL hg (by
    intro A hA
    filter_upwards [hgood A hA] with y hy
    intro hp
    simp [g, hy hp])
  filter_upwards [h] with u hu
  filter_upwards [hu] with A hA
  by_contra hp
  simp [g, hp] at hA

lemma residualRows_equal_labels {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) (R : Rows d k) (i : Fin (m+1)) :
    labels (residualRows u R) (u i) = labels (residualRows u R) (u 0) := by
  refine Fin.cases rfl (fun i => ?_) i
  ext j
  have h := congrFun (labels_kernelComponent hu (R j)) i
  change ⟪differences u i, kernelComponent (differences u) (R j)⟫ = 0 at h
  rw [real_inner_comm, differences, inner_sub_right] at h
  exact sub_eq_zero.mp h

lemma ae_constrained_equal_labels {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    ∀ᵐ A ∂constrainedRows k u, ∀ i, labels A (u i) = labels A (u 0) := by
  rw [constrainedRows_eq_residualRows hu]
  have hp : Measurable (fun A : Rows d k => ∀ i, labels A (u i) = labels A (u 0)) := by
    unfold labels
    fun_prop
  apply (ae_map_iff ((show Measurable (residualRows u) by unfold residualRows; fun_prop).aemeasurable) hp.setOf).mpr
  exact Filter.Eventually.of_forall (fun R => residualRows_equal_labels hu R)

lemma projectedDensity_positive_sphere {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (A : Rows d k) (y : Labels k) (hp : 0 < projectedDensity base f A y) :
    LinearIndependent ℝ A ∧ (base = .spherical → ‖liftLabel A y‖ < 1) := by
  have hb : baseDensity base A y ≠ 0 := by
    intro hc
    simp [projectedDensity, hc] at hp
  by_cases hA : LinearIndependent ℝ A
  · refine ⟨hA, ?_⟩
    intro hs
    subst base
    by_contra hy
    exact hb (by simp [baseDensity, hA, hy])
  · exact False.elim (hb (by simp [baseDensity, hA]))

lemma ae_constrained_support {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      LinearIndependent ℝ (differences u) ∧
      ∀ᵐ A ∂constrainedRows k u,
        LinearIndependent ℝ A ∧ (∀ i, labels A (u i) = labels A (u 0)) ∧
        (base = .spherical → ‖liftLabel A (labels A (u 0))‖ < 1) ∧
        0 < projectedDensity base f A (labels A (u 0)) ∧
        projectedDensity base f A (labels A (u 0)) ≠ ∞ := by
  have hp := equal_label_transfer_prop hd hk hm base hf hL hfL
    (P := fun A y => 0 < projectedDensity base f A y)
    (measurableSet_lt measurable_const (measurable_projectedDensity base hf))
    (fun A _ => Filter.Eventually.of_forall fun y => id)
  filter_upwards [hp, ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d) base hf hL hfL]
    with u hu hU
  refine ⟨hU, ?_⟩
  filter_upwards [hu, ae_constrained_equal_labels hU] with A hA heq
  have hsup := projectedDensity_positive_sphere base A (labels A (u 0)) hA
  exact ⟨hsup.1, heq, hsup.2, hA, projectedDensity_ne_top base hL hfL A (labels A (u 0))⟩

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_LabelEllipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma liftLabel_norm_coordinates {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) : ‖liftLabel A y‖ = labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y) := by
  have h := pairingLift_energy hA y
  have he : labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y)^2 =
      ∑ i, (((pairingTriangular A).transpose⁻¹ *ᵥ y) i)^2 := by
    exact EuclideanSpace.real_norm_sq_eq _
  have hn : 0 ≤ labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y) := norm_nonneg _
  change ‖liftLabel A y‖^2 = _ at h
  nlinarith [norm_nonneg (liftLabel A y)]

lemma label_closedBall_volume {k : ℕ} (r : ℝ) :
    (volume : Measure (Labels k)) {y | labelNorm y ≤ r} =
      volume (closedBall (0 : Vec k) r) := by
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (by measurability)]
  congr 1
  ext y
  simp [labelNorm, mem_closedBall, dist_zero_right]

lemma label_ellipsoid_volume {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (r : ℝ) :
    (volume : Measure (Labels k)) {y | ‖liftLabel A y‖ ≤ r} =
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ r} := by
  have hd := (pairingTriangular_det_pos hA).ne'
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := (pairingTriangular A).transpose⁻¹)
    (by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hd)
  have h := congrArg (fun μ : Measure (Labels k) => μ {y | labelNorm y ≤ r}) hm
  rw [Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) measurable_const),
    Measure.smul_apply, smul_eq_mul] at h
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv, pairingTriangular_det, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ext y
  simp only [mem_ofPred_eq, mem_preimage, Matrix.toLin'_apply, liftLabel_norm_coordinates hA]
  all_goals rfl

lemma projectedDensity_support_ellipsoid {d k : ℕ} (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) (hy : projectedDensity .spherical f A y ≠ 0) :
    ‖liftLabel A y‖ < 1 := by
  unfold projectedDensity baseDensity at hy
  split_ifs at hy with hA hy' <;> simp_all

lemma projectedDensity_support_volume {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (f : Vec d → ℝ≥0∞) :
    (volume : Measure (Labels k)) {y | projectedDensity .spherical f A y ≠ 0} ≤
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1} := by
  rw [← label_ellipsoid_volume hA 1]
  exact measure_mono (fun y hy => (projectedDensity_support_ellipsoid f A y hy).le)

lemma gaussian_integrable_gramVolume {d k : ℕ} :
    Integrable (gramVolume : Rows d k → ℝ) (gaussianRows d k) := by
  have hp : Integrable (fun A : Rows d k => ∏ i, ‖A i‖) (gaussianRows d k) :=
    Integrable.fintype_prod (fun _ => (IsGaussian.integrable_id (μ := stdGaussian (Vec d))).norm)
  apply hp.mono' (by fun_prop)
  exact ae_of_all _ (fun A => by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gramVolume A from Real.sqrt_nonneg _), gramVolume_eq_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun index _ => norm_gramSchmidt_le_norm A index))

lemma gaussian_label_support_volume_finite {d k : ℕ} (hd : 3 ≤ d) (hk : k < d)
    {f : Vec d → ℝ≥0∞} (_hf : Measurable f) :
    (∫⁻ A, (volume : Measure (Labels k)) {y | projectedDensity .spherical f A y ≠ 0}
      ∂gaussianRows d k) < ∞ := by
  apply lt_of_le_of_lt (lintegral_mono_ae (g := fun A : Rows d k =>
    ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1}) ?_) ?_
  · filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
    exact projectedDensity_support_volume hA f
  · rw [lintegral_mul_const _ (by fun_prop)]
    apply ENNReal.mul_lt_top
    · exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => Real.sqrt_nonneg _))).mp
        gaussian_integrable_gramVolume.hasFiniteIntegral
    · rw [label_closedBall_volume]
      exact measure_closedBall_lt_top

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_EntropyTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

variable {X : Type*} [MeasurableSpace X]

lemma integrable_exp_neg_llr (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : Integrable (fun x => Real.exp (-llr μ ν x)) μ := by
  exact ν.integrable_toReal_rnDeriv.congr (exp_neg_llr hac).symm

lemma llr_withDensity_ae (ν : Measure X) [SigmaFinite ν] {g : X → ℝ≥0∞}
    (hg : Measurable g) [IsFiniteMeasure (ν.withDensity g)] :
    llr (ν.withDensity g) ν =ᵐ[ν.withDensity g] (fun x => Real.log (g x).toReal) := by
  filter_upwards [(withDensity_absolutelyContinuous ν g).ae_le (ν.rnDeriv_withDensity hg)] with x hx
  exact congrArg (fun t : ℝ≥0∞ => Real.log t.toReal) hx

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_LikelihoodIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma abs_le_pos_add_exp_neg (x : ℝ) : |x| ≤ max x 0 + Real.exp (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx), max_eq_right (le_of_not_ge hx)]
    linarith [Real.add_one_le_exp (-x)]

lemma integrable_llr_of_positive {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) (hi : Integrable (fun x => max (llr μ ν x) 0) μ) :
    Integrable (llr μ ν) μ := by
  apply (hi.add (integrable_exp_neg_llr μ ν hac)).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by simpa using abs_le_pos_add_exp_neg (llr μ ν x))

lemma likelihood_positive_log_bound {w a : ℝ} (hw : 0 ≤ w) (ha : 0 < a) (m : ℕ) :
    (w*a⁻¹^m) * max (Real.log (w*a⁻¹^m)) 0 ≤
      1+w^4 + (2*(m:ℝ)) * (w*a⁻¹^(m+1)) := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hrp : 0 < w*a⁻¹^m := mul_pos hwp (pow_pos (inv_pos.mpr ha) _)
  have hlog : max (Real.log (w*a⁻¹^m)) 0 ≤ w*a⁻¹^m :=
    max_le (Real.log_le_self hrp.le) hrp.le
  by_cases hlarge : a⁻¹^m ≤ max 1 w
  · have hwmax : w ≤ max 1 w := le_max_right _ _
    have hmpos : 0 ≤ max 1 w := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
    have hr : w*a⁻¹^m ≤ (max 1 w)^2 := by
      simpa [pow_two] using mul_le_mul hwmax hlarge (by positivity) hmpos
    have hsq : (w*a⁻¹^m)^2 ≤ (max 1 w)^4 := by
      have ht := (sq_le_sq₀ hrp.le (sq_nonneg _)).mpr hr
      simpa only [← pow_mul] using ht
    have hm4 : (max 1 w)^4 ≤ 1+w^4 := by
      by_cases h : w ≤ 1
      · rw [max_eq_left h]
        norm_num
        positivity
      · rw [max_eq_right (le_of_not_ge h)]
        linarith
    calc
      _ ≤ (w*a⁻¹^m)^2 := by nlinarith [mul_le_mul_of_nonneg_left hlog hrp.le]
      _ ≤ 1+w^4 := hsq.trans hm4
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hwa : w ≤ a⁻¹^m := (le_max_right 1 w).trans (le_of_not_ge hlarge)
    have h1a : 1 ≤ a⁻¹^m := (le_max_left 1 w).trans (le_of_not_ge hlarge)
    have hlw := Real.log_le_log hwp hwa
    have hlognon : 0 ≤ Real.log (a⁻¹^m) := Real.log_nonneg h1a
    have hlogupper : max (Real.log (w*a⁻¹^m)) 0 ≤ 2*(m:ℝ)*a⁻¹ := by
      rw [Real.log_mul hw0 (pow_ne_zero _ (inv_ne_zero ha.ne'))]
      have ha' := (Real.log_le_self (inv_pos.mpr ha).le)
      rw [Real.log_pow] at hlw hlognon
      rw [Real.log_pow]
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
      have ht := mul_le_mul_of_nonneg_left ha' hm
      apply max_le <;> nlinarith
    calc
      _ ≤ (w*a⁻¹^m) * (2*(m:ℝ)*a⁻¹) := mul_le_mul_of_nonneg_left hlogupper hrp.le
      _ = (2*(m:ℝ)) * (w*a⁻¹^(m+1)) := by rw [pow_succ]; ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma replica_likelihood_integrable {X : Type*} [MeasurableSpace X]
    (R : Measure X) [IsFiniteMeasure R] {w a : X → ℝ} (hw : Measurable w) (ha : Measurable a)
    (hwp : ∀ᵐ x ∂ R, 0 ≤ w x) (hap : ∀ᵐ x ∂ R, 0 < a x) (m : ℕ)
    (hw4 : Integrable (fun x => w x^4) R)
    (hwa : Integrable (fun x => w x*(a x)⁻¹^(m+1)) R)
    [IsFiniteMeasure (R.withDensity (fun x => ENNReal.ofReal (w x*(a x)⁻¹^m)))] :
    Integrable (fun x => Real.log (w x*(a x)⁻¹^m))
      (R.withDensity (fun x => ENNReal.ofReal (w x*(a x)⁻¹^m))) := by
  let g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (w x*(a x)⁻¹^m)
  have hg : Measurable g := by unfold g; fun_prop
  have hp : Integrable (fun x => max (Real.log (w x*(a x)⁻¹^m)) 0) (R.withDensity g) := by
    rw [integrable_withDensity_iff_integrable_smul' hg (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    apply (((integrable_const 1).add hw4).add (hwa.const_mul (2*(m:ℝ)))).mono' (by fun_prop)
    filter_upwards [hwp,hap] with x hwx hax
    rw [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (ENNReal.ofReal (w x*(a x)⁻¹^m)).toReal * _ ≤ _
    rw [ENNReal.toReal_ofReal (mul_nonneg hwx (pow_nonneg (inv_nonneg.mpr hax.le) _))]
    exact likelihood_positive_log_bound hwx hax m
  have he : llr (R.withDensity g) R =ᵐ[R.withDensity g]
      (fun x => Real.log (w x*(a x)⁻¹^m)) := by
    apply (llr_withDensity_ae R hg).trans
    filter_upwards [(withDensity_absolutelyContinuous R g).ae_le hwp,
      (withDensity_absolutelyContinuous R g).ae_le hap] with x hwx hax
    dsimp only [g]
    rw [ENNReal.toReal_ofReal (by positivity)]
  exact (integrable_llr_of_positive (R.withDensity g) R (withDensity_absolutelyContinuous R g)
    (hp.congr (he.symm.fun_comp (fun x => max x 0)))).congr he

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

lemma equalReference_lintegral {d k m : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂equalReference ν = ∫⁻ u : Tuple d m, ∫⁻ A,
      H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
      ∂Measure.pi (fun _ => ν) := by
  rw [equalReference, lintegral_map hH measurable_rightBasePoint,
    lintegral_prod _ (show AEMeasurable (fun z => H (rightBasePoint z)) _ from
      (hH.comp measurable_rightBasePoint).aemeasurable)]
  rfl

lemma density_power_cancel (m : ℕ) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    a^(m+1) * a⁻¹^m = a := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [pow_succ, mul_comm (a^m) a, mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 ha,
      one_pow, mul_one]

lemma replicaLaw_lintegral {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂replicaLaw base f =
      ∫⁻ A, ∫⁻ y, projectedDensity base f A y *
        ∫⁻ u, H (A,y,u) ∂Measure.pi (fun _ : Fin (m+1) => tiltedFiber base f A y)
        ∂volume ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have hG : Measurable (fun z : EqualSpace d k m =>
      (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by fun_prop
  have he := equal_label_tilt_identity hd hk hm base hf hLt hfL hG
  rw [equalLabelRight_residual (by omega) (by omega) base hf hLt hfL hG] at he
  have hrep : (∫⁻ z, H z ∂replicaLaw base f) = equalLabelLeft base f
      (fun z : EqualSpace d k m => (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by
    rw [he]
    rw [replicaLaw, lintegral_withDensity_eq_lintegral_mul _ (measurable_replicaDensity base hf) hH]
    simp only [Pi.mul_apply]
    rw [equalReference_lintegral (base.measure d |>.withDensity f) (by fun_prop)]
    unfold replicaDensity
    simp only
    rw [← lintegral_const_mul _ (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹^k *
      ∫⁻ A, (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k) by
      unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro u
    rw [← mul_assoc, ← lintegral_const_mul _ (show Measurable (fun A =>
      (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u)) by unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro A
    ring
  rw [hrep]
  unfold equalLabelLeft
  apply lintegral_congr
  intro A
  apply lintegral_congr
  intro y
  dsimp only
  rw [lintegral_const_mul _ (show Measurable (fun u : Tuple d m => H (A,y,u)) by fun_prop),
    ← mul_assoc, density_power_cancel m (projectedDensity_ne_top base hLt hfL A y)]

lemma lintegral_projectedDensity {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, projectedDensity base f A y) = (base.measure d).withDensity f univ := by
  have h := congrArg (fun μ : Measure (Labels k) => μ univ) (projected_measure hA hk base hf)
  rw [Measure.map_apply (by unfold labels; fun_prop) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h.symm

lemma replicaLaw_mass {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    replicaLaw (k := k) (m := m) base f univ = (base.measure d).withDensity f univ := by
  rw [← lintegral_one, replicaLaw_lintegral hd hk hm base hf hLt hfL measurable_const]
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  simp only [lintegral_one, measure_univ, mul_one]
  calc
    _ = ∫⁻ (_ : Rows d k), (base.measure d).withDensity f univ ∂gaussianRows d k := by
      apply lintegral_congr_ae
      filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
      exact lintegral_projectedDensity hA (by omega) base hf
    _ = _ := by simp

lemma replicaLaw_probability {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)] :
    IsProbabilityMeasure (replicaLaw (k := k) (m := m) base f) := by
  constructor
  rw [replicaLaw_mass hd hk hm base hf hLt hfL, measure_univ]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_ReferenceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma tilt_tuple_inverse_finite {d k m : ℕ} (hd : k+m+2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹^k
      ∂Measure.pi (fun _ => (base.measure d).withDensity f)) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  rw [pi_withDensity _ _ (fun _ => hf),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hbound (u : Tuple d m) : (∏ i, f (u i)) ≤ L^(m+1) := by
    simpa using Finset.prod_le_prod' (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m+1)))) => hfL (u i))
  simp only [Pi.mul_apply]
  apply lt_of_le_of_lt (lintegral_mono (fun u => mul_le_mul' (hbound u) le_rfl))
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hLt.lt_top) (base_tuple_inverse_finite hd hm base)

lemma ae_equalReference_of_constrained {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {P : EqualSpace d k m → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, P (A,labels A (u 0),u)) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f), P z := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  unfold equalReference
  apply (ae_map_iff measurable_rightBasePoint.aemeasurable hP).mpr
  apply (Measure.ae_prod_iff_ae_ae (hP.preimage measurable_rightBasePoint)).mpr
  filter_upwards [h, ae_tilt_tuple_full_rank hd hm base hf hLt hfL] with u hu hU
  rw [constrainedRows_eq_residualRows hU] at hu
  exact (ae_map_iff (show Measurable (residualRows u) by fun_prop).aemeasurable
    (hP.preimage (show Measurable (fun A => (A,labels A (u 0),u)) by unfold labels; fun_prop))).mp hu

lemma ae_equalReference_density_pos {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      0 < projectedDensity base f z.1 z.2.1 := by
  apply ae_equalReference_of_constrained (by omega) (by omega) base hf hLt hfL
    (measurableSet_lt measurable_const (by fun_prop))
  filter_upwards [ae_constrained_support hd hk hm base hf hLt hfL] with u hu
  filter_upwards [hu.2] with A hA
  exact hA.2.2.2.1

lemma ae_equalReference_affine_pos {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      0 < affineVolume z.2.2 := by
  apply ae_equalReference_of_constrained hd hm base hf hLt hfL
    (measurableSet_lt measurable_const (by fun_prop))
  filter_upwards [ae_tilt_tuple_full_rank hd hm base hf hLt hfL] with u hu
  apply ae_of_all
  intro A
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hu).det_pos

lemma reference_weight_moment {d k m n : ℕ} (hd : k*n+m+2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k)^n
      ∂equalReference ((base.measure d).withDensity f)) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  rw [equalReference_lintegral _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one, mul_pow, ← pow_mul]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (by unfold equalConstant; finiteness)
    (tilt_tuple_inverse_finite hd hm base hf hLt hfL)

lemma reference_inverse_density_moment {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k) *
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)
      ∂equalReference ((base.measure d).withDensity f)) =
      ∫⁻ A, (volume : Measure (Labels k)) {y | projectedDensity base f A y ≠ 0} ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  have he := equal_label_tilt_identity hd hk hm base hf hLt hfL
    (H := fun z : EqualSpace d k m => (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)) (by fun_prop)
  have hr : (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k) *
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)
      ∂equalReference ((base.measure d).withDensity f)) =
      equalLabelRight base f (fun z : EqualSpace d k m =>
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)) := by
    rw [equalLabelRight_residual (by omega) (by omega) base hf hLt hfL (by fun_prop),
      equalReference_lintegral _ (by fun_prop)]
    rw [← lintegral_const_mul _ (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹^k * ∫⁻ A, (projectedDensity base f
        (residualRows u A) (labels (residualRows u A) (u 0)))⁻¹^(m+1) ∂gaussianRows d k) by
          unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro u
    dsimp only [Prod.fst, Prod.snd]
    rw [lintegral_const_mul _ (show Measurable (fun A : Rows d k =>
      (projectedDensity base f (residualRows u A) (labels (residualRows u A) (u 0)))⁻¹^(m+1)) by
        unfold residualRows; fun_prop)]
    rw [mul_assoc]
  rw [hr, ← he]
  unfold equalLabelLeft
  apply lintegral_congr
  intro A
  simp only [lintegral_const, measure_univ, mul_one]
  rw [← lintegral_indicator_one (show MeasurableSet {y | projectedDensity base f A y ≠ 0} by
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl)]
  apply lintegral_congr
  intro y
  by_cases ha : projectedDensity base f A y = 0
  · simp [ha]
  · rw [Set.indicator_of_mem (show y ∈ {y | projectedDensity base f A y ≠ 0} from ha)]
    rw [← mul_pow, ENNReal.mul_inv_cancel ha (projectedDensity_ne_top base hLt hfL A y), one_pow]
    rfl

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaFiniteKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma replicaDensity_ne_top_ae {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      replicaDensity base f z ≠ ∞ := by
  filter_upwards [ae_equalReference_density_pos hd hk hm base hf hLt hfL,
    ae_equalReference_affine_pos (by omega) (by omega) base hf hLt hfL] with z ha hw
  unfold replicaDensity equalConstant
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top (by finiteness)
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hw).ne')
  · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr ha.ne')

lemma replica_log_integrable {d k m : ℕ} (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    Integrable (fun z : EqualSpace d k m => Real.log (replicaDensity .spherical f z).toReal)
      (replicaLaw .spherical f) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hd' : k+m+2 ≤ d := by omega
  have := replicaLaw_probability hd' hk hm .spherical hf hLt hfL
  let R : Measure (EqualSpace d k m) := equalReference ((sphereLaw d).withDensity f)
  let w : EqualSpace d k m → ℝ≥0∞ := fun z => equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k
  let a : EqualSpace d k m → ℝ≥0∞ := fun z => projectedDensity .spherical f z.1 z.2.1
  have hw : Measurable w := by unfold w; fun_prop
  have ha : Measurable a := by unfold a; fun_prop
  have he : R.withDensity (fun z => ENNReal.ofReal ((w z).toReal * (a z).toReal⁻¹^m)) =
      replicaLaw .spherical f := by
    apply withDensity_congr_ae
    filter_upwards [replicaDensity_ne_top_ae hd' hk hm .spherical hf hLt hfL] with z hz
    rw [← ENNReal.toReal_inv, ← ENNReal.toReal_pow, ← ENNReal.toReal_mul]
    exact ENNReal.ofReal_toReal hz
  have : IsFiniteMeasure (R.withDensity (fun z => ENNReal.ofReal ((w z).toReal * (a z).toReal⁻¹^m))) := by
    rw [he]; infer_instance
  have hw4 : Integrable (fun z => (w z).toReal^4) R := by
    have h := reference_weight_moment (n := 4) (by omega : k*4+m+2 ≤ d) hm .spherical hf hLt hfL
    simpa only [ENNReal.toReal_pow, BaseLaw.measure, R] using
      (integrable_toReal_of_lintegral_ne_top (hw.pow_const 4).aemeasurable h.ne)
  have hwa : Integrable (fun z => (w z).toReal * (a z).toReal⁻¹^(m+1)) R := by
    have h := reference_inverse_density_moment hd' hk hm .spherical hf hLt hfL
    have ht : (∫⁻ z, w z * (a z)⁻¹^(m+1) ∂ R) < ∞ := by
      exact lt_of_eq_of_lt (by simpa only [R,w,a,BaseLaw.measure] using h)
        (gaussian_label_support_volume_finite (by omega) (by omega) hf)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv] using
      (integrable_toReal_of_lintegral_ne_top (show AEMeasurable (fun z => w z * (a z)⁻¹^(m+1)) R by fun_prop) ht.ne)
  have hap : ∀ᵐ z ∂ R, 0 < (a z).toReal := by
    filter_upwards [ae_equalReference_density_pos hd' hk hm .spherical hf hLt hfL] with z hz
    exact ENNReal.toReal_pos hz.ne' (projectedDensity_ne_top .spherical hLt hfL z.1 z.2.1)
  have hi := replica_likelihood_integrable R hw.ennreal_toReal ha.ennreal_toReal
    (ae_of_all _ (fun z => ENNReal.toReal_nonneg)) hap m hw4 hwa
  rw [he] at hi
  simpa only [replicaDensity, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, w, a] using hi

lemma replica_klDiv_ne_top_oai {d k m : ℕ} (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    klDiv (replicaLaw (k := k) (m := m) .spherical f)
      (equalReference ((sphereLaw d).withDensity f)) ≠ ∞ := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability (by omega : k+m+2 ≤ d) hk hm .spherical hf hLt hfL
  apply klDiv_ne_top_iff.mpr
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  have : IsFiniteMeasure
      ((equalReference ((BaseLaw.spherical.measure d).withDensity f)).withDensity
        (@replicaDensity d k m .spherical f)) := by
    change IsFiniteMeasure (replicaLaw (k := k) (m := m) .spherical f); infer_instance
  exact (replica_log_integrable hd hk hm hf hLt hfL).congr
    (llr_withDensity_ae _ (measurable_replicaDensity .spherical hf)).symm

end PosteriorReplicas
end

end OAI
end

theorem solution : type_of% @OAI.PosteriorReplicas.replica_klDiv_ne_top_oai := @OAI.PosteriorReplicas.replica_klDiv_ne_top_oai
