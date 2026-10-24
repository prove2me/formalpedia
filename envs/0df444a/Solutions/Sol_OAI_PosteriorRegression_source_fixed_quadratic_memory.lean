-- Prove2me | solution 1 for OAI.PosteriorRegression.source_fixed_quadratic_memory
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:35:10.526755+00:00
-- url     : https://prove2.me/submissions/100e4057-622b-4646-b81d-f2291059cda4

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section
-- module Solutions.OAIQW_PosteriorReplicas.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaKernel
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
section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma lintegral_fin_prod (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_snoc μ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [lintegral_const_mul _ (hf (Fin.last n))]
    rw [lintegral_mul_const _ (by fun_prop), ih _ (fun i => hf i.castSucc)]

lemma lintegral_pow_pi (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, f x ∂μ)^n =
      ∫⁻ x : Fin n → X, ∏ i, f (x i) ∂Measure.pi (fun _ => μ) := by
  rw [lintegral_fin_prod μ n _ (fun _ => hf)]
  simp

lemma lintegral_product_differences (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ x, φ x = 1) (m n : ℕ) (y : Fin m → ℝ) :
    ∫⁻ z : Fin m → Fin n → ℝ,
      ∏ j, φ (y j) * ∏ i, φ (y j - z j i) = ∏ j, φ (y j) := by
  rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin n → ℝ)) m
    (fun j z => φ (y j) * ∏ i, φ (y j - z i)) (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro j _
  rw [lintegral_const_mul _ (by fun_prop), volume_pi,
    lintegral_fin_prod (volume : Measure ℝ) n
      (fun _ z => φ (y j - z)) (by intro i; fun_prop)]
  simp_rw [lintegral_sub_left_eq_self φ (y j), hφ1]
  simp

end ReplicaKernel

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ProductDensity
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
section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GaussianNoise
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
section GaussianNoise
lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

lemma pi_gaussian_withDensity (m : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 v) =
      (volume : Measure (Fin m → ℝ)).withDensity (fun y => ∏ j, gaussianPDF 0 v (y j)) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  rw [measure_pi_withDensity (volume : Measure ℝ) m
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)]
  rfl
lemma lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by
  let v : ℝ≥0 := NNReal.mk (δ^2) (sq_nonneg δ)
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  have he :
      (∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫⁻ y : Fin m → ℝ, f (a + y) ∂Measure.pi (fun _ => gaussianReal 0 v) := by
    rw [← pi_gaussian_map_scale m δ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, pi_gaussian_withDensity m v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hh (y : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 v (y j)) * f (a + y) =
      (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) (a + y) := by
    simp only [Pi.add_apply, add_sub_cancel_left]
  exact (lintegral_congr (μ := volume) hh).trans (lintegral_add_left_eq_self
    (μ := volume) (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) a)
end GaussianNoise

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_HolderSet
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
section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_LimitSet
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
section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_OuterBound
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
section OuterBound
variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)
end OuterBound

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

lemma gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  filter_upwards [] with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    norm_num only [NNReal.coe_one, mul_one]
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x - 0)^2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hs)).trans he
lemma measure_pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod' fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤ (volume : Measure (Fin n → ℝ)) :=
  measure_pi_mono (fun _ => gaussianReal_le_volume)
lemma gaussian_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹) •
        (volume : Measure (Fin n → ℝ)) := by
  let u := gramSchmidtNormed ℝ v
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * gsUpper n v
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hexp (j : Fin n) : ∑ i, R i j • u i = v j := by
    rw [← gsUpper_expansion n v j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    dsimp only [R]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal, gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hpos : 0 ≤ R.transpose.det := by rw [hdet]; positivity
  have hf : Measurable (Matrix.toLin' R.transpose) :=
    (Matrix.toLin' R.transpose).continuous_of_finiteDimensional.measurable
  have heq : (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' R.transpose) ∘ (fun x => fun i => ⟪u i, x⟫) := by
    funext x j
    rw [← hexp j]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner,
      inner_smul_left]
  rw [heq, ← Measure.map_map hf (by fun_prop), orthonormal_gaussian_map hu]
  calc
    _ ≤ (volume : Measure (Fin n → ℝ)).map (Matrix.toLin' R.transpose) :=
      Measure.map_mono (pi_gaussianReal_le_volume n) hf
    _ = _ := by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
        abs_of_nonneg (inv_nonneg.mpr hpos), hdet]
lemma measure_pi_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  simp_rw [Measure.coe_nnreal_smul]
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

lemma gaussian_rows_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j i => ⟪v i, A j⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
    (fun x : E => fun i => ⟪v i, x⟫)).aemeasurable)]
  have h := measure_pi_mono (fun _ : Fin m => gaussian_pairings_le v hv)
  rw [measure_pi_smul _ _ ENNReal.ofReal_ne_top] at h
  rw [ENNReal.ofReal_pow (by positivity)]
  simpa only [Fintype.card_fin, volume_pi] using h
end GaussianDomination

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GaussianKernel
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
section GaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]
end GaussianKernel

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_FiniteNets
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
section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

theorem exists_net_of_finite_packing_bound (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by
  classical
  let S : Set ℕ := {n | ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧ s.card = n}
  have hS : S.Finite := (Set.finite_Iic N).subset (by
    rintro n ⟨s, hs, hsep, rfl⟩
    exact hcard s hs hsep)
  have hS0 : S.Nonempty := ⟨0, ∅, by simp⟩
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hS hS0
  obtain ⟨s, hs, hsep, rfl⟩ := hn
  refine ⟨s, hs, hsep, ?_⟩
  intro x hx
  by_contra! hnot
  have hxs : x ∉ s := by
    intro h
    have := hnot x h
    simpa using lt_of_le_of_lt hr this
  have hins : ∀ y ∈ insert x s, y ∈ A := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hs y hy
  have hsep' : ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → r < dist y z := by
    intro y hy z hz hne
    rcases Finset.mem_insert.mp hy with hxy | hys
    · subst y
      rcases Finset.mem_insert.mp hz with hxz | hzs
      · exact (hne hxz.symm).elim
      · exact hnot z hzs
    · rcases Finset.mem_insert.mp hz with hxz | hzs
      · subst z
        simpa [dist_comm] using hnot y hys
      · exact hsep y hys z hzs hne
  have hinS : (insert x s).card ∈ S := ⟨insert x s, hins, hsep', rfl⟩
  have hh := hmax _ hinS
  simp only [id_eq, Finset.card_insert_of_notMem hxs] at hh
  omega

end FiniteNets

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_FrostmanGeometry
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
section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in

theorem HasLocalMassBound.any_center {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (z : E) {r : ℝ} (hr : 0 < r) :
    ν (Metric.closedBall z r) ≤ ENNReal.ofReal ((2 * r) ^ a) := by
  by_cases hmass : ν (Metric.closedBall z r) = 0
  · simp [hmass]
  obtain ⟨t, htball, htsupp⟩ := ν.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hmass)
  refine (measure_mono ?_).trans (hν t htsupp (2 * r) (by positivity))
  intro x hx
  apply Metric.mem_closedBall.mpr
  calc
    dist x t ≤ dist x z + dist z t := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (Metric.mem_closedBall.mp hx)
      (by simpa [dist_comm] using Metric.mem_closedBall.mp htball)
    _ = 2 * r := by ring

theorem card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by
  classical
  let ν : Measure E := Measure.addHaar
  let δ : ℝ := r / 2
  let ρ : ℝ := R + r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A : Set E := ⋃ c ∈ s, Metric.ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hsub : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    dsimp [δ, ρ]
    rw [dist_zero_right]
    linarith [hs x hx]
  have I :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) = ν A := by
        dsimp only [A]
        rw [measure_biUnion_finset hd (fun _ _ => Metric.isOpen_ball.measurableSet)]
        simp only [ν.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Metric.ball (0 : E) ρ) := measure_mono hsub
      _ = _ := ν.addHaar_ball_of_pos 0 hρ
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (Metric.measure_ball_pos ν 0 zero_lt_one).ne'
      measure_ball_lt_top.ne).mp I
  have K : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤ ρ ^ Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr K

end FrostmanGeometry

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_EuclideanNets
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
section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by
  classical
  have hbound : ∀ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) →
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s hr zero_le_one hs
      (fun x hx y hy hne => (hsep x hx y hy hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < r / 2) hr).mpr
    nlinarith
  obtain ⟨s, hs, hsep, hnet⟩ := exists_net_of_finite_packing_bound
    {x : E | ‖x‖ ≤ 1} hr.le ⌈(3 / r) ^ Module.finrank ℝ E⌉₊
    (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s, hs, hbound s hs hsep, hnet⟩

end EuclideanNets

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_AffineTubes
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
section AffineTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open EuclideanGeometry

theorem exists_affine_tube_cover (L : AffineSubspace ℝ E) [Nonempty L]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ L.direction ∧
      ∀ t : E, ‖t‖ ≤ 1 → Metric.infDist t L ≤ r →
        ∃ y ∈ s, dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤ 2 * r := by
  classical
  obtain ⟨s, _, hcard, hnet⟩ := exists_unit_ball_net (E := L.direction) hr hr1
  refine ⟨s, hcard, ?_⟩
  intro t ht hdist
  obtain ⟨y, hy, hty⟩ := hnet (L.direction.orthogonalProjectionOnto t)
    ((L.direction.norm_orthogonalProjectionOnto_apply_le t).trans ht)
  refine ⟨y, hy, ?_⟩
  have hproj : (orthogonalProjection L t : E) =
      (L.direction.orthogonalProjectionOnto t : E) + (orthogonalProjection L 0 : E) := by
    have h := (orthogonalProjection L).map_vadd (0 : E) t
    simpa only [vadd_eq_add, add_zero, orthogonalProjection_contLinear,
      AffineSubspace.coe_vadd] using congrArg (fun x : L => (x : E)) h
  have hpdist : dist (orthogonalProjection L t : E)
      ((y : E) + (orthogonalProjection L 0 : E)) ≤ r := by
    rw [hproj, dist_add_right]
    exact hty
  have hd : dist t (orthogonalProjection L t : E) ≤ r := by
    rwa [dist_orthogonalProjection_eq_infDist]
  calc
    dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤
        dist t (orthogonalProjection L t : E) +
          dist (orthogonalProjection L t : E) ((y : E) + (orthogonalProjection L 0 : E)) :=
      dist_triangle _ _ _
    _ ≤ r + r := add_le_add hd hpdist
    _ = 2 * r := by ring

theorem HasLocalMassBound.affine_tube {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction * (4 * r) ^ a) := by
  classical
  obtain ⟨s, hcard, hcover⟩ := exists_affine_tube_cover L hr hr1
  let c : L.direction → E := fun y => (y : E) + (orthogonalProjection L 0 : E)
  have hsub : {t | Metric.infDist t L ≤ r} ≤ᵐ[ν]
      ⋃ y ∈ s, Metric.closedBall (c y) (2 * r) := by
    filter_upwards [ν.support_mem_ae] with t ht
    intro hdist
    have htunit : ‖t‖ ≤ 1 := by simpa using hsupport ht
    obtain ⟨y, hy, hty⟩ := hcover t htunit hdist
    exact mem_iUnion₂.mpr ⟨y, hy, hty⟩
  calc
    ν {t | Metric.infDist t L ≤ r} ≤ ν (⋃ y ∈ s, Metric.closedBall (c y) (2 * r)) :=
      measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, ν (Metric.closedBall (c y) (2 * r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal ((4 * r) ^ a) := by
      refine Finset.sum_le_sum fun y _ => ?_
      simpa only [show (2 : ℝ) * (2 * r) = 4 * r by ring] using
        hν.any_center (c y) (r := 2 * r) (by positivity)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal ((4 * r) ^ a) := by simp
    _ ≤ ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction) *
        ENNReal.ofReal ((4 * r) ^ a) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma tube_radius_factors (ℓ : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (3 / r) ^ ℓ * (4 * r) ^ a =
      (3 : ℝ) ^ ℓ * (4 : ℝ) ^ a * r ^ (a - ℓ) := by
  rw [div_pow, Real.mul_rpow (by norm_num) hr.le,
    Real.rpow_sub_natCast hr.ne']
  ring

theorem HasLocalMassBound.affine_tube_pow {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (k : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + k ≤ a)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
        ENNReal.ofReal (r ^ k) := by
  refine (hν.affine_tube hsupport L hr hr1).trans ?_
  rw [tube_radius_factors _ _ hr, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)

theorem HasLocalMassBound.affine_inverse_moment {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ t, ENNReal.ofReal ((Metric.infDist t L)⁻¹ ^ m) ∂ν ≤
      ν Set.univ +
        ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
          (2 : ℝ≥0∞) ^ (m + 1) := by
  apply inverse_moment_of_tube_bound ν _ m (Metric.continuous_infDist_pt _).measurable
    (fun _ => Metric.infDist_nonneg)
  intro r hr hr1
  exact hν.affine_tube_pow hsupport L (m + 1) hmargin hr hr1

theorem HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by
  let C : ℝ := (3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (n : ℕ) : ν L ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n) := by
    have hn : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      ν L ≤ ν {t | Metric.infDist t L ≤ (1 / 2 : ℝ) ^ n} := by
        apply measure_mono
        intro t ht
        simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem ht]
        exact hn.le
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 1) :=
        hν.affine_tube_pow hsupport L 1 (by simpa using hmargin) hn hn1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) (by positivity)

end AffineTubes

open InnerProductSpace

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

lemma affine_inverse_moment_le_replicaConstant {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ replicaConstant ν a m := by
  apply (hν.affine_inverse_moment hsupport L m hmargin).trans
  dsimp [replicaConstant]
  gcongr
  · norm_num
  · exact Submodule.finrank_le L.direction

theorem replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hmargin' : (n : ℝ) + m ≤ a := by exact le_trans (by push_cast; linarith) hmargin
    have hinner (v : Fin n → E) :
        ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν ≤
          replicaWeight m p v * replicaConstant ν a m := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply affine_inverse_moment_le_replicaConstant hν hsupport
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin] at hdim
      have hdim' : (Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => v i - p))) : ℝ) ≤ n :=
        by exact_mod_cast hdim
      rw [AffineSubspace.direction_mk']
      push_cast at hmargin ⊢
      linarith
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := lintegral_pi_snoc ν _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v * replicaConstant ν a m
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν)) *
          replicaConstant ν a m := lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (replicaConstant ν a m)^n * replicaConstant ν a m :=
          mul_le_mul' (ih hmargin') le_rfl
      _ = _ := (pow_succ _ _).symm
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

theorem ae_gramSchmidt_ne_zero {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc ν (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hn : (n : ℝ) ≤ a := by push_cast at hmargin; linarith
    filter_upwards [ih hn] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : (Module.finrank ℝ L.direction : ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have hnull : ν L = 0 := hν.affine_null hsupport L (by push_cast at hmargin; linarith)
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      convert hnull using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

theorem ae_replica_linearIndependent {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      LinearIndependent ℝ (fun j => v j - p) := by
  filter_upwards [ae_gramSchmidt_ne_zero hν hsupport p n hmargin] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SmoothingMoments
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
section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

lemma projectionSmoothing_pow (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m n : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (projectionSmoothing ν φ m z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        (∏ j, φ (z.2 j - ⟪w.1, z.1 j⟫)) *
          ∏ i, ∏ j, φ (z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, ∏ j, φ (z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← lintegral_pow_pi ν
    (fun t : E => ∏ j, φ (z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), replicaWeight_eq_det, sqrt_det_gram]
      exact gaussian_replica_kernel_bound p v hv φ hφ hφ1 m
    _ ≤ ∫⁻ _p, (replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]
end SmoothingMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ProjectionCoupling
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
section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m δ),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hf]
  dsimp [gaussianCoupling, matrixLabelReference, noisyObservation]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by
    exact ((measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _).mul hf).aemeasurable)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  have he (p : E) := lintegral_gaussian_shift_scale m δ hδ
    (fun j => ⟪p, A j⟫) (fun y => f (A, y)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl
lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
    ((Measure.pi (fun _ : Fin m => stdGaussian E)).prod volume)).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

theorem projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have hC : ν Set.univ * (replicaConstant ν a m)^n ≠ ∞ := by
    unfold replicaConstant
    finiteness
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one, matrixLabelReference]
    using projectionSmoothing_moment hν hsupport
      (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
        (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv) m n hmargin

end ProjectionCoupling

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SupportVolume
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
section SupportVolume
open scoped Pointwise

lemma coordinateNorm_sq {m : ℕ} (y : Fin m → ℝ) :
    coordinateNorm y ^ 2 = ∑ j, (y j)^2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y)

lemma coordinateNorm_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    coordinateNorm (c • y) = |c| * coordinateNorm y := by
  simp [coordinateNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma measurableSet_coordinateBall (m : ℕ) (r : ℝ) :
    MeasurableSet (coordinateBall m r) :=
  measurableSet_le continuous_coordinateNorm.measurable measurable_const

lemma coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    coordinateBall m (c * r) = c • coordinateBall m r := by
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, ?_, by simp [hc.ne']⟩
    change coordinateNorm (c⁻¹ • y) ≤ r
    rw [coordinateNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_le_iff₀ hc).mpr hy
  · rintro ⟨y, hy, rfl⟩
    change coordinateNorm (c • y) ≤ c * r
    rw [coordinateNorm_smul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hy hc.le

lemma volume_coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    volume (coordinateBall m (c * r)) =
      ENNReal.ofReal (c^m) * volume (coordinateBall m r) := by
  rw [coordinateBall_smul m c r hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp

lemma gaussianPDF_le_exp (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-(x^2)/2)) := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [Real.pi_gt_three]

lemma lintegral_quarterGaussian_le :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x^2)/4))) ≤ 4 := by
  have he : (fun x : ℝ => Real.exp (-(x^2)/4)) =
      (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  simp_rw [show ∀ x : ℝ, Real.exp (-(x^2)/4) = Real.exp (-(1/4 : ℝ) * x^2) from congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq (by norm_num)) (by filter_upwards [] with x; positivity),
    integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/4 : ℝ)) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma gaussian_density_pair_bound {m : ℕ} (x y : Fin m → ℝ)
    (h : coordinateNorm y ≤ coordinateNorm x) :
    (∏ j, gaussianPDF 0 1 (x j)) ≤
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
      ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
  calc
    _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/2)) :=
      Finset.prod_le_prod' fun j _ => gaussianPDF_le_exp (x j)
    _ = ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2) / 2)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2)/4 - (∑ j, (y j)^2)/4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ coordinateNorm y := norm_nonneg _
      have hs := pow_le_pow_left₀ hn h 2
      rw [coordinateNorm_sq, coordinateNorm_sq] at hs
      linarith
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← Real.exp_sum, ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      simp only [← Finset.sum_div, Finset.sum_neg_distrib]
      ring

lemma measurable_coordinateVolume (m : ℕ) : Measurable (fun x : Fin m → ℝ => volume (coordinateBall m (coordinateNorm x))) := by
  have : Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) =>
      ({z | coordinateNorm z.2 ≤ coordinateNorm z.1} : Set _).indicator
        (fun _ => (1 : ℝ≥0∞)) z) :=
    measurable_const.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  change Measurable (Function.uncurry (fun x y : Fin m → ℝ =>
    (coordinateBall m (coordinateNorm x)).indicator (fun _ => (1 : ℝ≥0∞)) y)) at this
  convert this.lintegral_prod_right (ν := (volume : Measure (Fin m → ℝ))) using 1
  ext x
  rw [lintegral_indicator (measurableSet_coordinateBall m _)]
  simp

lemma gaussian_expected_coordinate_volume (m : ℕ) :
    (∫⁻ x : Fin m → ℝ, volume (coordinateBall m (coordinateNorm x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ (16 : ℝ≥0∞)^m := by
  have hB := measurable_coordinateVolume m
  rw [pi_gaussian_withDensity m 1 (by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hB]
  have hi (x : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 1 (x j)) * volume (coordinateBall m (coordinateNorm x)) =
      ∫⁻ y : Fin m → ℝ, (coordinateBall m (coordinateNorm x)).indicator
        (fun _ => ∏ j, gaussianPDF 0 1 (x j)) y := by
    rw [lintegral_indicator (measurableSet_coordinateBall m _)]
    simp
  simp only [Pi.mul_apply]
  simp_rw [hi]
  calc
    _ ≤ ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin m → ℝ,
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
        ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ coordinateBall m (coordinateNorm x)
      · rw [Set.indicator_of_mem hy]
        exact gaussian_density_pair_bound x y hy
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m)^2 := by
      have hJ : (∫⁻ y : Fin m → ℝ, ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))) =
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m := by
        rw [volume_pi, lintegral_fin_prod volume m
          (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
        simp
      have hj (x : Fin m → ℝ) := lintegral_const_mul (μ := volume)
        (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4)))
        (by fun_prop : Measurable (fun y : Fin m → ℝ =>
          ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))))
      simp_rw [hj, hJ]
      rw [lintegral_mul_const _ (by fun_prop), hJ, pow_two]
    _ ≤ ((4 : ℝ≥0∞)^m)^2 := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) lintegral_quarterGaussian_le m) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

lemma rows_expected_coordinate_volume (u : E) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    (∫⁻ A : Fin m → E, volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (16 : ℝ≥0∞)^m := by
  have h := congrArg (fun μ : Measure (Fin m → ℝ) =>
    ∫⁻ y, volume (coordinateBall m (coordinateNorm y)) ∂μ) (rows_inner_map u m)
  rw [lintegral_map (measurable_coordinateVolume m) (by fun_prop),
    lintegral_map (measurable_coordinateVolume m) (by fun_prop)] at h
  rw [h]
  apply le_trans _ (gaussian_expected_coordinate_volume m)
  apply lintegral_mono
  intro x
  apply measure_mono
  intro y hy
  change coordinateNorm y ≤ coordinateNorm x
  apply le_trans hy
  rw [coordinateNorm_smul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hu

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowOperator_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowOperator A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  exact real_inner_comm _ _

lemma measurableSet_netProjectionSupport (s : Finset E) (m : ℕ) :
    MeasurableSet (netProjectionSupport s m) := by
  apply MeasurableSet.biUnion s.countable_toSet
  intro u _
  exact measurableSet_le (by fun_prop) (by fun_prop)

lemma netProjectionSupport_volume (s : Finset E) (hs : ∀ u ∈ s, ‖u‖ ≤ 1) (m : ℕ) :
    matrixLabelReference (E := E) m (netProjectionSupport s m) ≤
      (s.card : ℝ≥0∞) * (32 : ℝ≥0∞)^m := by
  classical
  apply (measure_biUnion_finset_le s _).trans
  calc
    _ ≤ ∑ _u ∈ s, (32 : ℝ≥0∞)^m := by
      apply Finset.sum_le_sum
      intro u hu
      rw [matrixLabelReference, Measure.prod_apply (measurableSet_le (by fun_prop) (by fun_prop))]
      change (∫⁻ A : Fin m → E,
        volume (coordinateBall m (2 * coordinateNorm (fun j => ⟪u, A j⟫)))
        ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
      simp_rw [volume_coordinateBall_smul m 2 _ (by norm_num)]
      have hme : Measurable (fun A : Fin m → E =>
          volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))) :=
        (measurable_coordinateVolume m).comp (by fun_prop)
      rw [lintegral_const_mul _ hme]
      calc
        _ ≤ ENNReal.ofReal ((2 : ℝ)^m) * (16 : ℝ≥0∞)^m :=
          mul_le_mul' le_rfl (rows_expected_coordinate_volume u (hs u hu) m)
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num [← mul_pow]
    _ = _ := by simp
end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma opNorm_le_twice_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/2) :
    ‖f‖ ≤ 2 * (s.sup (fun u => ‖f u‖₊) : ℝ≥0) := by
  classical
  let K : ℝ := (s.sup (fun u => ‖f u‖₊) : ℝ≥0)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hbound : ‖f‖ ≤ K + ‖f‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx.le
    have hfy : ‖f y‖ ≤ K := by
      exact_mod_cast (Finset.le_sup (f := fun u => ‖f u‖₊) hy)
    calc
      ‖f x‖ = ‖f y + f (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖f y‖ + ‖f (x-y)‖ := norm_add_le _ _
      _ ≤ K + ‖f‖ * (1/2) := add_le_add hfy
        ((f.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm] using hxy) (norm_nonneg _)))
      _ = _ := by ring
  dsimp [K] at hbound
  linarith
end NetNorm

section SupportExistence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_unit_ball_net (E := E)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hsne : s.Nonempty := by
    obtain ⟨u, hu, _⟩ := hnet 0 (by simp)
    exact ⟨u, hu⟩
  refine ⟨netProjectionSupport s m, measurableSet_netProjectionSupport s m, ?_, ?_⟩
  · intro A t ht
    obtain ⟨u, hu, he⟩ := s.exists_mem_eq_sup hsne (fun u => ‖rowOperator A u‖₊)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    change coordinateNorm (fun j => ⟪t, A j⟫) ≤
      2 * coordinateNorm (fun j => ⟪u, A j⟫)
    change ‖WithLp.toLp 2 (fun j => ⟪t, A j⟫)‖ ≤
      2 * ‖WithLp.toLp 2 (fun j => ⟪u, A j⟫)‖
    rw [← rowOperator_apply, ← rowOperator_apply]
    calc
      _ ≤ ‖rowOperator A‖ * ‖t‖ := (rowOperator A).le_opNorm t
      _ ≤ ‖rowOperator A‖ := mul_le_of_le_one_right (norm_nonneg _) ht
      _ ≤ _ := by simpa [he] using opNorm_le_twice_net (rowOperator A) s hnet
  · apply (netProjectionSupport_volume s hs m).trans
    have hcard : (s.card : ℝ≥0∞) ≤ (6 : ℝ≥0∞)^(Module.finrank ℝ E) := by
      have h : (s.card : ℝ) ≤ (6 : ℝ)^(Module.finrank ℝ E) := by norm_num at hc ⊢; exact hc
      simpa using ENNReal.ofReal_le_ofReal h
    calc
      _ ≤ (6 : ℝ≥0∞)^Module.finrank ℝ E * (32 : ℝ≥0∞)^Module.finrank ℝ E :=
        mul_le_mul' hcard (pow_le_pow_right₀ (by norm_num) hm)
      _ = _ := by rw [← mul_pow]; norm_num
end SupportExistence

end SupportVolume

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SphereBounds
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
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallLaw_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    unitBallLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  have h0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have ht : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ ≤ ((volume : Measure E) (Metric.ball 0 1))⁻¹ * volume (Metric.closedBall z r) := by
      exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = _ := by
      rw [Measure.addHaar_closedBall _ _ hr.le, mul_comm _ (_ * _), mul_assoc,
        ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma unitBallLaw_local : HasLocalMassBound (unitBallLaw : Measure E)
    (Module.finrank ℝ E : ℝ) := by
  intro z _ r hr
  simpa only [Real.rpow_natCast] using unitBallLaw_closedBall z hr

lemma unitBallLaw_support : (unitBallLaw : Measure E).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  simp

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

lemma sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
  classical
  let L := (Submodule.span ℝ ({z} : Set E)).toAffineSubspace
  let : Nonempty L := ⟨⟨0, (Submodule.span ℝ ({z} : Set E)).zero_mem⟩⟩
  have hl : Module.finrank ℝ L.direction ≤ 1 := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    simpa using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hm : (Module.finrank ℝ L.direction : ℝ) + (Module.finrank ℝ E - 1 : ℕ) ≤
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (by omega : Module.finrank ℝ L.direction + (Module.finrank ℝ E - 1) ≤ Module.finrank ℝ E)
  have hsub : Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r}) ⊆
      {t | Metric.infDist t L ≤ r} := by
    rintro _ ⟨c, hc, _, ⟨s, hs, rfl⟩, rfl⟩
    have hz : c • z ∈ L := Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    exact (Metric.infDist_le_dist_of_mem hz).trans (by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc.1]
      exact (mul_le_mul_of_nonneg_left hs hc.1.le).trans (mul_le_of_le_one_left hr.le hc.2.le))
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L _ hm hr hr1).trans
  simp only [Real.rpow_natCast]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hl)
    (by positivity)

end SphereBounds

open scoped Pointwise

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SphereGeometry
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
open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by
  by_cases hr1 : r ≤ 1
  · rw [ambientSphereLaw, Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
    apply (sphereLaw_cap_raw z hr hr1 (Module.finrank_pos (R := ℝ) (M := E))).trans
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)
  · have hr1 : 1 ≤ r := (le_of_not_ge hr1)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply one_le_mul
        · rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : (1 : ℝ) ≤ 4 ^ Module.finrank ℝ E := one_le_pow₀ (by norm_num)
          linarith
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr1)

lemma terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le h a) (by positivity)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

lemma sphere_inner_sq_integrable [Nontrivial E] (v : E) :
    Integrable (fun x => ⟪v,x⟫^2) (ambientSphereLaw (E := E)) := by
  apply (integrable_const (‖v‖^2)).mono' (by fun_prop)
  filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
  have h := abs_real_inner_le_norm v x
  rw [hx, mul_one] at h
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 h)

lemma sphere_inner_sq_eq [Nontrivial E] {v w : E} (h : ‖v‖ = ‖w‖) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = ∫ x, ⟪w,x⟫^2 ∂ambientSphereLaw := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  have hi := (ambientSphereLaw_isometry e).integral_comp
    e.toMeasurableEquiv.measurableEmbedding (fun x => ⟪w,x⟫^2)
  rw [← he] at hi
  simp only [e.inner_map_map] at hi
  simpa only [he] using hi

lemma sphere_inner_sq_unit [Nontrivial E] {v : E} (hv : ‖v‖ = 1) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, (∑ i, ⟪b i,x⟫^2) = ‖x‖^2 := by
    intro x
    simpa only [real_inner_comm x, pow_two, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have h : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw := by
        have heq : ∀ i, (∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw) =
            ∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw := fun i =>
          sphere_inner_sq_eq (by rw [b.norm_eq_one, hv])
        simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i,x⟫^2 ∂ambientSphereLaw :=
        (integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i))).symm
      _ = ∫ _ : E, (1 : ℝ) ∂ambientSphereLaw := by
        apply integral_congr_ae
        filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
        rw [hsum, hx, one_pow]
      _ = 1 := by simp
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact (eq_div_iff hd).2 (by simpa only [mul_comm] using h)

lemma sphere_projection_sq_integrable [Nontrivial E] (U : Submodule ℝ E) :
    Integrable (fun x => ‖U.orthogonalProjectionOnto x‖^2) (ambientSphereLaw (E := E)) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  exact integrable_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))

lemma sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  rw [integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))]
  have hi : ∀ i, (∫ x, ⟪(b i : E), x⟫^2 ∂ambientSphereLaw) =
      1 / (Module.finrank ℝ E : ℝ) := fun i =>
    sphere_inner_sq_unit (by exact b.norm_eq_one i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

lemma sphereIsometry_preserving [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry e) (sphereLaw (E := E)) (sphereLaw (E := E)) := by
  refine ⟨(sphereIsometry e).continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (sphereLaw (E := E)).map (e ∘ Subtype.val) = ambientSphereLaw
  rw [← Measure.map_map e.continuous.measurable (by fun_prop)]
  exact (ambientSphereLaw_isometry e).map_eq

omit [MeasurableSpace E] [BorelSpace E] in
lemma reflection_dist (U : Submodule ℝ E) (x : E) :
    dist x (U.reflection x) = 2 * ‖Uᗮ.starProjection x‖ := by
  rw [dist_eq_norm, Submodule.reflection_apply]
  have heq : x - (2 • U.starProjection x - x) = (2 : ℝ) • Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, two_smul ℝ]
    abel
  rw [heq, norm_smul]
  norm_num

lemma sphere_projection_large [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/16 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have : (4 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/4 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/16 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

lemma sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by
  let f := sphereIsometry U.reflection
  have hp := sphereIsometry_preserving U.reflection
  have hi : S ∩ f ⁻¹' S ⊆
      {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} := by
    intro s hs
    have hd := hsep s hs.1 hs.2
    rw [reflection_dist] at hd
    have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
    rw [mem_sphere_zero_iff_norm.mp s.property] at hn
    change (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
    have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
    rw [he] at hn
    nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
  have hinter := (measure_mono hi).trans (sphere_projection_large U hU)
  have heq := measure_union_add_inter₀ S (hS.preimage hp.quasiMeasurePreserving)
  rw [hp.measure_preimage hS] at heq
  calc
    sphereLaw S = ENNReal.ofReal (1/2 : ℝ) * (sphereLaw S + sphereLaw S) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2 : ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ = ENNReal.ofReal (1/2 : ℝ) *
        (sphereLaw (S ∪ f ⁻¹' S) + sphereLaw (S ∩ f ⁻¹' S)) := by rw [heq]
    _ ≤ ENNReal.ofReal (1/2 : ℝ) * (1 + ENNReal.ofReal (5/16 : ℝ)) := by
      exact mul_le_mul' le_rfl (add_le_add prob_le_one hinter)
    _ = ENNReal.ofReal (21/32 : ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num

end MoreSphere

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_Fubini
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
open scoped Pointwise
section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

lemma prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod_symm _ hm]
  apply (lintegral_mono_ae ?_).trans_eq (lintegral_const c)
  filter_upwards [h, ae_fiber_aemeasurable hm] with y hy hmy
  have hs : NullMeasurableSet {x | (x,y) ∈ S} μ := by
    have heq : {x | (x,y) ∈ S} = {x | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext x
      by_cases hx : (x,y) ∈ S <;> simp [hx]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmy aemeasurable_const
  change (∫⁻ x, ({x | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) ≤ c
  simpa [lintegral_indicator_const₀ hs] using hy
end FubiniAux

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_LabelDependence
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
open scoped Pointwise
namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

lemma linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := ENNReal.ofReal (21/32 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ (Vector d) := by
    simpa only [Vector, finrank_euclideanSpace_fin] using (Nat.mul_le_mul_left 4 hdim).trans hT
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_reflection_success_bound U hU
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s hs ht
    let t := sphereIsometry U.reflection s
    have he : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      have hi : z.2 i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      have he := U.reflection.inner_map_map (z.2 i) s.val
      rw [(Submodule.reflection_eq_self_iff (z.2 i)).2 hi] at he
      exact he.symm
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ = dist s.val t.val := rfl
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [he, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith
end Learner

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ProjectionBlocks
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
open scoped Pointwise
section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_univ {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    localNormalize ν a C z r univ ≤ 1 := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  simp only [localNormalize, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z))) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (mul_le_mul' le_rfl (hν z r hr)).trans_eq (ENNReal.inv_mul_cancel hc0 hct)

omit [FiniteDimensional ℝ E] in
lemma localNormalize_finite {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (localNormalize ν a C z r) :=
  ⟨(localNormalize_univ hν hC hCt z hr).trans_lt (by simp)⟩

omit [FiniteDimensional ℝ E] in
lemma localNormalize_support (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (localNormalize ν a C z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, localNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : E => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩ Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_local {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    HasLocalMassBound (localNormalize ν a C z r) (a : ℝ) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  intro t _ ρ hρ
  rw [localNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : E => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x - (z+r • t) = r • (r⁻¹ • (x-z) - t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * ν (Metric.closedBall (z+r • t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * (C * ENNReal.ofReal ((r*ρ)^a)) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (ρ^(a : ℝ)) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le a), ← mul_assoc C,
        ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have h2 : (2 : ℝ≥0∞) ≤ 2^d := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hd
  have hp : (2 : ℝ≥0∞)^(m+1) ≤ 4^d := by
    rw [pow_succ]
    calc
      _ ≤ (2 : ℝ≥0∞)^d * 2^d := mul_le_mul' (pow_le_pow_right₀ (by norm_num) hm) h2
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    replicaConstant ν (a : ℝ) m ≤ 1 + (4 : ℝ≥0∞)^d * 4^d * 4^d := by
      unfold replicaConstant
      rw [Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr <;> norm_num
    _ = 1 + (64 : ℝ≥0∞)^d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ≥0∞) * 64^d := by
      rw [two_mul]
      exact add_le_add (one_le_pow₀ (by norm_num)) le_rfl
    _ ≤ (2 : ℝ≥0∞)^d * 64^d := mul_le_mul' h2 le_rfl
    _ = _ := by rw [← mul_pow]; norm_num; rfl

lemma projectionLaw_uniform_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} (hν : HasLocalMassBound ν (a : ℝ)) (hν1 : ν univ ≤ 1)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hn : 1 ≤ n) (hmargin : n+m ≤ a) (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ)+1)) := by
  apply (projectionLaw_set_bound hν hsupport m n hn (by exact_mod_cast hmargin) S).trans
  apply mul_le_mul' _ le_rfl
  have hn0 : (0 : ℝ) < n+1 := by positivity
  calc
    _ ≤ (((128 : ℝ≥0∞)^Module.finrank ℝ E) ^ n)^(1 / ((n : ℝ)+1)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      simpa only [one_mul] using mul_le_mul' hν1 (pow_le_pow_left' (replicaConstant_le hν1 hd ha hm) n)
    _ = ((128 : ℝ≥0∞)^Module.finrank ℝ E)^((n : ℝ)/(n+1)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      rw [mul_one_div]
    _ ≤ ((128 : ℝ≥0∞)^Module.finrank ℝ E)^(1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        ((div_le_one hn0).2 (by linarith))
    _ = _ := ENNReal.rpow_one _

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by
  classical
  obtain ⟨D, hD, hDs, hDV⟩ := exists_projection_support (E := E) m hm
  let S : J → Set ((Fin m → E) × (Fin m → ℝ)) := fun j => D ∩ {x | φ x = j}
  have hS (j : J) : MeasurableSet (S j) := hD.inter (hφ (measurableSet_singleton j))
  have hSD (j : J) : projectionLaw (ν j) m (S j) = projectionLaw (ν j) m {x | φ x = j} := by
    apply Measure.measure_inter_eq_of_ae
    unfold projectionLaw
    apply (ae_map_iff (by fun_prop) hD).2
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν j).support_mem_ae] with x hx
    exact hDs x.1 x.2 (by simpa using hsupport j hx)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hUnion : (⋃ j, S j) = D := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨φ x,h,rfl⟩⟩
  have hsum : ∑ j, matrixLabelReference (E := E) m (S j) = matrixLabelReference (E := E) m D := by
    simpa only [hUnion, tsum_fintype] using (measure_iUnion (μ := matrixLabelReference (E := E) m) hdis hS).symm
  have hα : 0 ≤ 1 - 1/((n : ℝ)+1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ n+1)]
  have hV : (matrixLabelReference (E := E) m D)^(1-1/((n : ℝ)+1)) ≤
      (256 : ℝ≥0∞)^Module.finrank ℝ E := by
    calc
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^(1-1/((n : ℝ)+1)) :=
        ENNReal.rpow_le_rpow (hDV.trans (pow_le_pow_left' (by norm_num) _)) hα
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ = ∑ j, projectionLaw (ν j) m (S j) := by simp_rw [hSD]
    _ ≤ ∑ j, (128 : ℝ≥0∞)^Module.finrank ℝ E *
        (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) :=
      Finset.sum_le_sum fun j _ => projectionLaw_uniform_set_bound
        (hν j) (hν1 j) (hsupport j) hd ha hm hn hmargin (S j)
    _ = (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ∑ j, (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
         (∑ j, matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1))) :=
      mul_le_mul' le_rfl (finite_rpow_holder _ (by exact_mod_cast Nat.lt_add_one_of_le hn))
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * (256 : ℝ≥0∞)^Module.finrank ℝ E) := by
      rw [hsum]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hV)
    _ = _ := by rw [mul_left_comm, ← mul_pow]; norm_num; rw [mul_comm]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_reconstruct (ν : Measure E) (a : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (C * ENNReal.ofReal (r^a)) • (localNormalize ν a C z r).map (fun t => z+r • t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  rw [localNormalize, Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel hc0 hct,
    one_smul, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : E => z+r • t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma projectionLaw_smul (ν : Measure E) [SFinite ν] (m : ℕ) (c : ℝ≥0∞) :
    projectionLaw (c • ν) m = c • projectionLaw ν m := by
  rw [projectionLaw, Measure.prod_smul_right, Measure.map_smul]
  rfl

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

lemma localized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : ∀ j, PolynomialMass (ν j) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ)
    (z : E) {r : ℝ} (hr : 0 < r) :
    (∑ j, projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
        C * ENNReal.ofReal (r^a) := by
  let τ (j : J) := localNormalize (ν j) a C z r
  let F : ((Fin m → E) × (Fin m → ℝ)) → ((Fin m → E) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r * x.2 i)
  have hF : Measurable F := by fun_prop
  let (j : J) : IsFiniteMeasure (τ j) := localNormalize_finite (hν j) hC hCt z hr
  have hb := normalized_routing_bound τ
    (fun j => localNormalize_local (hν j) hC hCt z hr)
    (fun j => localNormalize_univ (hν j) hC hCt z hr)
    (fun j => localNormalize_support (ν j) a C z hr) hd ha hm hn hmargin (φ ∘ F) (hφ.comp hF)
  have he (j : J) : projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j} =
      (C * ENNReal.ofReal (r^a)) * projectionLaw (τ j) m {x | φ (F x) = j} := by
    rw [← localNormalize_reconstruct (ν j) a hC hCt z hr, projectionLaw_smul,
      projectionLaw_affine, Measure.smul_apply, smul_eq_mul, Measure.map_apply hF
      (measurableSet_eq_fun hφ measurable_const)]
    rfl
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul' le_rfl hb).trans_eq (by ring)

lemma projectionLaw_withDensity_apply (μ : Measure E) [SFinite μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) [SFinite (μ.withDensity h)] (m : ℕ)
    {S : Set ((Fin m → E) × (Fin m → ℝ))} (hS : MeasurableSet S) :
    projectionLaw (μ.withDensity h) m S =
      ∫⁻ s, h s * (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (A, fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian E)) ∂μ := by
  have hobs : Measurable (fun x : (Fin m → E) × E => (x.1, fun j => ⟪x.2,x.1 j⟫)) := by fun_prop
  have hi : Measurable (fun x : (Fin m → E) × E => S.indicator (fun _ => (1 : ℝ≥0∞))
      (x.1, fun j => ⟪x.2,x.1 j⟫)) :=
    ((measurable_const : Measurable (fun _ => (1 : ℝ≥0∞))).indicator hS).comp hobs
  rw [projectionLaw, Measure.map_apply hobs hS]
  rw [← one_mul (((Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) _),
    ← lintegral_indicator_const (hobs hS) 1]
  change (∫⁻ x : (Fin m → E) × E, S.indicator (fun _ => (1 : ℝ≥0∞))
    (x.1, fun j => ⟪x.2,x.1 j⟫) ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) = _
  rw [lintegral_prod_symm _ hi.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ hh hi.lintegral_prod_left]
  rfl

lemma blockValue_mass_identity (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {m : ℕ} {h : J → E → ℝ≥0∞} (hh : ∀ j, Measurable (h j))
    (hh1 : ∀ j s, h j s ≤ 1)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ)
    {S : Set E} (hS : MeasurableSet S) :
    (μ.withDensity (blockValue h φ)) S =
      ∑ j, projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} := by
  classical
  let g (j : J) (s : E) (A : Fin m → E) : ℝ≥0∞ :=
    if φ (A, fun k => ⟪s,A k⟫) = j then h j s else 0
  have hg (j : J) : Measurable (Function.uncurry (g j)) := by
    exact Measurable.ite (measurableSet_eq_fun (hφ.comp (by fun_prop)) measurable_const)
      ((hh j).comp measurable_fst) measurable_const
  have hselect (s : E) (A : Fin m → E) : h (φ (A, fun k => ⟪s,A k⟫)) s = ∑ j, g j s A := by
    simp [g]
  have he (j : J) : projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} =
      ∫⁻ s in S, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
    rw [restrict_withDensity hS]
    let : IsFiniteMeasure ((μ.restrict S).withDensity (h j)) :=
      isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
    rw [projectionLaw_withDensity_apply _ (hh j) _ (measurableSet_eq_fun hφ measurable_const)]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 j s).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    by_cases hx : φ (A, fun k => ⟪s,A k⟫) = j <;> simp [g, hx]
  rw [withDensity_apply _ hS]
  calc
    _ = ∫⁻ s in S, ∑ j, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
      apply lintegral_congr
      intro s
      unfold blockValue
      simp_rw [hselect]
      exact lintegral_finsetSum _ (fun j _ => (hg j).comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => (hg j).lintegral_prod_right)]
      simp_rw [he]

lemma blockValue_mass_bound (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {a m n : ℕ} {C : ℝ≥0∞} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) (hh1 : ∀ j s, h j s ≤ 1)
    (hlocal : ∀ j, PolynomialMass (μ.withDensity (h j)) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ) :
    PolynomialMass (μ.withDensity (blockValue h φ)) a
      ((32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * C) := by
  let (j : J) : IsFiniteMeasure (μ.withDensity (h j)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
  intro z r hr
  rw [blockValue_mass_identity μ hh hh1 hφ Metric.isClosed_closedBall.measurableSet]
  exact localized_routing_bound (fun j => μ.withDensity (h j)) hlocal hC hCt hd ha hm hn hmargin φ hφ z hr

end Block

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamIntegrals
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
open scoped Pointwise
section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_cons (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f v ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ v : Fin n → E, f (Fin.cons x v) ∂Measure.pi (fun _ => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (0 : Fin (n+1))).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f, lintegral_prod]
  · congr 1
    ext x
    congr 1
    ext v
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp
  · exact (hf.comp hp.measurable).aemeasurable

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) => streamRoute δ (n+1) k (δ (n+1) j (x.1 0,x.2 0)) (Fin.tail x.1,Fin.tail x.2))
    have ht : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        (Fin.tail x.1, Fin.tail x.2)) := by
      change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        ((fun i : Fin k => x.1 i.succ), (fun i : Fin k => x.2 i.succ)))
      fun_prop
    have hd : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        δ (n+1) j (x.1 0,x.2 0)) := (hδ (n+1) j).comp (by fun_prop)
    exact measurable_select (fun a => (ih (n+1) a).comp ht) hd

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma continuation_le_one {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih => exact (lintegral_mono (fun x => ih _ _)).trans_eq (by simp)

lemma continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by
  induction m generalizing n j with
  | zero =>
    simp [blockValue, streamRoute]
  | succ m ih =>
    rw [Nat.succ_add, continuation]
    simp_rw [ih]
    unfold blockValue
    have hf : Measurable (fun A : Fin (m+1) → E =>
        continuation δ w (n+(m+1)) k (streamRoute δ n (m+1) j (A,fun i => ⟪s,A i⟫)) s) := by
      exact (measurable_of_finite (fun a => continuation δ w (n+(m+1)) k a s)).comp
        ((measurable_streamRoute hδ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro A
    have he : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x A : Fin (m+1) → E) i⟫) = (fun i => ⟪s,A i⟫) := by
      ext i
      simp [Fin.tail]
    simp [streamRoute, he, Nat.add_left_comm, Nat.add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

lemma continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : k/q = (k-q)/q+1 := by
        conv_lhs => rw [← Nat.add_sub_of_le hk]
        exact Nat.add_div_left _ hq0
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      rw [hden, ← streamFactor, Nat.div_eq_of_lt (by omega : k < q)]
      simp [mul_comm]

lemma fin_tail_snoc {X : Type*} {k : ℕ} (A : Fin (k+1) → X) (x : X) :
    Fin.tail (Fin.snoc A x : Fin (k+2) → X) =
      (Fin.snoc (Fin.tail A : Fin k → X) x : Fin (k+1) → X) := by
  rw [← Fin.cons_self_tail A, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_cons]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_snoc (δ : ℕ → J → (E × ℝ) → J) (n k : ℕ) (j : J)
    (A : Fin k → E) (b : Fin k → ℝ) (x : E) (y : ℝ) :
    streamRoute δ n (k+1) j (Fin.snoc A x, Fin.snoc b y) =
      δ (n+k+1) (streamRoute δ n k j (A,b)) (x,y) := by
  induction k generalizing n j with
  | zero => simp [streamRoute, Fin.snoc_zero]
  | succ k ih =>
    rw [streamRoute]
    simp only [Fin.snoc_apply_zero, fin_tail_snoc]
    rw [ih, streamRoute]
    congr 1; omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by
  induction T with
  | zero =>
    have : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases h : t ≤ T
    · have he (x : Fin T → E) (y : E) :
          (fun i : Fin t => (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE ht i)) =
            (fun i : Fin t => x (Fin.castLE h i)) := by
        ext i
        change (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE h i).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      rw [lintegral_pi_snoc ν (fun x : Fin (T+1) → E => f (fun i => x (Fin.castLE ht i)))
        (hf.comp (by fun_prop))]
      simp_rw [he, lintegral_const, measure_univ, mul_one]
      exact ih h
    · have he : t = T+1 := by omega
      subst t
      rfl

end StreamAux

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamSlices
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
open scoped Pointwise
namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

lemma forcedRun_eq_route (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.forcedRun s ω x n =
      streamRoute (fun t j obs => (L.transition t ω j obs).2) 0 n (L.initialChoice ω).2
        ((fun i => x (Fin.castLE hn i)), (fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forcedRun, dite_eq_left (by omega), ih (by omega)]
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫), streamRoute_snoc]
    simp only [zero_add, real_inner_comm]

lemma run_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    (n : ℕ) (hn : n ≤ T) :
    (L.run s ω x n = .inl (L.forcedRun s ω x n)) ∨
      ∃ t ≤ n, L.run s ω x n = .inr (t, L.forcedRun s ω x t) := by
  induction n with
  | zero =>
    simp only [run, start, forcedRun]
    split
    · exact Or.inr ⟨0, le_rfl, rfl⟩
    · exact Or.inl rfl
  | succ n ih =>
    rcases ih (by omega) with h | ⟨t,ht,h⟩
    · have hnt : n < T := by omega
      rw [run, h]
      simp only [dite_eq_left hnt, forcedRun]
      split
      · exact Or.inr ⟨n+1, le_rfl, by simp [forcedRun, hnt]⟩
      · exact Or.inl rfl
    · right
      exact ⟨t, by omega, by rw [run, h]⟩

lemma terminal_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    ∃ t ≤ T, L.terminal s ω x = (t, L.forcedRun s ω x t) := by
  rcases L.run_forced_witness s ω x T le_rfl with h | ⟨t,ht,h⟩
  · exact ⟨T, le_rfl, by simp [terminal, h]⟩
  · exact ⟨t, ht, by simp [terminal, h]⟩

end Learner

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ObservationContinuity
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
open scoped Pointwise
section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by
  let ν' := C⁻¹ • ν
  have hCi : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC
  let : IsFiniteMeasure ν' := ⟨by simp only [ν', Measure.smul_apply, smul_eq_mul]; finiteness⟩
  have hlocal : HasLocalMassBound ν' (a : ℝ) := by
    intro z _ r hr
    have hh := mul_le_mul' (le_rfl : C⁻¹ ≤ C⁻¹) (hν z r hr)
    simpa only [ν', Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCt, one_mul, Real.rpow_natCast] using hh
  have hs : ν'.support ⊆ Metric.closedBall 0 1 :=
    (Measure.smul_absolutelyContinuous.support_mono).trans hsupport
  have hbound (S : Set ((Fin m → E) × (Fin m → ℝ))) :=
    projectionLaw_set_bound hlocal hs m n hn (by exact_mod_cast hmargin) S
  have he : projectionLaw ν' m = C⁻¹ • projectionLaw ν m := by
    exact projectionLaw_smul ν m C⁻¹
  intro S hS
  have h := hbound S
  rw [hS, ENNReal.zero_rpow_of_pos (by
    have : (1 : ℝ) < n+1 := by exact_mod_cast (by omega : 1 < n+1)
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr this)), mul_zero, he,
    Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left (ENNReal.inv_ne_zero.mpr hCt)

lemma sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by
  have hac : projectionLaw (ambientSphereLaw (E := E)) 1 ≪ matrixLabelReference (E := E) 1 := by
    apply projectionLaw_absolutelyContinuous (a := 2) (n := 1)
      (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
    · intro z r hr
      exact ambientSphereLaw_closedBall z hr 2 (by omega)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → E) × E => (z.1, fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian E)).prod (ambientSphereLaw (E := E)))
      (matrixLabelReference (E := E) 1) := ⟨by fun_prop, hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian E) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) E)).prod
    (measurable_subtype_coe.measurePreserving (sphereLaw (E := E)))
  have h2 := (measurePreserving_funUnique (stdGaussian E) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  ext z <;> simp [MeasurableEquiv.funUnique]

end ObservationAC

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamCaps
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
open scoped Pointwise
section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma measurable_capWeight (y : E) (ε : ℝ) : Measurable (capWeight y ε) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma capWeight_le_one (y s : E) (ε : ℝ) : capWeight y ε s ≤ 1 := by
  classical
  simp only [capWeight, Set.indicator_apply]
  split <;> simp

lemma capWeight_mass (y : E) {ε : ℝ} (hε : 0 < ε) (a : ℕ)
    (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    PolynomialMass ((ambientSphereLaw (E := E)).withDensity (capWeight y ε)) a
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) := by
  change PolynomialMass ((ambientSphereLaw (E := E)).withDensity ((Metric.closedBall y ε).indicator 1)) a _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact fun z r hr => terminal_cap_mass y z hε hr a ha

lemma ambient_mass_bound {f : E → ℝ≥0∞} {a : ℕ} {C : ℝ≥0∞}
    (h : PolynomialMass ((ambientSphereLaw (E := E)).withDensity f) a C) :
    (∫⁻ s, f s ∂ambientSphereLaw) ≤ C := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  apply (measure_mono_ae ?_).trans (by simpa using h 0 1 zero_lt_one)
  filter_upwards [(withDensity_absolutelyContinuous (ambientSphereLaw (E := E)) f).ae_le
    (ambientSphereLaw_ae_norm (E := E))] with s hs
  intro _
  change dist s 0 ≤ 1
  simp [dist_zero_right, hs]

lemma continuation_cap_integral_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by
  apply ambient_mass_bound
  apply continuation_mass_bound _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass (y n j) hε a ha)
    (Module.finrank_pos (R := ℝ) (M := E)) (by omega) hq hqa

lemma route_cap_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (k/q+1) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_cap_integral_bound hδ (fun _ => y) hε ha hq hqa 0 k j

end StreamCaps

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamTransfer
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
open scoped Pointwise
section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurePreserving_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν]
    {t T : ℕ} (ht : t ≤ T) :
    MeasurePreserving (fun x : Fin T → E => fun i : Fin t => x (Fin.castLE ht i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => ν)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_pi_prefix ν ht f hf

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

lemma prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0 : E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (route_cap_bound hδ y hε ha hq hqa k j).trans
  apply mul_le_mul' le_rfl
  exact pow_le_pow_right₀ (one_le_streamFactor (by omega : 0 < q))
    (Nat.add_le_add_right (Nat.div_le_div_right hk) 1)

end StreamTransfer

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_StreamEstimates
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
open scoped Pointwise
namespace Learner

lemma frozen_success_bound {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S : Fin (T+1) → Set (UnitSphere d × Samples d T) := fun t =>
    {z | dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE (by omega) i)),fun i => ⟪z.1.val,z.2 (Fin.castLE (by omega) i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] ⋃ t, S t := by
    filter_upwards [hgood] with z hz
    intro hs
    rcases L.terminal_forced_witness z.1 ω z.2 with ⟨t,ht,he⟩
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError, dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    refine Set.mem_iUnion.mpr ⟨⟨t,by omega⟩, ?_⟩
    change dist z.1.val (L.output t ω _) ≤ ε
    simpa only [estimate, he, hf] using hc
  let B : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
    streamFactor (E := Vector d) (J := State M) q ^ (T/q+1)
  have hb (t : Fin (T+1)) : μ (S t) ≤ B := by
    simpa only [B, μ, S, uniformSphere, sphereLaw, sampleLaw, finrank_euclideanSpace_fin] using
      prefix_route_cap_bound hδ (fun j => (L.output t ω j).val) hε
        (by simpa using ha) hq hqa (by omega : (t : ℕ) ≤ T) (L.initialChoice ω).2
  calc
    _ ≤ μ (⋃ t, S t) := measure_mono_ae hmono
    _ ≤ ∑' t, μ (S t) := measure_iUnion_le S
    _ ≤ ∑' _ : Fin (T+1), B := ENNReal.tsum_le_tsum hb
    _ = _ := by simp [B, tsum_fintype, nsmul_eq_mul, mul_assoc]

lemma streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

end Learner

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_MemoryPrecision
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
open scoped Pointwise
namespace Learner

lemma streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (L.streaming_success_bound ρ hL hd hε ha hq hqa)
  have ht : (T+1 : ℝ≥0∞) *
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top (streamFactor_ne_top q)
  have hr := ENNReal.toReal_mono ht hb
  simpa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^d),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ε^a), streamFactor,
    ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
    Fintype.card_fin, State, Nat.cast_pow, Nat.cast_ofNat, Vector] using hr

end Learner

lemma precision_from_stream_bound {d M T a q : ℕ} {ε A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hq : 0 < q) (hdq : d ≤ 8*q)
    (ha : d ≤ 4*a) (hM : (M : ℝ) ≤ A * (d : ℝ)^2) (hA : 0 < A)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbound : (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1)) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdp : (d : ℝ) ≤ 4*T := by exact_mod_cast hT
  have hdqp : (d : ℝ) ≤ 8*q := by exact_mod_cast hdq
  have hap : (d : ℝ) ≤ 4*a := by exact_mod_cast ha
  have hB : ((T/q+1 : ℕ) : ℝ) * d ≤ 12*T := by
    have hbd : (T/q+1)*d ≤ 12*T := by
      have hmul := Nat.div_mul_le_self T q
      calc
        (T/q+1)*d = (T/q)*d+d := by ring
        _ ≤ (T/q)*(8*q)+d := Nat.add_le_add_right (Nat.mul_le_mul_left _ hdq) _
        _ = 8*((T/q)*q)+d := by ring
        _ ≤ 8*T+d := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hmul) _
        _ ≤ 12*T := by omega
    exact_mod_cast hbd
  have hMq : (M : ℝ) / q ≤ 8*A*d := by
    apply (div_le_iff₀ hq0).2
    calc
      (M : ℝ) ≤ A*d^2 := hM
      _ ≤ A*d*(8*q) := by nlinarith [mul_le_mul_of_nonneg_left hdqp (by positivity : 0 ≤ A*d)]
      _ = 8*A*d*q := by ring
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2/3) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_pow] at hlog
  have hlogε : Real.log (1/ε) = -Real.log ε := by simp
  have hlogε0 : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
  have heq : (1/(q : ℝ)) * ((M : ℝ)*Real.log 2) = ((M : ℝ)/q)*Real.log 2 := by ring
  rw [heq] at hlog
  have hlT : Real.log ((T : ℝ)+1) ≤ T := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T+1)
  have hl3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hl4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hl32 : Real.log (32768 : ℝ) ≤ 32768 := Real.log_le_self (by norm_num)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hl23 : -(1 : ℝ) ≤ Real.log (2/3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2/3)
    norm_num at h
    linarith
  have hinside : (d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2 ≤
      (32768+8*A)*d := by
    have hm0 : (0 : ℝ) ≤ (M : ℝ)/q := by positivity
    have h1 := mul_le_mul_of_nonneg_left hl32 hd0.le
    have h2 := mul_le_mul_of_nonneg_left hl2 hm0
    nlinarith
  have hfull : ((T/q+1 : ℕ) : ℝ) *
      ((d : ℝ)*Real.log 32768 + ((M : ℝ)/q)*Real.log 2) ≤
      12*T*(32768+8*A) := by
    calc
      _ ≤ ((T/q+1 : ℕ) : ℝ) * ((32768+8*A)*d) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg _)
      _ = (32768+8*A)*(((T/q+1 : ℕ) : ℝ)*d) := by ring
      _ ≤ (32768+8*A)*(12*T) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hlogbound : (a : ℝ)*Real.log (1/ε) ≤ (400000+100*A)*T := by
    have h4 := mul_le_mul_of_nonneg_left hl4 hd0.le
    rw [hlogε]
    nlinarith [mul_nonneg hA.le hT0]
  have hmain : (d : ℝ)*Real.log (1/ε) ≤ 4*(400000+100*A)*T := by
    have ham := mul_le_mul_of_nonneg_right hap hlogε0
    linarith
  have hden : (0 : ℝ) < 4*(400000+100*A) := by positivity
  calc
    _ = ((d : ℝ)*Real.log (1/ε))/(4*(400000+100*A)) := by ring
    _ ≤ T := (div_le_iff₀ hden).2 (by nlinarith [hmain])

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Learners_LearnerModelBridge
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
namespace Learner

lemma UniformAdmissible.angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] {L : Learner d M T Ω} {ρ : Measure Ω}
    (hL : L.UniformAdmissible ρ) (ε : ℝ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

lemma UniformAdmissible.linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (hL.angularSuccess_nullMeasurable ε)
    (c := ENNReal.ofReal (21/32 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ (Vector d) := by
    simpa only [Vector, finrank_euclideanSpace_fin] using (Nat.mul_le_mul_left 4 hdim).trans hT
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_reflection_success_bound U hU
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s hs ht
    let t := sphereIsometry U.reflection s
    have he : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      have hi : z.2 i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      have he := U.reflection.inner_map_map (z.2 i) s.val
      rw [(Submodule.reflection_eq_self_iff (z.2 i)).2 hi] at he
      exact he.symm
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ = dist s.val t.val := rfl
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [he, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith

lemma UniformAdmissible.streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  have : NeZero d := ⟨by omega⟩
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    hL.angularSuccess_nullMeasurable ε
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hL.transition] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

lemma UniformAdmissible.streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {L : Learner d M T Ω} {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    (hL : L.UniformAdmissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (hL.streaming_success_bound hd hε ha hq hqa)
  have ht : (T+1 : ℝ≥0∞) *
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top (streamFactor_ne_top q)
  have hr := ENNReal.toReal_mono ht hb
  simpa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^d),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ε^a), streamFactor,
    ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
    Fintype.card_fin, State, Nat.cast_pow, Nat.cast_ofNat, Vector] using hr

end Learner

lemma source_fixed_quadratic_memory_oai {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {A : ℝ} (hA : 0 < A) (hd : 32 ≤ d) (hM : (M:ℝ) ≤ A*(d:ℝ)^2)
    {ε : ℝ} (hε : 0<ε) (hε10 : ε≤1/10)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (L : Learner d M T Ω)
    (hL : L.UniformAdmissible ρ) (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have hT : d ≤ 4*T := by
    by_contra h
    have hb := hs.trans (hL.linear_success_bound (by omega) (by omega) hε10)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  exact precision_from_stream_bound hd hT (by omega) hdq hda hM hA hε (by linarith)
    (hL.streaming_success_bound_real (by omega) hε ha hq hqa hs)

end PosteriorRegression
end

end OAI
end

theorem solution.{u} : type_of% @OAI.PosteriorRegression.source_fixed_quadratic_memory_oai.{u} := @OAI.PosteriorRegression.source_fixed_quadratic_memory_oai.{u}
