-- Prove2me | solution 1 for OAI.SK.Analytic.skBlockPressure_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:17:50.341307+00:00
-- url     : https://prove2.me/submissions/1727a2e3-f8be-48b5-8182-d75faf13679c

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPenalty
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem hierarchy_fixed_spin_density (n : ℕ) (m : Fin n → ℝ)
    (f U : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z * Real.exp (U z-f z) =
      Real.exp (U z-hierarchyPenalty n m 1 f z) := by
  rw [hierarchyPathWeight_eq n m f 1, ← Real.exp_add]
  apply congrArg Real.exp
  ring

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section GaussianGrowth
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.norm_id : HasExpGrowth (fun x : E => ‖x‖) := by
  refine ⟨1,1,zero_le_one,zero_le_one,?_⟩
  intro x
  simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),one_mul]
  exact le_trans (by linarith) (Real.add_one_le_exp ‖x‖)

theorem HasExpGrowth.section_right {f : E × ℝ → F} (hf : HasExpGrowth f) (y : ℝ) :
    HasExpGrowth (fun x => f (x,y)) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨C*Real.exp (M*|y|),M,by positivity,hM,?_⟩
  intro x
  apply (hf (x,y)).trans
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_left (abs_nonneg y))
    (le_add_of_nonneg_right (norm_nonneg x))

end GaussianGrowth

section LinearGrowth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasExpGrowth.linear (L : E →L[ℝ] ℝ) : HasExpGrowth L := by
  apply (HasExpGrowth.norm_id (E := E)).congr_bound (norm_nonneg L)
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using L.le_opNorm x

theorem HasExpGrowth.derivative_eval {f : E → ℝ} (h : HasExpGrowth (fderiv ℝ f)) (u : E) :
    HasExpGrowth (fun x => fderiv ℝ f x u) := h.clm (ContinuousLinearMap.apply ℝ ℝ u)

end LinearGrowth
end SK.Analytic
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert! h using 1
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [Pi.neg_apply,Pi.pow_apply,id_eq]
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    norm_num
    ring

theorem integrable_standardGaussian_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => f x*gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul,mul_comm]

theorem gaussian_integral_mul_eq_integral_deriv (f f' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hix : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hi₀ := (integrable_standardGaussian_iff f).mp hi
  have hi₁ := (integrable_standardGaussian_iff f').mp hi'
  have hi₂ := (integrable_standardGaussian_iff (fun x => x*f x)).mp hix
  have hx : Integrable (fun x => f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert hi₂.neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change _ = -(x*f x*gaussianPDFReal 0 1 x)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x) hx hi₁ hi₀
  have he : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by funext x; ring
  rw [he,integral_neg] at h
  have h' := neg_injective h
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul,mul_comm] using h'

theorem integral_tilted_real_eq_div {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (V g : Ω → ℝ) :
    (∫ x, g x ∂μ.tilted V) =
      (∫ x, g x*Real.exp (V x) ∂μ) / ∫ x, Real.exp (V x) ∂μ := by
  rw [integral_tilted]
  simp only [smul_eq_mul]
  calc
    (∫ x, (Real.exp (V x)/(∫ x, Real.exp (V x) ∂μ))*g x ∂μ) =
        ∫ x, (g x*Real.exp (V x))/(∫ x, Real.exp (V x) ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_div _ _

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberGaussianStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem fiberGaussian_stein (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : HasExpGrowth f) (hg' : HasExpGrowth (fderiv ℝ f))
    (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z*f z ∂fiberGaussian n x) =
      ∫ z, fderiv ℝ f z (coordinateAxis n i) ∂fiberGaussian n x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hleft (i : Fin (n+1)) : Integrable (fun z => coordinateProjection (n+1) i z*f z)
        (fiberGaussian (n+1) x) :=
      ((HasExpGrowth.linear _).mul hg).integrable_fiberGaussian (n+1)
        ((coordinateProjection (n+1) i).continuous.mul hf.continuous) x
    have hright (i : Fin (n+1)) : Integrable (fun z => fderiv ℝ f z (coordinateAxis (n+1) i))
        (fiberGaussian (n+1) x) :=
      (hg'.derivative_eval _).integrable_fiberGaussian (n+1)
        ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hl := hleft (Fin.last n)
      have hr := hright (Fin.last n)
      simp only [coordinateAxis_last] at hr ⊢
      rw [fiberGaussian,integral_prod _ hl,integral_prod _ hr]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [coordinateProjection,Fin.lastCases_last,ContinuousLinearMap.coe_snd']
      have hd (y : ℝ) : HasDerivAt (fun y => f (z,y)) (fderiv ℝ f (z,y) (0,1)) y := by
        exact (hf.differentiable (by norm_num) (z,y)).hasFDerivAt.comp_hasDerivAt y
          ((hasDerivAt_const y z).prodMk (hasDerivAt_id y))
      apply gaussian_integral_mul_eq_integral_deriv _ _ hd
        (hg.integrable_gaussian_section hf.continuous z)
      · exact (hg'.derivative_eval (0,1)).integrable_gaussian_section
          ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
      · simpa only [coordinateProjection,Fin.lastCases_last,ContinuousLinearMap.coe_snd'] using
          ((HasExpGrowth.linear (coordinateProjection (n+1) (Fin.last n))).mul hg).integrable_gaussian_section
              ((coordinateProjection (n+1) (Fin.last n)).continuous.mul hf.continuous) z
    · have hl := hleft j.castSucc
      have hr := hright j.castSucc
      simp only [coordinateAxis_castSucc] at hr ⊢
      rw [fiberGaussian,integral_prod_symm _ hl,integral_prod_symm _ hr]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst']
      have hc : ContDiff ℝ 1 (fun z : ParameterSpace n => f (z,y)) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      have he : fderiv ℝ (fun z : ParameterSpace n => f (z,y)) =
          fun z => leftRestrict (fderiv ℝ f (z,y)) := by
        funext z
        exact (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num)) z y).fderiv
      have hcg : HasExpGrowth (fderiv ℝ (fun z : ParameterSpace n => f (z,y))) := by
        rw [he]
        exact (hg'.congr_bound zero_le_one (fun point =>
          (leftRestrict_apply_bound (fderiv ℝ f point)).trans_eq (one_mul _).symm)).section_right y
      have H := ih (fun z => f (z,y)) hc (hg.section_right y) hcg j
      simpa only [he,leftRestrict,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply] using H

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_GrowthOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section GrowthOps
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.add {f g : E → F} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun z => f z+g z) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C+D,M+N,add_nonneg hC hD,add_nonneg hM hN,fun z => ?_⟩
  calc
    ‖f z+g z‖ ≤ ‖f z‖+‖g z‖ := norm_add_le _ _
    _ ≤ C*Real.exp (M*‖z‖)+D*Real.exp (N*‖z‖) := add_le_add (hf z) (hg z)
    _ ≤ C*Real.exp ((M+N)*‖z‖)+D*Real.exp ((M+N)*‖z‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (norm_nonneg z))) hC)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg z))) hD)
    _ = _ := by ring

end GrowthOps

theorem fiberGaussian_tilted_weighted_stein (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hg : ContDiff ℝ 1 g)
    (hgg : HasExpGrowth g) (hgg' : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V := by
  have he := (hV.1.exp).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hge : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  have hge' : HasExpGrowth (fderiv ℝ (fun z => Real.exp (V z))) := by
    simpa only [one_mul] using (hV.exp_growths 1).2.1
  have hde (z) : fderiv ℝ (fun z => g z*Real.exp (V z)) z =
      g z • fderiv ℝ (fun z => Real.exp (V z)) z +
      Real.exp (V z) • fderiv ℝ g z := by
    exact fderiv_mul (hg.differentiable (by norm_num) z) (he.differentiable (by norm_num) z)
  have hprod : HasExpGrowth (fderiv ℝ (fun z => g z*Real.exp (V z))) := by
    have heq := funext hde
    rw [heq]
    exact (hgg.smul hge').add (hge.smul hgg')
  have H := fiberGaussian_stein n _ (hg.mul he) (hgg.mul hge) hprod x i
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have i₁ : Integrable (fun z => fderiv ℝ g z (coordinateAxis n i)*Real.exp (V z))
      (fiberGaussian n x) :=
    ((hgg'.derivative_eval _).mul hge).integrable_fiberGaussian n
      (((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul he.continuous) x
  have i₂ : Integrable (fun z => g z*fderiv ℝ V z (coordinateAxis n i)*Real.exp (V z))
      (fiberGaussian n x) :=
    ((hgg.mul (hdV.derivative_eval _)).mul hge).integrable_fiberGaussian n
      ((hg.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).mul
        he.continuous) x
  simp only [integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [← integral_add i₁ i₂]
  calc
    (∫ z, coordinateProjection n i z*g z*Real.exp (V z) ∂fiberGaussian n x) =
        ∫ z, coordinateProjection n i z*(g z*Real.exp (V z)) ∂fiberGaussian n x := by
      congr 1; funext z; ring
    _ = _ := H
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hde,((hV.1.differentiable (by norm_num) z).hasFDerivAt.exp).fderiv]
      simp only [add_apply,smul_apply,smul_eq_mul]
      ring
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) :
    BoundedDerivs (hierarchyLevel n m f j) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [hierarchyLevel,Fin.lastCases_last] using hf
    · simp only [hierarchyLevel,Fin.lastCases_castSucc]
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      exact (ih (fun i => m i.castSucc) _ (hf.gaussianStep (m (Fin.last n))) i).compCLM P

theorem fderiv_hierarchyPenalty_apply (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (z v : ParameterSpace n) :
    fderiv ℝ (hierarchyPenalty n m u f) z v =
      ∑ j, hierarchyAtom n m u j*fderiv ℝ (hierarchyLevel n m f j) z v := by
  have he : hierarchyPenalty n m u f = fun z =>
      ∑ j, hierarchyAtom n m u j*hierarchyLevel n m f j z := funext (hierarchyPenalty_sum n m u f)
  rw [he]
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hierarchyLevel_boundedDerivs n m f hf j).1.differentiable (by norm_num) z).hasFDerivAt.const_mul
      (hierarchyAtom n m u j))
  rw [hd.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]

section Translation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem TranslationInvariant.fderiv_zero {f : E → ℝ} {u : E}
    (hi : TranslationInvariant f u) (hf : Differentiable ℝ f) (z : E) : fderiv ℝ f z u = 0 := by
  have hd₀ : HasDerivAt (fun t : ℝ => z+t • u) u 0 := by
    convert (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1
    · rfl
    · simp
  have hd := (hf (z+(0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt 0 hd₀
  have he : (fun t : ℝ => f (z+t • u)) = fun _ => f z := funext (hi z)
  simp only [zero_smul,add_zero] at hd
  change HasDerivAt (fun t : ℝ => f (z+t • u)) (fderiv ℝ f z u) 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (f z))

end Translation

theorem hierarchyLevel_invariant_of_prefix (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ParameterSpace n) (j : Fin (n+1))
    (hz : PrefixZero n j u) : TranslationInvariant (hierarchyLevel n m f j) u := by
  induction n with
  | zero => simp only [PrefixZero] at hz; subst u; intro z t; simp
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun hz => ?_) (fun j hz => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hz
      subst u
      intro z t
      simp
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hz
      have H := ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) u.1 j hz
      intro z t
      simpa only [hierarchyLevel,Fin.lastCases_castSucc,Prod.fst_add,Prod.smul_fst] using H z.1 t

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMomentLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAverage_momentLevel (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (hierarchyMomentLevel n m f g j) x = hierarchyAverage n m f g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf]
      exact ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j

theorem hierarchyLevel_gradient (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1))
    (u z : ParameterSpace n) (hz : TailZero n j u) :
    fderiv ℝ (hierarchyLevel n m f j) z u =
      hierarchyMomentLevel n m f (directionalGradient f u) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_last,directionalGradient]
    · simp only [TailZero,Fin.lastCases_castSucc] at hz
      simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_castSucc]
      let f' := gaussianStep (m (Fin.last n)) f
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      have hD := ((hierarchyLevel_boundedDerivs n (fun i => m i.castSucc) f'
        (hf.gaussianStep _) j).1.differentiable (by norm_num) z.1).hasFDerivAt.comp z
        P.hasFDerivAt
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z u = _
      have hDeq : fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z =
          (fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1).comp P := hD.fderiv
      rw [hDeq]
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1 u.1 = _
      rw [ih (fun i => m i.castSucc) f' (hf.gaussianStep _) j u.1 z.1 hz.2]
      have he : directionalGradient f' u.1 = gaussianAverage (m (Fin.last n)) f (directionalGradient f u) := by
        funext y
        rw [directionalGradient,fderiv_gaussianStep_apply hf]
        have hui : u = (u.1,0) := Prod.ext rfl hz.1
        rw [hui]
        rfl
      rw [he]

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAverageProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section AverageProduct
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_prefix_mul (m : ℝ) (f g : E × ℝ → ℝ) (h : E → ℝ) :
    gaussianAverage m f (fun z => h z.1*g z) = fun z => h z*gaussianAverage m f g z := by
  funext z
  exact integral_const_mul (h z) (fun y : ℝ => g (z,y))
end AverageProduct

theorem hierarchyMomentLevel_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => hierarchyMomentLevel n m f h j z*g z) j =
      fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_prefix_mul]
      simp_rw [ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f g) (gaussianAverage (m (Fin.last n)) f h) j]

theorem hierarchyAverage_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (fun z => hierarchyMomentLevel n m f h j z*g z) x =
      hierarchyAverage n m f
        (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) x := by
  rw [← hierarchyAverage_momentLevel n m f _ hf j,hierarchyMomentLevel_mul]

theorem hierarchyPathLaw_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g) (hh : Continuous h)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hgb : ∀ z, ‖g z‖ ≤ C) (hhb : ∀ z, ‖h z‖ ≤ D)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f h j z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z
        ∂hierarchyPathLaw n m f x := by
  have H := hierarchyMomentLevel_bounded_continuous n m f h hf hh hD hhb j
  have G := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hgb j
  have hb₁ (z) : ‖hierarchyMomentLevel n m f h j z*g z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (hgb z) (norm_nonneg _) hD
  have hb₂ (z) : ‖hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (G.2 z) (norm_nonneg _) hD
  have hcont₁ : Continuous (fun z => hierarchyMomentLevel n m f h j z*g z) := H.1.mul hg
  have hcont₂ : Continuous (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) := H.1.mul G.1
  rw [← hierarchyAverage_eq_integral n m f hf _ hcont₁ (mul_nonneg hD hC) hb₁,
    ← hierarchyAverage_eq_integral n m f hf _ hcont₂ (mul_nonneg hD hC) hb₂]
  exact hierarchyAverage_prefix_mul n m f g h hf j x

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SpinStein
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Nonempty S] in
theorem finite_fiberGaussian_integrable (n : ℕ) (g : S → ParameterSpace n → ℝ)
    (hc : ∀ s, Continuous (g s)) (hi : ∀ s, Integrable (g s) (fiberGaussian n 0)) :
    Integrable (fun sz : S × ParameterSpace n => g sz.1 sz.2)
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
  apply (integrable_prod_iff ?_).2
  · exact ⟨ae_of_all _ hi,Integrable.of_finite⟩
  · exact (measurable_from_prod_countable_right (fun s => (hc s).measurable)).aestronglyMeasurable

theorem spinGaussianLaw_probability (n : ℕ) (V : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) : IsProbabilityMeasure (spinGaussianLaw n V 0) := by
  let : NeZero ((Measure.count : Measure S).prod (fiberGaussian n 0)) := by
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    rw [← univ_prod_univ,Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)
  apply isProbabilityMeasure_tilted
  apply finite_fiberGaussian_integrable n _ (fun s => (Real.continuous_exp.comp (hV s).1.continuous))
  intro s
  have hg := ((hV s).exp_growths 1).1
  simp only [one_mul] at hg
  exact hg.integrable_fiberGaussian n (Real.continuous_exp.comp (hV s).1.continuous) 0

end SpinStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinWeightedStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SpinWeightedStein
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem spinGaussian_integrable (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hg : ∀ s, HasExpGrowth (g s))
    (hc : ∀ s, Continuous (g s)) :
    Integrable (fun sz : S × ParameterSpace n => g sz.1 sz.2) (spinGaussianLaw n V 0) := by
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hI := finite_fiberGaussian_integrable n _ hce
    (fun s => (he s).integrable_fiberGaussian n (hce s) 0)
  rw [spinGaussianLaw,integrable_tilted_iff hI]
  exact finite_fiberGaussian_integrable n _ (fun s => (hce s).smul (hc s))
    (fun s => ((he s).smul (hg s)).integrable_fiberGaussian n ((hce s).smul (hc s)) 0)

theorem spinGaussian_weighted_stein (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (i : Fin n) :
    (∫ sz, coordinateProjection n i sz.2*g sz.1 sz.2 ∂spinGaussianLaw n V 0) =
      (∫ sz, fderiv ℝ (g sz.1) sz.2 (coordinateAxis n i) ∂spinGaussianLaw n V 0) +
      ∫ sz, g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i) ∂spinGaussianLaw n V 0 := by
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hdV (s : S) : HasExpGrowth (fderiv ℝ (V s)) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV s
    exact HasExpGrowth.of_bounded hC hb
  have hcdV (s : S) := (hV s).1.continuous_fderiv (by norm_num)
  have hcdg (s : S) := (hc s).continuous_fderiv (by norm_num)
  have il := finite_fiberGaussian_integrable n
    (fun s z => coordinateProjection n i z*g s z*Real.exp (V s z))
    (fun s => (((coordinateProjection n i).continuous.mul (hc s).continuous).mul (hce s)))
    (fun s => (((HasExpGrowth.linear _).mul (hg s)).mul (he s)).integrable_fiberGaussian n
      (((coordinateProjection n i).continuous.mul (hc s).continuous).mul (hce s)) 0)
  have ir₁ := finite_fiberGaussian_integrable n
    (fun s z => fderiv ℝ (g s) z (coordinateAxis n i)*Real.exp (V s z))
    (fun s => ((hcdg s).clm_apply continuous_const).mul (hce s))
    (fun s => (((hdg s).derivative_eval _).mul (he s)).integrable_fiberGaussian n
      (((hcdg s).clm_apply continuous_const).mul (hce s)) 0)
  have ir₂ := finite_fiberGaussian_integrable n
    (fun s z => g s z*fderiv ℝ (V s) z (coordinateAxis n i)*Real.exp (V s z))
    (fun s => ((hc s).continuous.mul ((hcdV s).clm_apply continuous_const)).mul (hce s))
    (fun s => (((hg s).mul ((hdV s).derivative_eval _)).mul (he s)).integrable_fiberGaussian n
      (((hc s).continuous.mul ((hcdV s).clm_apply continuous_const)).mul (hce s)) 0)
  simp only [spinGaussianLaw,integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [integral_prod _ il,integral_prod _ ir₁,integral_prod _ ir₂,
    integral_count,integral_count,integral_count,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have H := fiberGaussian_tilted_weighted_stein n (V s) (g s) (hV s) (hc s) (hg s) (hdg s) 0 i
  simp only [integral_tilted_real_eq_div] at H
  rw [← add_div] at H
  exact (div_left_inj' (integral_exp_pos
    ((he s).integrable_fiberGaussian n (hce s) 0)).ne').mp H

end SpinWeightedStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LawIdentification
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyTerminalGibbs_sum (n : ℕ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (z : ParameterSpace n) : ∑ s, hierarchyTerminalGibbs n U s z = 1 := by
  have hp : 0 < ∑ s, Real.exp (U s z) :=
    Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [hierarchyTerminalGibbs,Real.exp_sub,affineLogPartition,zero_add,
    Real.exp_log hp,← Finset.sum_div,div_self hp.ne']

end LawIdentification
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section HierarchyDensity
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyPotential_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) : BoundedDerivs (hierarchyPotential n m U s) := by
  have hu : BoundedDerivs (fun z => U s z) := by
    refine ⟨(U s).contDiff,‖U s‖,0,norm_nonneg _,le_rfl,?_,?_⟩
    · intro z; simp only [ContinuousLinearMap.fderiv]; exact le_rfl
    · intro z
      have he : fderiv ℝ (fun z => U s z) = fun _ => U s := by
        funext z; exact (U s).hasFDerivAt.fderiv
      rw [he]
      change ‖fderiv ℝ (Function.const (ParameterSpace n) (U s)) z‖ ≤ 0
      rw [fderiv_const]
      exact ContinuousLinearMap.opNorm_zero.le
  have hp := hierarchyPenalty_boundedDerivs n m 1 _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
  convert hu.add (hp.const_mul (-1)) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [hierarchyPotential,sub_eq_add_neg,neg_one_mul]

theorem hierarchyPotential_normalized (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    (∫ sz : S × ParameterSpace n, Real.exp (hierarchyPotential n m U sz.1 sz.2)
      ∂(Measure.count : Measure S).prod (fiberGaussian n 0)) = 1 := by
  have hg (s : S) : HasExpGrowth (fun z => Real.exp (hierarchyPotential n m U s z)) := by
    simpa only [one_mul] using ((hierarchyPotential_boundedDerivs n m U s).exp_growths 1).1
  have hc (s : S) := Real.continuous_exp.comp (hierarchyPotential_boundedDerivs n m U s).1.continuous
  have hi (s : S) := (hg s).integrable_fiberGaussian n (hc s) 0
  change (∫ sz : S × ParameterSpace n, (Real.exp ∘ hierarchyPotential n m U sz.1) sz.2
    ∂(Measure.count : Measure S).prod (fiberGaussian n 0)) = 1
  rw [integral_prod _ (finite_fiberGaussian_integrable n _ hc hi),integral_count]
  change (∑ s, ∫ z, Real.exp (hierarchyPotential n m U s z) ∂fiberGaussian n 0) = 1
  rw [← integral_finsetSum _ (fun s _ => hi s)]
  have he (z : ParameterSpace n) : (∑ s, Real.exp (hierarchyPotential n m U s z)) =
      hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z := by
    simp only [hierarchyPotential,← hierarchy_fixed_spin_density]
    rw [← Finset.mul_sum]
    change hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z *
      (∑ s, hierarchyTerminalGibbs n U s z) = _
    rw [hierarchyTerminalGibbs_sum,mul_one]
  simp_rw [he]
  exact (hierarchyPathWeight_normalized n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0).2

theorem hierarchyGaussianLaw_eq_spinGaussian (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    hierarchyGaussianLaw n m U = spinGaussianLaw n (hierarchyPotential n m U) 0 := by
  unfold hierarchyGaussianLaw spinGaussianLaw Measure.tilted
  rw [hierarchyPotential_normalized]
  simp only [div_one]
  congr 1
  funext sz
  congr 1
  exact hierarchy_fixed_spin_density n m _ (U sz.1) sz.2

end HierarchyDensity
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SmoothObservables
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem HasExpGrowth.const (c : F) : HasExpGrowth (fun _ : E => c) :=
  HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)

end SmoothObservables

end SK.Analytic

end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PrefixAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section TerminalMarginal
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyTerminalGibbs_eq_affineGibbs (n : ℕ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) :
    hierarchyTerminalGibbs n U s z = affineGibbs (fun _ => 0) U z s := by
  have hp : 0 < ∑ t, Real.exp (U t z) := by
    simpa only [zero_add] using affinePartition_pos (fun _ => 0) U z
  simp only [hierarchyTerminalGibbs,affineGibbs,affineLogPartition,zero_add,Real.exp_sub,
    Real.exp_log hp]

theorem hierarchyGaussian_terminal_marginal (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (h : ParameterSpace n → ℝ)
    (hh : Continuous h) (hb : HasExpGrowth h) :
    (∫ sz, c sz.1*h sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, affineMoment (fun _ => 0) U c z*h z
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let V := hierarchyPotential n m U
  have hV (s : S) := hierarchyPotential_boundedDerivs n m U s
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hi (s : S) : Integrable (fun z => c s*h z*Real.exp (V s z)) (fiberGaussian n 0) :=
    (((HasExpGrowth.const (c s)).mul hb).mul (he s)).integrable_fiberGaussian n
      ((continuous_const.mul hh).mul (hce s)) 0
  have hI : Integrable (fun sz : S × ParameterSpace n => c sz.1*h sz.2*
      Real.exp (hierarchyPotential n m U sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) :=
    finite_fiberGaussian_integrable n (fun s z => c s*h z*Real.exp (V s z))
      (fun s => (continuous_const.mul hh).mul (hce s)) hi
  rw [hierarchyGaussianLaw_eq_spinGaussian,spinGaussianLaw,integral_tilted_real_eq_div,
    hierarchyPotential_normalized,div_one,integral_prod _ hI,integral_count]
  rw [← integral_finsetSum _ (fun s _ => hi s),hierarchyPathLaw_integral n m _
    (affineLogPartition_boundedDerivs (fun _ => 0) U)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [V,hierarchyPotential,← hierarchy_fixed_spin_density]
  change (∑ s, c s*h z*(hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z *
    hierarchyTerminalGibbs n U s z)) = _
  simp only [hierarchyTerminalGibbs_eq_affineGibbs,affineMoment,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end TerminalMarginal

end SK.Analytic

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_retained (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (j l : Fin (n+1)) (hjl : j ≤ l) :
    hierarchyMomentLevel n m f (hierarchyMomentLevel n m f g j) l =
      hierarchyMomentLevel n m f g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hjl
    refine Fin.lastCases (fun _ => ?_) (fun l hjl => ?_) l
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hjl
      refine Fin.lastCases (fun hjl => ?_) (fun j hjl => ?_) j
      · exact (Nat.not_le_of_gt l.isLt hjl).elim
      · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf]
        funext z
        exact congrFun (ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j l hjl) z.1

theorem hierarchyPathLaw_fixed_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g) (hh : Continuous h)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hgb : ∀ z, ‖g z‖ ≤ C) (hhb : ∀ z, ‖h z‖ ≤ D)
    (j : Fin (n+1)) (hj : hierarchyMomentLevel n m f h j = h) (x : ℝ) :
    (∫ z, h z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, h z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have H := hierarchyPathLaw_prefix_mul n m f g h hf hg hh hC hD hgb hhb j x
  rwa [hj] at H

section SpinMeans
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyLevel_spinMean (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (j : Fin (n+1))
    (u : ParameterSpace n) (hu : TailZero n j u) (hU : ∀ s, U s u = c s) :
    directionalGradient (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u =
      hierarchySpinMean n m U c j := by
  funext z
  rw [directionalGradient,hierarchyLevel_gradient n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j u z hu]
  have he : directionalGradient (affineLogPartition (fun _ => 0) U) u = affineMoment (fun _ => 0) U c := by
    funext z
    simp only [directionalGradient,fderiv_affineLogPartition_apply,hU]
  rw [he]
  rfl

end SpinMeans
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinatePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SpinProduct
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchySpinMean_terminal_product (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ s, ‖c s‖ ≤ C) (j : Fin (n+1)) :
    (∫ sz, c sz.1*hierarchySpinMean n m U c j sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, (hierarchySpinMean n m U c j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hr := hierarchySpinMean_regular n m U c hC hc j
  rw [hierarchyGaussian_terminal_marginal n m U c _ hr.1 (HasExpGrowth.of_bounded hC hr.2)]
  have he : hierarchyMomentLevel n m f (hierarchySpinMean n m U c j) j =
      hierarchySpinMean n m U c j := hierarchyMomentLevel_retained n m f _ hf j j le_rfl
  have H := hierarchyPathLaw_fixed_mul n m f (affineMoment (fun _ => 0) U c)
    (hierarchySpinMean n m U c j) hf (affineMoment_continuous _ _ _) hr.1 hC hC
    (affineMoment_norm_le _ _ _ hc) hr.2 j he 0
  calc
    _ = ∫ z, hierarchySpinMean n m U c j z*affineMoment (fun _ => 0) U c z
        ∂hierarchyPathLaw n m f 0 := by congr 1; funext z; ring
    _ = _ := H.trans (by congr 1; funext z; change hierarchySpinMean n m U c j z * hierarchySpinMean n m U c j z = _; ring)

end SpinProduct
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

section ParameterGrowth
variable {P E F G : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem ParamExpGrowth.clm {f : P × E → F} (hf : ParamExpGrowth f) (L : F →L[ℝ] G) :
    ParamExpGrowth (fun z => L (f z)) := hf.of_norm_le (norm_nonneg L) (fun z => L.le_opNorm (f z))

end ParameterGrowth
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_LocalStepDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section LocalStepDerivative
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_local_gaussianStep {f : E × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (m : ℝ) (he : GaussianLocallyDominated (fun z => Real.exp (m*f z)))
    (he₁ : GaussianLocallyDominated (fderiv ℝ (fun z => Real.exp (m*f z)))) (x : E) :
    fderiv ℝ (gaussianStep m f) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x := by
  have hd := hf.differentiable (by norm_num)
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    have hfun : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep,ite_true]
    rw [hfun]
    exact fderiv_local_gaussian_integral f hf hg hg₁ x
  · let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
    have hc : ContDiff ℝ 1 (fun z => Real.exp (m*f z)) := (contDiff_const.mul hf).exp
    have hp : Z x ≠ 0 := (integral_exp_pos (he.integrable_section hc.continuous x)).ne'
    have hi := hasFDerivAt_local_gaussian_integral (fun z => Real.exp (m*f z)) _
      hc.continuous (leftRestrict.continuous.comp
        ((hc.fderiv_right (m := 0) (by norm_num)).continuous)) he (he₁.clm leftRestrict)
      (leftRestrict_hasFDerivAt _ (hc.differentiable (by norm_num))) x
    have hfun : gaussianStep m f = fun x => Real.log (Z x)/m := by
      funext x
      simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z]
    rw [hfun]
    have hder := (hi.log hp).mul_const m⁻¹
    simp only [div_eq_mul_inv] at ⊢
    rw [hder.fderiv]
    rw [← integral_smul,← integral_smul,gaussianStepLaw,integral_tilted]
    apply integral_congr_ae
    filter_upwards [] with y
    have hdexp := ((hd (x,y)).hasFDerivAt.const_mul m).exp.fderiv
    simp only [Function.comp_apply]
    rw [hdexp]
    ext v
    simp only [smul_apply,smul_eq_mul,leftRestrict,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
    dsimp only [Z] at hp ⊢
    field_simp [hm,hp]
end LocalStepDerivative
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterStepDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterStepDerivative
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem param_reassoc_fderiv_growth {f : P × (E × ℝ) → ℝ}
    (hf : Differentiable ℝ f) (hg : ParamExpGrowth (fderiv ℝ f)) :
    ParamExpGrowth (fun z : P × (E × ℝ) =>
      fderiv ℝ (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) ((z.1,z.2.1),z.2.2)) := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let ι : P × (E × ℝ) → (P × E) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  have h : ParamExpGrowth (fun z => fderiv ℝ (fun w => f (L w)) (ι z)) :=
    param_fderiv_compCLM_growth f L ι hf hg
  exact h

theorem ParamExpGrowth.integrable_paramStepLaw {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f)
    {g : P × (E × ℝ) → F} (hg : ParamExpGrowth g) (hc : Continuous g)
    (m : ℝ) (z : P × E) : Integrable (fun y => g (z.1,(z.2,y)))
      (gaussianStepLaw m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) z) := by
  have he := hf.2.1.exp_mul m
  have hce : Continuous (fun w : (P × E) × ℝ => Real.exp (m*f (w.1.1,(w.1.2,w.2)))) :=
    Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))
  rw [gaussianStepLaw,integrable_tilted_iff (he.weakLocallyDominated.integrable_section hce z)]
  exact (he.smul hg).weakLocallyDominated.integrable_section (hce.smul
    (hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))) z

theorem ParamRegular.fderiv_gaussianStep {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) :
    fderiv ℝ (SK.Analytic.gaussianStep m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))) z =
      ∫ y, leftRestrict (fderiv ℝ (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) (z,y))
        ∂gaussianStepLaw m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) z := by
  have hg₁ := param_reassoc_fderiv_growth (hf.1.differentiable (by norm_num)) hf.2.2.1
  have he := (hf.const_mul m).expSmooth
  have he₁ := param_reassoc_fderiv_growth (he.1.differentiable (by norm_num)) he.2.2.1
  apply fderiv_local_gaussianStep
  · exact (hf.1.comp (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).contDiff).of_le (by norm_num)
  · exact hf.2.1.expGrowth.weakLocallyDominated
  · exact hg₁.weakLocallyDominated
  · exact he.2.1.weakLocallyDominated
  · exact he₁.weakLocallyDominated

theorem ParamRegular.parameterDerivative_gaussianStep {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) (v : P) :
    fderiv ℝ (SK.Analytic.gaussianStep m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))) z (v,0) =
      gaussianAverage m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))
        (fun w : (P × E) × ℝ => fderiv ℝ f (w.1.1,(w.1.2,w.2)) (v,0)) z := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let g := fun w : (P × E) × ℝ => f (L w)
  have hcg : ContDiff ℝ 2 g := hf.1.comp L.contDiff
  have hg := param_reassoc_fderiv_growth (hf.1.differentiable (by norm_num)) hf.2.2.1
  have hi := (hg.clm leftRestrict).integrable_paramStepLaw hf
    ((leftRestrict.continuous.comp (hcg.fderiv_right (m := 1) (by norm_num)).continuous).comp
      (continuous_fst.prodMk continuous_snd.fst |>.prodMk continuous_snd.snd)) m z
  rw [hf.fderiv_gaussianStep,ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with y
  have hD := ((hf.1.differentiable (by norm_num) (L (z,y))).hasFDerivAt.comp (z,y) L.hasFDerivAt).fderiv
  change leftRestrict (fderiv ℝ g (z,y)) (v,0) = _
  change fderiv ℝ g (z,y) = _ at hD
  rw [hD]
  rfl
end ParameterStepDerivative
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_MeanStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SharedSpinTest
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyGaussian_integrable (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hg : ∀ s, HasExpGrowth (g s)) (hc : ∀ s, Continuous (g s)) :
    Integrable (fun sz => g sz.1 sz.2) (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussian_integrable n _ g (hierarchyPotential_boundedDerivs n m U) hg hc

end SharedSpinTest
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tailZero_coordinateAxis (n : ℕ) (i : Fin n) (j : Fin (n+1)) (h : i.val < j.val) :
    TailZero n j (coordinateAxis n i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.lastCases (fun _ => by simp only [TailZero,Fin.lastCases_last]) (fun j h => ?_) j
    revert h
    refine Fin.lastCases (fun h => ?_) (fun i h => ?_) i
    · exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ j.isLt) h).elim
    · simp only [coordinateAxis_castSucc,TailZero,Fin.lastCases_castSucc]
      exact ⟨trivial,ih i j h⟩

theorem prefixZero_coordinateAxis (n : ℕ) (i : Fin n) (j : Fin (n+1)) (h : j.val ≤ i.val) :
    PrefixZero n j (coordinateAxis n i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.lastCases (fun h => ?_) (fun j h => ?_) j
    · exact (Nat.not_le_of_gt i.isLt h).elim
    · revert h
      refine Fin.lastCases (fun _ => ?_) (fun i h => ?_) i
      · simpa only [coordinateAxis_last,PrefixZero,Fin.lastCases_castSucc] using PrefixZero.zero n j
      · simpa only [coordinateAxis_castSucc,PrefixZero,Fin.lastCases_castSucc] using ih i j h

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem normalizedDot_sq_le {N : ℕ} (a b : Fin N → ℝ) :
    (normalizedDot a b)^2 ≤ normalizedSquare a*normalizedSquare b := by
  have H := div_le_div_of_nonneg_right
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b) (sq_nonneg (N : ℝ))
  simpa only [normalizedDot,normalizedSquare,div_pow,div_mul_div_comm,← pow_two] using H

theorem abs_normalizedDot_le {N : ℕ} (a b : Fin N → ℝ) :
    |normalizedDot a b| ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare b) := by
  rw [← Real.sqrt_mul (normalizedSquare_nonneg a)]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using normalizedDot_sq_le a b

end SK.Analytic
namespace SK.Analytic

theorem massFromAtoms_castSucc (n : ℕ) (w : Fin (n+2) → ℝ) (i : Fin n) :
    massFromAtoms (n+1) w i.castSucc = massFromAtoms n (fun j => w j.castSucc) i := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have h : ¬ n+1 ≤ i.val := by omega
  rw [ite_eq_right h,add_zero]

theorem massFromAtoms_last (n : ℕ) (w : Fin (n+2) → ℝ) :
    massFromAtoms (n+1) w (Fin.last n) = ∑ j : Fin (n+1), w j.castSucc := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,show ¬ n+1 ≤ n by omega,ite_false,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (by omega)]

theorem hierarchyAtom_massFromAtoms (n : ℕ) (w : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    hierarchyAtom n (massFromAtoms n w) (∑ k, w k) j = w j := by
  induction n with
  | zero => simp [hierarchyAtom,Fin.eq_zero j]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyAtom,Fin.lastCases_last,massFromAtoms_last]
      rw [Fin.sum_univ_castSucc]
      ring
    · simp only [hierarchyAtom,Fin.lastCases_castSucc,massFromAtoms_castSucc,massFromAtoms_last]
      exact ih (fun j => w j.castSucc) j

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockAtom_sum (D N k : ℕ) : ∑ t, blockAtom D N k t = 1 := by
  unfold blockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem hierarchyAtom_blockMass (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 t = blockAtom D N k t := by
  rw [← blockAtom_sum D N k]
  exact hierarchyAtom_massFromAtoms _ _ t

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_eq_natAdd (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    fieldIndex D N k b i = Fin.natAdd D (finProdFinEquiv (b,i)) := by
  apply Fin.ext
  change D+b.val*N+i.val = D+(i.val+N*b.val)
  ring

@[simp] theorem blockInteraction_field {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (b : Fin (k+1)) (i : Fin N) : blockInteraction (k := k) I (fieldIndex D N k b i) = {i} := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockInteraction,Fin.addCases_right,Equiv.symm_apply_apply]

@[simp] theorem blockCoefficients_field {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) : blockCoefficients (N := N) a v (fieldIndex D N k b i) = v b := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockCoefficients,Fin.addCases_right,Equiv.symm_apply_apply]

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section PathMarginal
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
theorem hierarchyGaussian_probability (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) : IsProbabilityMeasure (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussianLaw_probability n _ (hierarchyPotential_boundedDerivs n m U)

end PathMarginal

end SK.Analytic
namespace SK.Analytic

section MeanVariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem abs_normalizedDot_le_one {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) : |normalizedDot a b| ≤ 1 := by
  have h₁ : Real.sqrt (normalizedSquare a) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
  have h₂ : Real.sqrt (normalizedSquare b) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one b hb)
  exact (abs_normalizedDot_le a b).trans (by nlinarith [Real.sqrt_nonneg (normalizedSquare a),Real.sqrt_nonneg (normalizedSquare b)])

end MeanVariance
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section CascadeProbability
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {S : Type} [Fintype S] [Nonempty S]

theorem affineGibbs_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => affineGibbs c L x s) := by
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun t _ => Real.continuous_exp.comp (continuous_const.add (L t).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineGibbs_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    affineGibbs c L x s ≤ 1 := by
  rw [← affineGibbs_sum c L x]
  exact Finset.single_le_sum (fun t _ => (affineGibbs_pos c L x t).le) (Finset.mem_univ s)

theorem affineGibbs_norm_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    ‖affineGibbs c L x s‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
  exact affineGibbs_le_one c L x s

end CascadeProbability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_nonneg (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hg : ∀ z, 0 ≤ g z) (j : Fin (n+1)) (z : ParameterSpace n) :
    0 ≤ hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => exact hg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg z
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      apply ih
      intro x
      exact integral_nonneg (fun y => hg (x,y))

theorem hierarchyMomentLevel_const (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun _ => a) j = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_const_prefix hf _ (fun _ => a),ih _ _ (hf.gaussianStep _)]

theorem hierarchyMomentLevel_const_mul (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => a*g z) j = fun z => a*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
          fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
        funext z; exact integral_const_mul a _
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he,ih]

theorem hierarchyMomentLevel_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (g : T → ParameterSpace n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => ∑ t, g t z) j =
      fun z => ∑ t, hierarchyMomentLevel n m f (g t) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
          fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
        funext z
        let := gaussianStepLaw_probability hf (m (Fin.last n)) z
        apply integral_finsetSum
        intro t _
        exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (C t) (ae_of_all _ (fun y => hb t (z,y)))
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he]
      rw [ih _ _ (hf.gaussianStep _) _
        (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
        (fun t z => gaussianAverage_norm_le hf _ (hb t) z) j]

section Probability
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinWeight_regular (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (s : S) :
    Continuous (fun z => hierarchySpinWeight n m U j z s) ∧
      ∀ z, ‖hierarchySpinWeight n m U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineGibbs_continuous (fun _ => 0) U s) (by norm_num) (fun z => affineGibbs_norm_le_one (fun _ => 0) U z s) j

theorem hierarchySpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : 0 ≤ hierarchySpinWeight n m U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => le_of_lt (affineGibbs_pos (fun _ => 0) U z s)) j z

theorem hierarchySpinWeight_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) : ∑ s, hierarchySpinWeight n m U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => affineGibbs (fun _ => 0) U z s)
    (affineGibbs_continuous (fun _ => 0) U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one (fun _ => 0) U z s) j
  have he : (fun z => ∑ s, affineGibbs (fun _ => 0) U z s) = fun _ => 1 :=
    funext (fun z => affineGibbs_sum (fun _ => 0) U z)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U)] at H
  exact (congrFun H z).symm

theorem hierarchySpinMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchySpinMean n m U v j z = ∑ s, hierarchySpinWeight n m U j z s*v s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => v s*affineGibbs (fun _ => 0) U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous (fun _ => 0) U s))
    (fun s => ‖v s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one (fun _ => 0) U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => ∑ s, affineGibbs (fun _ => 0) U z s*v s) j z = _
  simpa only [hierarchySpinWeight,mul_comm] using congrFun H z
end Probability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinCovarianceVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SpinCovarianceVariation
variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem hierarchySpinMean_const_mul (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (j : Fin (n+1)) :
    hierarchySpinMean n m U (fun s => a*c s) j =
      fun z => a*hierarchySpinMean n m U c j z := by
  have he : affineMoment (fun _ => 0) U (fun s => a*c s) =
      fun z => a*affineMoment (fun _ => 0) U c z := by
    funext z
    simp only [affineMoment,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [hierarchySpinMean,he,hierarchyMomentLevel_const_mul]

theorem hierarchyLevel_coordinate_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (j : Fin (n+1)) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z (coordinateAxis n i) =
      if i.val < j.val then a*hierarchySpinMean n m U c j z else 0 := by
  split_ifs with h
  · have H := congrFun (hierarchyLevel_spinMean n m U (fun s => a*c s) j
      (coordinateAxis n i) (tailZero_coordinateAxis n i j h) hU) z
    rw [hierarchySpinMean_const_mul] at H
    exact H
  · exact (hierarchyLevel_invariant_of_prefix n m _ _ j
      (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j).1.differentiable
          (by norm_num)) z

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyPotential_coordinate_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (s : S) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyPotential n m U s) z (coordinateAxis n i) =
      a*c s-∑ j : Fin (n+1), if i.val < j.val then
        hierarchyAtom n m 1 j*(a*hierarchySpinMean n m U c j z) else 0 := by
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hp := hierarchyPenalty_boundedDerivs n m 1 _ hf
  change fderiv ℝ (fun z => U s z-hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) z _ = _
  rw [fderiv_fun_sub (U s).differentiableAt (hp.1.differentiable (by norm_num) z)]
  simp only [sub_apply,ContinuousLinearMap.fderiv,hU]
  rw [fderiv_hierarchyPenalty_apply n m 1 _ hf]
  simp_rw [hierarchyLevel_coordinate_gradient n m U c a i hU]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [mul_zero]

theorem hierarchyGaussian_coordinate_spin (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (hc : ∀ s, ‖c s‖ ≤ 1)
    (hsq : ∀ s, (c s)^2 = 1) :
    (∫ sz, c sz.1*coordinateProjection n i sz.2 ∂hierarchyGaussianLaw n m U) =
      a*(1-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
        (∫ z, (hierarchySpinMean n m U c j z)^2
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) else 0) := by
  let μ := hierarchyGaussianLaw n m U
  let := hierarchyGaussian_probability n m U
  have hr (j : Fin (n+1)) := hierarchySpinMean_regular n m U c (by norm_num : (0:ℝ) ≤ 1) hc j
  have hI (j : Fin (n+1)) : Integrable (fun sz => c sz.1*hierarchySpinMean n m U c j sz.2) μ := by
    change Integrable (fun sz => c sz.1*hierarchySpinMean n m U c j sz.2) (hierarchyGaussianLaw n m U)
    apply hierarchyGaussian_integrable n m U (fun s z => c s*hierarchySpinMean n m U c j z)
    · intro s
      exact (HasExpGrowth.const (c s)).mul (HasExpGrowth.of_bounded (by norm_num) (hr j).2)
    · intro s
      exact continuous_const.mul (hr j).1
  have H := spinGaussian_weighted_stein n (hierarchyPotential n m U) (fun s _ => c s)
    (hierarchyPotential_boundedDerivs n m U) (fun _ => contDiff_const)
    (fun s => HasExpGrowth.const (c s)) (fun s => by
      have he : fderiv ℝ (fun _ : ParameterSpace n => c s) = fun _ => 0 := by funext z; exact fderiv_const_apply _
      rw [he]
      exact HasExpGrowth.const (0 : ParameterSpace n →L[ℝ] ℝ)) i
  rw [← hierarchyGaussianLaw_eq_spinGaussian] at H
  simp only [fderiv_const_apply,zero_apply,integral_zero,zero_add] at H
  have he (sz : S × ParameterSpace n) :
      c sz.1*fderiv ℝ (hierarchyPotential n m U sz.1) sz.2 (coordinateAxis n i) =
        a-∑ j : Fin (n+1), if i.val < j.val then
          a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0 := by
    rw [hierarchyPotential_coordinate_gradient n m U c a i hU,mul_sub,Finset.mul_sum]
    have hc2 : c sz.1*(a*c sz.1) = a := by
      calc
        _ = a*(c sz.1)^2 := by ring
        _ = a := by rw [hsq sz.1,mul_one]
    rw [hc2]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hJ (j : Fin (n+1)) : Integrable (fun sz : S × ParameterSpace n =>
      if i.val < j.val then a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0) μ := by
    by_cases h : i.val < j.val
    · simpa only [ite_eq_left h] using ((hI j).const_mul (hierarchyAtom n m 1 j)).const_mul a
    · simp only [ite_eq_right h]; exact integrable_const 0
  calc
    _ = ∫ sz, coordinateProjection n i sz.2*c sz.1 ∂μ := by congr 1; funext sz; ring
    _ = ∫ sz, a-∑ j : Fin (n+1), if i.val < j.val then
        a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0 ∂μ :=
      H.trans (integral_congr_ae (ae_of_all _ he))
    _ = a-∑ j : Fin (n+1), if i.val < j.val then
        a*(hierarchyAtom n m 1 j*(∫ z, (hierarchySpinMean n m U c j z)^2
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) else 0 := by
      rw [integral_sub (integrable_const _) (integrable_finsetSum _ (fun j _ => hJ j)),
        integral_finsetSum _ (fun j _ => hJ j),integral_const]
      simp only [probReal_univ,one_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i.val < j.val
      · simp only [ite_eq_left h,integral_const_mul]
        rw [hierarchySpinMean_terminal_product n m U c (by norm_num) hc j]
      · simp only [ite_eq_right h,integral_zero]
    _ = _ := by
      rw [mul_sub,mul_one,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
end SpinCovarianceVariation
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyParameterDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyParameterDerivative
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_parameterDerivative (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (z : P × ℝ) (v : P) :
    fderiv ℝ (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) z (v,0) =
      hierarchyAverage n m (fun w => f (z.1,w))
        (fun w => fderiv ℝ f (z.1,w) (v,0)) z.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let g := gaussianStep (m (Fin.last n))
      (fun w : (P × ParameterSpace n) × ℝ => f (w.1.1,(w.1.2,w.2)))
    have hg : ParamRegular g := hf.gaussianStep _
    have hrec := ih (fun i => m i.castSucc) g hg
    change fderiv ℝ (fun z : P × ℝ => hierarchyPressure n (fun i => m i.castSucc)
      (fun w => g (z.1,w)) z.2) z (v,0) = _
    rw [hrec]
    have he : (fun w => fderiv ℝ g (z.1,w) (v,0)) = fun w : ParameterSpace n =>
        gaussianAverage (m (Fin.last n)) (fun w => f (z.1,w))
          (fun w => fderiv ℝ f (z.1,w) (v,0)) w := by
      funext w
      exact hf.parameterDerivative_gaussianStep _ (z.1,w) v
    rw [he]
    rfl

theorem parameterFDeriv_at_field {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : P × E → ℝ} (hf : Differentiable ℝ f) (p v : P) (y : E) :
    fderiv ℝ (fun p => f (p,y)) p v = fderiv ℝ f (p,y) (v,0) := by
  have hh : HasFDerivAt (fun a : P => (a,y)) (ContinuousLinearMap.inl ℝ P E) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const y p)
  have h := ((hf (p,y)).hasFDerivAt.comp p hh).fderiv
  change fderiv ℝ (fun p => f (p,y)) p = _ at h
  rw [h]
  rfl

end HierarchyParameterDerivative
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section ParameterHierarchy
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_paramRegular (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) :
    ParamRegular (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ =>
        f (z.1.1,(z.1.2,z.2)))) (hf.gaussianStep (m (Fin.last n)))

end ParameterHierarchy

theorem spinPressure_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (m : Fin d → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ℝ =>
      hierarchyPressure d m (affineLogPartition c (spinExponent d z.1 I)) z.2) :=
  hierarchyPressure_paramRegular d m _ (spinTerminal_paramRegular d I c)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinTerminalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinTerminal_parameterDerivative {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (a v : Fin d → ℝ) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (spinExponent d w.1 I) w.2) (a,z) (v,0) =
      affineMoment c (spinExponent d a I) (fun s => spinExponent d v I s z) z := by
  rw [← parameterFDeriv_at_field ((spinTerminal_paramRegular d I c).1.differentiable (by norm_num))
    a v z]
  let L : Config N → (Fin d → ℝ) →L[ℝ] ℝ :=
    fun s => (spinCoefficientBilinear d I s).flip z
  have he : (fun a : Fin d → ℝ => affineLogPartition c (spinExponent d a I) z) =
      affineLogPartition c L := by
    funext a
    simp only [affineLogPartition,L,ContinuousLinearMap.flip_apply,
      spinCoefficientBilinear_apply]
  rw [he,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,L,ContinuousLinearMap.flip_apply,spinCoefficientBilinear_apply]

theorem spinExponent_single {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (i : Fin d) (s : Config N) (z : ParameterSpace d) :
    spinExponent d (Pi.single i 1) I s z = spinMonomial s (I i)*coordinateProjection d i z := by
  classical
  simp [spinExponent,coordinateLinear_apply,Pi.single_apply]

theorem spinTerminal_parameterDerivative_single {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (i : Fin d) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition (fun _ => 0) (spinExponent d w.1 I) w.2) (a,z) (Pi.single i 1,0) =
      affineMoment (fun _ => 0) (spinExponent d a I) (fun s => spinMonomial s (I i)) z *
        coordinateProjection d i z := by
  rw [spinTerminal_parameterDerivative]
  simp only [spinExponent_single,affineMoment,Finset.sum_mul,mul_assoc]

theorem spinPressure_parameterDerivative_single {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) a
      (Pi.single i 1) =
      ∫ sz, spinMonomial sz.1 (I i)*coordinateProjection d i sz.2
        ∂hierarchyGaussianLaw d m (spinExponent d a I) := by
  rw [parameterFDeriv_at_field ((spinPressure_paramRegular d I (fun _ => 0) m).1.differentiable (by norm_num)),
    hierarchyPressure_parameterDerivative d m _ (spinTerminal_paramRegular d I (fun _ => 0))]
  simp only [spinTerminal_parameterDerivative_single]
  rw [hierarchyAverage_eq_integral_exp d m _
    (affineLogPartition_boundedDerivs (fun _ => 0) (spinExponent d a I))]
  · exact (hierarchyGaussian_terminal_marginal d m (spinExponent d a I)
      (fun s => spinMonomial s (I i)) (coordinateProjection d i)
      (coordinateProjection d i).continuous (HasExpGrowth.linear _)).symm
  · exact (affineMoment_continuous _ _ _).mul (coordinateProjection d i).continuous
  · exact (HasExpGrowth.of_bounded (by norm_num : (0:ℝ) ≤ 1)
      (affineMoment_norm_le _ _ _ (fun s => by
        rw [Real.norm_eq_abs]
        exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith [spinMonomial_sq s (I i)])))).mul (HasExpGrowth.linear _)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinCoefficientVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinPressure_coefficient_variation {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) a
      (Pi.single i 1) =
      a i*(1-∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j *
        (∫ z, (hierarchySpinMean d m (spinExponent d a I) (fun s => spinMonomial s (I i)) j z)^2
          ∂hierarchyPathLaw d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) else 0) := by
  rw [spinPressure_parameterDerivative_single]
  apply hierarchyGaussian_coordinate_spin d m (spinExponent d a I) (fun s => spinMonomial s (I i)) (a i) i
  · intro s
    simp only [spinExponent,coordinateLinear_coordinateAxis]
  · intro s
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith [spinMonomial_sq s (I i)])
  · intro s
    exact spinMonomial_sq s (I i)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockDerivativeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockAtom_sum_mul (D N k : ℕ) (f : Fin (blockDimension D N k+1) → ℝ) :
    (∑ j, hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*f j) =
      ∑ b : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*f (blockLevel D N k b) := by
  simp only [hierarchyAtom_blockMass,blockAtom,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem fieldIndex_lt_blockLevel_iff (D N k : ℕ) (b l : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val < (blockLevel D N k l).val ↔ b ≤ l := by
  simp only [fieldIndex_val,blockLevel_val,Fin.le_def]
  constructor
  · intro h
    by_contra hn
    have hbl : l.val+1 ≤ b.val := by omega
    have hmul := Nat.mul_le_mul_right N hbl
    omega
  · intro h
    have hmul := Nat.mul_le_mul_right N h
    nlinarith [i.isLt]

theorem blockPressure_coordinate_variation {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (Pi.single (fieldIndex D N k b i) 1) =
      v b * (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹ *
        (∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
          (fun s => spin (s i)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k)
            (affineLogPartition (fun _ => 0) (blockExponent I a v)) 0) else 0) := by
  rw [spinPressure_coefficient_variation,blockCoefficients_field,blockInteraction_field]
  simp only [spinMonomial,Finset.prod_singleton]
  congr 2
  have he (j : Fin (blockDimension D N k+1)) (c : ℝ) :
      (if (fieldIndex D N k b i).val < j.val then
        hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*c else 0) =
      hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j *
        (if (fieldIndex D N k b i).val < j.val then c else 0) := by split_ifs <;> simp
  simp_rw [he]
  rw [blockAtom_sum_mul]
  simp only [fieldIndex_lt_blockLevel_iff,mul_ite,mul_zero]
  rfl
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockDisorderDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem disorderIndex_lt_blockLevel (D N k : ℕ) (i : Fin D) (l : Fin (k+1)) :
    (Fin.castAdd ((k+1)*N) i).val < (blockLevel D N k l).val := by
  rw [blockLevel_val]
  simp only [Fin.val_castAdd]
  omega

theorem blockPressure_disorder_coordinate {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) (i : Fin D) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (Pi.single (Fin.castAdd ((k+1)*N) i) 1) =
      a i * (1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
        (∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
          (fun s => spinMonomial s (I i)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k)
            (affineLogPartition (fun _ => 0) (blockExponent I a v)) 0)) := by
  rw [spinPressure_coefficient_variation]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left]
  congr 2
  have he (j : Fin (blockDimension D N k+1)) (c : ℝ) :
      (if (Fin.castAdd ((k+1)*N) i).val < j.val then
        hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*c else 0) =
      hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j *
        (if (Fin.castAdd ((k+1)*N) i).val < j.val then c else 0) := by split_ifs <;> simp
  simp_rw [he]
  rw [blockAtom_sum_mul]
  simp only [disorderIndex_lt_blockLevel,ite_true]
  rfl
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockFieldDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem linearMap_blockCoefficients {D N k : ℕ}
    (L : (Fin (blockDimension D N k) → ℝ) →L[ℝ] ℝ) (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    L (blockCoefficients (N := N) a v) =
      (∑ i : Fin D, a i*L (Pi.single (Fin.castAdd ((k+1)*N) i) 1))+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*L (Pi.single (fieldIndex D N k b i) 1) := by
  conv_lhs => rw [pi_eq_sum_univ' (blockCoefficients (N := N) a v)]
  rw [map_sum,Fin.sum_univ_add]
  simp only [map_smul,smul_eq_mul,blockCoefficients,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*L (Pi.single (Fin.natAdd D t) 1))]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,fieldIndex_eq_natAdd]

theorem field_derivative_sum {N k : ℕ} (hN : 0 < N) (E : Fin N → Fin (k+1) → ℝ)
    (v w : Fin (k+1) → ℝ) :
    (∑ b, ∑ i : Fin N, w b*(v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*E i l else 0))) =
    (N:ℝ)*∑ b, w b*v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*((∑ i, E i l)/(N:ℝ)) else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : b ≤ l
  · simp only [h,ite_true]
    simp only [← Finset.mul_sum]
    field_simp
  · simp only [h,ite_false,mul_zero,Finset.sum_const_zero]

theorem blockPressure_field_differential {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ) (v w : Fin (k+1) → ℝ) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (blockCoefficients (N := N) (fun _ => 0) w) =
    (N:ℝ)*∑ b, w b*v b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
        (fun i s => spin (s i)) (blockLevel D N k l) else 0) := by
  rw [linearMap_blockCoefficients]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,blockPressure_coordinate_variation]
  simp only [hierarchyMeanOverlap_eq_mean_integrals (blockDimension D N k) (blockMass D N k) (blockExponent I a v) (fun i s => spin (s i)) (fun i s => by cases s i <;> norm_num [spin])]
  exact field_derivative_sum hN _ v w

theorem blockCoefficients_hasDerivAt {D N k : ℕ} {a : ℝ → Fin D → ℝ}
    {v : ℝ → Fin (k+1) → ℝ} {a' : Fin D → ℝ} {v' : Fin (k+1) → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun u => blockCoefficients (N := N) (a u) (v u)) (blockCoefficients a' v') t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [blockCoefficients,Fin.addCases_left] using hasDerivAt_pi.mp ha j
  · simpa only [blockCoefficients,Fin.addCases_right] using hasDerivAt_pi.mp hv (finProdFinEquiv.symm j).1
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaVarianceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section ReplicaVarianceSplit
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_const (p : S → ℝ) (hp : ∑ s, p s = 1) (c : ℝ) :
    finiteReplicaMoment p (fun _ _ => c) = c := by
  simp only [finiteReplicaMoment,← Finset.mul_sum,← Finset.sum_mul,hp,mul_one,one_mul]

theorem finiteReplicaMoment_add (p : S → ℝ) (g h : S → S → ℝ) :
    finiteReplicaMoment p (fun s t => g s t+h s t) = finiteReplicaMoment p g+finiteReplicaMoment p h := by
  simp only [finiteReplicaMoment,mul_add,Finset.sum_add_distrib]

theorem finiteReplicaMoment_const_mul (p : S → ℝ) (g : S → S → ℝ) (c : ℝ) :
    finiteReplicaMoment p (fun s t => c*g s t) = c*finiteReplicaMoment p g := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

end ReplicaVarianceSplit
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section FiniteReplicaBounds
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_mono (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g h : S → S → ℝ)
    (hgh : ∀ s t, g s t ≤ h s t) : finiteReplicaMoment p g ≤ finiteReplicaMoment p h := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (hgh s t) (mul_nonneg (hp s) (hp t))

theorem finiteReplicaMoment_nonneg (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g : S → S → ℝ)
    (hg : ∀ s t, 0 ≤ g s t) : 0 ≤ finiteReplicaMoment p g :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => mul_nonneg (mul_nonneg (hp s) (hp t)) (hg s t)

theorem finiteReplicaMoment_le_const (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (g : S → S → ℝ) (C : ℝ) (hg : ∀ s t, g s t ≤ C) : finiteReplicaMoment p g ≤ C := by
  exact (finiteReplicaMoment_mono p hp g (fun _ _ => C) hg).trans_eq (finiteReplicaMoment_const p hs C)

theorem finiteReplicaMoment_continuous {Ω : Type} [TopologicalSpace Ω]
    (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (g : S → S → ℝ) :
    Continuous (fun z => finiteReplicaMoment (P z) g) := by
  exact continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => ((hP s).mul (hP t)).mul continuous_const))
end FiniteReplicaBounds

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplicaSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SecondMoment
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyReplicaSecond_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t))^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (finiteReplicaMoment_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) _) (C := 1) _ 0
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _))]
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have H := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have H0 := abs_nonneg (normalizedDot (v s) (v t))
  nlinarith [sq_abs (normalizedDot (v s) (v t))]

end SecondMoment
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaEdgeIdentity
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

section FiniteReplicaAlgebra
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_separable_square (p c : S → ℝ) :
    finiteReplicaMoment p (fun s t => c s*c t) = (∑ s, p s*c s)^2 := by
  simp only [finiteReplicaMoment,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem finiteReplicaMoment_sum {I : Type} [Fintype I] (p : S → ℝ) (g : I → S → S → ℝ) :
    finiteReplicaMoment p (fun s t => ∑ i, g i s t) = ∑ i, finiteReplicaMoment p (g i) := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  calc
    _ = ∑ s, ∑ i, ∑ t, p s*p t*g i s t := by
      apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]
end FiniteReplicaAlgebra

theorem replica_edge_polynomial {N : ℕ} (hN : 0 < N) (s t : Config N) :
    2*(∑ e : Edge N, (spin (s e.val.1)*spin (s e.val.2))*(spin (t e.val.1)*spin (t e.val.2))) =
      (N:ℝ)^2*(normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2-N := by
  have H := sum_sq_eq_edges (fun i => spin (s i)*spin (t i))
  have hd : (∑ i : Fin N, (spin (s i)*spin (t i))^2) = (N:ℝ) := by simp [mul_pow]
  rw [hd] at H
  have he : (∑ e : Edge N, (spin (s e.val.1)*spin (s e.val.2))*(spin (t e.val.1)*spin (t e.val.2))) =
      ∑ e : Edge N, (spin (s e.val.1)*spin (t e.val.1))*(spin (s e.val.2)*spin (t e.val.2)) := by
    apply Finset.sum_congr rfl; intro e _; ring
  rw [he]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold normalizedDot
  field_simp
  simp only [mul_assoc] at H ⊢
  nlinarith [H]

theorem finiteReplica_edge_variation {N : ℕ} (hN : 0 < N) (p : Config N → ℝ)
    (hp : ∑ s, p s = 1) :
    2*(∑ e : Edge N, (1-(∑ s, p s*(spin (s e.val.1)*spin (s e.val.2)))^2)) =
      (N:ℝ)^2*(1-finiteReplicaMoment p (fun s t =>
        (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)) := by
  have hc := sum_sq_eq_edges (fun _ : Fin N => (1:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_pow] at hc
  have H := congrArg (finiteReplicaMoment p) (funext fun s => funext fun t => replica_edge_polynomial hN s t)
  rw [finiteReplicaMoment_const_mul,finiteReplicaMoment_sum] at H
  simp_rw [finiteReplicaMoment_separable_square] at H
  have hr : finiteReplicaMoment p (fun s t => (N:ℝ)^2 *
      (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2-N) =
      (N:ℝ)^2*finiteReplicaMoment p (fun s t =>
        (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)-N := by
    simp only [sub_eq_add_neg,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,
      finiteReplicaMoment_const p hp]
  rw [hr] at H
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyEdgeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchySpinMean_square_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ)
    (hc : ∀ s, ‖c s‖ ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => (hierarchySpinMean n m U c j z)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  have hr := hierarchySpinMean_regular n m U c (by norm_num : (0:ℝ) ≤ 1) hc j
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hr.1.pow 2) (C := 1) _ 0
  intro z
  dsimp only [Pi.pow_apply]
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hr.2 z)

theorem hierarchy_edge_variation {N : ℕ} (hN : 0 < N)
    (n : ℕ) (m : Fin n → ℝ) (U : Config N → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) :
    2*(∑ e : Edge N, (1-∫ z, (hierarchySpinMean n m U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) =
      (N:ℝ)^2*(1-hierarchyReplicaSecond n m U (fun s i => spin (s i)) j) := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hi (e : Edge N) : Integrable (fun z => (hierarchySpinMean n m U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2) μ := by
    exact hierarchySpinMean_square_integrable n m U _ (fun s => by cases s e.val.1 <;> cases s e.val.2 <;> norm_num [spin]) j
  have hs := hierarchyReplicaSecond_integrable n m U (fun s i => spin (s i))
    (fun s i => by cases s i <;> norm_num [spin]) j
  calc
    _ = ∫ z, 2*(∑ e : Edge N, (1-(hierarchySpinMean n m U
        (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2)) ∂μ := by
      rw [integral_const_mul,integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [integral_sub (integrable_const 1) (hi e)]
        simp [μ]
      · intro e _
        exact (integrable_const 1).sub (hi e)
    _ = ∫ z, (N:ℝ)^2*(1-finiteReplicaMoment (hierarchySpinWeight n m U j z)
        (fun s t => (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [hierarchySpinMean_eq_sum]
        exact finiteReplica_edge_variation hN _ (hierarchySpinWeight_sum n m U j z)
    _ = _ := by
      rw [integral_const_mul,integral_sub (integrable_const 1) hs]
      simp [hierarchyReplicaSecond]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKBlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem spinMonomial_skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) (s : Config N) :
    spinMonomial s (skInteraction N i) =
      spin (s ((Fintype.equivFin (Edge N)).symm i).val.1)*
        spin (s ((Fintype.equivFin (Edge N)).symm i).val.2) := by
  exact Finset.prod_pair (ne_of_lt (((Fintype.equivFin (Edge N)).symm i).property))

theorem weighted_complement_sum {I J : Type} [Fintype I] [Fintype J]
    (w : J → ℝ) (hw : ∑ j, w j = 1) (E : I → J → ℝ) :
    (∑ i, (1-∑ j, w j*E i j)) = ∑ j, w j*∑ i, (1-E i j) := by
  calc
    _ = ∑ i, ∑ j, w j*(1-E i j) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hw]
    _ = ∑ j, ∑ i, w j*(1-E i j) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

theorem blockCoefficients_add_split {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    blockCoefficients (N := N) a v =
      blockCoefficients (fun _ : Fin D => 0) v+blockCoefficients a (fun _ : Fin (k+1) => 0) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [blockCoefficients]
  · simp [blockCoefficients]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKHamiltonianDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlock_disorder_differential {N k : ℕ} (hN : 0 < N)
    (h h' : ℝ) (v : Fin (k+1) → ℝ) :
    let D := Fintype.card (Edge N)
    let n := blockDimension D N k
    let a : Fin D → ℝ := fun _ => h/Real.sqrt (N:ℝ)
    let U := blockExponent (skInteraction N) a v
    fderiv ℝ (fun c : Fin n → ℝ => hierarchyPressure n (blockMass D N k)
      (affineLogPartition (fun _ => 0) (spinExponent n c (blockInteraction (skInteraction N)))) 0)
      (blockCoefficients a v) (blockCoefficients (N := N) (fun _ : Fin D => h'/Real.sqrt (N:ℝ)) (fun _ : Fin (k+1) => 0)) =
      (N:ℝ)*(h*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
        hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l)) := by
  dsimp only
  let D := Fintype.card (Edge N)
  let n := blockDimension D N k
  let a : Fin D → ℝ := fun _ => h/Real.sqrt (N:ℝ)
  let U := blockExponent (skInteraction N) a v
  let E := fun i : Fin D => fun l : Fin (k+1) =>
    ∫ z, (hierarchySpinMean n (blockMass D N k) U (fun s => spinMonomial s (skInteraction N i))
      (blockLevel D N k l) z)^2 ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0
  let S := fun l : Fin (k+1) => hierarchyReplicaSecond n (blockMass D N k) U
    (fun s i => spin (s i)) (blockLevel D N k l)
  have hE (l : Fin (k+1)) : (∑ i : Fin D, (1-E i l)) = (N:ℝ)^2/2*(1-S l) := by
    have H := hierarchy_edge_variation hN n (blockMass D N k) U (blockLevel D N k l)
    have he : (∑ i : Fin D, (1-E i l)) = ∑ e : Edge N, (1-∫ z, (hierarchySpinMean n (blockMass D N k) U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) (blockLevel D N k l) z)^2
        ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0) := by
      dsimp only [E]
      simp only [spinMonomial_skInteraction]
      exact (Fintype.equivFin (Edge N)).symm.sum_comp (fun e : Edge N => (1-∫ z, (hierarchySpinMean n (blockMass D N k) U
        (fun s => spin (s e.val.1)*spin (s e.val.2)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw n (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0))
    rw [he]
    dsimp only [S]
    linarith [H]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have sqN := Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)
  have ha : h'/Real.sqrt (N:ℝ)*(h/Real.sqrt (N:ℝ)) = h*h'/(N:ℝ) := by
    rw [div_mul_div_comm,← pow_two,sqN]
    ring
  rw [linearMap_blockCoefficients]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,blockPressure_disorder_coordinate]
  change (∑ i : Fin D, h'/Real.sqrt (N:ℝ)*(h/Real.sqrt (N:ℝ)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*E i l))) =
    (N:ℝ)*(h*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*S l)
  simp only [← mul_assoc,ha]
  rw [← Finset.mul_sum,weighted_complement_sum _ (uniformAtom_sum k)]
  simp_rw [hE]
  have he : (∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*((N:ℝ)^2/2*(1-S l))) =
      (N:ℝ)^2/2*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*S l) := by
    rw [mul_sub,mul_one,Finset.mul_sum]
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [← Finset.sum_mul,uniformAtom_sum,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  field_simp
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKPressureCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockPressure_hasDerivAt_oai {N k : ℕ} (hN : 0 < N)
    (h : ℝ → ℝ) (v : ℝ → Fin (k+1) → ℝ) {t h' : ℝ} {v' : Fin (k+1) → ℝ}
    (hh : HasDerivAt h h' t) (hv : HasDerivAt v v' t) :
    let D := Fintype.card (Edge N)
    let n := blockDimension D N k
    let U := blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
    HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
      ((h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
        hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l))+
      ∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
        hierarchyMeanOverlap n (blockMass D N k) U (fun i s => spin (s i)) (blockLevel D N k l) else 0)) t := by
  dsimp only
  let D := Fintype.card (Edge N)
  let n := blockDimension D N k
  let a := fun u => fun _ : Fin D => h u/Real.sqrt (N:ℝ)
  let a' : Fin D → ℝ := fun _ => h'/Real.sqrt (N:ℝ)
  let P := fun c : Fin n → ℝ => hierarchyPressure n (blockMass D N k)
    (affineLogPartition (fun _ => 0) (spinExponent n c (blockInteraction (skInteraction N)))) 0
  have hd : Differentiable ℝ P :=
    (parameter_contDiff_at_field (spinPressure_paramRegular n (blockInteraction (skInteraction N))
      (fun _ => 0) (blockMass D N k)).1 (0:ℝ)).differentiable (by norm_num)
  have ha : HasDerivAt a a' t := hasDerivAt_pi.mpr (fun _ => hh.div_const _)
  have hc := blockCoefficients_hasDerivAt (N := N) ha hv
  have H := ((hd (blockCoefficients (a t) (v t))).hasFDerivAt.comp_hasDerivAt t hc).div_const (N:ℝ)
  change HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
    (fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients a' v')/(N:ℝ)) t at H
  apply H.congr_deriv
  rw [blockCoefficients_add_split a' v',map_add]
  rw [show fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients (fun _ : Fin D => 0) v') =
    (N:ℝ)*∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap n (blockMass D N k) (blockExponent (skInteraction N) (a t) (v t))
        (fun i s => spin (s i)) (blockLevel D N k l) else 0) from
    blockPressure_field_differential hN (skInteraction N) (a t) (v t) v']
  rw [show fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients a' (fun _ : Fin (k+1) => 0)) =
    (N:ℝ)*(h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
      hierarchyReplicaSecond n (blockMass D N k) (blockExponent (skInteraction N) (a t) (v t))
        (fun s i => spin (s i)) (blockLevel D N k l)) from
    skBlock_disorder_differential hN (h t) h' (v t)]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [a,D,n]
  field_simp
  ring
end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.skBlockPressure_hasDerivAt_oai := @OAI.SK.Analytic.skBlockPressure_hasDerivAt_oai
