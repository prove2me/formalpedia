-- Prove2me | solution 1 for OAI.SK.Analytic.tripleConstrainedPressure_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:21:08.947019+00:00
-- url     : https://prove2.me/submissions/07b19a45-308a-467d-81be-fba1a97327a8

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S005
import Definitions.Def_OAIQ036S006
import Theorems.Thm_OAI_SK_Analytic_tripleConstrainedPressure_schedule
import Theorems.Thm_OAI_SK_Analytic_tripleSchedule_value_expansion

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateSigns
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

theorem scalarSign_gaussian (b : Bool) :
    MeasurePreserving (scalarSign b) (gaussianReal 0 1) (gaussianReal 0 1) := by
  refine ⟨(scalarSign_continuous b).measurable, ?_⟩
  cases b
  · simp only [scalarSign_false,Measure.map_id]
  · simpa only [scalarSign_true,neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianResponse
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

theorem HasExpGrowth.integrable_tilted_fiberGaussian {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (V : ParameterSpace n → ℝ) (hV : BoundedDerivs V)
    {g : ParameterSpace n → F} (hg : HasExpGrowth g) (hc : Continuous g) (x : ℝ) :
    Integrable g ((fiberGaussian n x).tilted V) := by
  have he : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  have hce := Real.continuous_exp.comp hV.1.continuous
  rw [integrable_tilted_iff (he.integrable_fiberGaussian n hce x)]
  exact (he.smul hg).integrable_fiberGaussian n (hce.smul hc) x

theorem fiberGaussian_tilted_probability (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) : IsProbabilityMeasure ((fiberGaussian n x).tilted V) := by
  apply isProbabilityMeasure_tilted
  have he : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  exact he.integrable_fiberGaussian n (Real.continuous_exp.comp hV.1.continuous) x

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeBlockLaw
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

theorem parameter_ae_fiberGaussian (n : ℕ) (x : ℝ) :
    ∀ᵐ z ∂fiberGaussian n x, parameter n z = x := by
  induction n with
  | zero => simp [fiberGaussian,parameter]
  | succ n ih =>
    change ∀ᵐ z ∂(fiberGaussian n x).prod (gaussianReal 0 1), parameter n z.1 = x
    exact Measure.quasiMeasurePreserving_fst.ae ih

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootHessian_continuous (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) :
    Continuous (rootHessian n f) :=
  ((hf.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const |>.clm_apply continuous_const

end SK.Analytic

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
section Cauchy
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem abs_integral_mul_le_sqrt (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ z, f z*g z ∂μ| ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*Real.sqrt (∫ z, (g z)^2 ∂μ) := by
  have H := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow] at H
  calc
    |∫ z, f z*g z ∂μ| = ‖∫ z, f z*g z ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖f z*g z‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ z, |f z| * |g z| ∂μ := by simp only [norm_mul,Real.norm_eq_abs]
    _ ≤ _ := H

theorem abs_integral_mul_le_sqrt_of_bound [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ᵐ z ∂μ, |g z| ≤ 1) :
    |∫ z, f z*g z ∂μ| ≤ Real.sqrt (∫ z, (f z)^2 ∂μ) := by
  have hg₂ : MemLp g 2 μ := (memLp_const (1 : ℝ)).mono' hg hb
  have hsq : (∫ z, (g z)^2 ∂μ) ≤ 1 := by
    calc
      (∫ z, (g z)^2 ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hg₂.integrable_sq (integrable_const 1)
        filter_upwards [hb] with z hz
        nlinarith [abs_nonneg (g z),sq_abs (g z)]
      _ = 1 := by simp
  calc
    _ ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*Real.sqrt (∫ z, (g z)^2 ∂μ) :=
      abs_integral_mul_le_sqrt f g hf hg₂
    _ ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*1 :=
      mul_le_mul_of_nonneg_left (by simpa using Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

end Cauchy
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

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarHierarchy_lipschitz (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hLip : LipschitzWith K f) :
    LipschitzWith K (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hLip
  | succ n ih =>
    exact ih _ _ (fun i => hm i.castSucc) (scalarStep_regular hf _ _)
      (scalarStep_lipschitz hf hLip (hm _) _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterMomentSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarMomentSquare_eq_parameterAverage (n : ℕ) (m v : Fin n → ℝ)
    (F H : ℝ → ℝ → ℝ) (x a : ℝ)
    (hf : BoundedDerivs (scalarParameterTerminal n v F x)) (j : Fin (n+1)) :
    scalarMomentSquare n m v (F a) (H a) j x =
      hierarchyAverage n m (scalarParameterTerminal n v F x)
        (fun z => (hierarchyMomentLevel n m (scalarParameterTerminal n v F x)
          (scalarParameterTerminal n v H x) j z)^2) a := by
  induction n generalizing F H with
  | zero => simp [scalarMomentSquare,hierarchyAverage,hierarchyMomentLevel,
      scalarParameterTerminal,coordinateLinear,parameter]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last,hierarchyMomentLevel]
      exact (hierarchyAverage_scalarParameterTerminal (n+1) m v F
        (fun a x => (H a x)^2) x a).symm
    · simp only [scalarMomentSquare,hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf (m (Fin.last n)) (fun z =>
        (hierarchyMomentLevel n (fun i => m i.castSucc)
          (gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x))
          (gaussianAverage (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x)
            (scalarParameterTerminal (n+1) v H x)) j z)^2)]
      simp only [gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
      have hf' := hf.gaussianStep (m (Fin.last n))
      rw [gaussianStep_scalarParameterTerminal] at hf'
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun a => scalarStep (m (Fin.last n)) (v (Fin.last n)) (F a))
        (fun a => scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) (F a) (H a)) hf' j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_AffineMomentCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem affineMoment_const_mul (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (a : ℝ) :
    affineMoment c U (fun s => a*g s) = fun x => a*affineMoment c U g x := by
  funext x
  simp only [affineMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem affineMoment_contDiff (c : S → ℝ) (U : S → E →L[ℝ] ℝ) (g : S → ℝ) :
    ContDiff ℝ 1 (affineMoment c U g) := by
  unfold affineMoment affineGibbs
  apply ContDiff.sum
  intro s _
  exact (((contDiff_const.add (U s).contDiff).exp).div
    (ContDiff.sum (fun t _ => (contDiff_const.add (U t).contDiff).exp))
    (fun x => (affinePartition_pos c U x).ne')).mul contDiff_const

theorem fderiv_affineMoment_apply (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (x u : E) :
    fderiv ℝ (affineMoment c U g) x u =
      affineMoment c U (fun s => g s*U s u) x -
        affineMoment c U g x*affineMoment c U (fun s => U s u) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+U s x)
  let K : E → ℝ := fun x => ∑ s, Real.exp (c s+U s x)*g s
  have hz : HasFDerivAt Z (∑ s, Real.exp (c s+U s x) • U s) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using ((hasFDerivAt_const (c s) x).fun_add (U s).hasFDerivAt).exp
  have hk : HasFDerivAt K (∑ s, g s • (Real.exp (c s+U s x) • U s)) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using (((hasFDerivAt_const (c s) x).fun_add (U s).hasFDerivAt).exp).mul_const (g s)
  have he : affineMoment c U g = fun x => K x / Z x := by
    ext x
    simp only [affineMoment,affineGibbs,K,Z,Finset.sum_div,mul_div_assoc]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hi : HasFDerivAt (fun y => (Z y)⁻¹)
      (-(Z x ^ 2)⁻¹ • (∑ s, Real.exp (c s+U s x) • U s)) x := by
    convert (hasDerivAt_inv (affinePartition_pos c U x).ne').comp_hasFDerivAt x hz using 1
    all_goals try with_reducible_and_instances rfl
    all_goals rfl
  have hq := hk.fun_mul hi
  rw [he]
  simp only [div_eq_mul_inv]
  rw [hq.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,sum_apply]
  have hZ : Z x ≠ 0 := (affinePartition_pos c U x).ne'
  have h1 : affineMoment c U (fun s => g s*U s u) x =
      (∑ s, g s*(Real.exp (c s+U s x)*U s u))/Z x := by
    simp only [affineMoment,affineGibbs,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    change _ = _ / Z x
    dsimp only [Z]
    ring
  have h2 : affineMoment c U (fun s => U s u) x =
      (∑ s, Real.exp (c s+U s x)*U s u)/Z x := by
    simp only [affineMoment,affineGibbs,Z,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h1,h2]
  change _ = _ - K x / Z x * _
  field_simp
  ring

theorem affineMoment_fderiv_bounded (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (affineMoment c U g) x‖ ≤ C := by
  classical
  let B := ∑ s, ‖g s‖
  let M := ∑ s, ‖U s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb (s : S) : ‖g s‖ ≤ B := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hm (s : S) : ‖U s‖ ≤ M := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  refine ⟨2*B*M,by positivity,fun x => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)⟩
  rw [fderiv_affineMoment_apply]
  have Hu : ∀ s, ‖U s u‖ ≤ M*‖u‖ := fun s =>
    ((U s).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hm s) (norm_nonneg _))
  have HgU : ∀ s, ‖g s*U s u‖ ≤ B*(M*‖u‖) := fun s => by
    rw [norm_mul]
    exact mul_le_mul (hb s) (Hu s) (norm_nonneg _) hB
  calc
    _ ≤ ‖affineMoment c U (fun s => g s*U s u) x‖ +
        ‖affineMoment c U g x*affineMoment c U (fun s => U s u) x‖ := norm_sub_le _ _
    _ ≤ B*(M*‖u‖)+B*(M*‖u‖) := add_le_add (affineMoment_norm_le c U _ HgU x)
      (by
        rw [norm_mul]
        exact mul_le_mul (affineMoment_norm_le c U g hb x)
          (affineMoment_norm_le c U _ Hu x) (norm_nonneg _) hB)
    _ = _ := by ring

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ExponentialPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_exp_regular (n : ℕ) (m : Fin n → ℝ)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hG : HasExpGrowth g) (j : Fin (n+1)) :
    Continuous (hierarchyMomentLevel n m f g j) ∧
      HasExpGrowth (hierarchyMomentLevel n m f g j) := by
  induction n with
  | zero => exact ⟨hg,hG⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using And.intro hg hG
    · have H := ih (fun i => m i.castSucc) (hf.gaussianStep (m (Fin.last n)))
        (gaussianAverage_continuous_of_expGrowth hf (m (Fin.last n)) hG hg)
        (gaussianAverage_expGrowth hf (m (Fin.last n)) hG) j
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      refine ⟨H.1.comp continuous_fst,?_⟩
      obtain ⟨C,M,hC,hM,hb⟩ := H.2
      refine ⟨C,M,hC,hM,fun z => (hb z.1).trans ?_⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (norm_fst_le z) hM)) hC

theorem hierarchyPathLaw_prefix_mul_exp (n : ℕ) (m : Fin n → ℝ)
    {f g h : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hG : HasExpGrowth g) (hH : HasExpGrowth h)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f h j z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have G := hierarchyMomentLevel_exp_regular n m hf hg hG j
  have H := hierarchyMomentLevel_exp_regular n m hf hh hH j
  rw [← hierarchyAverage_eq_integral_exp n m f hf (fun z => hierarchyMomentLevel n m f h j z*g z) (H.1.mul hg) (H.2.mul hG),
    ← hierarchyAverage_eq_integral_exp n m f hf (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) (H.1.mul G.1) (H.2.mul G.2)]
  exact hierarchyAverage_prefix_mul n m f g h hf j x

theorem hierarchyPathLaw_fixed_mul_exp (n : ℕ) (m : Fin n → ℝ)
    {f g h : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hG : HasExpGrowth g) (hH : HasExpGrowth h)
    (j : Fin (n+1)) (hj : hierarchyMomentLevel n m f h j=h) (x : ℝ) :
    (∫ z, h z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, h z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have H := hierarchyPathLaw_prefix_mul_exp n m hf hg hh hG hH j x
  rwa [hj] at H

theorem hierarchyMomentLevel_coordinate_fixed (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (i : Fin n) (j : Fin (n+1))
    (hij : i.val < j.val) :
    hierarchyMomentLevel n m f (coordinateProjection n i) j=coordinateProjection n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hij
    refine Fin.lastCases (fun _ => ?_) (fun j hij => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hij
      refine Fin.lastCases (fun hij => ?_) (fun i hij => ?_) i
      · simp only [Fin.val_last,Fin.val_castSucc] at hij
        omega
      · have he : (coordinateProjection (n+1) i.castSucc : ParameterSpace (n+1) → ℝ)=
            fun z => coordinateProjection n i z.1 := by funext z; exact coordinateProjection_castSucc n i z
        rw [he]
        simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf,ih (fun i => m i.castSucc) (hf.gaussianStep _) i j hij]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianQuadraticIBP
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

theorem coordinateLinear_coordinateVector (n : ℕ) (a : Fin n → ℝ) :
    coordinateLinear n a (coordinateVector n a) = ∑ i, (a i)^2 := by
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    coordinateProjection_coordinateAxis,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,pow_two]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedHierarchyCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_integral_tilt (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) :
    (∫ z, g z ∂hierarchyPathLaw n m f x) =
      ∫ z, g z ∂(fiberGaussian n x).tilted (fun z => f z-hierarchyPenalty n m 1 f z) := by
  rw [integral_tilted_real_eq_div]
  have he : (fun z => Real.exp (f z-hierarchyPenalty n m 1 f z)) = hierarchyPathWeight n m f := by
    funext z
    simpa only [one_mul] using (hierarchyPathWeight_eq n m f 1 z).symm
  rw [he,(hierarchyPathWeight_normalized n m f hf x).2,div_one,hierarchyPathLaw_integral n m f hf]
  congr 1
  funext z
  rw [show Real.exp (f z-hierarchyPenalty n m 1 f z) = hierarchyPathWeight n m f z from congrFun he z]
  ring

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyLevel_affine_coordinate (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition c U) j) z (coordinateAxis n i) =
      if i.val < j.val then a*hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z else 0 := by
  have hf := affineLogPartition_boundedDerivs c U
  split_ifs with h
  · rw [hierarchyLevel_gradient n m _ hf j _ z (tailZero_coordinateAxis n i j h)]
    have he : directionalGradient (affineLogPartition c U) (coordinateAxis n i) =
        fun z => a*affineMoment c U g z := by
      funext z
      simp only [directionalGradient,fderiv_affineLogPartition_apply,hU,affineMoment_const_mul]
    rw [he,hierarchyMomentLevel_const_mul]
  · exact (hierarchyLevel_invariant_of_prefix n m _ _ j
      (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m _ hf j).1.differentiable (by norm_num)) z

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyScoreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ s, |U s (coordinateAxis n i)| ≤ C)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m (affineLogPartition c U) j) z (coordinateAxis n i)| ≤ C := by
  have H := hierarchyLevel_affine_coordinate n m c U (fun s => U s (coordinateAxis n i)) 1 i
    (fun s => by simp) j z
  rw [H]
  split_ifs
  · simp only [one_mul]
    have Hb := affineMoment_norm_le c U (fun s => U s (coordinateAxis n i))
      (fun s => by simpa only [Real.norm_eq_abs] using hU s)
    simpa only [Real.norm_eq_abs] using
      (hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs c U)
        (affineMoment_contDiff c U _).continuous hC Hb j).2 z
  · simpa using hC

theorem hierarchyPathLogDensity_regular (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) : BoundedDerivs (hierarchyPathLogDensity n m f) := by
  convert hf.add ((hierarchyPenalty_boundedDerivs n m 1 f hf).const_mul (-1)) using 1
  all_goals try with_reducible_and_instances rfl
  funext z; dsimp only [hierarchyPathLogDensity]; ring

theorem affineHierarchy_score_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ s, |U s (coordinateAxis n i)| ≤ C)
    (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateAxis n i)| ≤ 2*C := by
  let f := affineLogPartition c U
  have hf := affineLogPartition_boundedDerivs c U
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hw (j) : 0 ≤ hierarchyAtom n m 1 j :=
    hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hl (j) := affineHierarchy_coordinate_bound n m c U i hC hU j z
  have hpB : |fderiv ℝ (hierarchyPenalty n m 1 f) z (coordinateAxis n i)| ≤ C := by
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    calc
      _ ≤ ∑ j, |hierarchyAtom n m 1 j*fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, hierarchyAtom n m 1 j*C := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hl j) (hw j)
      _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have hfB : |fderiv ℝ f z (coordinateAxis n i)| ≤ C := by
    have H := hl (Fin.last n)
    have he : hierarchyLevel n m f (Fin.last n)=f := by
      cases n with
      | zero => rfl
      | succ n => simp only [hierarchyLevel,Fin.lastCases_last]
    change |fderiv ℝ (hierarchyLevel n m f (Fin.last n)) z (coordinateAxis n i)| ≤ C at H
    simpa only [he] using H
  change |fderiv ℝ (fun z => f z-hierarchyPenalty n m 1 f z) z (coordinateAxis n i)| ≤ 2*C
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply]
  exact (abs_sub _ _).trans (by linarith)

theorem affineHierarchy_score_direction_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hU : ∀ s i, |U s (coordinateAxis n i)| ≤ C i)
    (a : Fin n → ℝ) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateVector n a)| ≤
      2*∑ i, |a i| *C i := by
  rw [coordinateVector,map_sum]
  calc
    _ ≤ ∑ i, |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (a i • coordinateAxis n i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| *(2*C i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,smul_eq_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left
        (affineHierarchy_score_coordinate_bound n m hm hmono c U i (hC i) (fun s => hU s i) z) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TiltedDirectionalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem HasExpGrowth.pow {E : Type} [NormedAddCommGroup E] {f : E → ℝ}
    (hf : HasExpGrowth f) (k : ℕ) : HasExpGrowth (fun x => f x^k) := by
  induction k with
  | zero => simpa using HasExpGrowth.const (E:=E) (1:ℝ)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem fiberGaussian_tilted_directional_stein (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, coordinateLinear n a z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateVector n a) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateVector n a) ∂(fiberGaussian n x).tilted V := by
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := ((HasExpGrowth.linear (coordinateProjection n i)).mul hg).integrable_tilted_fiberGaussian n V hV
    ((coordinateProjection n i).continuous.mul hc.continuous) x
  have hi₂ (i : Fin n) := (hdg.derivative_eval (coordinateAxis n i)).integrable_tilted_fiberGaussian n V hV
    ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  have hi₃ (i : Fin n) := (hg.mul (hdV.derivative_eval (coordinateAxis n i))).integrable_tilted_fiberGaussian n V hV
    (hc.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun z : ParameterSpace n => ∑ i, g z*(a i*fderiv ℝ V z (coordinateAxis n i))) =
      fun z => ∑ i, a i*(g z*fderiv ℝ V z (coordinateAxis n i)) := by
    funext z; apply Finset.sum_congr rfl; intro i _; ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [fiberGaussian_tilted_weighted_stein n V g hV hc hg hdg,mul_add]

theorem tilted_linear_moment_recursion (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(p+2) ∂(fiberGaussian n x).tilted V) =
      (p+1:ℕ)*(∑ i, (a i)^2)*(∫ z, (coordinateLinear n a z)^p ∂(fiberGaussian n x).tilted V)+
      ∫ z, (coordinateLinear n a z)^(p+1)*fderiv ℝ V z (coordinateVector n a)
        ∂(fiberGaussian n x).tilted V := by
  let L := coordinateLinear n a
  have hc : ContDiff ℝ 1 (fun z => L z^(p+1)) := L.contDiff.pow _
  have he : fderiv ℝ (fun z => L z^(p+1))=fun z => ((p+1:ℕ)*L z^p) • L := by
    funext z
    simpa only [Nat.add_sub_cancel,L.fderiv,nsmul_eq_mul] using (L.hasFDerivAt.pow (p+1)).fderiv
  have hg := (HasExpGrowth.linear L).pow p
  have hdg : HasExpGrowth (fderiv ℝ (fun z => L z^(p+1))) := by
    rw [he]
    exact ((HasExpGrowth.const ((p+1:ℕ):ℝ)).mul hg).smul (HasExpGrowth.const L)
  have H := fiberGaussian_tilted_directional_stein n V (fun z => L z^(p+1)) hV hc
    ((HasExpGrowth.linear L).pow _) hdg x a
  simp only [he,smul_apply,smul_eq_mul,L,coordinateLinear_coordinateVector] at H
  rw [show (fun z => (p+1:ℕ)*coordinateLinear n a z^p*(∑ i, a i^2))=
      fun z => ((p+1:ℕ)*(∑ i, a i^2))*coordinateLinear n a z^p by funext z; ring,
    integral_const_mul] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1; funext z; ring

theorem tilted_linear_even_moment_step (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(2*p+2) ∂(fiberGaussian n x).tilted V) ≤
      (2*(2*p+1:ℕ)*(∑ i, (a i)^2)+B^2)*
        (∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) := by
  let L := coordinateLinear n a
  let μ := (fiberGaussian n x).tilted V
  let d := fun z => fderiv ℝ V z (coordinateVector n a)
  have hi (k : ℕ) : Integrable (fun z => L z^k) μ :=
    ((HasExpGrowth.linear L).pow k).integrable_tilted_fiberGaussian n V hV (L.continuous.pow k) x
  have hd : Continuous d := (hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : HasExpGrowth d := HasExpGrowth.of_bounded hB (fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hip : Integrable (fun z => L z^(2*p+1)*d z) μ :=
    (((HasExpGrowth.linear L).pow _).mul hdg).integrable_tilted_fiberGaussian n V hV
      ((L.continuous.pow _).mul hd) x
  have hb' (z) : 2*(L z^(2*p+1)*d z) ≤ L z^(2*p+2)+B^2*L z^(2*p) := by
    have hz : 0 ≤ L z^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    have hdz : d z^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d z)) hB).mpr (hb z)
    have H := mul_nonneg hz (sq_nonneg (L z-d z))
    have H' := mul_le_mul_of_nonneg_right hdz hz
    simp only [pow_succ] at ⊢
    nlinarith
  have H := integral_mono (hip.const_mul 2) ((hi _).add ((hi _).const_mul (B^2))) hb'
  simp only [Pi.add_apply] at H
  rw [integral_const_mul,integral_add (hi _) ((hi _).const_mul (B^2)),integral_const_mul] at H
  have HE := tilted_linear_moment_recursion n V hV x a (2*p)
  change (∫ z, L z^(2*p+2) ∂μ)=(2*p+1:ℕ)*(∑ i, a i^2)*(∫ z, L z^(2*p) ∂μ)+
    ∫ z, L z^(2*p+1)*d z ∂μ at HE
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyExponentialMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_eq_tilted (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPathLaw n m f x=(fiberGaussian n x).tilted (hierarchyPathLogDensity n m f) := by
  have he : (fun z => Real.exp (hierarchyPathLogDensity n m f z))=hierarchyPathWeight n m f := by
    funext z
    simpa only [hierarchyPathLogDensity,one_mul] using (hierarchyPathWeight_eq n m f 1 z).symm
  rw [Measure.tilted,he,(hierarchyPathWeight_normalized n m f hf x).2]
  simp only [div_one,hierarchyPathLaw]
  simp_rw [show ∀ z, Real.exp (hierarchyPathLogDensity n m f z)=hierarchyPathWeight n m f z from fun z => congrFun he z]

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (d : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hU : ∀ s i, |U s (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, (coordinateLinear n a z)^2
      ∂hierarchyPathLaw n m (affineLogPartition d U) x) ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2 := by
  rw [hierarchyPathLaw_eq_tilted n m _ (affineLogPartition_boundedDerivs d U) x]
  have H := tilted_linear_even_moment_step n _
    (hierarchyPathLogDensity_regular n m (affineLogPartition_boundedDerivs d U)) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (affineHierarchy_score_direction_bound n m hm hmono d U C hC hU a) 0
  let := fiberGaussian_tilted_probability n _
    (hierarchyPathLogDensity_regular n m (affineLogPartition_boundedDerivs d U)) x
  simpa using H

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMassPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem massFromAtoms_hierarchyAtom (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (i : Fin n) :
    massFromAtoms n (hierarchyAtom n m u) i=m i := by
  induction n generalizing u with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [massFromAtoms_last]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact hierarchyAtom_sum n _ _
    · rw [massFromAtoms_castSucc]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact ih _ _ j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchySandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem HasExpGrowth.integrable_hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : HasExpGrowth g)
    (hc : Continuous g) (x : ℝ) : Integrable g (hierarchyPathLaw n m f x) := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  exact hg.integrable_tilted_fiberGaussian n _ (hierarchyPathLogDensity_regular n m hf) hc x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyProjectedCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAtom_tail_sum (n : ℕ) (m : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)=c-m i := by
  have H := massFromAtoms_hierarchyAtom n m c i
  have he : (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)+
      massFromAtoms n (hierarchyAtom n m c) i=c := by
    rw [massFromAtoms,← Finset.sum_add_distrib]
    convert hierarchyAtom_sum n m c using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i.val < j.val <;> simp [hij,show (j.val ≤ i.val) ↔ ¬i.val < j.val by omega]
  rw [H] at he
  linarith

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_score_coordinate (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i)=a*g s) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateAxis n i)=
      a*(affineMoment c U g z-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z else 0) := by
  have hf := affineLogPartition_boundedDerivs c U
  have hp := hierarchyPenalty_boundedDerivs n m 1 (affineLogPartition c U) hf
  change fderiv ℝ (fun z => affineLogPartition c U z-hierarchyPenalty n m 1 (affineLogPartition c U) z) z (coordinateAxis n i)=_
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply,fderiv_affineLogPartition_apply]
  simp only [hU,affineMoment_const_mul]
  rw [fderiv_hierarchyPenalty_apply n m 1 _ hf]
  simp_rw [hierarchyLevel_affine_coordinate n m c U g a i hU]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedCovarianceAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem weightedHierarchy_coordinate_covariance_at (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s) (x : ℝ) :
    (∫ z, coordinateProjection n i z*affineMoment c U g z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x) =
      a*((∫ z, affineMoment c U (fun s => (g s)^2) z
        ∂hierarchyPathLaw n m (affineLogPartition c U) x)-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
          (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
            ∂hierarchyPathLaw n m (affineLogPartition c U) x) else 0) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let A := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  let V (z : ParameterSpace n) := f z-hierarchyPenalty n m 1 f z
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hV : BoundedDerivs V := by
    convert hf.add (hp.const_mul (-1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    dsimp [V]
    ring
  let B := ∑ s, ‖g s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖ ≤ B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hG := affineMoment_contDiff c U g
  have hGb := affineMoment_norm_le c U g hb
  obtain ⟨C,hC,hC'⟩ := affineMoment_fderiv_bounded c U g
  have H := fiberGaussian_tilted_weighted_stein n V G hV hG
    (HasExpGrowth.of_bounded hB hGb) (HasExpGrowth.of_bounded hC hC') x i
  dsimp only [V] at H
  simp_rw [← hierarchyPathLaw_integral_tilt n m f hf x] at H
  have hA (j : Fin (n+1)) := hierarchyMomentLevel_bounded_continuous n m f G hf hG.continuous hB hGb j
  have hi (j : Fin (n+1)) : Integrable (fun z => G z*A j z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hG.continuous.mul (hA j).1)
      (fun z => by simp only [Pi.mul_apply,norm_mul]; exact mul_le_mul (hGb z) ((hA j).2 z) (norm_nonneg _) hB) x
  have hi2 : Integrable (fun z => affineMoment c U (fun s => (g s)^2) z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (affineMoment_continuous _ _ _)
      (affineMoment_norm_le c U _ (fun s => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)) x
  have hprod (j : Fin (n+1)) :
      (∫ z, G z*A j z ∂μ) = ∫ z, (A j z)^2 ∂μ := by
    have H := hierarchyPathLaw_fixed_mul n m f G (A j) hf hG.continuous (hA j).1 hB hB
      hGb (hA j).2 j (hierarchyMomentLevel_retained n m f G hf j j le_rfl) x
    calc
      _ = ∫ z, A j z*G z ∂μ := by congr 1; funext z; ring
      _ = _ := H.trans (by congr 1; funext z; change A j z*A j z = _; ring)
  have hdG (z) : fderiv ℝ G z (coordinateAxis n i) =
      a*(affineMoment c U (fun s => (g s)^2) z-(G z)^2) := by
    rw [fderiv_affineMoment_apply]
    simp only [hU]
    have he : (fun s => g s*(a*g s)) = fun s => a*(g s)^2 := by funext s; ring
    rw [he,affineMoment_const_mul,affineMoment_const_mul]
    dsimp [G]
    ring
  have hdV (z) : fderiv ℝ V z (coordinateAxis n i) = a*G z-
      ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*(a*A j z) else 0 := by
    rw [show V = fun z => f z-hierarchyPenalty n m 1 f z from rfl,
      fderiv_fun_sub (hf.1.differentiable (by norm_num) z) (hp.1.differentiable (by norm_num) z)]
    simp only [sub_apply]
    rw [fderiv_affineLogPartition_apply]
    simp only [hU,affineMoment_const_mul]
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    dsimp only [f]
    simp_rw [hierarchyLevel_affine_coordinate n m c U g a i hU]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [A,G,f]
  have hI1 : Integrable (fun z => fderiv ℝ G z (coordinateAxis n i)) μ := by
    apply hierarchyPathLaw_integrable n m f _ hf
      ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    intro z
    exact ((fderiv ℝ G z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC' z) (norm_nonneg _))
  have hI2 : Integrable (fun z => G z*fderiv ℝ V z (coordinateAxis n i)) μ := by
    obtain ⟨hVc,D,E,hD,_,hbV,_⟩ := hV
    apply hierarchyPathLaw_integrable n m f _ hf
      (hG.continuous.mul ((hVc.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      (C:=B*(D*‖coordinateAxis n i‖))
    intro z
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_mul (hGb z)
      (((fderiv ℝ V z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbV z) (norm_nonneg _)))
      (norm_nonneg _) hB
  have hJ (j : Fin (n+1)) : Integrable (fun z =>
      if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) μ := by
    by_cases h : i.val < j.val
    · simpa only [ite_eq_left h] using (hi j).const_mul (hierarchyAtom n m 1 j)
    · simp only [ite_eq_right h]; exact integrable_const 0
  change (∫ z, coordinateProjection n i z*G z ∂μ) = _ at H ⊢
  rw [H,← integral_add hI1 hI2]
  have he (z) : fderiv ℝ G z (coordinateAxis n i)+G z*fderiv ℝ V z (coordinateAxis n i) =
      a*(affineMoment c U (fun s => (g s)^2) z-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) := by
    rw [hdG,hdV]
    simp only [mul_sub,Finset.mul_sum]
    have he : (∑ j : Fin (n+1), G z*(if i.val < j.val then hierarchyAtom n m 1 j*(a*A j z) else 0)) =
        ∑ j : Fin (n+1), a*(if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [he]
    ring
  rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,
    integral_sub hi2 (integrable_finsetSum _ (fun j _ => hJ j)),integral_finsetSum _ (fun j _ => hJ j)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.val < j.val
  · simp only [ite_eq_left h,integral_const_mul,hprod]
    rfl
  · simp only [ite_eq_right h,integral_zero]

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyIncrementCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_increment_covariance (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s)
    (i j : Fin n) (hij : i ≤ j) (x : ℝ) :
    (∫ z, coordinateProjection n i z*coordinateProjection n j z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (if i=j then 1 else 0)+a i*a j*m j*affineHierarchyResponse n m c U g i x := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let M := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  have hV := hierarchyPathLogDensity_regular n m hf
  let B := ∑ s, ‖g s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖ ≤ B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hcG := affineMoment_continuous c U g
  have hbG := affineMoment_norm_le c U g hb
  have hM (k) := hierarchyMomentLevel_bounded_continuous n m f G hf hcG hB hbG k
  let L := coordinateProjection n i
  have hL := HasExpGrowth.linear L
  have hMG (k) : HasExpGrowth (M k) := HasExpGrowth.of_bounded hB (hM k).2
  have hprod (k : Fin (n+1)) (hik : i.val < k.val) :
      (∫ z, L z*M k z ∂μ)=∫ z, L z*G z ∂μ := by
    exact (hierarchyPathLaw_fixed_mul_exp n m hf hcG L.continuous
      (HasExpGrowth.of_bounded hB hbG) hL k (hierarchyMomentLevel_coordinate_fixed n m hf i k hik) x).symm
  have hdL : HasExpGrowth (fderiv ℝ (L : ParameterSpace n → ℝ)) := by
    have he : fderiv ℝ (L : ParameterSpace n → ℝ) = fun _ => L := funext (fun _ => L.fderiv)
    rw [he]
    exact HasExpGrowth.const L
  have H := fiberGaussian_tilted_weighted_stein n (hierarchyPathLogDensity n m f) L hV L.contDiff hL hdL x j
  rw [← hierarchyPathLaw_eq_tilted n m f hf x] at H
  simp only [L.fderiv,L,coordinateProjection_coordinateAxis] at H
  have hiG : Integrable (fun z => L z*G z) μ :=
    (hL.mul (HasExpGrowth.of_bounded hB hbG)).integrable_hierarchyPathLaw n m hf (L.continuous.mul hcG) x
  have hJ (k : Fin (n+1)) : Integrable (fun z =>
      if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) μ := by
    by_cases hjk : j.val < k.val
    · simp only [ite_eq_left hjk]
      exact ((hL.mul (hMG k)).integrable_hierarchyPathLaw n m hf (L.continuous.mul (hM k).1) x).const_mul _
    · simp only [ite_eq_right hjk]; exact integrable_const 0
  have he (z) : L z*fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n j)=
      a j*(L z*G z-∑ k : Fin (n+1), if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) := by
    rw [affineHierarchy_score_coordinate n m c U g (a j) j (fun s => hU s j)]
    simp only [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
  have heS : (∑ k : Fin (n+1), ∫ z, (if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) ∂μ)=
      (1-m j)*(∫ z, L z*G z ∂μ) := by
    rw [← hierarchyAtom_tail_sum n m 1 j,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hjk : j.val < k.val
    · rw [ite_eq_left hjk]
      simp only [ite_eq_left hjk,integral_const_mul,hprod k (show i.val < k.val from lt_of_le_of_lt hij hjk)]
    · simp only [ite_eq_right hjk,integral_zero,zero_mul]
  have hc : (∫ z, L z*G z ∂μ)=a i*affineHierarchyResponse n m c U g i x :=
    weightedHierarchy_coordinate_covariance_at n m c U g (a i) i (fun s => hU s i) x
  calc
    _ = ∫ z, coordinateProjection n j z*L z ∂μ := by congr 1; funext z; ring
    _ = (if i=j then 1 else 0)+∫ z, L z*fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n j) ∂μ := by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using H
    _ = (if i=j then 1 else 0)+a j*((∫ z, L z*G z ∂μ)-(1-m j)*(∫ z, L z*G z ∂μ)) := by
      rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,integral_sub hiG
        (integrable_finsetSum _ (fun k _ => hJ k)),integral_finsetSum _ (fun k _ => hJ k),heS]
    _ = _ := by rw [hc]; ring

theorem affineHierarchy_increment_covariance_symm (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s)
    (i j : Fin n) (x : ℝ) :
    (∫ z, coordinateProjection n i z*coordinateProjection n j z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (if i=j then 1 else 0)+a i*a j*m (max i j)*affineHierarchyResponse n m c U g (min i j) x := by
  classical
  rcases le_total i j with hij|hji
  · simpa only [max_eq_right hij,min_eq_left hij] using affineHierarchy_increment_covariance n m c U g a hU i j hij x
  · rw [max_eq_left hji,min_eq_right hji]
    have H := affineHierarchy_increment_covariance n m c U g a hU j i hji x
    rw [integral_congr_ae (ae_of_all _ (fun z => mul_comm (coordinateProjection n i z) (coordinateProjection n j z))),H]
    have he : (if j=i then (1:ℝ) else 0)=(if i=j then 1 else 0) := by simp only [eq_comm]
    rw [he]
    ring

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyScoreGeneral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z, |fderiv ℝ f z (coordinateAxis n i)| ≤ C)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| ≤ C := by
  by_cases h : i.val < j.val
  · rw [hierarchyLevel_gradient n m f hf j _ z (tailZero_coordinateAxis n i j h)]
    have hc : Continuous (directionalGradient f (coordinateAxis n i)) :=
      (hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hb : ∀ z, ‖directionalGradient f (coordinateAxis n i) z‖ ≤ C := by
      intro z; simpa only [directionalGradient,Real.norm_eq_abs] using hF z
    simpa only [Real.norm_eq_abs] using
      (hierarchyMomentLevel_bounded_continuous n m f _ hf hc hC hb j).2 z
  · rw [(hierarchyLevel_invariant_of_prefix n m f _ j
        (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m f hf j).1.differentiable (by norm_num)) z]
    simpa using hC

theorem hierarchy_score_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z, |fderiv ℝ f z (coordinateAxis n i)| ≤ C)
    (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i)| ≤ 2*C := by
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hw (j) : 0 ≤ hierarchyAtom n m 1 j :=
    hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hpB : |fderiv ℝ (hierarchyPenalty n m 1 f) z (coordinateAxis n i)| ≤ C := by
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    calc
      _ ≤ ∑ j, |hierarchyAtom n m 1 j*fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, hierarchyAtom n m 1 j*C := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hierarchyLevel_coordinate_bound n m f hf i hC hF j z) (hw j)
      _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  change |fderiv ℝ (fun z => f z-hierarchyPenalty n m 1 f z) z (coordinateAxis n i)| ≤ 2*C
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply]
  exact (abs_sub _ _).trans (by have := hF z; linarith)

theorem hierarchy_score_direction_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (a : Fin n → ℝ) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateVector n a)| ≤
      2*∑ i, |a i| *C i := by
  rw [coordinateVector,map_sum]
  calc
    _ ≤ ∑ i, |fderiv ℝ (hierarchyPathLogDensity n m f) z (a i • coordinateAxis n i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| *(2*C i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,smul_eq_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hierarchy_score_coordinate_bound n m hm hmono f hf i (hC i) (fun z => hF z i) z) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

theorem hierarchy_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m f x) ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2 := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  have H := tilted_linear_even_moment_step n _ (hierarchyPathLogDensity_regular n m hf) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (hierarchy_score_direction_bound n m hm hmono f hf C hC hF a) 0
  let := fiberGaussian_tilted_probability n _ (hierarchyPathLogDensity_regular n m hf) x
  simpa using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyWeightedIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_weighted_increment_square (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a k : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s) (x : ℝ) :
    (∫ z, (∑ i, k i*a i*coordinateProjection n i z)^2
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (∑ i, (k i)^2*(a i)^2)+
      ∑ i, ∑ j, k i*k j*(a i)^2*(a j)^2*m (max i j)*
        affineHierarchyResponse n m c U g (min i j) x := by
  classical
  let f := affineLogPartition c U
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  have hij (i j : Fin n) : Integrable (fun z =>
      (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z)) μ :=
    (((HasExpGrowth.const (k i*a i)).mul (HasExpGrowth.linear (coordinateProjection n i))).mul
      ((HasExpGrowth.const (k j*a j)).mul (HasExpGrowth.linear (coordinateProjection n j)))).integrable_hierarchyPathLaw n m hf
      (((coordinateProjection n i).continuous.const_mul _).mul
        ((coordinateProjection n j).continuous.const_mul _)) x
  have he (z : ParameterSpace n) : (∑ i, k i*a i*coordinateProjection n i z)^2=
      ∑ i, ∑ j, (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z) := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [integral_congr_ae (ae_of_all _ he),integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hij _ j)]
  have hterm (i j : Fin n) : (∫ z,
      (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z) ∂μ)=
      (if i=j then (k i)^2*(a i)^2 else 0)+
        k i*k j*(a i)^2*(a j)^2*m (max i j)*affineHierarchyResponse n m c U g (min i j) x := by
    have hp (z : ParameterSpace n) :
        (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z)=
        (k i*a i*(k j*a j))*(coordinateProjection n i z*coordinateProjection n j z) := by ring
    rw [integral_congr_ae (ae_of_all _ hp),integral_const_mul,
      affineHierarchy_increment_covariance_symm n m c U g a hU i j x]
    by_cases h : i=j
    · subst j; simp only [ite_true]; ring
    · simp only [ite_eq_right h]; ring
  simp_rw [hterm,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hierarchyAverage_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f g : E → ℝ) (c : ℝ → E) :
    hierarchyAverage n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))
      (fun z => g (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchyAverage n m v f g (c x) := by
  induction n generalizing f g with
  | zero => simp [hierarchyAverage,vectorHierarchyAverage,parameter]
  | succ n ih =>
    have he (F : E → ℝ) : (fun z : ParameterSpace (n+1) =>
        F (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => F ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he f,he g,hierarchyAverage]
    change hierarchyAverage n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))
      (fun z => vectorStepAverage (m (Fin.last n)) (v (Fin.last n)) f g
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f : F → ℝ) :
    vectorStep m v (f ∘ L)=vectorStep m (L v) f ∘ L := by
  funext x
  simp only [vectorStep,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorStepAverage_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f g : F → ℝ) :
    vectorStepAverage m v (f ∘ L) (g ∘ L)=vectorStepAverage m (L v) f g ∘ L := by
  funext x
  simp only [vectorStepAverage,Function.comp_def,map_add,map_smul]
  rfl

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_CommonBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem vectorStep_real (m v : ℝ) (f : ℝ → ℝ) : vectorStep m v f=scalarStep m v f := by
  simp only [vectorStep,scalarStep,smul_eq_mul,mul_comm]

theorem vectorStepAverage_real (m v : ℝ) (f g : ℝ → ℝ) : vectorStepAverage m v f g=scalarStepAverage m v f g := by
  funext x
  simp only [vectorStepAverage,scalarStepAverage,gaussianAverage,gaussianStepLaw,smul_eq_mul,mul_comm]

theorem vectorHierarchy_real (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) :
    vectorHierarchy n m v f=scalarHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [vectorHierarchy,vectorStep_real,ih]; rfl

theorem vectorHierarchyAverage_real (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    vectorHierarchyAverage n m v f g=scalarHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [vectorHierarchyAverage,vectorStep_real,vectorStepAverage_real,ih]; rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MergedBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarIncrementChain_regular (l : List BranchIncrement) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (scalarIncrementChain l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact scalarStep_regular ih p.1 p.2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_regular {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v : E) :
    BoundedDerivs (vectorStep m v f) :=
  (hf.compCLM (vectorTranslation v)).gaussianStep m

theorem vectorIncrementChain_regular (l : List (ℝ × E)) {f : E → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (vectorIncrementChain l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact vectorStep_regular ih p.1 p.2

theorem vectorIncrementChain_append (l r : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain (l++r) f=vectorIncrementChain l (vectorIncrementChain r f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementChain,ih]

theorem vectorIncrementAverage_append (l r : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage (l++r) f g=
      vectorIncrementAverage l (vectorIncrementChain r f) (vectorIncrementAverage r f g) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementAverage,vectorIncrementChain_append,ih]

theorem vectorIncrementChain_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f : E → ℝ) :
    vectorIncrementChain (List.ofFn (fun i => (m i,v i))) f=vectorHierarchy n m v f := by
  induction n generalizing f with
  | zero => simp [vectorIncrementChain,vectorHierarchy]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementChain_append]
    exact ih _ _ _

theorem vectorIncrementAverage_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f g : E → ℝ) :
    vectorIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => simp [vectorIncrementAverage,vectorHierarchyAverage]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementAverage_append]
    exact ih _ _ _ _

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

theorem chainPotentialPenalty_append (F : E → ℝ) (l r : List (ℝ × E)) (Q : E) :
    chainPotentialPenalty F (l++r) Q=chainPotentialPenalty F l Q+
      chainPotentialPenalty F r (Q+chainSum l) := by
  induction l generalizing Q with
  | nil => simp [chainPotentialPenalty]
  | cons p l ih => simp only [List.cons_append,chainPotentialPenalty,ih,chainSum_cons,add_assoc]

theorem chainSum_ofFn (n : ℕ) (p : Fin n → ℝ × E) : chainSum (List.ofFn p)=∑ i,(p i).2 := by
  simp [chainSum,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem strictPrefix_castSucc {n : ℕ} (v : Fin (n+1) → E) (i : Fin n) :
    strictPrefix v i.castSucc=strictPrefix (fun j => v j.castSucc) i := by
  simp [strictPrefix,Fin.sum_univ_castSucc,not_lt_of_ge (Fin.le_last i.castSucc)]

theorem strictPrefix_last (n : ℕ) (v : Fin (n+1) → E) :
    strictPrefix v (Fin.last n)=∑ j : Fin n,v j.castSucc := by
  simp [strictPrefix,Fin.sum_univ_castSucc]

theorem chainPotentialPenalty_ofFn (n : ℕ) (F : E → ℝ) (p : Fin n → ℝ × E) (Q : E) :
    chainPotentialPenalty F (List.ofFn p) Q=
      ∑ i,(p i).1*(F (Q+strictPrefix (fun j => (p j).2) i+(p i).2)-
        F (Q+strictPrefix (fun j => (p j).2) i)) := by
  induction n with
  | zero => simp [chainPotentialPenalty]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,chainPotentialPenalty_append,ih]
    simp only [chainPotentialPenalty,add_zero,chainSum_ofFn,Fin.sum_univ_castSucc,
      strictPrefix_castSucc,strictPrefix_last]
end Penalty

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTailValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementChain_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f : F → ℝ) :
    vectorIncrementChain l (f ∘ L)=
      vectorIncrementChain (l.map (fun p => (p.1,L p.2))) f ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,ih,vectorStep_pullback]; rfl
end Vector

theorem vectorIncrementChain_real (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    vectorIncrementChain l f=scalarIncrementChain l f := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,scalarIncrementChain,ih,vectorStep_real]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverageRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Composition
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Norm G]
theorem HasExpGrowth.compCLM {f : F → G} (hf : HasExpGrowth f) (L : E →L[ℝ] F) :
    HasExpGrowth (f ∘ L) := by
  obtain ⟨C,M,hC,hM,h⟩ := hf
  refine ⟨C,M*‖L‖,hC,mul_nonneg hM (norm_nonneg _),fun x => (h (L x)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  have H := mul_le_mul_of_nonneg_left (L.le_opNorm x) hM
  simpa only [mul_assoc] using H
end Composition
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStepAverage_expGrowth {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : HasExpGrowth g) (m : ℝ) (v : E) : HasExpGrowth (vectorStepAverage m v f g) :=
  gaussianAverage_expGrowth (hf.compCLM (vectorTranslation v)) m (hg.compCLM (vectorTranslation v))

theorem vectorStepAverage_continuous {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : HasExpGrowth g) (hc : Continuous g) (m : ℝ) (v : E) :
    Continuous (vectorStepAverage m v f g) :=
  gaussianAverage_continuous_of_expGrowth (hf.compCLM (vectorTranslation v)) m
    (hg.compCLM (vectorTranslation v)) (hc.comp (vectorTranslation v).continuous)

theorem vectorHierarchyAverage_regular (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    {f g : E → ℝ} (hf : BoundedDerivs f) (hg : HasExpGrowth g) (hc : Continuous g) :
    Continuous (vectorHierarchyAverage n m v f g) ∧ HasExpGrowth (vectorHierarchyAverage n m v f g) := by
  induction n generalizing f g with
  | zero => exact ⟨hc,hg⟩
  | succ n ih =>
    exact ih _ _ (vectorStep_regular hf _ _)
      (vectorStepAverage_expGrowth hf hg _ _) (vectorStepAverage_continuous hf hg hc _ _)

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_IncrementListAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementAverage_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f g : F → ℝ) :
    vectorIncrementAverage l (f ∘ L) (g ∘ L)=
      vectorIncrementAverage (l.map (fun p => (p.1,L p.2))) f g ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,vectorIncrementChain_pullback,ih,vectorStepAverage_pullback]
    rfl

theorem vectorIncrementChain_get (l : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain l f=vectorHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementChain_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f

theorem vectorIncrementAverage_get (l : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage l f g=vectorHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementAverage_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g

theorem vectorIncrementAverage_regular (l : List (ℝ × E)) {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (he : HasExpGrowth g) :
    Continuous (vectorIncrementAverage l f g) ∧ HasExpGrowth (vectorIncrementAverage l f g) := by
  rw [vectorIncrementAverage_get]
  exact vectorHierarchyAverage_regular _ _ _ hf he hg
end Vector

theorem vectorIncrementAverage_real (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    vectorIncrementAverage l f g=scalarIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,scalarIncrementAverage,vectorIncrementChain_real,ih,vectorStepAverage_real]

theorem scalarIncrementChain_ofFn (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) :
    scalarIncrementChain (List.ofFn (fun i => (m i,v i))) f=scalarHierarchy n m v f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_ofFn,vectorHierarchy_real]

theorem scalarIncrementChain_get (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain l f=scalarHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_get,vectorHierarchy_real]

theorem scalarIncrementAverage_get (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage l f g=scalarHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_get,vectorHierarchyAverage_real]

theorem scalarIncrementAverage_append (l r : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (l++r) f g=scalarIncrementAverage l (scalarIncrementChain r f) (scalarIncrementAverage r f g) := by
  simp only [← vectorIncrementAverage_real,← vectorIncrementChain_real,vectorIncrementAverage_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRecursiveExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Linear
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_composition_coordinate_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hL : LipschitzWith 1 f) (X : E →L[ℝ] ℝ) (z e : E) :
    |fderiv ℝ (f ∘ X) z e| ≤ |X e| := by
  rw [fderiv_comp z (hf.1.differentiable (by norm_num) _) X.differentiableAt,
    X.fderiv,ContinuousLinearMap.comp_apply]
  have H := ((fderiv ℝ f (X z)).le_opNorm (X e)).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul] using H
end Linear

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAverageCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem ScalarSpinConvex.bounds {f : ℝ → ℝ} (h : ScalarSpinConvex f) (x : ℝ) :
    |rootGradient 0 f x| ≤ 1 ∧ |rootHessian 0 f x| ≤ 1 := by
  have H := h x
  refine ⟨(sq_le_one_iff_abs_le_one _).mp (by linarith),?_⟩
  rw [abs_of_nonneg H.1]
  linarith [sq_nonneg (rootGradient 0 f x)]

theorem scalarStepAverage_continuous {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B) (m v : ℝ) :
    Continuous (scalarStepAverage m v f g) := by
  apply gaussianAverage_continuous (hf.compCLM (scalarStepLinear v)) m
    (hg.comp (scalarStepLinear v).continuous) hB
  intro z
  exact hb _

theorem scalarStepAverage_bound {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    |scalarStepAverage m v f g x| ≤ B := by
  exact gaussianAverage_norm_le (hf.compCLM (scalarStepLinear v)) m
    (g:=fun z => g (z.1+v*z.2)) (fun z => hb _) x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem ScalarSpinConvex.hessian_bounded {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) : BoundedScalar (rootHessian 0 f) :=
  ⟨rootHessian_continuous 0 hf,1,zero_le_one,fun x => (h.bounds x).2⟩

theorem BoundedScalar.scalarStepAverage {f g : ℝ → ℝ} (hg : BoundedScalar g)
    (hf : BoundedDerivs f) (m v : ℝ) : BoundedScalar (scalarStepAverage m v f g) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact ⟨scalarStepAverage_continuous hf hg.continuous hB hb m v,B,hB,
    scalarStepAverage_bound hf hb m v⟩

theorem scalarHierarchyAverage_bounded {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) :
    BoundedScalar (scalarHierarchyAverage n m v f g) := by
  induction n generalizing f g with
  | zero => exact hg
  | succ n ih => exact ih (scalarStep_regular hf _ _) (hg.scalarStepAverage hf _ _) _ _

theorem scalarHierarchyAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z => g (x+coordinateLinear n v z))
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) := by
  obtain ⟨B,_,hb⟩ := hg.bounded
  apply hierarchyPathLaw_integrable n m _ _ ((hf.translate x).compCLM (coordinateLinear n v))
    (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous))
  exact fun z => hb _

theorem scalarHierarchyAverage_integral {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact scalarHierarchyAverage_eq_integral n m v hf hg.continuous hB hb x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Covariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem covariance_small_field {a b X : Ω → ℝ} {c M L : ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hab : Integrable (fun z => a z*b z) μ)
    (hX : Integrable X μ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hs : ∀ z, |a z-c| ≤ L*|X z|) (hbM : ∀ z, |b z| ≤ M) :
    |(∫ z, a z*b z ∂μ)-(∫ z,a z ∂μ)*(∫ z,b z ∂μ)| ≤ 2*M*L*(∫ z,|X z| ∂μ) := by
  have hd : Integrable (fun z => a z-c) μ := ha.sub (integrable_const c)
  have hdb : Integrable (fun z => (a z-c)*b z) μ := by
    convert hab.sub (hb.const_mul c) using 1
    all_goals try with_reducible_and_instances rfl
    ext point
    simp only [Pi.sub_apply]
    ring
  have h1 : |∫ z, (a z-c)*b z ∂μ| ≤ M*L*(∫ z,|X z| ∂μ) := by
    calc
      _ ≤ ∫ z, |(a z-c)*b z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => (a z-c)*b z)
      _ ≤ ∫ z, M*L*|X z| ∂μ := by
        apply integral_mono_ae hdb.abs (hX.abs.const_mul (M*L))
        exact ae_of_all _ (fun z => by
          change |(a z-c)*b z| ≤ M*L*|X z|
          rw [abs_mul]
          calc
            _ ≤ |a z-c| * M := mul_le_mul_of_nonneg_left (hbM z) (abs_nonneg _)
            _ ≤ (L*|X z|)*M := mul_le_mul_of_nonneg_right (hs z) hM
            _ = _ := by ring)
      _ = _ := integral_const_mul _ _
  have h2 : |∫ z, a z-c ∂μ| ≤ L*(∫ z,|X z| ∂μ) := by
    calc
      _ ≤ ∫ z, |a z-c| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => a z-c)
      _ ≤ ∫ z, L*|X z| ∂μ := integral_mono_ae hd.abs (hX.abs.const_mul L) (ae_of_all _ hs)
      _ = _ := integral_const_mul _ _
  have h3 : |∫ z,b z ∂μ| ≤ M := by
    calc
      _ ≤ ∫ z,|b z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm b
      _ ≤ ∫ _ : Ω,M ∂μ := integral_mono_ae hb.abs (integrable_const M) (ae_of_all _ hbM)
      _ = M := by simp
  have he : (∫ z, a z*b z ∂μ)-(∫ z,a z ∂μ)*(∫ z,b z ∂μ)=
      (∫ z,(a z-c)*b z ∂μ)-(∫ z,a z-c ∂μ)*(∫ z,b z ∂μ) := by
    have hfun : (fun z => (a z-c)*b z)=fun z => a z*b z-c*b z := by funext z; ring
    rw [hfun,integral_sub hab (hb.const_mul c),integral_const_mul,integral_sub ha (integrable_const c)]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  rw [he]
  calc
    _ ≤ |∫ z,(a z-c)*b z ∂μ|+|(∫ z,a z-c ∂μ)*(∫ z,b z ∂μ)| := abs_sub _ _
    _ ≤ M*L*(∫ z,|X z| ∂μ)+(L*(∫ z,|X z| ∂μ))*M := by
      rw [abs_mul]
      exact add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
    _ = _ := by ring
end Covariance

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_covariance_small (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f A B : ℝ → ℝ} (hf : BoundedDerivs f) (hfL : LipschitzWith 1 f)
    (hA : BoundedScalar A) (hB : BoundedScalar B) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hBM : ∀ x, |B x| ≤ M)
    (hAL : ∀ x, |A x-A 0| ≤ L*|x|) :
    |scalarHierarchyAverage n m v f (fun x => A x*B x) 0-
      scalarHierarchyAverage n m v f A 0*scalarHierarchyAverage n m v f B 0| ≤
        2*M*L*Real.sqrt (2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2) := by
  let X := coordinateLinear n v
  let F := f ∘ X
  let μ := hierarchyPathLaw n m F 0
  have hF : BoundedDerivs F := hf.compCLM X
  let := hierarchyPathLaw_probability n m F hF 0
  have hX : Integrable X μ := (HasExpGrowth.linear X).integrable_hierarchyPathLaw n m hF X.continuous 0
  have hXsq : Integrable (fun z => (X z)^2) μ := ((HasExpGrowth.linear X).pow 2).integrable_hierarchyPathLaw
    n m hF (X.continuous.pow 2) 0
  have hXi : MemLp X 2 μ := (memLp_two_iff_integrable_sq X.continuous.aestronglyMeasurable).2 hXsq
  have hAs : Integrable (A ∘ X) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hA n m v 0
  have hBs : Integrable (B ∘ X) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hB n m v 0
  have hAB : BoundedScalar (fun x => A x*B x) := by
    obtain ⟨Ca,hCa,ha⟩ := hA.bounded
    obtain ⟨Cb,hCb,hb⟩ := hB.bounded
    exact ⟨hA.continuous.mul hB.continuous,⟨Ca*Cb,mul_nonneg hCa hCb,fun x => by
      rw [abs_mul]; exact mul_le_mul (ha x) (hb x) (abs_nonneg _) hCa⟩⟩
  have hABs : Integrable (fun z => A (X z)*B (X z)) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hAB n m v 0
  have H := covariance_small_field hAs hBs hABs hX hM hL (fun z => hAL (X z)) (fun z => hBM (X z))
  have hS := hierarchy_square_bound n m hm hmono F hF (fun i => |v i|) (fun i => abs_nonneg _)
    (fun z i => by
      have H := scalar_composition_coordinate_bound hf hfL X z (coordinateAxis n i)
      simpa only [F,X,coordinateLinear_coordinateAxis] using H) 0 v
  have hsum : (∑ i, |v i| * |v i|)=∑ i,(v i)^2 := by
    apply Finset.sum_congr rfl; intro i _; rw [← sq_abs]; ring
  rw [hsum] at hS
  have hS' : (∫ z,(X z)^2 ∂μ) ≤ 2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2 := by nlinarith [hS]
  have hE : (∫ z,|X z| ∂μ) ≤ Real.sqrt (2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2) := by
    have H := abs_integral_mul_le_sqrt_of_bound (fun z => |X z|) (fun _ => (1:ℝ)) hXi.abs
      aestronglyMeasurable_const (ae_of_all _ (fun _ => by norm_num))
    simp only [mul_one,sq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at H
    exact H.trans (Real.sqrt_le_sqrt hS')
  rw [scalarHierarchyAverage_integral hf hAB,scalarHierarchyAverage_integral hf hA,
    scalarHierarchyAverage_integral hf hB]
  simp only [zero_add]
  simpa only [μ,F,X,Function.comp_def] using H.trans (mul_le_mul_of_nonneg_left hE (by positivity))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootSusceptibilitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tailZero_parameterAxis (n : ℕ) (j : Fin (n+1)) :
    TailZero n j (parameterAxis n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [TailZero,Fin.lastCases_last]
    · simp only [TailZero,Fin.lastCases_castSucc,parameterAxis]
      exact ⟨trivial,ih j⟩

theorem hierarchyLevel_rootGradient (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (j : Fin (n+1)) :
    rootGradient n (hierarchyLevel n m f j)=
      hierarchyMomentLevel n m f (rootGradient n f) j := by
  funext z
  exact hierarchyLevel_gradient n m f hf j (parameterAxis n) z (tailZero_parameterAxis n j)

theorem hierarchyPressure_rootHessian_overlap_sum (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      1-∑ j, hierarchyAtom n m 1 j*(∫ z,
        (hierarchyMomentLevel n m f (rootGradient n f) j z)^2 ∂hierarchyPathLaw n m f x) := by
  have hg := rootGradient_continuous n hf
  have hb (z) : ‖rootGradient n f z‖≤1 := (h.bounds z).1
  have hM := hierarchyMomentLevel_bounded_continuous n m f (rootGradient n f) hf hg zero_le_one hb
  have hint (j : Fin (n+1)) : Integrable (fun z => hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z))
      (hierarchyPathLaw n m f x) := by
    apply Integrable.const_mul
    apply hierarchyPathLaw_integrable n m f _ hf ((hM j).1.mul hg) (C:=1)
    intro z
    simpa only [Pi.mul_apply,norm_mul,one_mul] using mul_le_mul ((hM j).2 z) (hb z) (norm_nonneg _) zero_le_one
  have Hpair : rootPair n m f=fun z => ∑ j, hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z) := by
    funext z
    have Hp := fderiv_hierarchyPenalty_apply n m 1 f hf z (parameterAxis n)
    change rootGradient n (hierarchyPenalty n m 1 f) z=
      ∑ j, hierarchyAtom n m 1 j*rootGradient n (hierarchyLevel n m f j) z at Hp
    rw [rootPair,Hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hierarchyLevel_rootGradient n m hf]
    ring
  rw [hierarchyPressure_rootHessian_spin_formula n m hm hmono hf h he x,Hpair,
    integral_finsetSum _ (fun j _ => hint j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,hierarchyPathLaw_prefix_mul n m f (rootGradient n f)
    (rootGradient n f) hf hg hg zero_le_one zero_le_one hb hb j x]
  simp only [pow_two]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleBaseFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem weightedBranch_value (w : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ) :
    vectorIncrementChain w (fun p : ℝ × ℝ => f p.1)=fun p => scalarIncrementChain (weightedUnderlying w) f p.1 := by
  have H := vectorIncrementChain_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f
  rw [vectorIncrementChain_real] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStepAverage_frozen {f : E → ℝ} (hf : BoundedDerivs f) (g : E → ℝ)
    (m : ℝ) (v : E) (hi : ∀ x (s : ℝ),g (x+s • v)=g x) :
    vectorStepAverage m v f g=g := by
  unfold vectorStepAverage
  have he : (fun z : E × ℝ => g (z.1+z.2 • v))=fun z => g z.1 := funext (fun z => hi z.1 z.2)
  rw [he]
  have hF : BoundedDerivs (fun z : E × ℝ => f (z.1+z.2 • v)) := hf.compCLM (vectorTranslation v)
  exact gaussianAverage_const_prefix hF m g
end Vector

theorem zeroWeightChain_average {f : ℝ → ℝ} (hf : BoundedDerivs f) (t : List (ℝ × ℝ)) :
    vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2)=fun p => p.2^2 := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change vectorStepAverage p.1 (p.2,0) (vectorIncrementChain (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1))
      (vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2))=_
    rw [ih]
    apply vectorStepAverage_frozen (vectorIncrementChain_regular _ (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    intro x s
    simp only [Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

theorem weightedFull_average (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
      (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (0,0)=
      scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t f))
        (fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t f p.1) (fun p => p.2^2) (x,0)) 0 := by
  rw [vectorIncrementAverage_append,zeroWeightChain_average hf,weightedBranch_value,weightedUnderlying_zeroWeight,
    vectorIncrementAverage_append,weightedBranch_value]
  have H := congrFun (vectorIncrementAverage_pullback zeroNoiseEmbedding c
    (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) (scalarIncrementChain t f) p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t f p.1) (fun p => p.2^2))) 0
  simp only [Function.comp_def,zeroNoiseEmbedding_apply,vectorIncrementAverage_real] at H
  exact H.symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetainedStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem sum_get_map {α : Type} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length,f (l.get i))=(l.map f).sum := by
  rw [← List.sum_ofFn]
  simpa only [List.ofFn_get,Function.comp_def] using
    congrArg List.sum (List.map_ofFn (f:=l.get) (g:=f)).symm

theorem mass_get_monotone {E : Type} {l : List (ℝ × E)}
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : Monotone (fun i : Fin l.length => (l.get i).1) := by
  have H := hs
  rw [← List.ofFn_get l,List.pairwise_ofFn] at H
  intro i j hij
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact H hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_even {f : ℝ → ℝ} (hf : Function.Even f) (m v : ℝ) :
    Function.Even (scalarStep m v f) := by
  intro z
  have he (y : ℝ) : f (-z+v*y) = f (z+v*(-y)) := by
    rw [← hf (-z+v*y)]
    congr 1
    ring
  have hi (g : ℝ → ℝ) : (∫ y, g (-y) ∂gaussianReal 0 1) = ∫ y, g y ∂gaussianReal 0 1 := by
    simpa only [scalarSign_true] using
      (scalarSign_gaussian true).integral_comp (scalarSignEquiv true).measurableEmbedding g
  simp only [scalarStep,gaussianStep,positiveGaussianLogStep,he]
  rw [hi (fun y => f (z+v*y)),hi (fun y => Real.exp (m*f (z+v*y)))]

theorem scalarHierarchy_even (n : ℕ) (m v : Fin n → ℝ) {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (scalarStep_even hf _ _)

theorem scalarHierarchy_spin_even (n : ℕ) (m v : Fin n → ℝ) :
    Function.Even (scalarHierarchy n m v scalarSpinTerminal) :=
  scalarHierarchy_even n m v (fun z => by simp only [scalarSpinTerminal,Real.cosh_neg])

theorem scalarHierarchy_spin_gradient_zero (n : ℕ) (m v : Fin n → ℝ) :
    fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal) 0 1 = 0 := by
  let f := scalarHierarchy n m v scalarSpinTerminal
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular n m v
  have hD := ((hf.1.differentiable (by norm_num)) 0).hasDerivAt
  have hD' : HasDerivAt f (deriv f 0) (-(0:ℝ)) := by simpa only [neg_zero] using hD
  have H := hD'.comp (0:ℝ) (hasDerivAt_neg (0:ℝ))
  have he : (fun x => f (-x)) = f := funext (scalarHierarchy_spin_even n m v)
  change HasDerivAt (fun x => f (-x)) (deriv f 0 * (-1)) 0 at H
  rw [he] at H
  have hh := H.unique hD
  change deriv f 0 = 0
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarMomentLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_scalar_split (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (F G : ℝ → ℝ → ℝ) (c : ℝ) (z : ParameterSpace (a+b)) :
    hierarchyMomentLevel (a+b) m (scalarParameterTerminal (a+b) v F c)
      (scalarParameterTerminal (a+b) v G c) ⟨a,by omega⟩ z =
      scalarHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (F (parameter (a+b) z)) (G (parameter (a+b) z))
        (c+∑ i : Fin a, v (i.castAdd b)*coordinateProjection (a+b) (i.castAdd b) z) := by
  induction b generalizing F G with
  | zero =>
    have he : (⟨a,by omega⟩ : Fin (a+1))=Fin.last a := rfl
    rw [he]
    cases a with
    | zero => simp [hierarchyMomentLevel,scalarHierarchyAverage,scalarParameterTerminal,coordinateLinear]
    | succ a =>
      simp only [hierarchyMomentLevel,Fin.lastCases_last,scalarHierarchyAverage]
      change G (parameter (a+1) z) (c+coordinateLinear (a+1) v z) = _
      rw [coordinateLinear_apply]
      rfl
  | succ b ih =>
    change hierarchyMomentLevel (a+b+1) m (scalarParameterTerminal (a+b+1) v F c)
      (scalarParameterTerminal (a+b+1) v G c) (Fin.castSucc ⟨a,by omega⟩) z = _
    simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,
      gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
    rw [ih]
    change scalarHierarchyAverage b _ _ _ _ _ = scalarHierarchyAverage b _ _ _ _ _
    congr 1
    apply congrArg (c+·)
    apply Finset.sum_congr rfl
    intro i _
    have he : (i.castAdd b).castSucc=i.castAdd (b+1) := by ext; rfl
    rw [← he]
    change _ = v (i.castAdd b).castSucc * coordinateProjection (a+b+1) (i.castAdd b).castSucc z
    rw [coordinateProjection_castSucc]

theorem scalarHierarchyAverage_spin_abs_le_field (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (x : ℝ) :
    |scalarHierarchyAverage n m v scalarSpinTerminal scalarMagnetization x| ≤ |x| := by
  rw [← scalarHierarchy_gradient_average n m v scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt]
  change |rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x| ≤ |x|
  have H := (scalarHierarchy_spin_gradient_lipschitz n m v hm).norm_sub_le x 0
  have h0 : rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) 0=0 :=
    scalarHierarchy_spin_gradient_zero n m v
  simpa only [h0,sub_zero,Real.norm_eq_abs,NNReal.coe_one,one_mul] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSusceptibilitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpinParameter_eq (n : ℕ) (v : Fin n → ℝ) :
    scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
  rw [← scalarSpinTerminal_affine]
  funext z
  simp only [scalarParameterTerminal,zero_add,coordinateLinear_apply]

theorem scalarSpinRoot_gradient (n : ℕ) (v : Fin n → ℝ) :
    rootGradient n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v))=
      scalarParameterTerminal n v (fun a y => scalarMagnetization (a+y)) 0 := by
  rw [← scalarSpinParameter_eq]
  funext z
  have HE : scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      fun z => scalarSpinTerminal (scalarSpinField n v z) := by
    funext z
    simp only [scalarParameterTerminal,zero_add,scalarSpinField,add_apply]
  have HD := (scalarSpinTerminal_hasDerivAt (scalarSpinField n v z)).comp_hasFDerivAt z
    (scalarSpinField n v).hasFDerivAt
  have HD' : fderiv ℝ (fun z => scalarSpinTerminal (scalarSpinField n v z)) z=
      scalarMagnetization (scalarSpinField n v z) • scalarSpinField n v := by
    convert HD.fderiv using 1; rfl
  rw [rootGradient,HE,HD']
  simp only [smul_apply,smul_eq_mul,scalarSpinField,add_apply,parameter_axis,
    coordinateLinear_axis,add_zero,mul_one,scalarParameterTerminal,zero_add]

theorem scalarStepAverage_translate (m v c : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    scalarStepAverage m v (fun t => f (c+t)) (fun t => g (c+t)) x=
      scalarStepAverage m v f g (c+x) := by
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,add_assoc]

theorem scalarHierarchyAverage_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v (fun y => f (c+y)) (fun y => g (c+y)) x=
      scalarHierarchyAverage n m v f g (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage]
    rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
    exact ih _ _ _ _

theorem scalarMomentSquare_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (j : Fin (n+1)) (c x : ℝ) :
    scalarMomentSquare n m v (fun y => f (c+y)) (fun y => g (c+y)) j x=
      scalarMomentSquare n m v f g j (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_translate (n+1) m v f (fun x => (g x)^2) c x
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
      exact ih _ _ _ _ j

theorem scalarHierarchy_spin_hessian_overlap_sum (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
    rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x=
      1-∑ j, hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
  rw [scalarHierarchy_spin_eq,hierarchyPressure_rootHessian_overlap_sum n m hm hmono
    (affineLogPartition_boundedDerivs _ _) (scalarSpinRoot_curvature n v)
    (scalarSpinRoot_curvature_eq n v)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hf₀ := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v)
  have hM := hierarchyMomentLevel_bounded_continuous n m _ _ hf₀
    (rootGradient_continuous n hf₀) zero_le_one (fun z => (scalarSpinRoot_curvature n v |>.bounds z).1) j
  rw [← hierarchyAverage_eq_integral n m _ hf₀ (fun z =>
    (hierarchyMomentLevel n m _ _ j z)^2) (hM.1.pow 2) zero_le_one (fun z => by
    rw [norm_pow]
    simpa using (pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2)) x]
  rw [scalarSpinRoot_gradient n v,← scalarSpinParameter_eq n v]
  have hf : BoundedDerivs (scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0) := by
    rw [scalarSpinParameter_eq]
    exact affineLogPartition_boundedDerivs _ _
  have H := scalarMomentSquare_eq_parameterAverage n m v
    (fun a y => scalarSpinTerminal (a+y)) (fun a y => scalarMagnetization (a+y)) 0 x hf j
  have HE : scalarMomentSquare n m v (fun y => scalarSpinTerminal (x+y))
      (fun y => scalarMagnetization (x+y)) j 0=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
    simpa only [add_zero] using scalarMomentSquare_translate n m v scalarSpinTerminal scalarMagnetization j x 0
  exact (H.symm.trans HE)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpin_affineMoment (n : ℕ) (v : Fin n → ℝ) :
    affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin =
      rootGradient n (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)) := by
  funext z
  rw [rootGradient,fderiv_affineLogPartition_apply]
  congr 2
  funext b
  simp only [smul_apply,smul_eq_mul,scalarSpinField,add_apply,parameter_axis,coordinateLinear_axis,add_zero,mul_one]

theorem scalarMomentSquare_eq_path_integral (n : ℕ) (m v : Fin n → ℝ)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, (hierarchyMomentLevel n m
      (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
      (affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin) j z)^2
      ∂hierarchyPathLaw n m
        (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)) x)=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
  rw [scalarSpin_affineMoment]
  have hf₀ := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v)
  have hM := hierarchyMomentLevel_bounded_continuous n m _ _ hf₀
    (rootGradient_continuous n hf₀) zero_le_one (fun z => (scalarSpinRoot_curvature n v |>.bounds z).1) j
  rw [← hierarchyAverage_eq_integral n m _ hf₀ (fun z =>
    (hierarchyMomentLevel n m _ _ j z)^2) (hM.1.pow 2) zero_le_one (fun z => by
    rw [norm_pow]
    simpa using (pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2)) x]
  rw [scalarSpinRoot_gradient n v,← scalarSpinParameter_eq n v]
  have hf : BoundedDerivs (scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0) := by
    rw [scalarSpinParameter_eq]
    exact affineLogPartition_boundedDerivs _ _
  have H := scalarMomentSquare_eq_parameterAverage n m v
    (fun a y => scalarSpinTerminal (a+y)) (fun a y => scalarMagnetization (a+y)) 0 x hf j
  have HE : scalarMomentSquare n m v (fun y => scalarSpinTerminal (x+y))
      (fun y => scalarMagnetization (x+y)) j 0=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
    simpa only [add_zero] using scalarMomentSquare_translate n m v scalarSpinTerminal scalarMagnetization j x 0
  exact (H.symm.trans HE)

theorem affineHierarchyResponse_scalar (n : ℕ) (m v : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    affineHierarchyResponse n m (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v) spin i x = scalarFiniteResponse n m v i x := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs _ _) x
  have he : affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)
      (fun b => (spin b)^2) = fun _ => (1:ℝ) := by
    funext z
    have hs : (fun b : Bool => (spin b)^2)=fun _ => (1:ℝ) := by funext b; cases b <;> norm_num [spin]
    rw [hs]
    simp only [affineMoment,mul_one,affineGibbs_sum]
  unfold affineHierarchyResponse scalarFiniteResponse
  rw [he]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [scalarMomentSquare_eq_path_integral]

theorem scalarFiniteResponse_eq_hessian_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (i : Fin n) (x : ℝ) :
    scalarFiniteResponse n m v i x=
      rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x+
        ∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m 1 j*
          scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0 := by
  rw [scalarHierarchy_spin_hessian_overlap_sum n m v hm hmono]
  unfold scalarFiniteResponse
  have he : (∑ j : Fin (n+1), hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x)=
      (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0)+
      (∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i.val < j.val
    · simp only [ite_eq_left h,ite_eq_right (not_le.mpr h),add_zero]
    · simp only [ite_eq_right h,ite_eq_left (le_of_not_gt h),zero_add]
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEarlyMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem coordinateLinear_prefix_split (a b : ℕ) (v : Fin (a+b) → ℝ)
    (z : ParameterSpace (a+b)) :
    coordinateLinear (a+b) (scalarPrefixVector (a+b) v ⟨a,by omega⟩) z=
      ∑ i : Fin a, v (i.castAdd b)*coordinateProjection (a+b) (i.castAdd b) z := by
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [scalarPrefixVector,Fin.val_castAdd,Fin.val_natAdd]
  simp only [show ∀ i : Fin a, i.val < a from Fin.isLt,ite_true]
  have he (i : Fin b) : ¬ a+i.val < a := by omega
  simp only [he,ite_false,zero_mul,Finset.sum_const_zero,add_zero]

theorem hierarchyMomentLevel_spin_abs_le_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    |hierarchyMomentLevel n m
      (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
      (affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin) j z| ≤
      |parameter n z+coordinateLinear n (scalarPrefixVector n v j) z| := by
  rw [scalarSpin_affineMoment,scalarSpinRoot_gradient,← scalarSpinParameter_eq]
  rcases j with ⟨a,ha⟩
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ ha)
  subst n
  rw [hierarchyMomentLevel_scalar_split,coordinateLinear_prefix_split]
  simp only [zero_add]
  rw [scalarHierarchyAverage_translate]
  exact scalarHierarchyAverage_spin_abs_le_field b _ _ (fun i => hm _) _

theorem parameter_ae_hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (x : ℝ) :
    ∀ᵐ z ∂hierarchyPathLaw n m f x, parameter n z=x := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (parameter_ae_fiberGaussian n x)

theorem parameter_coordinateAxis (n : ℕ) (i : Fin n) : parameter n (coordinateAxis n i)=0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateAxis_last,parameter]
    · simpa only [coordinateAxis_castSucc,parameter,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'] using ih j

theorem scalarPrefix_square_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (n+1)) (x : ℝ) :
    (∫ z, (coordinateLinear n (scalarPrefixVector n v j) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x) ≤
      2*scalarPrefixVariance n v j+4*(scalarPrefixVariance n v j)^2 := by
  have H := affineHierarchy_square_bound n m hm hmono (fun _ : Bool => 0)
    (fun b => spin b • scalarSpinField n v) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun b i => by
      cases b <;> simp [spin,scalarSpinField,parameter_coordinateAxis,coordinateLinear_coordinateAxis]) x
    (scalarPrefixVector n v j)
  have he : (∑ i, |scalarPrefixVector n v j i| * |v i|)=scalarPrefixVariance n v j := by
    apply Finset.sum_congr rfl
    intro i _
    unfold scalarPrefixVector
    split_ifs
    · rw [← sq_abs]; ring
    · simp
  rw [he] at H
  change _ ≤ 2*scalarPrefixVariance n v j+(2*scalarPrefixVariance n v j)^2 at H
  nlinarith

theorem scalarMomentSquare_origin_le_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (n+1)) :
    scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0 ≤
      2*scalarPrefixVariance n v j+4*(scalarPrefixVariance n v j)^2 := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  let G := affineMoment (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v) spin
  let μ := hierarchyPathLaw n m f 0
  let L := coordinateLinear n (scalarPrefixVector n v j)
  have hf : BoundedDerivs f := affineLogPartition_boundedDerivs _ _
  have hG := affineMoment_continuous (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v) spin
  have hbG (z) : ‖G z‖ ≤ 1 := affineMoment_norm_le _ _ _ (by intro b; cases b <;> norm_num [spin]) z
  have hM := hierarchyMomentLevel_bounded_continuous n m f G hf hG zero_le_one hbG j
  have hiM : Integrable (fun z => (hierarchyMomentLevel n m f G j z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hM.1.pow 2) (C:=1) (fun z => by
      simp only [Pi.pow_apply,norm_pow]; simpa using pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2) 0
  have hiL : Integrable (fun z => (L z)^2) μ :=
    ((HasExpGrowth.linear L).pow 2).integrable_hierarchyPathLaw n m hf (L.continuous.pow 2) 0
  rw [← scalarMomentSquare_eq_path_integral]
  apply (integral_mono_ae hiM hiL ?_).trans (scalarPrefix_square_bound n m v hm hmono j 0)
  filter_upwards [parameter_ae_hierarchyPathLaw n m f 0] with z hz
  have H := hierarchyMomentLevel_spin_abs_le_prefix n m v hm j z
  rw [hz,zero_add] at H
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpatialAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchyAverage_abs_le {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {C : ℝ} (hg : ∀ z, |g z| ≤ C) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x| ≤ C := by
  induction n generalizing f g with
  | zero => exact hg x
  | succ n ih =>
    exact ih (scalarStep_regular hf _ _) (scalarStepAverage_bound hf hg _ _) _ _

theorem scalarHierarchyAverage_spatial_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L C : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hgC : ∀ z, |g z| ≤ C) (x y : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f g y| ≤
      ((L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)))*|x-y| := by
  have hExp : 1 ≤ Real.exp (2*(K:ℝ)) := Real.one_le_exp (by positivity)
  by_cases hd : |x-y| ≤ 1
  · have H := scalarHierarchyAverage_terminal_stability n m v hm hmono
      (hf.translate x) (hf.translate y) (by positivity : 0 ≤ (K:ℝ)*|x-y|)
      (fun z => by simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using
        hfK.norm_sub_le (x+z) (y+z))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      (hgL.continuous.comp (continuous_const.add continuous_id))
      C.coe_nonneg (fun z => hgC (x+z)) (fun z => hgC (y+z))
      (fun z => by simpa only [Function.comp_apply, Pi.add_apply, id_eq, Real.norm_eq_abs,add_sub_add_right_eq_sub] using
        hgL.norm_sub_le (x+z) (y+z)) 0
    change |scalarHierarchyAverage n m v (fun z => f (x+z)) (fun z => g (x+z)) 0 -
      scalarHierarchyAverage n m v (fun z => f (y+z)) (fun z => g (y+z)) 0| ≤ _ at H
    rw [scalarHierarchyAverage_translate,scalarHierarchyAverage_translate] at H
    simp only [add_zero] at H
    have E := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (2*(K:ℝ)))
      (by linarith : 0 ≤ 1-|x-y|) (abs_nonneg (x-y)) (by ring : 1-|x-y|+|x-y|=1)
    simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at E
    have Ee : Real.exp (2*((K:ℝ)*|x-y|))-1 ≤ Real.exp (2*(K:ℝ))*|x-y| := by
      rw [show 2*((K:ℝ)*|x-y|)=|x-y| *(2*(K:ℝ)) by ring]
      nlinarith [abs_nonneg (x-y)]
    have E2 := mul_le_mul_of_nonneg_left Ee (by positivity : 0 ≤ 2*(C:ℝ))
    nlinarith
  · have H := (abs_sub (scalarHierarchyAverage n m v f g x)
        (scalarHierarchyAverage n m v f g y)).trans
      (add_le_add (scalarHierarchyAverage_abs_le hf hgC n m v x)
        (scalarHierarchyAverage_abs_le hf hgC n m v y))
    have hlow : 2*(C:ℝ) ≤ (L:ℝ)+2*(C:ℝ)*Real.exp (2*(K:ℝ)) := by
      have := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 2*(C:ℝ))
      linarith [L.coe_nonneg]
    have H2 := hlow.trans (le_mul_of_one_le_right (by positivity) (le_of_not_ge hd))
    linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarResponseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPrefixVariance_nonneg (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) :
    0 ≤ scalarPrefixVariance n v j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem scalarPrefixVariance_monotone (n : ℕ) (v : Fin n → ℝ) :
    Monotone (scalarPrefixVariance n v) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  unfold scalarPrefixVector
  by_cases h : k.val < i.val
  · rw [ite_eq_left h,ite_eq_left (lt_of_lt_of_le h hij)]
  · rw [ite_eq_right h,zero_pow (by norm_num : 2≠0)]
    exact sq_nonneg _

theorem scalarFiniteResponse_origin_le (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (i : Fin n) :
    scalarFiniteResponse n m v i 0 ≤
      rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) 0+
        (2*scalarPrefixVariance n v i.castSucc+4*(scalarPrefixVariance n v i.castSucc)^2) := by
  rw [scalarFiniteResponse_eq_hessian_prefix n m v hm hmono]
  apply add_le_add_right
  let C := 2*scalarPrefixVariance n v i.castSucc+4*(scalarPrefixVariance n v i.castSucc)^2
  have hC : 0 ≤ C := by
    have hV := scalarPrefixVariance_nonneg n v i.castSucc
    dsimp [C]; positivity
  calc
    _ ≤ ∑ j : Fin (n+1), hierarchyAtom n m 1 j*C := by
      apply Finset.sum_le_sum
      intro j _
      have ha := hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
      split_ifs with hj
      · apply mul_le_mul_of_nonneg_left _ ha
        have hV := scalarPrefixVariance_monotone n v (show j ≤ i.castSucc from hj)
        have hsq := (sq_le_sq₀ (scalarPrefixVariance_nonneg n v j)
          (scalarPrefixVariance_nonneg n v i.castSucc)).mpr hV
        exact (scalarMomentSquare_origin_le_prefix n m v hm hmono j).trans (by
          dsimp [C]; nlinarith)
      · exact mul_nonneg ha hC
    _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem finiteClockPenalty_eq_double (n : ℕ) (m a : Fin n → ℝ) :
    finiteClockPenalty n m a=∑ i, ∑ j, a i*a j*m (max i j) := by
  classical
  have ht (i j : Fin n) : a i*a j*m (max i j)=
      (if i < j then m j*a j*a i else 0)+
      (if j < i then m i*a i*a j else 0)+(if i=j then m i*(a i)^2 else 0) := by
    rcases lt_trichotomy i j with hij|hij|hij
    · simp only [max_eq_right (le_of_lt hij),ite_eq_left hij,
        ite_eq_right (not_lt_of_ge (le_of_lt hij)),ite_eq_right (ne_of_lt hij)]
      ring
    · subst j; simp; ring
    · simp only [max_eq_left (le_of_lt hij),ite_eq_left hij,
        ite_eq_right (not_lt_of_ge (le_of_lt hij)),ite_eq_right (ne_of_gt hij)]
      ring
  have hs : (∑ i : Fin n, ∑ j : Fin n, if i < j then m j*a j*a i else 0)=
      ∑ i : Fin n, ∑ j : Fin n, if j < i then m i*a i*a j else 0 := Finset.sum_comm
  rw [show (∑ i, ∑ j, a i*a j*m (max i j))=
      (∑ i, ∑ j, if i < j then m j*a j*a i else 0)+
      (∑ i, ∑ j, if j < i then m i*a i*a j else 0)+∑ i, m i*(a i)^2 by
    simp_rw [ht,Finset.sum_add_distrib]
    simp]
  rw [hs]
  unfold finiteClockPenalty
  rw [← Finset.sum_sub_distrib]
  have hl (i : Fin n) : m i*((∑ j, if j < i then a j else 0)+a i)^2-
      m i*(∑ j, if j < i then a j else 0)^2=
      2*(∑ j, if j < i then m i*a i*a j else 0)+m i*(a i)^2 := by
    have he : (∑ j, if j < i then m i*a i*a j else 0)=m i*a i*(∑ j, if j < i then a j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [he]; ring
  simp_rw [hl,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem scalarHierarchy_weighted_increment_square (n : ℕ) (m v k : Fin n → ℝ) (x : ℝ) :
    (∫ z, (coordinateLinear n (fun i => k i*v i) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x)=
      (∑ i, (k i)^2*(v i)^2)+
      ∑ i, ∑ j, k i*k j*(v i)^2*(v j)^2*m (max i j)*
        scalarFiniteResponse n m v (min i j) x := by
  have hu (b : Bool) (i : Fin n) :
      (spin b • scalarSpinField n v) (coordinateAxis n i)=v i*spin b := by
    simp only [smul_apply,smul_eq_mul,scalarSpinField,
      add_apply,parameter_coordinateAxis,coordinateLinear_coordinateAxis,zero_add]
    ring
  have H := affineHierarchy_weighted_increment_square n m (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v) spin v k hu x
  simp only [affineHierarchyResponse_scalar] at H
  simpa only [coordinateLinear_apply] using H

theorem scalarHierarchy_weighted_increment_square_le (n : ℕ) (m v k : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hk : ∀ i, 0 ≤ k i) (x R : ℝ)
    (hR : ∀ i, k i≠0 → scalarFiniteResponse n m v i x ≤ R) :
    (∫ z, (coordinateLinear n (fun i => k i*v i) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x) ≤
      (∑ i, (k i)^2*(v i)^2)+R*finiteClockPenalty n m (fun i => k i*(v i)^2) := by
  rw [scalarHierarchy_weighted_increment_square,finiteClockPenalty_eq_double]
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have ha : 0 ≤ k i*k j*(v i)^2*(v j)^2*m (max i j) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hk i) (hk j)) (sq_nonneg _)) (sq_nonneg _)) (hm _)
  by_cases hi : k i=0
  · simp [hi]
  by_cases hj : k j=0
  · simp [hj]
  have H := mul_le_mul_of_nonneg_left (hR (min i j) (by
    rcases le_total i j with h|h
    · simpa only [min_eq_left h] using hi
    · simpa only [min_eq_right h] using hj)) ha
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarWeightedVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarWeightedAverage_integral (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    scalarWeightedAverage n m v a f x=
      ∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have he (z : ParameterSpace n) :
      (parameter n z, (0:ℝ)) + ∑ i, coordinateProjection n i z • (v i,a i)=
        (scalarSpinField n v z,coordinateLinear n a z) := by
    have hfst := map_sum (ContinuousLinearMap.fst ℝ ℝ ℝ) (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    have hsnd := map_sum (ContinuousLinearMap.snd ℝ ℝ ℝ) (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    have heq : (∑ i, coordinateProjection n i z • (v i,a i)) =
        (∑ i, v i*coordinateProjection n i z, ∑ i, a i*coordinateProjection n i z) := by
      apply Prod.ext
      · simpa only [ContinuousLinearMap.coe_fst',Prod.smul_fst,smul_eq_mul,mul_comm] using hfst
      · simpa only [ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,mul_comm] using hsnd
    rw [heq]
    simp [scalarSpinField,coordinateLinear_apply]
  have H := congrFun (hierarchyAverage_vector_linear n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (fun x => (x,0))) x
  simp only [he] at H
  unfold scalarWeightedAverage
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v))
    _ ((coordinateLinear n a).continuous.pow 2) ((HasExpGrowth.linear _).pow 2) x

theorem scalarWeightedAverage_nonneg (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    0 ≤ scalarWeightedAverage n m v a f x := by
  rw [scalarWeightedAverage_integral n m v a hf x]
  exact integral_nonneg (fun z => sq_nonneg _)

theorem scalarWeightedAverage_le (n : ℕ) (m v a : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) (x : ℝ) :
    scalarWeightedAverage n m v a f x ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| * |v i|)^2 := by
  rw [scalarWeightedAverage_integral n m v a hf x]
  apply hierarchy_square_bound n m hm hmono _ (hf.compCLM (scalarSpinField n v))
    (fun i => |v i|) (fun i => abs_nonneg _) _ x a
  intro z i
  have H := scalar_composition_coordinate_bound hf hL (scalarSpinField n v) z (coordinateAxis n i)
  simpa only [Function.comp_def,scalarSpinField,add_apply,parameter_coordinateAxis,coordinateLinear_coordinateAxis,zero_add] using H

theorem scalarWeightedAverage_spin_le (n : ℕ) (m v k : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hk : ∀ i,0 ≤ k i) (x R : ℝ)
    (hR : ∀ i,k i≠0 → scalarFiniteResponse n m v i x ≤ R) :
    scalarWeightedAverage n m v (fun i => k i*v i) scalarSpinTerminal x ≤
      (∑ i, (k i)^2*(v i)^2)+R*finiteClockPenalty n m (fun i => k i*(v i)^2) := by
  rw [scalarWeightedAverage_integral n m v _ scalarSpinTerminal_regular x]
  have he : scalarSpinTerminal ∘ scalarSpinField n v=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
    simpa only [Function.comp_def,scalarSpinField,add_apply,coordinateLinear_apply] using scalarSpinTerminal_affine n v
  rw [he]
  exact scalarHierarchy_weighted_increment_square_le n m v k hm hk x R hR

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem finiteClockPenalty_eq_chain (n : ℕ) (m a : Fin n → ℝ) :
    finiteClockPenalty n m a=chainPotentialPenalty (fun x : ℝ => x^2) (List.ofFn (fun i => (m i,a i))) 0 := by
  rw [chainPotentialPenalty_ofFn]
  simp only [finiteClockPenalty,strictPrefix,zero_add,Finset.sum_sub_distrib,mul_sub]

theorem weightedCrossPenalty_get (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty w 0=finiteClockPenalty w.length (fun i => (w.get i).1)
      (fun i => (w.get i).2.1*(w.get i).2.2) := by
  rw [finiteClockPenalty_eq_chain]
  unfold weightedCrossPenalty
  congr 1
  simpa only [List.ofFn_get,Function.comp_def] using
    (List.map_ofFn (f:=w.get) (g:=fun p => (p.1,p.2.1*p.2.2)))

theorem weightedList_spin_response_le (w : List (ℝ × (ℝ × ℝ))) (k : Fin w.length → ℝ)
    (hm : ∀ p∈w,0≤p.1) (hk : ∀ i,0≤k i)
    (he : ∀ i,(w.get i).2.2=k i*(w.get i).2.1) (R : ℝ)
    (hR : ∀ i,k i≠0 → scalarFiniteResponse w.length (fun j => (w.get j).1)
      (fun j => (w.get j).2.1) i 0≤R) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+R*weightedCrossPenalty w 0 := by
  rw [vectorIncrementAverage_get]
  have H := scalarWeightedAverage_spin_le w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1) k
    (fun i => hm _ (List.get_mem w i)) hk 0 R hR
  have hev : (fun i : Fin w.length => ((w.get i).2.1,k i*(w.get i).2.1))=fun i => (w.get i).2 := by
    funext i; rw [← he i]
  have hs : (∑ i : Fin w.length,(k i)^2*((w.get i).2.1)^2)=weightedVariance w := by
    simp_rw [← mul_pow,← he]
    exact sum_get_map w (fun p => p.2.2^2)
  have hp : finiteClockPenalty w.length (fun i => (w.get i).1) (fun i => k i*((w.get i).2.1)^2)=
      weightedCrossPenalty w 0 := by
    rw [weightedCrossPenalty_get]
    congr 1
    funext i; rw [he i]; ring
  simpa only [scalarWeightedAverage,hev,hs,hp] using H

theorem weightedList_spin_early_le (w : List (ℝ × (ℝ × ℝ))) (k : Fin w.length → ℝ)
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    (hk : ∀ i,0≤k i) (he : ∀ i,(w.get i).2.2=k i*(w.get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance w.length (fun j => (w.get j).2.1) i.castSucc≤V) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+(rootHessian 0 (scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal) 0+
        (2*V+4*V^2))*weightedCrossPenalty w 0 := by
  apply weightedList_spin_response_le w k (fun p hp => (hm p hp).1) hk he
  intro i hi
  have H := scalarFiniteResponse_origin_le w.length (fun j => (w.get j).1) (fun j => (w.get j).2.1)
    (fun j => hm _ (List.get_mem w j)) (mass_get_monotone hs) i
  have Hsq := (sq_le_sq₀ (scalarPrefixVariance_nonneg w.length (fun j => (w.get j).2.1) i.castSucc) hV).mpr (hactive i hi)
  have hchain : scalarHierarchy w.length (fun j => (w.get j).1) (fun j => (w.get j).2.1) scalarSpinTerminal=
      scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal := by
    rw [← scalarIncrementChain_ofFn]
    congr 1
    simpa only [List.ofFn_get,Function.comp_def,weightedUnderlying] using
      (List.map_ofFn (f:=w.get) (g:=fun p => (p.1,p.2.1))).symm
  rw [hchain] at H
  nlinarith [hactive i hi]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedAugment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem weightedCrossPenalty_append (l r : List (ℝ × (ℝ × ℝ))) (g : ℝ) :
    weightedCrossPenalty (l++r) g=weightedCrossPenalty l g+weightedCrossPenalty r (g+weightedCross l) := by
  simp only [weightedCrossPenalty,List.map_append,chainPotentialPenalty_append,chainSum,
    List.map_map,weightedCross,Function.comp_def]

@[simp] theorem weightedCrossPenalty_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedCrossPenalty (zeroWeightChain c++w++zeroWeightChain t) 0=weightedCrossPenalty w 0 := by
  simp [weightedCrossPenalty_append]

theorem weighted_mass_iff (w : List (ℝ × (ℝ × ℝ))) {P : ℝ → Prop} :
    (∀ p∈w,P p.1) ↔ ∀ p∈weightedUnderlying w,P p.1 := by
  constructor
  · intro H p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact H q hq
  · intro H p hp; exact H _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem weighted_sorted_iff (w : List (ℝ × (ℝ × ℝ))) :
    w.Pairwise (fun p q => p.1≤q.1) ↔ (weightedUnderlying w).Pairwise (fun p q => p.1≤q.1) := by
  simp only [weightedUnderlying,List.pairwise_map]

theorem weightedFull_spin_early_le (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (k : Fin (zeroWeightChain c++w++zeroWeightChain t).length → ℝ) (hk : ∀ i,0≤k i)
    (he : ∀ i,((zeroWeightChain c++w++zeroWeightChain t).get i).2.2=
      k i*((zeroWeightChain c++w++zeroWeightChain t).get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain c++w++zeroWeightChain t).length
      (fun j => ((zeroWeightChain c++w++zeroWeightChain t).get j).2.1) i.castSucc≤V) :
    vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
      (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)≤
      weightedVariance w+(rootHessian 0 (scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal) 0+
        (2*V+4*V^2))*weightedCrossPenalty w 0 := by
  have H := weightedList_spin_early_le (zeroWeightChain c++w++zeroWeightChain t) k
    ((weighted_mass_iff _).mpr (by simpa using hm))
    ((weighted_sorted_iff _).mpr (by simpa using hs)) hk he hV hactive
  simpa only [weightedUnderlying_append,weightedUnderlying_zeroWeight,weightedVariance_full,
    weightedCrossPenalty_full] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarListBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarIncrementChain_lipschitz (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,0≤p.1) {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hL : LipschitzWith K f) :
    LipschitzWith K (scalarIncrementChain l f) := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_lipschitz _ _ _ (fun i => hm _ (List.get_mem l i)) hf hL

theorem scalarIncrementChain_spin_convex (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) : ScalarSpinConvex (scalarIncrementChain l scalarSpinTerminal) := by
  rw [scalarIncrementChain_get]
  intro x
  have H := (scalarHierarchy_spin_derivative_bounds l.length (fun i => (l.get i).1)
    (fun i => (l.get i).2) (fun i => hm _ (List.get_mem l i)) x).2
  exact ⟨H.1.le,H.2⟩

theorem scalarIncrementChain_hessian_lipschitz (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    LipschitzWith susceptibilityLipschitzConstant (rootHessian 0 (scalarIncrementChain l scalarSpinTerminal)) := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_spin_hessian_lipschitz _ _ _ (fun i => hm _ (List.get_mem l i)) (mass_get_monotone hs)

theorem scalarIncrementAverage_bounded (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) : BoundedScalar (scalarIncrementAverage l f g) := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_bounded hf hg _ _ _

theorem scalarIncrementAverage_nonneg (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hpos : ∀ x,0≤g x) (x : ℝ) :
    0 ≤ scalarIncrementAverage l f g x := by
  rw [scalarIncrementAverage_get,scalarHierarchyAverage_integral hf hg]
  exact integral_nonneg (fun _ => hpos _)

theorem weightedAverage_nonneg (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) (x : ℝ) :
    0≤vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0) := by
  rw [vectorIncrementAverage_get]
  have h : (fun i : Fin w.length => ((w.get i).2.1,(w.get i).2.2))=fun i => (w.get i).2 := rfl
  simpa only [scalarWeightedAverage,h] using
    scalarWeightedAverage_nonneg w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
      (fun i => (w.get i).2.2) hf x

theorem weightedMomentBound_nonneg (w : List (ℝ × (ℝ × ℝ))) : 0≤weightedMomentBound w := by
  have H : 0≤weightedVariance w := List.sum_nonneg (by intro a ha; obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha; exact sq_nonneg _)
  dsimp [weightedMomentBound]; positivity

theorem weightedAverage_abs_le (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)|≤weightedMomentBound w := by
  rw [abs_of_nonneg (weightedAverage_nonneg w hf x),vectorIncrementAverage_get]
  have H := scalarWeightedAverage_le w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => (w.get i).2.2) (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hL x
  rw [sum_get_map w (fun p => p.2.2^2),sum_get_map w (fun p => |p.2.2| * |p.2.1|)] at H
  exact H

theorem weightedAverage_bounded (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1≤q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hL : LipschitzWith 1 f) :
    BoundedScalar (fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)) := by
  have H := (vectorIncrementAverage_regular w (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ))
    (continuous_snd.pow 2) ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2)).1
  exact ⟨H.comp (continuous_id.prodMk continuous_const),weightedMomentBound w,
    weightedMomentBound_nonneg w,weightedAverage_abs_le w hm hs hf hL⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleDecoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleBaseQuadratic_decoupling (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    |tripleBaseQuadratic c w t-tripleSusceptibility c w t*
      vectorIncrementAverage (zeroWeightChain c++w++zeroWeightChain t)
        (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2^2) (0,0)|≤tripleCommonError c w := by
  have hmc : ∀ p∈c,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_left _ (List.mem_append_left _ hp))
  have hmw : ∀ p∈weightedUnderlying w,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_left _ (List.mem_append_right _ hp))
  have hmt : ∀ p∈t,p.1∈Icc (0:ℝ) 1 := fun p hp => hm p (List.mem_append_right _ hp)
  have hs0 := List.pairwise_append.mp hs
  have hs1 := List.pairwise_append.mp hs0.1
  have hww : ∀ p∈w,p.1∈Icc (0:ℝ) 1 := fun p hp => hmw _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hsw : w.Pairwise (fun p q => p.1≤q.1) := by
    simpa only [weightedUnderlying,List.pairwise_map] using hs1.2.1
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  let A := scalarIncrementAverage (weightedUnderlying w) f (rootHessian 0 f)
  let B := fun x => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)
  have hf : BoundedDerivs f := scalarIncrementChain_regular _ scalarSpinTerminal_regular
  have hfL : LipschitzWith 1 f := scalarIncrementChain_lipschitz t (fun p hp => (hmt p hp).1)
    scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  have hFL : LipschitzWith 1 F := scalarIncrementChain_lipschitz _ (fun p hp => (hmw p hp).1) hf hfL
  have hfc : ScalarSpinConvex f := scalarIncrementChain_spin_convex t hmt
  have hA : BoundedScalar A := scalarIncrementAverage_bounded _ hf (hfc.hessian_bounded hf)
  have hB : BoundedScalar B := weightedAverage_bounded w hww hsw hf hfL
  have hAL (x : ℝ) : |A x-A 0|≤((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*|x| := by
    have H := scalarHierarchyAverage_spatial_bound (weightedUnderlying w).length
      (fun i => ((weightedUnderlying w).get i).1) (fun i => ((weightedUnderlying w).get i).2)
      (fun i => hmw _ (List.get_mem _ i)) (mass_get_monotone hs1.2.1) hf hfL
      (scalarIncrementChain_hessian_lipschitz t hmt hs0.2.1) (C:=1) (fun z => (hfc.bounds z).2) x 0
    simpa only [← scalarIncrementAverage_get,NNReal.coe_one,mul_one,sub_zero,A] using H
  have H := scalarHierarchyAverage_covariance_small c.length (fun i => (c.get i).1) (fun i => (c.get i).2)
    (fun i => hmc _ (List.get_mem c i)) (mass_get_monotone hs1.1) hF hFL hA hB
    (weightedMomentBound_nonneg w) (show 0≤(susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2 by positivity)
    (weightedAverage_abs_le w hww hsw hf hfL) hAL
  rw [sum_get_map c (fun p => p.2^2)] at H
  simp only [← scalarIncrementAverage_get] at H
  rw [weightedFull_average c w t scalarSpinTerminal_regular]
  unfold tripleBaseQuadratic tripleSusceptibility tripleCommonError
  rw [scalarIncrementAverage_append]
  simpa only [A,B,F,f,rawVariance,mul_comm] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ProductBranchMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
section Map
variable {E F E' F' : Type}

theorem mergedProductBranches_map (f : E → E') (g : F → F') (l : List (ℝ × E)) (r : List (ℝ × F)) :
    (mergedProductBranches l r).map (mapProductIncrement f g)=
      mergedProductBranches (l.map (fun p => (p.1,f p.2))) (r.map (fun p => (p.1,g p.2))) := by
  unfold mergedProductBranches
  rw [List.map_merge (s:=fun p q => decide (productMass p≤productMass q))
    (by intro a ha b hb; simp only [productMass_map])]
  simp only [List.map_map,Function.comp_def,mapProductIncrement,Sum.map_inl,Sum.map_inr]
end Map

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

theorem weightedUnderlying_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (scaleIncrementChain β w)=scaleIncrementChain β (weightedUnderlying w) := by
  simp only [weightedUnderlying,scaleIncrementChain,List.map_map,Function.comp_def,Prod.smul_fst]

theorem tripleCommonSchedule_scale (β : ℝ) (c : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleCommonSchedule c)=tripleCommonSchedule (scaleIncrementChain β c) := by
  simp only [scaleIncrementChain,tripleCommonSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  · funext i; fin_cases i <;> rfl

theorem tripleMiddleSchedule_scale (β δ : ℝ) (l : List TripleMiddleIncrement) :
    scaleIncrementChain β (tripleMiddleSchedule δ l)=
      tripleMiddleSchedule δ (l.map (mapProductIncrement (fun x : ℝ × ℝ => β • x) (fun x : ℝ => β • x))) := by
  simp only [scaleIncrementChain,tripleMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · simp only [Function.comp_def,productMass_map]
  · cases p <;> ext i <;> fin_cases i <;>
      norm_num [Function.comp_def,mapProductIncrement,tripleMiddleVector,smul_eq_mul] <;> ring

theorem tripleTailBlock_scale (β : ℝ) (p : ℝ × ℝ) :
    scaleIncrementChain β (tripleTailBlock p)=tripleTailBlock (p.1,β*p.2) := by
  simp only [scaleIncrementChain,tripleTailBlock,List.map_cons,List.map_nil]
  have h0 : β • ![p.2,0,0]=![β*p.2,0,0] := by ext i; fin_cases i <;> simp
  have h1 : β • ![0,p.2,0]=![0,β*p.2,0] := by ext i; fin_cases i <;> simp
  have h2 : β • ![0,0,p.2]=![0,0,β*p.2] := by ext i; fin_cases i <;> simp
  rw [h0,h1,h2]

theorem tripleTailSchedule_scale (β : ℝ) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleTailSchedule t)=tripleTailSchedule (scaleIncrementChain β t) := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change scaleIncrementChain β (tripleTailBlock p++tripleTailSchedule t)=
      tripleTailBlock (p.1,β*p.2)++tripleTailSchedule (scaleIncrementChain β t)
    rw [scaleIncrementChain_append,tripleTailBlock_scale,ih]

theorem tripleSchedule_scale (β δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    scaleIncrementChain β (tripleSchedule δ c w t)=
      tripleSchedule δ (scaleIncrementChain β c) (scaleIncrementChain β w) (scaleIncrementChain β t) := by
  simp only [tripleSchedule,scaleIncrementChain_append,tripleCommonSchedule_scale,tripleMiddleSchedule_scale,
    tripleTailSchedule_scale,mergedProductBranches_map,weightedUnderlying_scale]
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScaleStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem weightedCrossPenalty_scale (β g : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty (scaleIncrementChain β w) (β^2*g)=β^4*weightedCrossPenalty w g := by
  induction w generalizing g with
  | nil => simp [weightedCrossPenalty,scaleIncrementChain,chainPotentialPenalty]
  | cons p w ih =>
    change p.1*((β^2*g+(β*p.2.1)*(β*p.2.2))^2-(β^2*g)^2)+
      weightedCrossPenalty (scaleIncrementChain β w) (β^2*g+(β*p.2.1)*(β*p.2.2))=
        β^4*(p.1*((g+p.2.1*p.2.2)^2-g^2)+weightedCrossPenalty w (g+p.2.1*p.2.2))
    rw [show β^2*g+(β*p.2.1)*(β*p.2.2)=β^2*(g+p.2.1*p.2.2) by ring,ih]
    ring

@[simp] theorem weightedCrossPenalty_scale_zero (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCrossPenalty (scaleIncrementChain β w) 0=β^4*weightedCrossPenalty w 0 := by
  simpa only [mul_zero] using weightedCrossPenalty_scale β 0 w

theorem scaleIncrementChain_mass {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E)) {P : ℝ → Prop}
    (hm : ∀ p∈l,P p.1) : ∀ p∈scaleIncrementChain β l,P p.1 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hm q hq

theorem scaleIncrementChain_sorted {E : Type} [SMul ℝ E] (β : ℝ) (l : List (ℝ × E))
    (hs : l.Pairwise (fun p q => p.1≤q.1)) : (scaleIncrementChain β l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [scaleIncrementChain,List.pairwise_map] using hs

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleQuadraticPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleSusceptibility_nonneg (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈t,p.1∈Icc (0:ℝ) 1) : 0 ≤ tripleSusceptibility c w t := by
  have hf := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hc := scalarIncrementChain_spin_convex t hm
  exact scalarIncrementAverage_nonneg _ hf (hc.hessian_bounded hf) (fun x => (hc x).1) 0

theorem tripleConstrainedPressure_quadratic_oai {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w)))))
    (k : Fin (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length → ℝ)
    (hk : ∀ i,0≤k i)
    (he : ∀ i,((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.2=
      k i*((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get i).2.1)
    {V : ℝ} (hV : 0≤V)
    (hactive : ∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).length
      (fun j => ((zeroWeightChain (scaleIncrementChain β c)++scaleIncrementChain β w++zeroWeightChain (scaleIncrementChain β t)).get j).2.1) i.castSucc≤V)
    {a : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*β^2*weightedVariance w+(2*β^2*weightedAbsCross w)^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      3*(scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0-
        β^2/4*rawPenalty (c++weightedUnderlying w++t) 0)+
      δ^2*tripleQuadraticCoefficient β V c w t+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*(weightedVariance w)^2 := by
  let c' := scaleIncrementChain β c
  let w' := scaleIncrementChain β w
  let t' := scaleIncrementChain β t
  have hall : c'++weightedUnderlying w'++t'=scaleIncrementChain β (c++weightedUnderlying w++t) := by
    simp only [c',w',t',scaleIncrementChain_append,weightedUnderlying_scale]
  have hm' : ∀ p∈c'++weightedUnderlying w'++t',p.1∈Icc (0:ℝ) 1 := by
    rw [hall]; exact scaleIncrementChain_mass β _ hm
  have hs' : (c'++weightedUnderlying w'++t').Pairwise (fun p q => p.1≤q.1) := by
    rw [hall]; exact scaleIncrementChain_sorted β _ hs
  have hmt : ∀ p∈t',p.1∈Icc (0:ℝ) 1 := fun p hp => hm' p (List.mem_append_right _ hp)
  have hχ := tripleSusceptibility_nonneg c' w' t' hmt
  have HB := weightedFull_spin_early_le c' w' t' hm' hs' k hk he hV hactive
  have HD := tripleBaseQuadratic_decoupling c' w' t' hm' hs'
  have HQ : tripleBaseQuadratic c' w' t' ≤
      tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w' := by
    have H := (abs_le.mp HD).2
    have H' := mul_le_mul_of_nonneg_left HB hχ
    linarith
  have HE := tripleSchedule_value_expansion c' w' t' hm' hs' ha hδ hδ1 (by
    simpa only [w',weightedVariance_scale,weightedAbsCross_scale,mul_assoc] using hsmall)
  have HP := tripleConstrainedPressure_schedule hN β δ c w t hm hs ht hg hD
  change matrixConstrainedPressure N 3 β _ ≤ vectorIncrementChain (scaleIncrementChain β (tripleSchedule δ c w t)) _ 0-_-_+_ at HP
  rw [tripleSchedule_scale] at HP
  change matrixConstrainedPressure N 3 β _ ≤ vectorIncrementChain (tripleSchedule δ c' w' t') _ 0-_-_+_ at HP
  have HVE : vectorIncrementChain (tripleSchedule δ c' w' t') (fun x => ∑ u,scalarSpinTerminal (x u)) 0 ≤
      3*scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal 0+
      δ^2*(tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w')+
      tripleExpansionConstant a*|δ|^3 := HE.trans (by
    linarith [mul_le_mul_of_nonneg_left HQ (sq_nonneg δ)])
  rw [hall] at HVE
  have HA : vectorIncrementChain (tripleSchedule δ c' w' t') (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+β^2*δ^4*(weightedVariance w)^2 ≤
      (3*scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal 0+
      δ^2*(tripleSusceptibility c' w' t'*(weightedVariance w'+
        (rootHessian 0 (scalarIncrementChain (c'++weightedUnderlying w'++t') scalarSpinTerminal) 0+
          (2*V+4*V^2))*weightedCrossPenalty w' 0)+tripleCommonError c' w')+
      tripleExpansionConstant a*|δ|^3)-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+β^2*δ^4*(weightedVariance w)^2 := by
    rw [hall]; linarith
  apply (HP.trans HA).trans
  apply le_of_eq
  simp only [hall,w',weightedVariance_scale,weightedCrossPenalty_scale_zero,tripleQuadraticCoefficient,c',t']
  ring

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.tripleConstrainedPressure_quadratic_oai := @OAI.SK.Analytic.tripleConstrainedPressure_quadratic_oai
