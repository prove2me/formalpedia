-- Prove2me | solution 1 for OAI.SK.Analytic.fourBlockQuadratic_tent_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:06:18.547567+00:00
-- url     : https://prove2.me/submissions/4a3e10e0-1b66-4949-88f2-5b6e62e24482

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_StronglyConvexVariance
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
namespace SK.Analytic

section HessianComposition
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hessian_comp_linear (V : F → ℝ) (hV : ContDiff ℝ 2 V) (T : E →L[ℝ] F)
    (x u v : E) : Hessian (fun z => V (T z)) x u v = Hessian V (T x) (T u) (T v) := by
  have hD : fderiv ℝ (fun z => V (T z)) = fun z => (fderiv ℝ V (T z)).comp T := by
    funext z
    exact ((hV.differentiable (by norm_num) (T z)).hasFDerivAt.comp z T.hasFDerivAt).fderiv
  have hdV := (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd := ((hdV (T x)).hasFDerivAt.comp x T.hasFDerivAt).clm_comp (hasFDerivAt_const T x)
  simp only [Function.comp_def] at hd
  rw [Hessian, hD, hd.fderiv]
  simp [Hessian]

end HessianComposition

end SK.Analytic

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

section Directional
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.directionalGradient_bounds {F : E → ℝ} (hF : BoundedDerivs F) (u : E) :
    HasExpGrowth (directionalGradient F u) ∧ HasExpGrowth (fderiv ℝ (directionalGradient F u)) := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hF
  constructor
  · exact (HasExpGrowth.of_bounded hC hb).derivative_eval u
  · apply HasExpGrowth.of_bounded (mul_nonneg hD (norm_nonneg u))
    intro z
    rw [fderiv_directionalGradient F hc]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD (norm_nonneg u))
    intro v
    calc
      ‖(fderiv ℝ (fderiv ℝ F) z).flip u v‖ ≤
          ‖fderiv ℝ (fderiv ℝ F) z v‖*‖u‖ := (fderiv ℝ (fderiv ℝ F) z v).le_opNorm u
      _ ≤ (D*‖v‖)*‖u‖ := mul_le_mul_of_nonneg_right
          (((fderiv ℝ (fderiv ℝ F) z).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (hbb z) (norm_nonneg v))) (norm_nonneg u)
      _ = _ := by ring
end Directional

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

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem HasExpGrowth.fderiv_mul {f g : E → ℝ} (hc : Differentiable ℝ f) (hcg : Differentiable ℝ g)
    (hf : HasExpGrowth f) (hg : HasExpGrowth g) (hdf : HasExpGrowth (fderiv ℝ f))
    (hdg : HasExpGrowth (fderiv ℝ g)) : HasExpGrowth (fderiv ℝ (fun z => f z*g z)) := by
  have he : fderiv ℝ (fun z => f z*g z) = fun z => g z • fderiv ℝ f z+f z • fderiv ℝ g z := by
    funext z
    rw [fderiv_fun_mul (hc z) (hcg z)]
    exact add_comm _ _
  rw [he]
  exact (hg.smul hdf).add (hf.smul hdg)

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
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_last (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) : hierarchyLevel n m f (Fin.last n) = f := by
  cases n with
  | zero => rfl
  | succ n => simp only [hierarchyLevel,Fin.lastCases_last]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianStepSandwich
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasExpGrowth.integrable_gaussianStepLaw {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : HasExpGrowth g) (hc : Continuous g) (m : ℝ) (x : E) :
    Integrable (fun y => g (x,y)) (gaussianStepLaw m f x) := by
  rw [gaussianStepLaw,integrable_tilted_iff (hf.exp_integrable m x)]
  exact (((hf.exp_growths m).1).smul hg).integrable_gaussian_section
    ((Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)).smul hc) x

end

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

end
end SK.Analytic

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

theorem hierarchyPathLogDensity_regular (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) : BoundedDerivs (hierarchyPathLogDensity n m f) := by
  convert hf.add ((hierarchyPenalty_boundedDerivs n m 1 f hf).const_mul (-1)) using 1
  all_goals try with_reducible_and_instances rfl
  funext z; dsimp only [hierarchyPathLogDensity]; ring

end

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_AffineCoordinateMean
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

theorem affineHierarchy_coordinate_mean (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s,U s (coordinateAxis n i)=a*g s) (x : ℝ) :
    (∫ z, coordinateProjection n i z ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      a*m i*(∫ z, affineMoment c U g z ∂hierarchyPathLaw n m (affineLogPartition c U) x) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let M := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  let B := ∑ s, ‖g s‖
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖≤B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hcG := affineMoment_continuous c U g
  have hbG := affineMoment_norm_le c U g hb
  have hM (k) := hierarchyMomentLevel_bounded_continuous n m f G hf hcG hB hbG k
  have hiG : Integrable G μ := hierarchyPathLaw_integrable n m f G hf hcG hbG x
  have hmean (k : Fin (n+1)) : (∫ z, M k z ∂μ)=∫ z, G z ∂μ := by
    rw [← hierarchyAverage_eq_integral n m f hf (M k) (hM k).1 hB (hM k).2,
      ← hierarchyAverage_eq_integral n m f hf G hcG hB hbG]
    exact hierarchyAverage_momentLevel n m f G hf k x
  have hdConst : HasExpGrowth (fderiv ℝ (fun _ : ParameterSpace n => (1:ℝ))) := by
    have he : fderiv ℝ (fun _ : ParameterSpace n => (1:ℝ)) = fun _ => 0 := funext (fun _ => fderiv_const_apply 1)
    rw [he]
    exact HasExpGrowth.const 0
  have H := fiberGaussian_tilted_weighted_stein n (hierarchyPathLogDensity n m f)
    (fun _ => (1:ℝ)) (hierarchyPathLogDensity_regular n m hf) contDiff_const
    (HasExpGrowth.const 1) hdConst x i
  rw [← hierarchyPathLaw_eq_tilted n m f hf x] at H
  simp only [mul_one,one_mul,fderiv_const_apply,zero_apply,integral_zero,zero_add] at H
  have hJ (k : Fin (n+1)) : Integrable (fun z =>
      if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) μ := by
    by_cases hik : i.val<k.val
    · simp only [ite_eq_left hik]
      exact (hierarchyPathLaw_integrable n m f (M k) hf (hM k).1 (hM k).2 x).const_mul _
    · simp only [ite_eq_right hik]; exact integrable_const 0
  have he (z) : fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i)=
      a*(G z-∑ k : Fin (n+1), if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) :=
    affineHierarchy_score_coordinate n m c U g a i hU z
  have hsum : (∑ k : Fin (n+1), ∫ z, (if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) ∂μ)=
      (1-m i)*(∫ z, G z ∂μ) := by
    rw [← hierarchyAtom_tail_sum n m 1 i,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i.val<k.val
    · simp only [ite_eq_left hik,integral_const_mul,hmean]
    · simp only [ite_eq_right hik,integral_zero,zero_mul]
  calc
    _ = ∫ z, fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i) ∂μ := H
    _ = a*((∫ z, G z ∂μ)-(1-m i)*(∫ z, G z ∂μ)) := by
      rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,
        integral_sub hiG (integrable_finsetSum _ (fun k _ => hJ k)),
        integral_finsetSum _ (fun k _ => hJ k),hsum]
    _ = _ := by ring

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberTiltedTent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fiberGaussian_tilted_directional_stein_tent (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, coordinateLinear n a z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateVector n a) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateVector n a) ∂(fiberGaussian n x).tilted V := by
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := ((HasExpGrowth.linear (coordinateProjection n i)).mul hg).integrable_tilted_fiberGaussian
    n V hV ((coordinateProjection n i).continuous.mul hc.continuous) x
  have hi₂ (i : Fin n) := (hdg.derivative_eval (coordinateAxis n i)).integrable_tilted_fiberGaussian
    n V hV ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  have hi₃ (i : Fin n) := (hg.mul (hdV.derivative_eval (coordinateAxis n i))).integrable_tilted_fiberGaussian
    n V hV (hc.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun z : ParameterSpace n => ∑ i, g z*(a i*fderiv ℝ V z (coordinateAxis n i)))=
      fun z => ∑ i, a i*(g z*fderiv ℝ V z (coordinateAxis n i)) := by
    funext z; apply Finset.sum_congr rfl; intro i _; ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [fiberGaussian_tilted_weighted_stein n V g hV hc hg hdg,mul_add]

theorem fiberGaussian_tilted_quadratic_invariant (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ)
    (a : Fin n → ℝ) (hinv : TranslationInvariant g (coordinateVector n a)) :
    (∫ z, (coordinateLinear n a z)^2*g z ∂(fiberGaussian n x).tilted V) =
      (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*((fderiv ℝ (V ) z (coordinateVector n a))^2+
        fderiv ℝ (fderiv ℝ (V )) z (coordinateVector n a) (coordinateVector n a))
          ∂(fiberGaussian n x).tilted V := by
  let L := coordinateLinear n a
  let u := coordinateVector n a
  let d := directionalGradient V u
  have hdc : ContDiff ℝ 1 d := directionalGradient_contDiff V hV.1 u
  have hdg₀ := (hV.directionalGradient_bounds u).1
  have hdg₁ := (hV.directionalGradient_bounds u).2
  have hz (z) : fderiv ℝ g z u = 0 :=
    hinv.fderiv_zero (hc.differentiable (by norm_num)) z
  have hLc : ContDiff ℝ 1 (fun z => L z*g z) := L.contDiff.mul hc
  have hLg : HasExpGrowth (fun z => L z*g z) := (HasExpGrowth.linear L).mul hg
  have hLdg : HasExpGrowth (fderiv ℝ (fun z => L z*g z)) :=
    HasExpGrowth.fderiv_mul L.differentiable (hc.differentiable (by norm_num))
      (HasExpGrowth.linear L) hg (by
        apply HasExpGrowth.of_bounded (norm_nonneg L)
        intro z
        rw [L.fderiv]) hdg
  have H₁ := fiberGaussian_tilted_directional_stein_tent n V (fun z => L z*g z)
    hV hLc hLg hLdg x a
  have he₁ (z) : fderiv ℝ (fun z => L z*g z) z (coordinateVector n a) = (∑ i, (a i)^2)*g z := by
    change fderiv ℝ (fun z => L z*g z) z u = _
    rw [fderiv_fun_mul (L.differentiable z) (hc.differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,L.fderiv,zero_mul,zero_add,
      L,u,coordinateLinear_coordinateVector,mul_comm]
  simp_rw [he₁] at H₁
  rw [integral_const_mul] at H₁
  have hgc : ContDiff ℝ 1 (fun z => g z*d z) := hc.mul hdc
  have hgg : HasExpGrowth (fun z => g z*d z) := hg.mul hdg₀
  have hgg' : HasExpGrowth (fderiv ℝ (fun z => g z*d z)) :=
    HasExpGrowth.fderiv_mul (hc.differentiable (by norm_num))
      (hdc.differentiable (by norm_num)) hg hdg₀ hdg hdg₁
  have H₂ := fiberGaussian_tilted_directional_stein_tent n V (fun z => g z*d z)
    hV hgc hgg hgg' x a
  have he₂ (z) : fderiv ℝ (fun z => g z*d z) z (coordinateVector n a) =
      g z*fderiv ℝ d z u := by
    change fderiv ℝ (fun z => g z*d z) z u = _
    rw [fderiv_fun_mul (hc.differentiable (by norm_num) z)
      (hdc.differentiable (by norm_num) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hz,mul_zero,add_zero]
  simp_rw [he₂] at H₂
  have hi₁ := (hg.mul (hdg₁.derivative_eval u)).integrable_tilted_fiberGaussian n V hV
    (hc.continuous.mul ((hdc.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  have hi₂ := ((hg.mul hdg₀).mul hdg₀).integrable_tilted_fiberGaussian n V hV
    ((hc.continuous.mul hdc.continuous).mul hdc.continuous) x
  change (∫ z, L z*(g z*d  z) ∂(fiberGaussian n x).tilted V) =
    (∫ z, g z*fderiv ℝ (d ) z u ∂(fiberGaussian n x).tilted V)+
    ∫ z, g z*d  z*d  z ∂(fiberGaussian n x).tilted V at H₂
  rw [← integral_add hi₁ hi₂] at H₂
  have he₃ : (fun z : ParameterSpace n => L z*g z*
      fderiv ℝ (V ) z u) = fun z => L z*(g z*d  z) := by
    funext sz; simp only [d,directionalGradient,mul_assoc]
  change (∫ z, L z*(L z*g z) ∂(fiberGaussian n x).tilted V) =
    (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V)+
    ∫ z, L z*g z*fderiv ℝ (V ) z u ∂(fiberGaussian n x).tilted V at H₁
  rw [he₃,H₂] at H₁
  convert H₁ using 1
  · apply integral_congr_ae; filter_upwards [] with z; dsimp only [L]; ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [fderiv_directionalGradient _ hV.1,ContinuousLinearMap.flip_apply,
      directionalGradient,u]
    ring

end SK.Analytic

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

@[simp] theorem scalarStep_prefixHessian {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (v : ℝ) (z : ℝ × ℝ) :
    prefixHessian (fun z : ℝ × ℝ => f (z.1+v*z.2)) 1 1 z=
      rootHessian 0 f (z.1+v*z.2) := by
  have H := hessian_comp_linear f hf.1 (scalarStepLinear v) z (1,0) (1,0)
  simpa only [Hessian,prefixHessian,rootHessian,parameterAxis,scalarStepLinear_apply,mul_zero,add_zero] using H

theorem scalarStep_rootGradient {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v x : ℝ) :
    rootGradient 0 (scalarStep m v f) x=scalarStepAverage m v f (rootGradient 0 f) x := by
  have H := fderiv_gaussianStep_apply (hf.compCLM (scalarStepLinear v)) m x 1
  simpa only [rootGradient,parameterAxis,scalarStep,scalarStepAverage,
    gaussianAverage,scalarStepLinear_apply,scalarStep_prefixGradient hf v,rootGradient,parameterAxis] using H

theorem scalarStep_rootHessian {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v x : ℝ) :
    rootHessian 0 (scalarStep m v f) x=scalarStepAverage m v f (rootHessian 0 f) x+
      m*(scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x-
        (scalarStepAverage m v f (rootGradient 0 f) x)^2) := by
  have H := fderiv_fderiv_gaussianStep_apply (hf.compCLM (scalarStepLinear v)) m x 1 1
  simpa only [rootHessian,parameterAxis,scalarStep,scalarStepAverage,
    gaussianAverage,scalarStepLinear_apply,scalarStep_prefixGradient hf v,scalarStep_prefixHessian hf v,rootHessian,parameterAxis,pow_two] using H

theorem scalarStepAverage_bound {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    |scalarStepAverage m v f g x| ≤ B := by
  exact gaussianAverage_norm_le (hf.compCLM (scalarStepLinear v)) m
    (g:=fun z => g (z.1+v*z.2)) (fun z => hb _) x

theorem scalarStepAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    Integrable (fun y => g (x+v*y)) (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) := by
  exact integrable_gaussianStep_of_bounded (hf.compCLM (scalarStepLinear v)) m x
    (hg.comp (continuous_const.add (continuous_const.mul continuous_id))) (fun y => hb _)

theorem scalarStepAverage_variance_nonneg {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    0 ≤ scalarStepAverage m v f (fun y => (g y)^2) x-(scalarStepAverage m v f g x)^2 := by
  have : IsProbabilityMeasure (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    gaussianStepLaw_probability (hf.compCLM (scalarStepLinear v)) m x
  have H : MemLp (fun y => g (x+v*y)) 2
      (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    MemLp.of_bound (hg.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
      B (ae_of_all _ (fun y => hb _))
  simpa only [scalarStepAverage,gaussianAverage,variance_eq_sub H,Pi.pow_apply] using variance_nonneg (X:=fun y => g (x+v*y))
    (μ:=gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x)

theorem ScalarSpinConvex.scalarStep {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : ℝ) :
    ScalarSpinConvex (scalarStep m v f) := by
  intro x
  have : IsProbabilityMeasure (gaussianStepLaw m (fun z : ℝ×ℝ => f (z.1+v*z.2)) x) :=
    gaussianStepLaw_probability (hf.compCLM (scalarStepLinear v)) m x
  have hχ := rootHessian_continuous 0 hf
  have hu := rootGradient_continuous 0 hf
  have hiχ := scalarStepAverage_integrable hf hχ (fun y => (h.bounds y).2) m v x
  have hiu2 := scalarStepAverage_integrable hf (hu.pow 2)
    (fun y => show |(rootGradient 0 f y)^2| ≤ 1 from by
      rw [abs_of_nonneg (sq_nonneg _)]; exact (sq_le_one_iff_abs_le_one _).mpr (h.bounds y).1) m v x
  have HP : 0 ≤ scalarStepAverage m v f (rootHessian 0 f) x := integral_nonneg (fun y => (h _).1)
  have HV := scalarStepAverage_variance_nonneg hf hu (fun y => (h.bounds y).1) m v x
  have HU : scalarStepAverage m v f (rootHessian 0 f) x+
      scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x ≤ 1 := by
    have H := integral_mono (hiχ.add hiu2) (integrable_const (1:ℝ))
      (fun y => show rootHessian 0 f (x+v*y)+(rootGradient 0 f (x+v*y))^2 ≤ 1 by linarith [(h (x+v*y)).2])
    simp only [Pi.add_apply] at H
    rw [integral_add hiχ hiu2,integral_const,probReal_univ,one_smul] at H
    exact H
  rw [scalarStep_rootHessian hf,scalarStep_rootGradient hf]
  constructor
  · exact add_nonneg HP (mul_nonneg hm.1 HV)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) HV]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothedObservable
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

theorem scalarWindow_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    HasDerivAt (scalarWindow g h) (scalarWindowDerivative g h x) x := by
  convert (((boundedPrimitive_hasDerivAt hg (x+h)).comp x
    ((hasDerivAt_id x).add_const h)).sub (boundedPrimitive_hasDerivAt hg x)).div_const h using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ | simp only [scalarWindowDerivative,mul_one]

theorem scalarWindowDerivative_continuous {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    Continuous (scalarWindowDerivative g h) :=
  ((hg.comp (continuous_id.add continuous_const)).sub hg).div_const h

theorem scalarWindow_bound {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindow g h x| ≤ B := by
  have H := (boundedPrimitive_lipschitz hg hB).dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindow,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindowDerivative_bound {g : ℝ → ℝ} {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ 2*(B:ℝ)/h := by
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right ((abs_sub (g (x+h)) (g x)).trans (by linarith [hB (x+h),hB x])) hh.le

theorem scalarWindow_integral {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    scalarWindow g h x=(∫ y in x..x+h, g y)/h := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) 0 x) (hg.intervalIntegrable (μ:=volume) x (x+h))
  dsimp only [scalarWindow,boundedPrimitive]
  congr 1
  linarith

theorem scalarWindow_approx {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {h : ℝ} (hh : 0<h) (x : ℝ) : |scalarWindow g h x-g x| ≤ (L:ℝ)*h := by
  rw [scalarWindow_integral hg.continuous]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+h)
    (f:=fun y => g y-g x) (C:=(L:ℝ)*h) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      have H := hg.dist_le_mul y x
      simp only [Real.dist_eq] at H
      rw [abs_of_nonneg (show 0≤y-x by linarith [hy.1])] at H
      rw [Real.norm_eq_abs]
      exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg))
  rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,Real.norm_eq_abs,
    abs_of_pos hh] at H
  rw [show (∫ y in x..x+h, g y)/h-g x=((∫ y in x..x+h, g y)-h*g x)/h by field_simp,
    abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberLipschitzTent
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

theorem scalarWindow_contDiff {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    ContDiff ℝ 1 (scalarWindow g h) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (scalarWindow_hasDerivAt hg h x).differentiableAt,?_⟩
  have he : deriv (scalarWindow g h)=scalarWindowDerivative g h := funext (fun x => (scalarWindow_hasDerivAt hg h x).deriv)
  rw [he]
  exact scalarWindowDerivative_continuous hg h

theorem scalarWindow_comp_growth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0} (hb : ∀ x, |g x|≤B)
    {h : ℝ} (hh : 0<h) (L : E →L[ℝ] ℝ) :
    HasExpGrowth (fun z => scalarWindow g h (L z)) ∧
      HasExpGrowth (fderiv ℝ (fun z => scalarWindow g h (L z))) := by
  constructor
  · exact HasExpGrowth.of_bounded B.coe_nonneg (fun z => by simpa only [Real.norm_eq_abs] using scalarWindow_bound hg hb hh (L z))
  · apply HasExpGrowth.of_bounded (show 0≤(2*(B:ℝ)/h)*‖L‖ by positivity)
    intro z
    have H := ((scalarWindow_hasDerivAt hg h (L z)).hasFDerivAt.comp z L.hasFDerivAt).fderiv
    change ‖fderiv ℝ (scalarWindow g h ∘ ⇑L) z‖≤_
    rw [H]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg L)
    rw [ContinuousLinearMap.norm_toSpanSingleton,Real.norm_eq_abs]
    exact scalarWindowDerivative_bound hb hh (L z)

theorem fiberGaussian_tent_error_C1 (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g) (hg : HasExpGrowth g)
    (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ)
    (hinv : TranslationInvariant g (coordinateVector n a))
    (ε₁ ε₂ : ℝ) (hb : ∀ z, |g z|≤1)
    (h₁ : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε₁)
    (h₂ : ∀ z, |fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₂) :
    |(∫ z, (coordinateLinear n a z)^2*g z ∂(fiberGaussian n x).tilted V)-
      (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V)|≤ε₁^2+ε₂ := by
  let := fiberGaussian_tilted_probability n V hV x
  rw [fiberGaussian_tilted_quadratic_invariant n V g hV hc hg hdg x a hinv,add_sub_cancel_left]
  have H := norm_integral_le_of_norm_le_const (μ := (fiberGaussian n x).tilted V)
    (f := fun z => g z*((fderiv ℝ V z (coordinateVector n a))^2+
      fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)))
    (C := ε₁^2+ε₂) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      have he : |(fderiv ℝ V z (coordinateVector n a))^2+
          fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₁^2+ε₂ := by
        apply (abs_add_le _ _).trans
        apply add_le_add _ (h₂ z)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (h₁ z) 2
      exact (mul_le_mul (hb z) he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

theorem fiberGaussian_tent_error_lipschitz (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g)
    (hb : ∀ y, |g y|≤1) (L : ParameterSpace n →L[ℝ] ℝ)
    (x : ℝ) (a : Fin n → ℝ) (hinv : L (coordinateVector n a)=0) (ε₁ ε₂ : ℝ)
    (h₁ : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε₁)
    (h₂ : ∀ z, |fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₂) :
    |(∫ z, (coordinateLinear n a z)^2*g (L z) ∂(fiberGaussian n x).tilted V)-
      (∑ i, (a i)^2)*(∫ z, g (L z) ∂(fiberGaussian n x).tilted V)|≤ε₁^2+ε₂ := by
  let μ := (fiberGaussian n x).tilted V
  let := fiberGaussian_tilted_probability n V hV x
  let h : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hh (k) : 0<h k := by dsimp [h]; positivity
  have ht : Tendsto h atTop (𝓝 0) := by simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  let G : ℕ → ParameterSpace n → ℝ := fun k z => scalarWindow g (h k) (L z)
  have hc (k) : ContDiff ℝ 1 (G k) := (scalarWindow_contDiff hg.continuous (h k)).comp L.contDiff
  have hb' (k z) : |G k z|≤1 := scalarWindow_bound hg.continuous (B:=1) hb (hh k) (L z)
  have hlim (z) : Tendsto (fun k => G k z) atTop (𝓝 (g (L z))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => g (L z)-(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.sub (ht.const_mul (M:ℝ)))
      (show Tendsto (fun k => g (L z)+(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.add (ht.const_mul (M:ℝ)))
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).1; dsimp [G]; linarith
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).2; dsimp [G]; linarith
  have HI (k) : |(∫ z, (coordinateLinear n a z)^2*G k z ∂μ)-
      (∑ i,(a i)^2)*(∫ z, G k z ∂μ)|≤ε₁^2+ε₂ := by
    have he := scalarWindow_comp_growth hg.continuous (B:=1) hb (hh k) L
    apply fiberGaussian_tent_error_C1 n V (G k) hV (hc k) he.1 he.2 x a _ ε₁ ε₂ (hb' k) h₁ h₂
    intro z t
    simp only [G,map_add,map_smul,hinv,smul_zero,add_zero]
  have hi : Integrable (fun z => (coordinateLinear n a z)^2) μ :=
    by
      simpa only [pow_two] using
        ((HasExpGrowth.linear (coordinateLinear n a)).mul (HasExpGrowth.linear (coordinateLinear n a))).integrable_tilted_fiberGaussian
          n V hV ((coordinateLinear n a).continuous.mul (coordinateLinear n a).continuous) x
  have H₁ := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=fun k z => (coordinateLinear n a z)^2*G k z)
    (f:=fun z => (coordinateLinear n a z)^2*g (L z))
    (fun z => (coordinateLinear n a z)^2)
    (fun k => (((coordinateLinear n a).continuous.pow 2).mul (hc k).continuous).aestronglyMeasurable)
    hi (fun k => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hb' k z) (sq_nonneg _)).trans_eq (mul_one _)))
    (ae_of_all _ (fun z => (hlim z).const_mul _))
  have H₂ := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=G) (f:=fun z => g (L z)) (fun _ => (1:ℝ))
    (fun k => (hc k).continuous.aestronglyMeasurable) (integrable_const 1)
    (fun k => ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb' k z))
    (ae_of_all _ hlim)
  exact le_of_tendsto (H₁.sub (H₂.const_mul _)).abs (Eventually.of_forall HI)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_WindowIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory Filter
namespace SK.Analytic

theorem scalarWindow_integral_tendsto {E : Type} [MeasurableSpace E]
    {μ : Measure E} {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g)
    (hb : ∀ y, |g y|≤1) {L : E → ℝ} (hL : Measurable L)
    {w : E → ℝ} (hw : Integrable w μ) :
    Tendsto (fun k : ℕ => ∫ z, w z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)
      atTop (𝓝 (∫ z, w z*g (L z) ∂μ)) := by
  let h : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hh (k) : 0<h k := by dsimp [h]; positivity
  have ht : Tendsto h atTop (𝓝 0) := by simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim (z) : Tendsto (fun k => scalarWindow g (h k) (L z)) atTop (𝓝 (g (L z))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => g (L z)-(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.sub (ht.const_mul (M:ℝ)))
      (show Tendsto (fun k => g (L z)+(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.add (ht.const_mul (M:ℝ)))
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).1; linarith
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).2; linarith
  exact tendsto_integral_of_dominated_convergence (μ:=μ)
    (fun z => |w z|)
    (fun k => hw.aestronglyMeasurable.mul (((scalarWindow_contDiff hg.continuous (h k)).continuous.measurable.comp hL).aestronglyMeasurable))
    hw.abs (fun k => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_left (scalarWindow_bound hg.continuous (B:=1) hb (hh k) (L z)) (abs_nonneg _)).trans_eq (mul_one _)))
    (ae_of_all _ (fun z => (hlim z).const_mul _))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberLipschitzLinear
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

theorem fiberGaussian_linear_error_lipschitz (n : ℕ) (V F : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hFc : ContDiff ℝ 1 F) (hFg : HasExpGrowth F)
    (hFdg : HasExpGrowth (fderiv ℝ F)) (hFb : ∀ z, |F z|≤1)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y|≤1)
    (L : ParameterSpace n →L[ℝ] ℝ) (x : ℝ) (a : Fin n → ℝ)
    (hinv : L (coordinateVector n a)=0) (ε : ℝ)
    (hscore : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε) :
    |(∫ z, coordinateLinear n a z*F z*g (L z) ∂(fiberGaussian n x).tilted V)-
      (∫ z, fderiv ℝ F z (coordinateVector n a)*g (L z) ∂(fiberGaussian n x).tilted V)|≤ε := by
  let μ := (fiberGaussian n x).tilted V
  let := fiberGaussian_tilted_probability n V hV x
  let D : ParameterSpace n → ℝ := fun z => fderiv ℝ F z (coordinateVector n a)
  have hDc : Continuous D := (hFc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : HasExpGrowth D := hFdg.derivative_eval _
  have hDint : Integrable D μ := hDg.integrable_tilted_fiberGaussian n V hV hDc x
  have hLFint : Integrable (fun z => coordinateLinear n a z*F z) μ :=
    ((HasExpGrowth.linear _).mul hFg).integrable_tilted_fiberGaussian n V hV
      ((coordinateLinear n a).continuous.mul hFc.continuous) x
  have Hlim₁ := scalarWindow_integral_tendsto hg hb L.measurable hLFint
  have Hlim₂ := scalarWindow_integral_tendsto hg hb L.measurable hDint
  have HI (k : ℕ) : |(∫ z, coordinateLinear n a z*F z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)-
      (∫ z, D z*scalarWindow g (1/((k:ℝ)+1)) (L z) ∂μ)|≤ε := by
    let h : ℝ := 1/((k:ℝ)+1)
    have hh : 0<h := by dsimp [h]; positivity
    let G : ParameterSpace n → ℝ := fun z => scalarWindow g h (L z)
    have hGc : ContDiff ℝ 1 G := (scalarWindow_contDiff hg.continuous h).comp L.contDiff
    have hGgrow := scalarWindow_comp_growth hg.continuous (B:=1) hb hh L
    have hGb (z) : |G z|≤1 := scalarWindow_bound hg.continuous (B:=1) hb hh (L z)
    have hGi : TranslationInvariant G (coordinateVector n a) := by
      intro z t
      simp only [G,map_add,map_smul,hinv,smul_zero,add_zero]
    have hd (z) : fderiv ℝ (fun z => F z*G z) z (coordinateVector n a)=D z*G z := by
      rw [fderiv_fun_mul (hFc.differentiable (by norm_num) z) (hGc.differentiable (by norm_num) z)]
      simp only [add_apply,smul_apply,smul_eq_mul,
        hGi.fderiv_zero (hGc.differentiable (by norm_num)) z,mul_zero,zero_add,D,mul_comm]
    have H := fiberGaussian_tilted_directional_stein n V (fun z => F z*G z) hV
      (hFc.mul hGc) (hFg.mul hGgrow.1)
      (HasExpGrowth.fderiv_mul (hFc.differentiable (by norm_num))
        (hGc.differentiable (by norm_num)) hFg hGgrow.1 hFdg hGgrow.2) x a
    simp_rw [hd] at H
    have he : (fun z => coordinateLinear n a z*(F z*G z))=
        fun z => coordinateLinear n a z*F z*G z := by funext z; ring
    rw [he] at H
    change (∫ z, coordinateLinear n a z*F z*G z ∂μ)=
      (∫ z, D z*G z ∂μ)+∫ z, F z*G z*fderiv ℝ V z (coordinateVector n a) ∂μ at H
    change |(∫ z, coordinateLinear n a z*F z*G z ∂μ)-(∫ z, D z*G z ∂μ)|≤ε
    rw [H,add_sub_cancel_left]
    have Hb := norm_integral_le_of_norm_le_const (μ:=μ)
      (f:=fun z => F z*G z*fderiv ℝ V z (coordinateVector n a))
      (C:=ε) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul,abs_mul]
        have hFG : |F z| * |G z|≤1 :=
          (mul_le_mul (hFb z) (hGb z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        exact (mul_le_mul hFG (hscore z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using Hb
  exact le_of_tendsto (Hlim₁.sub Hlim₂).abs (Eventually.of_forall HI)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairRecursion
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

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStep_half_double (m : ℝ) (f : E × ℝ → ℝ) :
    gaussianStep (m/2) (fun z => 2*f z)=fun x => 2*gaussianStep m f x := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [zero_div,gaussianStep,ite_true,integral_const_mul]
  · have hm2 : m/2≠0 := div_ne_zero hm (by norm_num)
    simp only [gaussianStep,ite_eq_right hm,ite_eq_right hm2,positiveGaussianLogStep]
    simp only [show ∀ y, m/2*(2*f (x,y))=m*f (x,y) by intro y; ring]
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_half_double (m : ℝ) (f g : E × ℝ → ℝ) :
    gaussianAverage (m/2) (fun z => 2*f z) g=gaussianAverage m f g := by
  unfold gaussianAverage gaussianStepLaw
  simp only [show ∀ z : E × ℝ, m/2*(2*f z)=m*f z by intro z; ring]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_add_prefix (m : ℝ) (f g : E × ℝ → ℝ) (c : E → ℝ) :
    gaussianAverage m (fun z => f z+c z.1) g=gaussianAverage m f g := by
  funext x
  have htilt : (gaussianReal 0 1).tilted (fun y => m*(f (x,y)+c x))=
      (gaussianReal 0 1).tilted (fun y => m*f (x,y)) := by
    have H := tilted_tilted (μ:=gaussianReal 0 1)
      (f:=fun _ : ℝ => m*c x) (integrable_const _) (fun y => m*f (x,y))
    rw [tilted_const] at H
    rw [H]
    congr 1
    funext y
    simp only [Pi.add_apply]
    ring
  exact congrArg (fun μ => ∫ y, g (x,y) ∂μ) htilt

end Generic

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

theorem vectorHierarchy_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f : F → ℝ) :
    vectorHierarchy n m v (f ∘ L)=vectorHierarchy n m (L ∘ v) f ∘ L := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchy,vectorStep_pullback,ih]
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
section Generic
variable {E : Type}

theorem gaussianStep_div_scale (m c : ℝ) (hc : c≠0) (f : E × ℝ → ℝ) :
    gaussianStep (m/c) (fun z => c*f z)=fun x => c*gaussianStep m f x := by
  funext x
  by_cases hm : m=0
  · subst m; simp only [zero_div,gaussianStep,ite_true,integral_const_mul]
  · have hm2 : m/c≠0 := div_ne_zero hm hc
    have he : ∀ y, m/c*(c*f (x,y))=m*f (x,y) := by intro y; field_simp
    simp only [gaussianStep,ite_eq_right hm,ite_eq_right hm2,positiveGaussianLogStep,he]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring

theorem gaussianAverage_div_scale (m c : ℝ) (hc : c≠0) (f g : E × ℝ → ℝ) :
    gaussianAverage (m/c) (fun z => c*f z) g=gaussianAverage m f g := by
  unfold gaussianAverage gaussianStepLaw
  simp only [show ∀ z, m/c*(c*f z)=m*f z by intro z; field_simp]
end Generic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_div_scale (m c : ℝ) (hc : c≠0) (v : E) (f : E → ℝ) :
    vectorStep (m/c) v (fun x => c*f x)=fun x => c*vectorStep m v f x :=
  gaussianStep_div_scale m c hc _

theorem vectorStepAverage_div_scale (m c : ℝ) (hc : c≠0) (v : E) (f g : E → ℝ) :
    vectorStepAverage (m/c) v (fun x => c*f x) g=vectorStepAverage m v f g :=
  gaussianAverage_div_scale m c hc _ _

end Vector

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

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_prod_left {f : E → ℝ} (hf : BoundedDerivs f) (g : F → ℝ) (m : ℝ) (v : E) :
    vectorStep m (v,0) (fun p : E × F => f p.1+g p.2)=
      fun p => vectorStep m v f p.1+g p.2 := by
  let L : ((E × F) × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ)+
      (ContinuousLinearMap.snd ℝ (E × F) ℝ).smulRight v
  have H := gaussianStep_add_prefix (hf.compCLM L) (fun p : E × F => g p.2) m
  simpa only [vectorStep,Function.comp_def,L,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,gaussianStep,positiveGaussianLogStep] using H

theorem vectorStep_prod_right (f : E → ℝ) {g : F → ℝ} (hg : BoundedDerivs g) (m : ℝ) (v : F) :
    vectorStep m (0,v) (fun p : E × F => f p.1+g p.2)=
      fun p => f p.1+vectorStep m v g p.2 := by
  let L : ((E × F) × ℝ) →L[ℝ] F :=
    (ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ)+
      (ContinuousLinearMap.snd ℝ (E × F) ℝ).smulRight v
  have H := gaussianStep_add_prefix (hg.compCLM L) (fun p : E × F => f p.1) m
  simpa only [vectorStep,Function.comp_def,L,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,add_comm,gaussianStep,positiveGaussianLogStep] using H

theorem vectorStepAverage_prod_left (f a : E → ℝ) (g b : F → ℝ) (m : ℝ) (v : E) :
    vectorStepAverage m (v,0) (fun p : E × F => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => vectorStepAverage m v f a p.1*b p.2 := by
  unfold vectorStepAverage
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero]
  rw [gaussianAverage_add_prefix m (fun z : (E × F) × ℝ => f (z.1.1+z.2 • v)) _ (fun p => g p.2)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,integral_mul_const]

theorem vectorStepAverage_prod_right (f a : E → ℝ) (g b : F → ℝ) (m : ℝ) (v : F) :
    vectorStepAverage m (0,v) (fun p : E × F => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => a p.1*vectorStepAverage m v g b p.2 := by
  unfold vectorStepAverage
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero]
  simp_rw [add_comm (f _) (g _)]
  rw [gaussianAverage_add_prefix m (fun z : (E × F) × ℝ => g (z.1.2+z.2 • v)) _ (fun p => f p.1)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,integral_const_mul]

theorem vectorStep_half_double (m : ℝ) (v : E) (f : E → ℝ) :
    vectorStep (m/2) v (fun x => 2*f x)=fun x => 2*vectorStep m v f x :=
  gaussianStep_half_double m _

theorem vectorStepAverage_half_double (m : ℝ) (v : E) (f g : E → ℝ) :
    vectorStepAverage (m/2) v (fun x => 2*f x) g=vectorStepAverage m v f g :=
  gaussianAverage_half_double m _ _

theorem productBranchChain_factor (l : List (ProductIncrement (E:=E) (F:=F)))
    {f : E → ℝ} {g : F → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    productBranchChain l (fun p => f p.1+2*g p.2)=
      fun p => vectorIncrementChain (productLeft l) f p.1+
        2*vectorIncrementChain (productRight l) g p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStep (productMass p) (productVector p) (productBranchChain l _) = _
    rw [ih]
    cases p with
    | inl p =>
      simpa only [productMass,productVector,productLeft,productRight,List.filterMap_cons,vectorIncrementChain] using
        vectorStep_prod_left (vectorIncrementChain_regular (productLeft l) hf)
          (fun z => 2*vectorIncrementChain (productRight l) g z) p.1 p.2
    | inr p =>
      change vectorStep (p.1/2) (0,p.2)
        (fun z => vectorIncrementChain (productLeft l) f z.1+2*vectorIncrementChain (productRight l) g z.2)=_
      rw [vectorStep_prod_right _ ((vectorIncrementChain_regular _ hg).const_mul 2),vectorStep_half_double]
      rfl

theorem productBranchAverage_factor (l : List (ProductIncrement (E:=E) (F:=F)))
    {f : E → ℝ} {g : F → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) (a : E → ℝ) (b : F → ℝ) :
    productBranchAverage l (fun p => f p.1+2*g p.2) (fun p => a p.1*b p.2)=
      fun p => vectorIncrementAverage (productLeft l) f a p.1*
        vectorIncrementAverage (productRight l) g b p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage (productMass p) (productVector p) (productBranchChain l _)
      (productBranchAverage l _ _) = _
    rw [productBranchChain_factor l hf hg,ih]
    cases p with
    | inl p =>
      simpa only [productMass,productVector,productLeft,productRight,List.filterMap_cons,vectorIncrementAverage] using
        vectorStepAverage_prod_left (vectorIncrementChain (productLeft l) f)
          (vectorIncrementAverage (productLeft l) f a) (fun z => 2*vectorIncrementChain (productRight l) g z)
          (vectorIncrementAverage (productRight l) g b) p.1 p.2
    | inr p =>
      change vectorStepAverage (p.1/2) (0,p.2)
        (fun z => vectorIncrementChain (productLeft l) f z.1+2*vectorIncrementChain (productRight l) g z.2)
        (fun z => vectorIncrementAverage (productLeft l) f a z.1*vectorIncrementAverage (productRight l) g b z.2)=_
      rw [vectorStepAverage_prod_right (vectorIncrementChain (productLeft l) f)
        (vectorIncrementAverage (productLeft l) f a) (fun z => 2*vectorIncrementChain (productRight l) g z)
        (vectorIncrementAverage (productRight l) g b),vectorStepAverage_half_double]
      rfl
end Vector

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

theorem scalarIncrementChain_get (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain l f=scalarHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_get,vectorHierarchy_real]

theorem scalarIncrementAverage_get (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage l f g=scalarHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_get,vectorHierarchyAverage_real]

theorem scalarIncrementChain_append (l r : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain (l++r) f=scalarIncrementChain l (scalarIncrementChain r f) := by
  simp only [← vectorIncrementChain_real,vectorIncrementChain_append]

theorem scalarIncrementAverage_append (l r : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (l++r) f g=scalarIncrementAverage l (scalarIncrementChain r f) (scalarIncrementAverage r f g) := by
  simp only [← vectorIncrementAverage_real,← vectorIncrementChain_real,vectorIncrementAverage_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOneAtom
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
open scoped Topology

theorem scalarMagnetization_hasDerivAt (z : ℝ) :
    HasDerivAt scalarMagnetization (1/(Real.cosh z)^2) z := by
  have H : HasDerivAt scalarMagnetization
      ((Real.cosh z*Real.cosh z-Real.sinh z*Real.sinh z)/(Real.cosh z)^2) z :=
    (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
  apply H.congr_deriv
  congr 1
  nlinarith [Real.cosh_sq_sub_sinh_sq z]

theorem scalarMagnetization_lipschitz : LipschitzWith 1 scalarMagnetization := by
  rw [← lipschitzOnWith_univ]
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z _ => (scalarMagnetization_hasDerivAt z).hasDerivWithinAt)
  intro z _
  change ‖(1/(Real.cosh z)^2:ℝ)‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.one_le_cosh z]

end SK.Analytic

end
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

theorem parameter_coordinateAxis (n : ℕ) (i : Fin n) : parameter n (coordinateAxis n i)=0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateAxis_last,parameter]
    · simpa only [coordinateAxis_castSucc,parameter,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'] using ih j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ListPrefixTake
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem scalarPrefixVariance_list {A : Type} (w : List A) (f : A → ℝ) (j : Fin (w.length+1)) :
    scalarPrefixVariance w.length (fun i => f (w.get i)) j=((w.take j.val).map (fun p => (f p)^2)).sum := by
  induction w with
  | nil => simp [scalarPrefixVariance,scalarPrefixVector]
  | cons p w ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [scalarPrefixVariance,scalarPrefixVector]
    · unfold scalarPrefixVariance scalarPrefixVector
      change (∑ i : Fin (w.length+1), (if i.val<k.val+1 then f ((p::w).get i) else 0)^2)=_
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,Fin.val_succ,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,
        Nat.zero_lt_succ,ite_true,Nat.add_lt_add_iff_right,List.take_succ_cons,List.map_cons,List.sum_cons]
      rw [← ih k]
      rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ProductMerge
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
variable {E F : Type}

theorem mergedProductBranches_left (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productLeft (mergedProductBranches l r)=l := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productLeft,List.filterMap_cons]
        exact congrArg (List.cons p) (ih (q::r))
      · simp only [productLeft,List.filterMap_cons]
        exact ihr

theorem mergedProductBranches_right (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productRight (mergedProductBranches l r)=r := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productRight,List.filterMap_cons]
        exact ih (q::r)
      · simp only [productRight,List.filterMap_cons]
        exact congrArg (List.cons q) ihr

end Vector
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

theorem weighted_mass_iff (w : List (ℝ × (ℝ × ℝ))) {P : ℝ → Prop} :
    (∀ p∈w,P p.1) ↔ ∀ p∈weightedUnderlying w,P p.1 := by
  constructor
  · intro H p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact H q hq
  · intro H p hp; exact H _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem weighted_sorted_iff (w : List (ℝ × (ℝ × ℝ))) :
    w.Pairwise (fun p q => p.1≤q.1) ↔ (weightedUnderlying w).Pairwise (fun p q => p.1≤q.1) := by
  simp only [weightedUnderlying,List.pairwise_map]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarLevelRepresentation
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

theorem scalarSpinField_succ (n : ℕ) (v : Fin (n+1) → ℝ) (z : ParameterSpace n) (y : ℝ) :
    scalarSpinField (n+1) v (z,y)=scalarSpinField n (fun i => v i.castSucc) z+v (Fin.last n)*y := by
  change parameter n z+coordinateLinear (n+1) v (z,y)=
    parameter n z+coordinateLinear n (fun i => v i.castSucc) z+v (Fin.last n)*y
  rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
  simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

theorem gaussianStep_scalarSpinField (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ) (f : ℝ → ℝ) :
    gaussianStep m (fun z => f (scalarSpinField (n+1) v z))=
      fun z => scalarStep m (v (Fin.last n)) f (scalarSpinField n (fun i => v i.castSucc) z) := by
  have he : (fun z : ParameterSpace (n+1) => f (scalarSpinField (n+1) v z)) =
      fun z : ParameterSpace n × ℝ => f (scalarSpinField n (fun i => v i.castSucc) z.1+v (Fin.last n)*z.2) := by
    funext z
    rw [scalarSpinField_succ n v z.1 z.2]
  rw [he]
  rfl

theorem hierarchyLevel_scalar_representation (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hspin : ScalarSpinConvex f) (j : Fin (n+1)) :
    ∃ F : ℝ → ℝ, BoundedDerivs F ∧ ScalarSpinConvex F ∧
      hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j=
        fun z => F (scalarLevelField n v j z) := by
  induction n generalizing f with
  | zero => exact ⟨f,hf,hspin,by funext z; simp [hierarchyLevel,scalarLevelField,scalarSpinField,coordinateLinear,parameter]⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact ⟨f,hf,hspin,by simp [hierarchyLevel,scalarLevelField]⟩
    · obtain ⟨F,hF,hS,hEq⟩ := ih (fun k => m k.castSucc) (fun k => v k.castSucc)
        (fun k => hm k.castSucc) (scalarStep_regular hf (m (Fin.last n)) (v (Fin.last n)))
        (hspin.scalarStep hf (hm (Fin.last n)) (v (Fin.last n))) i
      refine ⟨F,hF,hS,?_⟩
      simp only [hierarchyLevel,Fin.lastCases_castSucc,gaussianStep_scalarSpinField,hEq,
        scalarLevelField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst']

theorem scalarLevelField_last (n : ℕ) (v : Fin n → ℝ) :
    scalarLevelField n v (Fin.last n)=scalarSpinField n v := by
  cases n with
  | zero => ext; simp [scalarLevelField,scalarSpinField,parameter,coordinateLinear]
  | succ n => simp [scalarLevelField]

theorem scalar_comp_directional {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (L : E →L[ℝ] ℝ) (z u : E) :
    fderiv ℝ (fun z => f (L z)) z u=rootGradient 0 f (L z)*L u ∧
      fderiv ℝ (fderiv ℝ (fun z => f (L z))) z u u=rootHessian 0 f (L z)*(L u)^2 := by
  have hd := hf.1.differentiable (by norm_num)
  have hF (z) : fderiv ℝ (fun z => f (L z)) z=(fderiv ℝ f (L z)).comp L :=
    ((hd _).hasFDerivAt.comp z L.hasFDerivAt).fderiv
  have he : fderiv ℝ (fun z => f (L z))=fun z => (fderiv ℝ f (L z)).comp L := funext hF
  constructor
  · rw [hF,ContinuousLinearMap.comp_apply]
    change fderiv ℝ f (L z) (L u)=fderiv ℝ f (L z) 1*L u
    rw [← smul_eq_mul,← map_smul]
    simp [smul_eq_mul,mul_comm]
  · rw [he]
    have hd' := (hf.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
    have H := ((hd' (L z)).hasFDerivAt.comp z L.hasFDerivAt).clm_comp (hasFDerivAt_const L z)
    change ((fderiv ℝ (fun y => (fderiv ℝ f ∘ ⇑L) y ∘L L) z) u) u = _
    rw [H.fderiv]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_zero,zero_add]
    change fderiv ℝ (fderiv ℝ f) (L z) (L u) (L u)=
      fderiv ℝ (fderiv ℝ f) (L z) 1 1*(L u)^2
    have hd₁ : fderiv ℝ (fderiv ℝ f) (L z) (L u) = (L u) • fderiv ℝ (fderiv ℝ f) (L z) 1 := by
      simpa only [smul_eq_mul,mul_one] using (map_smul (fderiv ℝ (fderiv ℝ f) (L z)) (L u) (1:ℝ))
    have hd₂ : fderiv ℝ (fderiv ℝ f) (L z) 1 (L u) = (L u)*fderiv ℝ (fderiv ℝ f) (L z) 1 1 := by
      simpa only [smul_eq_mul,mul_one] using (map_smul (fderiv ℝ (fderiv ℝ f) (L z) 1) (L u) (1:ℝ))
    rw [hd₁,smul_apply,hd₂]
    simp only [smul_eq_mul]
    ring

theorem hierarchyLevel_scalar_direction_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hspin : ScalarSpinConvex f) (j : Fin (n+1)) (z u : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j) z u|≤
      |scalarLevelField n v j u| ∧
    |fderiv ℝ (fderiv ℝ (hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j)) z u u|≤
      (scalarLevelField n v j u)^2 := by
  obtain ⟨F,hF,hS,he⟩ := hierarchyLevel_scalar_representation n m v hm hf hspin j
  rw [he]
  obtain ⟨h₁,h₂⟩ := scalar_comp_directional hF (scalarLevelField n v j) z u
  constructor
  · rw [h₁,abs_mul]
    exact (mul_le_mul_of_nonneg_right (hS.bounds _).1 (abs_nonneg _)).trans_eq (one_mul _)
  · rw [h₂,abs_mul,abs_of_nonneg (sq_nonneg (scalarLevelField n v j u))]
    exact (mul_le_mul_of_nonneg_right (hS.bounds _).2 (sq_nonneg _)).trans_eq (one_mul _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedSplitPath
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

section Product
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem vectorIncrementChain_prod_left (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f) (g : F → ℝ) :
    vectorIncrementChain (l.map (fun p => (p.1,(p.2,(0:F))))) (fun p : E × F => f p.1+g p.2)=
      fun p => vectorIncrementChain l f p.1+g p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementChain,ih]
    exact vectorStep_prod_left (vectorIncrementChain_regular l hf) _ _ _

theorem vectorIncrementAverage_prod_left (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f)
    (g : F → ℝ) (a : E → ℝ) (b : F → ℝ) :
    vectorIncrementAverage (l.map (fun p => (p.1,(p.2,(0:F))))) (fun p : E × F => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => vectorIncrementAverage l f a p.1*b p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementAverage,ih,vectorIncrementChain_prod_left l hf g]
    exact vectorStepAverage_prod_left _ _ _ _ _ _
end Product

theorem markedWeightedChain_average (c w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ × ℝ → ℝ) (U : ℝ → ℝ) (x : ℝ) :
    vectorIncrementAverage (markedWeightedChain c w) (fun p => f p.1.1) (fun p => g p.1*U p.2) ((x,0),x)=
      vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) g p*U p.1) (x,0) := by
  have hp : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have he : (fun p : MarkedWeightedState => f p.1.1)=fun p => (fun q : ℝ × ℝ => f q.1) p.1+(fun _ : ℝ => 0) p.2 := by
    funext p; simp
  rw [markedWeightedChain,vectorIncrementAverage_append,he,vectorIncrementChain_prod_left w hp (fun _ : ℝ => 0),
    vectorIncrementAverage_prod_left w hp (fun _ : ℝ => 0)]
  simp only [add_zero,weightedBranch_value]
  have H := congrFun (vectorIncrementAverage_pullback weightedMarker c
    (fun p : MarkedWeightedState => scalarIncrementChain (weightedUnderlying w) f p.1.1)
    (fun p => vectorIncrementAverage w (fun q => f q.1) g p.1*U p.2)) (x,0)
  exact H.symm

theorem scalarLevelField_eq_prefix (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    scalarLevelField n v j z=parameter n z+coordinateLinear n (scalarPrefixVector n v j) z := by
  induction n with
  | zero => simp [scalarLevelField,parameter,coordinateLinear]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarLevelField_last]
      change parameter (n+1) z+coordinateLinear (n+1) v z=_
      congr 2
      congr 1
      funext i
      simp only [scalarPrefixVector,Fin.val_last]
      exact (ite_eq_left (by omega)).symm
    · simp only [scalarLevelField,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ih]
      change parameter n z.1+coordinateLinear n _ z.1=parameter n z.1+coordinateLinear (n+1) _ z
      rw [coordinateLinear_apply,coordinateLinear_apply,Fin.sum_univ_castSucc]
      simp only [scalarPrefixVector,Fin.val_castSucc,Fin.val_last,ite_eq_right (show ¬ n<j.val by omega),zero_mul,add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [coordinateProjection_castSucc]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarWeightedMean
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

theorem scalarWeightedField_eq (n : ℕ) (v a : Fin n → ℝ) (z : ParameterSpace n) :
    (parameter n z,(0:ℝ))+∑ i, coordinateProjection n i z • (v i,a i)=
      (scalarSpinField n v z,coordinateLinear n a z) := by
  apply Prod.ext
  · have H := map_sum (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    simpa only [Prod.fst_add,ContinuousLinearMap.coe_fst',Prod.smul_fst,smul_eq_mul,
      scalarSpinField,add_apply,coordinateLinear_apply,mul_comm] using congrArg (parameter n z+·) H
  · have H := map_sum (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    simpa only [Prod.snd_add,zero_add,ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,
      coordinateLinear_apply,mul_comm] using H

theorem scalarWeightedTest_integral (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorHierarchyAverage n m (fun i => (v i,a i)) (fun p : ℝ × ℝ => f p.1) g (x,0)=
      ∫ z, g (scalarSpinField n v z,coordinateLinear n a z)
        ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) g (fun x => (x,0))) x
  simp only [scalarWeightedField_eq] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp ((scalarSpinField n v).prod (coordinateLinear n a)).continuous)
    (hE.compCLM ((scalarSpinField n v).prod (coordinateLinear n a))) x

theorem scalarHierarchyAverage_pathIntegral_exp (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (scalarSpinField n v z) ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m v f g id) x
  have he (z : ParameterSpace n) : parameter n z+∑ i, coordinateProjection n i z • v i=scalarSpinField n v z := by
    simp only [scalarSpinField,add_apply,coordinateLinear_apply,smul_eq_mul,mul_comm]
  simp only [id_eq] at H
  simp only [he,vectorHierarchyAverage_real] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp (scalarSpinField n v).continuous) (hE.compCLM (scalarSpinField n v)) x

theorem scalarPath_weighted_mean (n : ℕ) (m v a : Fin n → ℝ) (x : ℝ) :
    (∫ z, coordinateLinear n a z ∂hierarchyPathLaw n m (scalarSpinTerminal ∘ scalarSpinField n v) x)=
      (∑ i, a i*v i*m i)*deriv (scalarHierarchy n m v scalarSpinTerminal) x := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  have hf := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  have he : scalarSpinTerminal ∘ scalarSpinField n v=f := by
    simpa only [f,Function.comp_def,scalarSpinField,add_apply,coordinateLinear_apply] using scalarSpinTerminal_affine n v
  have hmean : (∫ z, affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin z
      ∂hierarchyPathLaw n m f x)=deriv (scalarHierarchy n m v scalarSpinTerminal) x := by
    rw [scalarSpin_affineMoment,scalarSpinRoot_gradient,← he]
    have hs : scalarParameterTerminal n v (fun a y => scalarMagnetization (a+y)) 0=
        scalarMagnetization ∘ scalarSpinField n v := by
      funext z
      simp only [scalarParameterTerminal,zero_add,Function.comp_def,scalarSpinField,
        add_apply,coordinateLinear_apply]
    rw [hs]
    exact (scalarHierarchyAverage_pathIntegral_exp n m v scalarSpinTerminal_regular
      scalarMagnetization_lipschitz.continuous (HasExpGrowth.of_bounded zero_le_one (fun y => by
        simpa only [Real.norm_eq_abs] using scalarMagnetization_abs_le_one y)) x).symm.trans
      (scalarHierarchy_gradient_average n m v scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x).symm
  rw [he]
  have hi (i : Fin n) : Integrable (fun z => a i*coordinateProjection n i z) (hierarchyPathLaw n m f x) :=
    ((HasExpGrowth.const (a i)).mul (HasExpGrowth.linear (coordinateProjection n i))).integrable_hierarchyPathLaw
      n m hf ((coordinateProjection n i).continuous.const_mul _) x
  simp_rw [coordinateLinear_apply]
  rw [integral_finsetSum _ (fun i _ => hi i),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,affineHierarchy_coordinate_mean n m (fun _ : Bool => 0)
    (fun b => spin b • scalarSpinField n v) spin (v i) i
    (fun b => by simp [scalarSpinField,parameter_coordinateAxis,coordinateLinear_coordinateAxis,mul_comm]) x,hmean]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMarkedIntegral
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

theorem markedScalarField_eq (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    ((parameter n z,0),parameter n z)+∑ i,coordinateProjection n i z • markedScalarVector n v a j i=
      ((scalarSpinField n v z,coordinateLinear n a z),scalarLevelField n v j z) := by
  apply Prod.ext
  · have H := map_sum (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
      (fun i => coordinateProjection n i z • markedScalarVector n v a j i) Finset.univ
    calc
      _ = (parameter n z,0)+∑ i,coordinateProjection n i z • (v i,a i) := by
        simpa only [ContinuousLinearMap.coe_fst',Prod.smul_fst,markedScalarVector,Prod.fst_add]
          using congrArg ((parameter n z,0)+·) H
      _ = _ := scalarWeightedField_eq n v a z
  · have H := map_sum (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
      (fun i => coordinateProjection n i z • markedScalarVector n v a j i) Finset.univ
    simpa only [ContinuousLinearMap.coe_snd',Prod.smul_snd,markedScalarVector,Prod.snd_add,smul_eq_mul,
      scalarLevelField_eq_prefix,coordinateLinear_apply,mul_comm] using congrArg (parameter n z+·) H

theorem markedScalarTest_integral (n : ℕ) (m v a : Fin n → ℝ) (j : Fin (n+1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {g : MarkedWeightedState → ℝ}
    (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorHierarchyAverage n m (markedScalarVector n v a j) (fun p => f p.1.1) g ((x,0),x)=
      ∫ z,g ((scalarSpinField n v z,coordinateLinear n a z),scalarLevelField n v j z)
        ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m (markedScalarVector n v a j)
    (fun p => f p.1.1) g (fun x => ((x,0),x))) x
  simp only [markedScalarField_eq] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp (((scalarSpinField n v).prod (coordinateLinear n a)).prod (scalarLevelField n v j)).continuous)
    (hE.compCLM (((scalarSpinField n v).prod (coordinateLinear n a)).prod (scalarLevelField n v j))) x

theorem markedWeightedChain_ofFn (c w : List (ℝ × (ℝ × ℝ))) :
    markedWeightedChain c w=List.ofFn (fun i : Fin (c++w).length =>
      ((c++w).get i |>.1,markedScalarVector (c++w).length
        (fun i => ((c++w).get i).2.1) (fun i => ((c++w).get i).2.2)
        ⟨c.length,by simp only [List.length_append]; omega⟩ i)) := by
  apply List.ext_getElem
  · simp [markedWeightedChain]
  · intro i hi hj
    simp only [List.getElem_ofFn,markedScalarVector,scalarPrefixVector,List.get_eq_getElem]
    by_cases h : i < c.length
    · simp only [markedWeightedChain]
      rw [List.getElem_append_left (by simpa only [List.length_map] using h)]
      simp only [List.getElem_map,List.getElem_append_left h,ite_eq_left h,weightedMarker_apply,Prod.mk.eta]
    · have h' : c.length ≤ i := by omega
      simp only [markedWeightedChain]
      rw [List.getElem_append_right (by simpa only [List.length_map] using h')]
      simp only [List.getElem_map,List.length_map,List.getElem_append_right h',ite_eq_right h,Prod.mk.eta]

theorem weightedSplit_integral (c w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ × ℝ → ℝ) (U : ℝ → ℝ)
    (hg : Continuous (fun p : MarkedWeightedState => g p.1*U p.2))
    (hE : HasExpGrowth (fun p : MarkedWeightedState => g p.1*U p.2)) (x : ℝ) :
    vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
      (fun p => vectorIncrementAverage w (fun p => f p.1) g p*U p.1) (x,0)=
      ∫ z, g (scalarSpinField (c++w).length (fun i => ((c++w).get i).2.1) z,
          coordinateLinear (c++w).length (fun i => ((c++w).get i).2.2) z)*
        U (scalarLevelField (c++w).length (fun i => ((c++w).get i).2.1)
          ⟨c.length,by simp only [List.length_append]; omega⟩ z)
        ∂hierarchyPathLaw (c++w).length (fun i => ((c++w).get i).1)
          (f ∘ scalarSpinField (c++w).length (fun i => ((c++w).get i).2.1)) x := by
  rw [← markedWeightedChain_average c w hf g U x,markedWeightedChain_ofFn,vectorIncrementAverage_ofFn]
  exact markedScalarTest_integral _ _ _ _ _ hf hg hE x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarGradientComposition
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

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarGradient_comp_fderiv {f : ℝ → ℝ} (hf : BoundedDerivs f) (L : E →L[ℝ] ℝ) (z : E) :
    fderiv ℝ (fun z => rootGradient 0 f (L z)) z=rootHessian 0 f (L z) • L := by
  have hd (y : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f y) y := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 y
  have H := ((hd (L z)).hasFDerivAt (𝕜 := ℝ)).comp z L.hasFDerivAt
  change HasFDerivAt (fun z => rootGradient 0 f (L z)) _ z at H
  have H := H.fderiv
  rw [H]
  ext u
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

theorem scalarGradient_comp_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (L : E →L[ℝ] ℝ) :
    ContDiff ℝ 1 (fun z => rootGradient 0 f (L z)) ∧
    HasExpGrowth (fun z => rootGradient 0 f (L z)) ∧
    HasExpGrowth (fderiv ℝ (fun z => rootGradient 0 f (L z))) := by
  have hc : ContDiff ℝ 1 (rootGradient 0 f) := directionalGradient_contDiff f hf.1 (parameterAxis 0)
  refine ⟨hc.comp L.contDiff,HasExpGrowth.of_bounded zero_le_one (fun z => ?_),?_⟩
  · simpa only [Real.norm_eq_abs] using (hspin.bounds (L z)).1
  · apply HasExpGrowth.of_bounded (norm_nonneg L)
    intro z
    rw [scalarGradient_comp_fderiv hf L z,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hspin.bounds (L z)).2 (norm_nonneg L)).trans_eq (one_mul _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarLocalDensity
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

theorem scalarLogDensity_direction_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) (hu : scalarSpinField n v u=0) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤
      ∑ j, hierarchyAtom n m 1 j*|scalarLevelField n v j u| ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤
      ∑ j, hierarchyAtom n m 1 j*(scalarLevelField n v j u)^2 := by
  let F : ParameterSpace n → ℝ := fun z => f (scalarSpinField n v z)
  let P := hierarchyPenalty n m 1 F
  let V := hierarchyPathLogDensity n m F
  have hF : BoundedDerivs F := hf.compCLM (scalarSpinField n v)
  have hP : BoundedDerivs P := hierarchyPenalty_boundedDerivs n m 1 F hF
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m hF
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hLv (j) := hierarchyLevel_boundedDerivs n m F hF j
  have he (z) : directionalGradient V u z =
      -(∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) := by
    change fderiv ℝ (fun z => F z-P z) z u = _
    rw [fderiv_fun_sub (hF.1.differentiable (by norm_num) z)
      (hP.1.differentiable (by norm_num) z),sub_apply]
    have hz := (scalar_comp_directional hf (scalarSpinField n v) z u).1
    change fderiv ℝ F z u=_ at hz
    rw [hz,hu,mul_zero,zero_sub,fderiv_hierarchyPenalty_apply n m 1 F hF]
    rfl
  have he' : directionalGradient V u = fun z =>
      -(∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) := funext he
  change directionalGradient V u = -(fun z => ∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) at he'
  have hd (j) := (directionalGradient_contDiff _ (hLv j).1 u).differentiable (by norm_num) z
  have H := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hd j).hasFDerivAt.const_mul (hierarchyAtom n m 1 j))).neg
  have hh : fderiv ℝ (fderiv ℝ V) z u u =
      -(∑ j, hierarchyAtom n m 1 j*fderiv ℝ (fderiv ℝ (hierarchyLevel n m F j)) z u u) := by
    have hh := congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L u) H.fderiv
    rw [← he',fderiv_directionalGradient _ hV.1] at hh
    simpa only [ContinuousLinearMap.flip_apply,neg_apply,sum_apply,smul_apply,smul_eq_mul,
      fderiv_directionalGradient _ (hLv _).1] using hh
  constructor
  · change |directionalGradient V u z|≤_
    rw [he,abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul,abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).1 (hw j)
  · change |fderiv ℝ (fderiv ℝ V) z u u|≤_
    rw [hh,abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul,abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).2 (hw j)

theorem scalarLogDensity_local_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) (hu : scalarSpinField n v u=0)
    (S : Finset (Fin (n+1))) {B : ℝ} (hB : 0≤B)
    (houtside : ∀ j, j∉S → scalarLevelField n v j u=0)
    (hinside : ∀ j∈S, |scalarLevelField n v j u|≤B) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤
      B*∑ j∈S, hierarchyAtom n m 1 j ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤
      B^2*∑ j∈S, hierarchyAtom n m 1 j := by
  have H := scalarLogDensity_direction_bounds n m v hm hmono hf hspin u hu z
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hb₁ : (∑ j, hierarchyAtom n m 1 j*|scalarLevelField n v j u|)≤
      B*∑ j∈S, hierarchyAtom n m 1 j := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [houtside j hj]; simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hinside j hj) (hw j)
  have hb₂ : (∑ j, hierarchyAtom n m 1 j*(scalarLevelField n v j u)^2)≤
      B^2*∑ j∈S, hierarchyAtom n m 1 j := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [houtside j hj]; simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hsq : (scalarLevelField n v j u)^2≤B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hinside j hj)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (hw j)
  exact ⟨H.1.trans hb₁,H.2.trans hb₂⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarPrefixCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLevelField_axis (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) :
    scalarLevelField n v j (coordinateAxis n i)=if i.val<j.val then v i else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarLevelField_last]
      simp only [Fin.val_last, i.isLt,ite_true]
      change parameter (n+1) (coordinateAxis (n+1) i)+coordinateLinear (n+1) v (coordinateAxis (n+1) i)=v i
      rw [parameter_coordinateAxis (n+1) i,coordinateLinear_coordinateAxis]
      simp
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [scalarLevelField,Fin.lastCases_castSucc,coordinateAxis_last,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',map_zero,
          Fin.val_last,Fin.val_castSucc]
        rw [ite_eq_right (by omega)]
      · simp only [scalarLevelField,Fin.lastCases_castSucc,coordinateAxis_castSucc,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ih,
          Fin.val_castSucc]

theorem scalarLevelField_vector (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n a)=∑ i, if i.val<j.val then a i*v i else 0 := by
  simp only [coordinateVector,map_sum,map_smul,smul_eq_mul,scalarLevelField_axis]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLevelField_prefixVector (n : ℕ) (v : Fin n → ℝ) (j k : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n (scalarPrefixVector n v k))=
      scalarPrefixVariance n v (min j k) := by
  rw [scalarLevelField_vector]
  unfold scalarPrefixVariance scalarPrefixVector
  apply Finset.sum_congr rfl
  intro i _
  have he : i.val<(min j k).val ↔ i.val<j.val ∧ i.val<k.val := by
    change i.val < min j.val k.val ↔ _
    exact lt_min_iff
  simp only [he]
  by_cases hj : i.val<j.val <;> by_cases hk : i.val<k.val <;> simp [hj,hk,pow_two]

theorem scalarLevelField_tentVector (n : ℕ) (v : Fin n → ℝ) (l r s j : Fin (n+1)) (h : ℝ) :
    scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))=
      (2*scalarPrefixVariance n v (min j r)-scalarPrefixVariance n v (min j l)-
        scalarPrefixVariance n v (min j s))/h := by
  rw [scalarLevelField_vector]
  conv_rhs => rw [← scalarLevelField_prefixVector,← scalarLevelField_prefixVector,← scalarLevelField_prefixVector]
  simp only [scalarLevelField_vector,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold scalarTentVector
  split_ifs <;> ring

theorem scalarPrefixVariance_monotone_tent (n : ℕ) (v : Fin n → ℝ) :
    Monotone (scalarPrefixVariance n v) := by
  intro j k hjk
  apply Finset.sum_le_sum
  intro i _
  unfold scalarPrefixVector
  by_cases hij : i.val<j.val
  · have hik : i.val<k.val := lt_of_lt_of_le hij (show j.val≤k.val from hjk)
    simp only [hij,hik,ite_true,le_refl]
  · simp only [hij,ite_false,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact sq_nonneg _

theorem scalarTentVector_prefix_bounds (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1))
    (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0≤B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    (j : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))∈Icc (0:ℝ) B ∧
      (j ≤ l ∨ s ≤ j → scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))=0) := by
  rw [scalarLevelField_tentVector]
  have hm := scalarPrefixVariance_monotone_tent n v
  rcases le_total j l with hj|hj
  · simp only [min_eq_left hj,min_eq_left (hj.trans hlr),min_eq_left (hj.trans (hlr.trans hrs))]
    have he : (2*scalarPrefixVariance n v j-scalarPrefixVariance n v j-scalarPrefixVariance n v j)/h=0 := by ring
    simp only [he]
    exact ⟨⟨le_rfl,hB⟩,fun _ => trivial⟩
  rcases le_total j r with hjr|hjr
  · simp only [min_eq_left hjr,min_eq_right hj,min_eq_left (hjr.trans hrs)]
    have hlow := hm hj
    have hhigh := hm hjr
    constructor
    · constructor
      · apply (le_div_iff₀ hh).mpr; nlinarith
      · apply (div_le_iff₀ hh).mpr; nlinarith
    · rintro (H|H)
      · have he : j=l := le_antisymm H hj
        subst j
        ring
      · have h1 := hm H
        have hn : 2*scalarPrefixVariance n v j-scalarPrefixVariance n v l-scalarPrefixVariance n v j=0 := by nlinarith
        rw [hn,zero_div]
  rcases le_total j s with hjs|hjs
  · simp only [min_eq_right hjr,min_eq_right hj,min_eq_left hjs]
    have hlow := hm hjr
    have hhigh := hm hjs
    constructor
    · constructor
      · apply (le_div_iff₀ hh).mpr
        nlinarith
      · apply (div_le_iff₀ hh).mpr
        nlinarith
    · rintro (H|H)
      · have h1 := hm H
        have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v j=0 := by nlinarith
        rw [hn,zero_div]
      · have he : j=s := le_antisymm hjs H
        subst j
        have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v s=0 := by linarith
        rw [hn,zero_div]
  · simp only [min_eq_right hjr,min_eq_right hj,min_eq_right hjs]
    have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v s=0 := by linarith
    rw [hn,zero_div]
    exact ⟨⟨le_rfl,hB⟩,fun _ => rfl⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarLocalTentMoments
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

theorem scalarLogDensity_tent_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z
      (coordinateVector n (scalarTentVector n v l r s h))| ≤ B*scalarTentAtomMass n m l s ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z
      (coordinateVector n (scalarTentVector n v l r s h)) (coordinateVector n (scalarTentVector n v l r s h))| ≤
      B^2*scalarTentAtomMass n m l s := by
  have HT (j) := scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright j
  apply scalarLogDensity_local_bound n m v hm hmono hf hspin _ _
    (Finset.univ.filter (fun j : Fin (n+1) => l < j ∧ j < s)) hB
  · intro j hj
    apply (HT j).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_and_or,not_lt] at hj
    exact hj
  · intro j _
    rw [abs_of_nonneg (HT j).1.1]
    exact (HT j).1.2
  · rw [← scalarLevelField_last]
    exact (HT _).2 (Or.inr (Fin.le_last s))

theorem scalarPath_tent_square_error (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y| ≤ 1) (x : ℝ) :
    |(∫ z, (coordinateLinear n (scalarTentVector n v l r s h) z)^2*g (scalarSpinField n v z)
      ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      (∑ i, (scalarTentVector n v l r s h i)^2)*(∫ z, g (scalarSpinField n v z)
        ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)| ≤
      (B*scalarTentAtomMass n m l s)^2+B^2*scalarTentAtomMass n m l s := by
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  apply fiberGaussian_tent_error_lipschitz n _
    (hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))) hg hb
    (scalarSpinField n v) x _ _ (B*scalarTentAtomMass n m l s) (B^2*scalarTentAtomMass n m l s)
  · intro z
    exact (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).1
  · intro z
    exact (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).2
  · rw [← scalarLevelField_last]
    exact (scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright _).2 (Or.inr (Fin.le_last s))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTentMixed
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

theorem scalarLevelField_tent_peak (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1))
    (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : h≠0)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h) :
    scalarLevelField n v r (coordinateVector n (scalarTentVector n v l r s h))=B := by
  rw [scalarLevelField_tentVector,min_self,min_eq_right hlr,min_eq_left hrs]
  have he : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v r=B*h := by linarith
  rw [he,mul_div_cancel_right₀ B hh]

theorem scalarPath_tent_mixed_error (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f F : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (hF : BoundedDerivs F) (hFs : ScalarSpinConvex F)
    (l r s : Fin (n+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y, |g y| ≤ 1) (x : ℝ) :
    |(∫ z, coordinateLinear n (scalarTentVector n v l r s h) z*
      rootGradient 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)
      ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      B*(∫ z, rootHessian 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)
        ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)| ≤
      B*scalarTentAtomMass n m l s := by
  let V := hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))
  have hV := hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))
  have HF := scalarGradient_comp_regular hF hFs (scalarLevelField n v r)
  have H := fiberGaussian_linear_error_lipschitz n V _ hV HF.1 HF.2.1 HF.2.2
    (fun z => (hFs.bounds _).1) hg hb (scalarSpinField n v) x (scalarTentVector n v l r s h)
    (by
      rw [← scalarLevelField_last]
      exact (scalarTentVector_prefix_bounds n v l r s hlr hrs hh hB hleft hright _).2 (Or.inr (Fin.le_last s)))
    (B*scalarTentAtomMass n m l s)
    (fun z => (scalarLogDensity_tent_bounds n m v hm hmono hf hspin l r s hlr hrs hh hB hleft hright z).1)
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  simp_rw [scalarGradient_comp_fderiv hF,smul_apply,smul_eq_mul,
    scalarLevelField_tent_peak n v l r s hlr hrs (ne_of_gt hh) hleft] at H
  have he : (fun z : ParameterSpace n => rootHessian 0 F (scalarLevelField n v r z)*B*g (scalarSpinField n v z))=
      fun z => B*(rootHessian 0 F (scalarLevelField n v r z)*g (scalarSpinField n v z)) := by funext z; ring
  rw [he,integral_const_mul] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListIntegral
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

theorem weightedBranch_average (w : List (ℝ × (ℝ × ℝ))) (f g : ℝ → ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => g p.1)=
      fun p => scalarIncrementAverage (weightedUnderlying w) f g p.1 := by
  have H := vectorIncrementAverage_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f g
  rw [vectorIncrementAverage_real] at H
  exact H

theorem weightedList_integral (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) g (x,0)=
      ∫ z,g (scalarSpinField w.length (fun i => (w.get i).2.1) z,
        coordinateLinear w.length (fun i => (w.get i).2.2) z)
        ∂hierarchyPathLaw w.length (fun i => (w.get i).1)
          (f ∘ scalarSpinField w.length (fun i => (w.get i).2.1)) x := by
  rw [vectorIncrementAverage_get]
  exact scalarWeightedTest_integral _ _ _ _ hf hg hE x

theorem weightedList_tent_square_error (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1 ≤ q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (w.length+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance w.length (fun i => (w.get i).2.1) r-
      scalarPrefixVariance w.length (fun i => (w.get i).2.1) l=B*h)
    (hright : scalarPrefixVariance w.length (fun i => (w.get i).2.1) s-
      scalarPrefixVariance w.length (fun i => (w.get i).2.1) r=B*h)
    (ha : (fun i => (w.get i).2.2)=scalarTentVector w.length (fun i => (w.get i).2.1) l r s h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y,|g y| ≤ 1) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2*g p.1) (x,0)-
      weightedVariance w*scalarIncrementAverage (weightedUnderlying w) f g x| ≤
      (B*scalarTentAtomMass w.length (fun i => (w.get i).1) l s)^2+
        B^2*scalarTentAtomMass w.length (fun i => (w.get i).1) l s := by
  have hG : HasExpGrowth g := HasExpGrowth.of_bounded zero_le_one (fun y => by
    simpa only [Real.norm_eq_abs] using hb y)
  have H := scalarPath_tent_square_error w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hspin l r s hlr hrs hh hB hleft hright hg hb x
  rw [← ha,sum_get_map w (fun p => p.2.2^2)] at H
  have hg1 : Continuous (fun p : ℝ × ℝ => p.2^2*g p.1) := (continuous_snd.pow 2).mul (hg.continuous.comp continuous_fst)
  have he1 : HasExpGrowth (fun p : ℝ × ℝ => p.2^2*g p.1) :=
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2).mul
      (hG.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ))
  have HI := weightedList_integral w hf hg1 he1 x
  dsimp only [Function.comp_def] at HI
  rw [← HI] at H
  have He := weightedList_integral w hf (hg.continuous.comp continuous_fst)
    (hG.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)) x
  dsimp only [Function.comp_def] at He
  rw [weightedBranch_average] at He
  rw [← He] at H
  exact H

theorem weightedSplit_tent_mixed_error (c w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1) (hs : (c++w).Pairwise (fun p q => p.1 ≤ q.1))
    {f F : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (hF : BoundedDerivs F) (hFs : ScalarSpinConvex F)
    (l s : Fin ((c++w).length+1))
    (hlr : l ≤ ⟨c.length,by simp only [List.length_append]; omega⟩)
    (hrs : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1)) ≤ s)
    {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
      ⟨c.length,by simp only [List.length_append]; omega⟩-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) l=B*h)
    (hright : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) s-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
        ⟨c.length,by simp only [List.length_append]; omega⟩=B*h)
    (ha : (fun i => ((c++w).get i).2.2)=scalarTentVector (c++w).length
      (fun i => ((c++w).get i).2.1) l ⟨c.length,by simp only [List.length_append]; omega⟩ s h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y,|g y| ≤ 1) (x : ℝ) :
    |vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) (fun p => g p.1*p.2) p*rootGradient 0 F p.1) (x,0)-
      B*vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) (fun p => g p.1) p*rootHessian 0 F p.1) (x,0)| ≤
      B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s := by
  have H := scalarPath_tent_mixed_error (c++w).length (fun i => ((c++w).get i).1) (fun i => ((c++w).get i).2.1)
    (fun i => hm _ (List.get_mem _ i)) (mass_get_monotone hs) hf hspin hF hFs l
    ⟨c.length,by simp only [List.length_append]; omega⟩ s hlr hrs hh hB hleft hright hg hb x
  rw [← ha] at H
  have hG : HasExpGrowth g := HasExpGrowth.of_bounded zero_le_one (fun y => by simpa only [Real.norm_eq_abs] using hb y)
  have hU : HasExpGrowth (rootGradient 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun y => by simpa only [Real.norm_eq_abs] using (hFs.bounds y).1)
  have hC : HasExpGrowth (rootHessian 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun y => by simpa only [Real.norm_eq_abs] using (hFs.bounds y).2)
  let L : MarkedWeightedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Y : MarkedWeightedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let R : MarkedWeightedState →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have HI := weightedSplit_integral c w hf (fun p => g p.1*p.2) (rootGradient 0 F)
    (((hg.continuous.comp L.continuous).mul Y.continuous).mul ((rootGradient_continuous 0 hF).comp R.continuous))
    (((hG.compCLM L).mul (HasExpGrowth.linear Y)).mul (hU.compCLM R)) x
  have HJ := weightedSplit_integral c w hf (fun p => g p.1) (rootHessian 0 F)
    ((hg.continuous.comp L.continuous).mul ((rootHessian_continuous 0 hF).comp R.continuous))
    ((hG.compCLM L).mul (hC.compCLM R)) x
  rw [HI,HJ]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg abs
  apply congrArg₂ (fun a b : ℝ => a-B*b)
  · apply integral_congr_ae
    filter_upwards [] with z
    ring
  · apply integral_congr_ae
    filter_upwards [] with z
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListMean
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

theorem weightedList_spin_mean (w : List (ℝ × (ℝ × ℝ))) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarSpinTerminal p.1) (fun p => p.2) (x,0)=
      weightedMean w*deriv (scalarIncrementChain (weightedUnderlying w) scalarSpinTerminal) x := by
  rw [vectorIncrementAverage_get]
  change vectorHierarchyAverage w.length (fun i => (w.get i).1)
    (fun i => ((w.get i).2.1,(w.get i).2.2)) _ _ _=_
  rw [scalarWeightedTest_integral _ _ _ _ scalarSpinTerminal_regular continuous_snd
    (HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)),scalarPath_weighted_mean]
  rw [sum_get_map w (fun p => p.2.2*p.2.1*p.1)]
  congr 2
  have H := vectorIncrementChain_get w (fun p : ℝ × ℝ => scalarSpinTerminal p.1)
  rw [weightedBranch_value] at H
  have H' := congrArg (fun F : ℝ × ℝ → ℝ => fun y => F (y,0)) H
  have Hhier := congrArg (fun F : ℝ × ℝ → ℝ => fun y => F (y,0))
    (vectorHierarchy_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w.length
      (fun i => (w.get i).1) (fun i => (w.get i).2) scalarSpinTerminal)
  rw [vectorHierarchy_real] at Hhier
  exact (H'.trans Hhier).symm

theorem zeroWeightChain_average_noise {f : ℝ → ℝ} (hf : BoundedDerivs f) (t : List (ℝ × ℝ)) (g : ℝ → ℝ) :
    vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => g p.2)=fun p => g p.2 := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    change vectorStepAverage p.1 (p.2,0) (vectorIncrementChain (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1))
      (vectorIncrementAverage (zeroWeightChain t) (fun p : ℝ × ℝ => f p.1) (fun p => g p.2))=_
    rw [ih]
    apply vectorStepAverage_frozen (vectorIncrementChain_regular _ (hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    intro x s
    simp only [Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

theorem weightedList_tail_mean (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => scalarIncrementChain t scalarSpinTerminal p.1)
      (fun p => p.2) (x,0)=
      weightedMean w*deriv (scalarIncrementChain (weightedUnderlying w++t) scalarSpinTerminal) x := by
  have H := weightedList_spin_mean (w++zeroWeightChain t) x
  rw [vectorIncrementAverage_append,zeroWeightChain_average_noise scalarSpinTerminal_regular t (fun y => y),
    weightedBranch_value,weightedUnderlying_zeroWeight,weightedMean_append,weightedMean_zeroWeight,add_zero,
    weightedUnderlying_append,weightedUnderlying_zeroWeight] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedPrefixBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedList_field_bound (w : List (ℝ × (ℝ × ℝ))) (j : Fin (w.length+1)) :
    |scalarLevelField w.length (fun i => (w.get i).2.1) j
      (coordinateVector w.length (fun i => (w.get i).2.2))| ≤ weightedAbsCross w := by
  rw [scalarLevelField_vector]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold weightedAbsCross
  rw [← sum_get_map w (fun p => |p.2.2| * |p.2.1|)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp only [abs_mul,abs_zero,le_refl]
  positivity

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarRampMoment
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

theorem scalarLogDensity_ramp_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) {B : ℝ} (hB : 0≤B)
    (hprefix : ∀ j, |scalarLevelField n v j u|≤B) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤2*B ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤2*B^2 := by
  let F : ParameterSpace n → ℝ := fun z => f (scalarSpinField n v z)
  let P := hierarchyPenalty n m 1 F
  let V := hierarchyPathLogDensity n m F
  have hF : BoundedDerivs F := hf.compCLM (scalarSpinField n v)
  have hP : BoundedDerivs P := hierarchyPenalty_boundedDerivs n m 1 F hF
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m hF
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hLv (j) := hierarchyLevel_boundedDerivs n m F hF j
  have he' : directionalGradient P u = fun z =>
      ∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z := by
    funext z
    exact fderiv_hierarchyPenalty_apply n m 1 F hF z u
  have hd (j) := (directionalGradient_contDiff _ (hLv j).1 u).differentiable (by norm_num) z
  have H := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hd j).hasFDerivAt.const_mul (hierarchyAtom n m 1 j))
  have hh : fderiv ℝ (fderiv ℝ P) z u u =
      ∑ j, hierarchyAtom n m 1 j*fderiv ℝ (fderiv ℝ (hierarchyLevel n m F j)) z u u := by
    have hh := congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L u) H.fderiv
    rw [← he',fderiv_directionalGradient _ hP.1] at hh
    simpa only [ContinuousLinearMap.flip_apply,sum_apply,smul_apply,smul_eq_mul,
      fderiv_directionalGradient _ (hLv _).1] using hh
  have hp₁ : |fderiv ℝ P z u|≤B := by
    change |directionalGradient P u z|≤B
    rw [he']
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j, hierarchyAtom n m 1 j*B := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left
          ((hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).1.trans (hprefix j)) (hw j)
      _ = B := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have hp₂ : |fderiv ℝ (fderiv ℝ P) z u u|≤B^2 := by
    rw [hh]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j, hierarchyAtom n m 1 j*B^2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        apply mul_le_mul_of_nonneg_left _ (hw j)
        exact (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).2.trans
          (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hprefix j))
      _ = B^2 := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have ht := hierarchyLevel_scalar_direction_bounds n m v hm hf hspin (Fin.last n) z u
  rw [hierarchyLevel_last,scalarLevelField_last] at ht
  have htl : |scalarSpinField n v u|≤B := by simpa only [scalarLevelField_last] using hprefix (Fin.last n)
  have ht₁ : |fderiv ℝ F z u|≤B := ht.1.trans htl
  have ht₂ : |fderiv ℝ (fderiv ℝ F) z u u|≤B^2 := ht.2.trans
    (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr htl)
  have hv₁ : fderiv ℝ V z u=fderiv ℝ F z u-fderiv ℝ P z u := by
    change fderiv ℝ (fun z => F z-P z) z u=_
    rw [fderiv_fun_sub (hF.1.differentiable (by norm_num) z) (hP.1.differentiable (by norm_num) z),sub_apply]
  have hv₂ : fderiv ℝ (fderiv ℝ V) z u u=fderiv ℝ (fderiv ℝ F) z u u-fderiv ℝ (fderiv ℝ P) z u u := by
    have he : fderiv ℝ V=fun z => fderiv ℝ F z-fderiv ℝ P z := by
      funext z
      exact fderiv_fun_sub (hF.1.differentiable (by norm_num) z) (hP.1.differentiable (by norm_num) z)
    rw [he,fderiv_fun_sub ((hF.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) z)
      ((hP.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) z),sub_apply,sub_apply]
  constructor
  · change |fderiv ℝ V z u|≤_
    rw [hv₁]
    exact (abs_sub _ _).trans (by linarith)
  · change |fderiv ℝ (fderiv ℝ V) z u u|≤_
    rw [hv₂]
    exact (abs_sub _ _).trans (by linarith)

theorem scalarPath_ramp_square_error (n : ℕ) (m v a : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    {B : ℝ} (hB : 0≤B)
    (hprefix : ∀ j, |scalarLevelField n v j (coordinateVector n a)|≤B) (x : ℝ) :
    |(∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      (∑ i, (a i)^2)|≤4*B^2+2*B^2 := by
  let V := hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))
  have H := fiberGaussian_tent_error_C1 n V (fun _ => 1) hV contDiff_const
    (HasExpGrowth.const 1) (by
      apply HasExpGrowth.of_bounded (C:=0) le_rfl
      intro z
      simp)
    x a (fun _ _ => rfl) (2*B) (2*B^2) (fun _ => by norm_num)
    (fun z => (scalarLogDensity_ramp_bounds n m v hm hmono hf hspin _ hB hprefix z).1)
    (fun z => (scalarLogDensity_ramp_bounds n m v hm hmono hf hspin _ hB hprefix z).2)
  have := fiberGaussian_tilted_probability n V hV x
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  simpa only [mul_one,integral_const,probReal_univ,smul_eq_mul,one_mul,show (2*B)^2=4*B^2 by ring] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedRampBridge
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

theorem weightedList_ramp_square_error (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1 ≤ q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ j, |scalarLevelField w.length (fun i => (w.get i).2.1) j
      (coordinateVector w.length (fun i => (w.get i).2.2))| ≤ B) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)-weightedVariance w| ≤ 6*B^2 := by
  have H := scalarPath_ramp_square_error w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => (w.get i).2.2) (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hspin hB hprefix x
  rw [sum_get_map w (fun p => p.2.2^2)] at H
  have HI := weightedList_integral w (g:=fun p : ℝ × ℝ => p.2^2) hf (continuous_snd.pow 2)
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2) x
  dsimp only [Function.comp_def] at HI
  rw [← HI] at H
  simpa only [weightedVariance, show 4*B^2+2*B^2=6*B^2 by ring] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockTent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem fourBlockTent_vector {κ d : ℝ} (hd : d≠0) (hκ : κ*d=1) (b l j k : List (ℝ × ℝ)) :
    (fun i => ((fourBlockTent κ b l j k).get i).2.2)=
      scalarTentVector (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
        (fourBlockLeft κ b l j k) (fourBlockMiddle κ b l j k) (fourBlockRight κ b l j k) d := by
  funext i
  simp only [List.get_eq_getElem]
  have hfactor : κ=1/d := (eq_div_iff hd).mpr hκ
  unfold scalarTentVector scalarPrefixVector
  simp only []
  by_cases hb : i.val<b.length
  · have hbl : i.val<b.length+l.length := by omega
    have hblj : i.val<b.length+l.length+j.length := by omega
    simp only [hb,hbl,hblj,ite_true]
    simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
      List.length_append,List.length_map,hbl,hb,dite_true,List.getElem_map]
    ring
  · by_cases hl : i.val<b.length+l.length
    · have hblj : i.val<b.length+l.length+j.length := by omega
      have hil : i.val-b.length<l.length := by omega
      simp only [hb,hl,hblj,ite_true,ite_false]
      simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
        List.length_append,List.length_map,hl,hb,dite_true,dite_false,List.getElem_map]
      apply (eq_div_iff hd).mpr
      linear_combination l[i.val-b.length].2*hκ
    · by_cases hj : i.val<b.length+l.length+j.length
      · have hij : i.val-(b.length+l.length)<j.length := by omega
        simp only [hb,hl,hj,ite_true,ite_false]
        simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
          List.length_append,List.length_map,hl,hb,hij,dite_true,dite_false,List.getElem_map]
        apply (eq_div_iff hd).mpr
        linear_combination -j[i.val-(b.length+l.length)].2*hκ
      · have hij : ¬i.val-(b.length+l.length)<j.length := by omega
        simp only [hb,hl,hj,ite_false]
        simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
          List.length_append,List.length_map,hl,hb,hij,dite_false,List.getElem_map]
        ring

theorem fourBlockTent_left_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockLeft κ b l j k)=rawVariance b := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [Nat.sub_eq_zero_of_le (show b.length≤b.length+l.length by omega)]

theorem fourBlockTent_middle_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockMiddle κ b l j k)=rawVariance b+rawVariance l := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [List.take_of_length_le]

theorem fourBlockTent_right_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockRight κ b l j k)=rawVariance b+rawVariance l+rawVariance j := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [List.take_of_length_le]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverageAlgebra
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

theorem vectorStepAverage_add {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (m : ℝ) (v : E) :
    vectorStepAverage m v f (fun x => g x+h x)=
      fun x => vectorStepAverage m v f g x+vectorStepAverage m v f h x := by
  funext x
  exact integral_add ((hgE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hg.comp (vectorTranslation v).continuous) m x)
    ((hhE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hh.comp (vectorTranslation v).continuous) m x)

theorem vectorStepAverage_const_mul (f g : E → ℝ) (m : ℝ) (v : E) (c : ℝ) :
    vectorStepAverage m v f (fun x => c*g x)=fun x => c*vectorStepAverage m v f g x := by
  funext x
  exact integral_const_mul c _

theorem vectorStepAverage_const {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v : E) (c : ℝ) :
    vectorStepAverage m v f (fun _ => c)=fun _ => c := by
  funext x
  let : IsProbabilityMeasure (gaussianStepLaw m (f ∘ vectorTranslation v) x) :=
    gaussianStepLaw_probability (hf.compCLM (vectorTranslation v)) m x
  change (∫ _y, c ∂gaussianStepLaw m (f ∘ vectorTranslation v) x)=c
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem vectorStepAverage_mono {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (hle : ∀ x,g x≤h x) (m : ℝ) (v x : E) :
    vectorStepAverage m v f g x≤vectorStepAverage m v f h x := by
  exact integral_mono ((hgE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hg.comp (vectorTranslation v).continuous) m x)
    ((hhE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hh.comp (vectorTranslation v).continuous) m x)
    (fun _ => hle _)

theorem vectorIncrementAverage_add (l : List (ℝ × E)) {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h) :
    vectorIncrementAverage l f (fun x => g x+h x)=
      fun x => vectorIncrementAverage l f g x+vectorIncrementAverage l f h x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih]
    have G := vectorIncrementAverage_regular l hf hg hgE
    have H := vectorIncrementAverage_regular l hf hh hhE
    exact vectorStepAverage_add (vectorIncrementChain_regular l hf) G.1 H.1 G.2 H.2 p.1 p.2

theorem vectorIncrementAverage_const_mul (l : List (ℝ × E)) (f g : E → ℝ) (c : ℝ) :
    vectorIncrementAverage l f (fun x => c*g x)=fun x => c*vectorIncrementAverage l f g x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih,vectorStepAverage_const_mul]
    rfl

theorem vectorIncrementAverage_const (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f) (c : ℝ) :
    vectorIncrementAverage l f (fun _ => c)=fun _ => c := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih]
    exact vectorStepAverage_const (vectorIncrementChain_regular l hf) p.1 p.2 c

theorem vectorIncrementAverage_mono (l : List (ℝ × E)) {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (hle : ∀ x,g x≤h x) (x : E) :
    vectorIncrementAverage l f g x≤vectorIncrementAverage l f h x := by
  induction l generalizing x with
  | nil => exact hle x
  | cons p l ih =>
    have G := vectorIncrementAverage_regular l hf hg hgE
    have H := vectorIncrementAverage_regular l hf hh hhE
    exact vectorStepAverage_mono (vectorIncrementChain_regular l hf) G.1 H.1 G.2 H.2
      (fun y => by exact ih y) p.1 p.2 x

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedFactor
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

theorem narrowRetainedMiddle_value (v w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (narrowRetainedMiddle (mergedProductBranches v w))
      (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)=
      fun p => scalarIncrementChain (weightedUnderlying v) f p.1.1+
        2*scalarIncrementChain (weightedUnderlying w) f p.2.1 := by
  have hF : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchChain _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*(fun q : ℝ × ℝ => f q.1) p.2)=_
  rw [productBranchChain_factor _ hF hF,mergedProductBranches_left,mergedProductBranches_right,
    weightedBranch_value,weightedBranch_value]

theorem narrowRetainedMiddle_moment (v w : List (ℝ × (ℝ × ℝ)))
    {f H : ℝ → ℝ} (hf : BoundedDerivs f) (hH : Continuous H) (hHE : HasExpGrowth H) :
    vectorIncrementAverage (narrowRetainedMiddle (mergedProductBranches v w))
      (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
      (fun p => H p.2.1*(p.1.2+p.2.2)^2)=
      fun p =>
        vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) p.1*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1) p.2+
        2*(vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2) p.1*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2) p.2)+
        vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2^2) p.2 := by
  let A : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))
  let B : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))
  let X : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))
  let V : NarrowRetainedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))
  let L := narrowRetainedMiddle (mergedProductBranches v w)
  let F := fun p : NarrowRetainedState => f p.1.1+2*f p.2.1
  have hF : BoundedDerivs F := (hf.compCLM V).add ((hf.compCLM X).const_mul 2)
  have hc1 : Continuous (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) := (A.continuous.pow 2).mul (hH.comp X.continuous)
  have he1 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) := ((HasExpGrowth.linear A).pow 2).mul (hHE.compCLM X)
  have hc2 : Continuous (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) := A.continuous.mul ((hH.comp X.continuous).mul B.continuous)
  have he2 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) := (HasExpGrowth.linear A).mul ((hHE.compCLM X).mul (HasExpGrowth.linear B))
  have hc3 : Continuous (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) := (hH.comp X.continuous).mul (B.continuous.pow 2)
  have he3 : HasExpGrowth (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) := (hHE.compCLM X).mul ((HasExpGrowth.linear B).pow 2)
  have he : (fun p : NarrowRetainedState => H p.2.1*(p.1.2+p.2.2)^2)=
      fun p => (p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2)))+H p.2.1*p.2.2^2 := by funext p; ring
  have hc2m : Continuous (fun p : NarrowRetainedState => 2*(p.1.2*(H p.2.1*p.2.2))) := hc2.const_mul 2
  have he2m : HasExpGrowth (fun p : NarrowRetainedState => 2*(p.1.2*(H p.2.1*p.2.2))) := (HasExpGrowth.const 2).mul he2
  have hc12 : Continuous (fun p : NarrowRetainedState => p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2))) := hc1.add hc2m
  have he12 : HasExpGrowth (fun p : NarrowRetainedState => p.1.2^2*H p.2.1+2*(p.1.2*(H p.2.1*p.2.2))) := he1.add he2m
  rw [he,vectorIncrementAverage_add L hF hc12 hc3 he12 he3,
    vectorIncrementAverage_add L hF hc1 hc2m he1 he2m,
    vectorIncrementAverage_const_mul]
  have hsf : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hfac (a b : ℝ × ℝ → ℝ) := productBranchAverage_factor (mergedProductBranches v w) hsf hsf a b
  simp only [mergedProductBranches_left,mergedProductBranches_right] at hfac
  have hfac3 := hfac (fun _ => 1) (fun q => H q.1*q.2^2)
  simp only [one_mul,vectorIncrementAverage_const v hsf 1] at hfac3
  change (fun p => (productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => p.1.2^2*H p.2.1) p+
    2*productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => p.1.2*(H p.2.1*p.2.2)) p)+
    productBranchAverage (mergedProductBranches v w) F (fun p : NarrowRetainedState => H p.2.1*p.2.2^2) p)=_
  dsimp only [F]
  rw [hfac (fun q => q.2^2) (fun q => H q.1),hfac (fun q => q.2) (fun q => H q.1*q.2),hfac3]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedCommon
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
section Scale
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementChain_div_scale (l : List (ℝ × E)) (c : ℝ) (hc : c≠0) (f : E → ℝ) :
    vectorIncrementChain (l.map (fun p => (p.1/c,p.2))) (fun x => c*f x)=
      fun x => c*vectorIncrementChain l f x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementChain,ih,vectorStep_div_scale p.1 c hc]

theorem vectorIncrementAverage_div_scale (l : List (ℝ × E)) (c : ℝ) (hc : c≠0) (f g : E → ℝ) :
    vectorIncrementAverage (l.map (fun p => (p.1/c,p.2))) (fun x => c*f x) g=
      vectorIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementAverage,ih,vectorIncrementChain_div_scale l c hc,
      vectorStepAverage_div_scale p.1 c hc]
end Scale

theorem narrowCommonBase_comp (f : ℝ → ℝ) :
    (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) ∘ narrowCommonEmbedding=
      fun p => 3*f p.1 := by
  funext p
  simp only [Function.comp_def,narrowCommonEmbedding_apply]
  ring

theorem narrowCommon_image (c : List (ℝ × (ℝ × ℝ))) :
    (c.map (fun p => (p.1/3,p.2))).map (fun p => (p.1,narrowCommonEmbedding p.2))=narrowRetainedCommon c := by
  simp only [List.map_map,narrowRetainedCommon,Function.comp_def,narrowCommonEmbedding_apply,Prod.mk.eta]

theorem narrowRetainedCommon_average (c : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ)
    (g : NarrowRetainedState → ℝ) (p : ℝ × ℝ) :
    vectorIncrementAverage (narrowRetainedCommon c) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) g
      (narrowCommonEmbedding p)=vectorIncrementAverage c (fun p : ℝ × ℝ => f p.1) (g ∘ narrowCommonEmbedding) p := by
  have H := congrFun (vectorIncrementAverage_pullback narrowCommonEmbedding
    (c.map (fun p => (p.1/3,p.2))) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1) g) p
  rw [narrowCommonBase_comp,narrowCommon_image,vectorIncrementAverage_div_scale c 3 (by norm_num)] at H
  exact H.symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowBaseFactor
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

theorem narrowRetainedPrefix_average (c v w : List (ℝ × (ℝ × ℝ)))
    (hv : weightedUnderlying v=weightedUnderlying w) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {H : ℝ → ℝ} (hH : Continuous H) (hHE : HasExpGrowth H) :
    vectorIncrementAverage (narrowRetainedPrefix c v w) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
      (fun p => H p.2.1*(p.1.2+p.2.2)^2) 0=
      vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
      (fun p =>
        vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (p.1,0)*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1) p+
        2*(vectorIncrementAverage v (fun q : ℝ × ℝ => f q.1) (fun q => q.2) (p.1,0)*
          vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2) p)+
        vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => H q.1*q.2^2) p) (0,0) := by
  rw [narrowRetainedPrefix,vectorIncrementAverage_append,narrowRetainedMiddle_value v w hf,hv,
    narrowRetainedMiddle_moment v w hf hH hHE]
  exact narrowRetainedCommon_average c (scalarIncrementChain (weightedUnderlying w) f) _ 0

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

theorem scalarIncrementAverage_abs_le (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {C : ℝ} (hg : ∀ x,|g x|≤C) (x : ℝ) :
    |scalarIncrementAverage l f g x|≤C := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_abs_le hf hg _ _ _ _

theorem scalarIncrementAverage_nonneg (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hpos : ∀ x,0≤g x) (x : ℝ) :
    0 ≤ scalarIncrementAverage l f g x := by
  rw [scalarIncrementAverage_get,scalarHierarchyAverage_integral hf hg]
  exact integral_nonneg (fun _ => hpos _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverageProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementAverage_product_plus_le (l : List (ℝ × E)) {f R C D T : E → ℝ}
    (hf : BoundedDerivs f) (hR : Continuous R) (hC : Continuous C) (hD : Continuous D) (hT : Continuous T)
    (hRE : HasExpGrowth R) (hCE : HasExpGrowth C) (hDE : HasExpGrowth D) (hTE : HasExpGrowth T)
    {V : ℝ} (hV : ∀ x,R x ≤ V) (hC0 : ∀ x,0 ≤ C x) (Λ : ℝ) (x : E) :
    vectorIncrementAverage l f (fun x => R x*C x+Λ*D x+T x) x ≤
      V*vectorIncrementAverage l f C x+Λ*vectorIncrementAverage l f D x+vectorIncrementAverage l f T x := by
  have H := vectorIncrementAverage_mono l (g:=fun x => R x*C x+Λ*D x+T x)
    (h:=fun x => V*C x+Λ*D x+T x) hf
    (((hR.mul hC).add (continuous_const.mul hD)).add hT)
    (((continuous_const.mul hC).add (continuous_const.mul hD)).add hT)
    (((hRE.mul hCE).add ((HasExpGrowth.const Λ).mul hDE)).add hTE)
    ((((HasExpGrowth.const V).mul hCE).add ((HasExpGrowth.const Λ).mul hDE)).add hTE)
    (fun x => by nlinarith [mul_le_mul_of_nonneg_right (hV x) (hC0 x)]) x
  rw [vectorIncrementAverage_add l (g:=fun x => V*C x+Λ*D x) (h:=T) hf
    ((continuous_const.mul hC).add (continuous_const.mul hD)) hT
    (((HasExpGrowth.const V).mul hCE).add ((HasExpGrowth.const Λ).mul hDE)) hTE] at H
  simp only at H
  rw [vectorIncrementAverage_add l (g:=fun x => V*C x) (h:=fun x => Λ*D x) hf (continuous_const.mul hC) (continuous_const.mul hD)
    ((HasExpGrowth.const V).mul hCE) ((HasExpGrowth.const Λ).mul hDE)] at H
  simpa only [vectorIncrementAverage_const_mul] using H
end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowMomentBound
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

theorem narrowSusceptibility_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowSusceptibility c w t=scalarIncrementAverage (weightedUnderlying (c++w))
      (scalarIncrementChain t scalarSpinTerminal) (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) 0 := by
  dsimp only [narrowSusceptibility]
  rw [weightedBranch_average,weightedBranch_average,weightedUnderlying_append,scalarIncrementAverage_append]

theorem narrowSusceptibility_abs_le (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈t,p.1∈Icc (0:ℝ) 1) : |narrowSusceptibility c w t| ≤ 1 := by
  rw [narrowSusceptibility_eq]
  exact scalarIncrementAverage_abs_le _ (scalarIncrementChain_regular t scalarSpinTerminal_regular)
    (fun x => ((scalarIncrementChain_spin_convex t hm).bounds x).2) 0

theorem narrowBaseQuadratic_ramp_le (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (ht : ∀ p∈t,p.1∈Icc (0:ℝ) 1)
    (hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1) (hsv : v.Pairwise (fun p q => p.1 ≤ q.1))
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ j,|scalarLevelField v.length (fun i => (v.get i).2.1) j
      (coordinateVector v.length (fun i => (v.get i).2.2))| ≤ B) :
    narrowBaseQuadratic c v w t ≤ weightedVariance v*narrowSusceptibility c w t+6*B^2+
      2*weightedMean v*narrowMixedMoment c w t+narrowTentSquare c w t := by
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  have hf : BoundedDerivs f := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hspin : ScalarSpinConvex f := scalarIncrementChain_spin_convex t ht
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  let P : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let Z : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := P.prod 0
  let R : ℝ × ℝ → ℝ := fun p => vectorIncrementAverage v (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (p.1,0)
  let C : ℝ × ℝ → ℝ := vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1)
  let D : ℝ × ℝ → ℝ := fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1)
    (fun p => rootHessian 0 f p.1*p.2) p*rootGradient 0 F p.1
  let T : ℝ × ℝ → ℝ := vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2^2)
  have hχ : HasExpGrowth (rootHessian 0 f) := HasExpGrowth.of_bounded zero_le_one
    (fun x => by simpa only [Real.norm_eq_abs] using (hspin.bounds x).2)
  have hχc : Continuous (fun p : ℝ × ℝ => rootHessian 0 f p.1) := (rootHessian_continuous 0 hf).comp continuous_fst
  have hχE := hχ.compCLM P
  have hR' := vectorIncrementAverage_regular v (hf.compCLM P)
    (g:=fun p : ℝ × ℝ => p.2^2) (continuous_snd.pow 2)
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2)
  have hR : Continuous R ∧ HasExpGrowth R := ⟨hR'.1.comp Z.continuous,hR'.2.compCLM Z⟩
  have hC : Continuous C ∧ HasExpGrowth C := vectorIncrementAverage_regular w (hf.compCLM P) hχc hχE
  have hT : Continuous T ∧ HasExpGrowth T := vectorIncrementAverage_regular w (hf.compCLM P)
    (hχc.mul (continuous_snd.pow 2)) (hχE.mul ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2))
  have hD' := vectorIncrementAverage_regular w (hf.compCLM P)
    (g:=fun p : ℝ × ℝ => rootHessian 0 f p.1*p.2) (hχc.mul continuous_snd)
    (hχE.mul (HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)))
  have hfull : ∀ p∈weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · rw [← hv] at hp
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      exact hmv z hz
    · exact ht p hp
  have hFspin : ScalarSpinConvex F := by
    dsimp only [F,f]
    rw [← scalarIncrementChain_append]
    exact scalarIncrementChain_spin_convex _ hfull
  have hU : HasExpGrowth (rootGradient 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun x => by simpa only [Real.norm_eq_abs] using (hFspin.bounds x).1)
  have hD : Continuous D ∧ HasExpGrowth D := ⟨hD'.1.mul ((rootGradient_continuous 0 hF).comp continuous_fst),hD'.2.mul (hU.compCLM P)⟩
  have hC0 (p : ℝ × ℝ) : 0 ≤ C p := by
    dsimp only [C]
    rw [weightedBranch_average]
    exact scalarIncrementAverage_nonneg _ hf (hspin.hessian_bounded hf) (fun x => (hspin x).1) p.1
  have hRle (p : ℝ × ℝ) : R p ≤ weightedVariance v+6*B^2 := by
    have H := (abs_le.mp (weightedList_ramp_square_error v hmv hsv hf hspin hB hprefix p.1)).2
    dsimp only [R]; linarith
  have H := vectorIncrementAverage_product_plus_le c (hf:=hF.compCLM P) hR.1 hC.1 hD.1 hT.1
    hR.2 hC.2 hD.2 hT.2 hRle hC0 (2*weightedMean v) (0,0)
  have hM (x : ℝ) : vectorIncrementAverage v (fun p : ℝ × ℝ => f p.1) (fun p => p.2) (x,0)=weightedMean v*rootGradient 0 F x := by
    rw [weightedList_tail_mean,hv,scalarIncrementChain_append]
    rfl
  have HQ : narrowBaseQuadratic c v w t=vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
      (fun p => R p*C p+(2*weightedMean v)*D p+T p) (0,0) := by
    rw [narrowBaseQuadratic,narrowRetainedPrefix_average c v w hv hf (rootHessian_continuous 0 hf) hχ]
    congr 2
    funext p
    rw [hM]
    dsimp only [R,C,D,T]
    ring
  rw [HQ]
  have Hs := (abs_le.mp (narrowSusceptibility_abs_le c w t ht)).2
  change _ ≤ (weightedVariance v+6*B^2)*narrowSusceptibility c w t+
    2*weightedMean v*narrowMixedMoment c w t+narrowTentSquare c w t at H
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left Hs (show 0 ≤ 6*B^2 by positivity)])

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTentBound
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

theorem narrowTentSquare_eq (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    narrowTentSquare c w t=vectorIncrementAverage (c++w)
      (fun p : ℝ × ℝ => scalarIncrementChain t scalarSpinTerminal p.1)
      (fun p => p.2^2*rootHessian 0 (scalarIncrementChain t scalarSpinTerminal) p.1) (0,0) := by
  dsimp only [narrowTentSquare]
  rw [vectorIncrementAverage_append,weightedBranch_value]
  congr 3
  funext p
  ring

theorem narrowBaseQuadratic_tent_le (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1) (hs : (c++w).Pairwise (fun p q => p.1 ≤ q.1))
    (ht : ∀ p∈t,p.1∈Icc (0:ℝ) 1) (hst : t.Pairwise (fun p q => p.1 ≤ q.1))
    (hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1) (hsv : v.Pairwise (fun p q => p.1 ≤ q.1))
    (hmean : 0 ≤ weightedMean v)
    (l s : Fin ((c++w).length+1))
    (hlr : l ≤ ⟨c.length,by simp only [List.length_append]; omega⟩)
    (hrs : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1)) ≤ s)
    {h B R : ℝ} (hh : 0<h) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hleft : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
      ⟨c.length,by simp only [List.length_append]; omega⟩-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) l=B*h)
    (hright : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) s-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
        ⟨c.length,by simp only [List.length_append]; omega⟩=B*h)
    (ha : (fun i => ((c++w).get i).2.2)=scalarTentVector (c++w).length
      (fun i => ((c++w).get i).2.1) l ⟨c.length,by simp only [List.length_append]; omega⟩ s h)
    (hprefix : ∀ j,|scalarLevelField v.length (fun i => (v.get i).2.1) j
      (coordinateVector v.length (fun i => (v.get i).2.2))| ≤ R) :
    narrowBaseQuadratic c v w t ≤ narrowVariance c v w*narrowSusceptibility c w t+
      2*weightedMean v*B*narrowJointMoment c w t+6*R^2+
      2*weightedMean v*B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s+
      (B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s)^2+
      B^2*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s := by
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  have hf : BoundedDerivs f := scalarIncrementChain_regular t scalarSpinTerminal_regular
  have hspin : ScalarSpinConvex f := scalarIncrementChain_spin_convex t ht
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ hf
  have hFspin : ScalarSpinConvex F := by
    dsimp only [F,f]
    rw [← scalarIncrementChain_append]
    apply scalarIncrementChain_spin_convex
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
      exact hm z (List.mem_append_right _ hz)
    · exact ht p hp
  have hχL := scalarIncrementChain_hessian_lipschitz t ht hst
  have hχb : ∀ y,|rootHessian 0 f y| ≤ 1 := fun y => (hspin.bounds y).2
  have HM := weightedSplit_tent_mixed_error c w hm hs hf hspin hF hFspin l s hlr hrs hh hB hleft hright ha hχL hχb 0
  change |narrowMixedMoment c w t-B*narrowJointMoment c w t| ≤ _ at HM
  have HT := weightedList_tent_square_error (c++w) hm hs hf hspin l
    ⟨c.length,by simp only [List.length_append]; omega⟩ s hlr hrs hh hB hleft hright ha hχL hχb 0
  rw [← narrowTentSquare_eq,← narrowSusceptibility_eq] at HT
  have HQ := narrowBaseQuadratic_ramp_le c v w t hv ht hmv hsv hR hprefix
  have HM' := mul_le_mul_of_nonneg_left (abs_le.mp HM).2 (show 0 ≤ 2*weightedMean v by positivity)
  have HT' := (abs_le.mp HT).2
  have HV : narrowVariance c v w=weightedVariance v+weightedVariance (c++w) := by
    rw [weightedVariance_append]
    unfold narrowVariance
    ring
  rw [HV]
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockQuadratic_tent_le_oai (κ η : ℝ) (b l j k t : List (ℝ × ℝ))
    (hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1)
    (hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1))
    (hmean : 0≤weightedMean (fourBlockFuture η j k))
    {d B : ℝ} (hd : 0<d) (hB : 0≤B) (hκ : κ*d=1)
    (hl : rawVariance l=B*d) (hj : rawVariance j=B*d) :
    narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤
      narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
        narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      2*weightedMean (fourBlockFuture η j k)*B*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      6*(weightedAbsCross (fourBlockFuture η j k))^2+
      2*weightedMean (fourBlockFuture η j k)*B*scalarTentAtomMass (fourBlockTent κ b l j k).length
        (fun i => ((fourBlockTent κ b l j k).get i).1) (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)+
      (B*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k))^2+
      B^2*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k) := by
  let c := fourBlockCommon κ b l
  let v := fourBlockFuture η j k
  let w := fourBlockFuture (-κ) j k
  have hc : weightedUnderlying c=b++l := by simp [c,fourBlockCommon]
  have hv : weightedUnderlying v=j++k := by simp [v,fourBlockFuture]
  have hw : weightedUnderlying w=j++k := by simp [w,fourBlockFuture]
  have hcw : weightedUnderlying (c++w)=(b++l)++(j++k) := by rw [weightedUnderlying_append,hc,hw]
  have hmcw : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1 := by
    apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
    rw [hcw]
    intro p hp; exact hm p (List.mem_append_left _ hp)
  have hscw : (c++w).Pairwise (fun p q => p.1≤q.1) := by
    apply (weighted_sorted_iff _).mpr
    rw [hcw]
    exact (List.pairwise_append.mp hs).1
  have hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1 := by
    apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
    rw [hv]
    intro p hp; exact hm p (List.mem_append_left _ (List.mem_append_right _ hp))
  have hsv : v.Pairwise (fun p q => p.1≤q.1) := by
    apply (weighted_sorted_iff _).mpr
    rw [hv]
    exact (List.pairwise_append.mp (List.pairwise_append.mp hs).1).2.1
  have hR : 0≤weightedAbsCross v := by
    unfold weightedAbsCross
    apply List.sum_nonneg
    intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx; positivity
  have he : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1))=
      fourBlockMiddle κ b l j k := by
    apply Fin.ext
    simp [c,fourBlockCommon,zeroWeightChain,constantWeightChain]
  apply narrowBaseQuadratic_tent_le c v w t (hv.trans hw.symm) hmcw hscw
    (fun p hp => hm p (List.mem_append_right _ hp)) (List.pairwise_append.mp hs).2.1 hmv hsv hmean
    (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)
  · rw [he]; change b.length≤b.length+l.length; omega
  · rw [he]; change b.length+l.length≤b.length+l.length+j.length; omega
  · exact hd
  · exact hB
  · exact hR
  · rw [he,fourBlockTent_middle_variance,fourBlockTent_left_variance,hl]; ring
  · rw [he,fourBlockTent_middle_variance,fourBlockTent_right_variance,hj]; ring
  · rw [he]; exact fourBlockTent_vector (ne_of_gt hd) hκ b l j k
  · exact weightedList_field_bound v

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.fourBlockQuadratic_tent_le_oai := @OAI.SK.Analytic.fourBlockQuadratic_tent_le_oai
