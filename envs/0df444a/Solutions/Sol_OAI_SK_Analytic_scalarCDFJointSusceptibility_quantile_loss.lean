-- Prove2me | solution 1 for OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:14:53.19088+00:00
-- url     : https://prove2.me/submissions/09b957a0-76cb-48d4-aec1-a19dacaf2bf5

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S006

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

theorem gaussian_tilted_stein (V V' g g' : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hi : Integrable (fun x => g x*Real.exp (V x)) (gaussianReal 0 1))
    (hi' : Integrable (fun x => g' x*Real.exp (V x)) (gaussianReal 0 1))
    (hiV : Integrable (fun x => g x*V' x*Real.exp (V x)) (gaussianReal 0 1))
    (hix : Integrable (fun x => x*(g x*Real.exp (V x))) (gaussianReal 0 1)) :
    (∫ x, x*g x ∂(gaussianReal 0 1).tilted V) =
      (∫ x, g' x ∂(gaussianReal 0 1).tilted V) +
      ∫ x, g x*V' x ∂(gaussianReal 0 1).tilted V := by
  have hd (x : ℝ) : HasDerivAt (fun x => g x*Real.exp (V x))
      (g' x*Real.exp (V x)+g x*V' x*Real.exp (V x)) x := by
    convert! (hg x).mul (hV x).exp using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := gaussian_integral_mul_eq_integral_deriv _ _ hd hi (hi'.add hiV) hix
  simp only [integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [← integral_add hi' hiV]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with x
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

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitBoundedProduct_sub {a b c d : ℝ} (hb : |b|≤1) (hc : |c|≤1) :
    |a*b-c*d|≤|a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * |b|+|c| * |b-d| := by rw [abs_mul,abs_mul]
    _ ≤ |a-c| * 1+1*|b-d| := add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

theorem unitBoundedProduct_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x,|f x|≤1) (hgb : ∀ x,|g x|≤1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := unitBoundedProduct_sub (a:=f x) (d:=g y) (hgb x) (hfb y)
  have Hf := hf.dist_le_mul x y
  have Hg := hg.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_add] at Hf Hg ⊢
  nlinarith

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianTiltedCramer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem HasExpGrowth.neg_real {f : ℝ → ℝ} (hf : HasExpGrowth f) :
    HasExpGrowth (fun x => -f x) :=
  hf.congr_bound zero_le_one (fun x => by simp only [norm_neg,one_mul]; exact le_rfl)

theorem HasExpGrowth.sub_real {f g : ℝ → ℝ} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg_real

theorem HasExpGrowth.integrable_gaussianTilt {V g : ℝ → ℝ}
    (hg : HasExpGrowth g) (he : HasExpGrowth (fun x => Real.exp (V x)))
    (hV : Continuous V) (hc : Continuous g) :
    Integrable g ((gaussianReal 0 1).tilted V) := by
  rw [integrable_tilted_iff (he.integrable_gaussianMeasure (Real.continuous_exp.comp hV))]
  exact (he.smul hg).integrable_gaussianMeasure ((Real.continuous_exp.comp hV).smul hc)

theorem HasExpGrowth.memLp_two_gaussianTilt {V g : ℝ → ℝ}
    (hg : HasExpGrowth g) (he : HasExpGrowth (fun x => Real.exp (V x)))
    (hV : Continuous V) (hc : Continuous g) :
    MemLp g 2 ((gaussianReal 0 1).tilted V) := by
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  simpa only [pow_two] using (hg.mul hg).integrable_gaussianTilt he hV (hc.mul hc)

theorem gaussian_tilted_stein_growth {V V' g g' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : HasExpGrowth (fun x => Real.exp (V x)))
    (heV : HasExpGrowth V') (heg : HasExpGrowth g) (heg' : HasExpGrowth g')
    (hcV : Continuous V') (hcg' : Continuous g') :
    (∫ x, x*g x ∂(gaussianReal 0 1).tilted V)=
      (∫ x, g' x ∂(gaussianReal 0 1).tilted V)+
        ∫ x, g x*V' x ∂(gaussianReal 0 1).tilted V := by
  have hcV0 := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have hcg := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hce := Real.continuous_exp.comp hcV0
  have hx : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  apply gaussian_tilted_stein _ _ _ _ hV hg
  · exact (heg.mul he).integrable_gaussianMeasure (hcg.mul hce)
  · exact (heg'.mul he).integrable_gaussianMeasure (hcg'.mul hce)
  · exact ((heg.mul heV).mul he).integrable_gaussianMeasure ((hcg.mul hcV).mul hce)
  · exact (hx.mul (heg.mul he)).integrable_gaussianMeasure (continuous_id.mul (hcg.mul hce))

theorem cramer_of_score {μ : Measure ℝ} [IsProbabilityMeasure μ] {g S : ℝ → ℝ}
    (hg : MemLp g 2 μ) (hS : MemLp S 2 μ) {d : ℝ}
    (hmean : (∫ x, S x ∂μ)=0) (hsecond : (∫ x, S x^2 ∂μ)≤1)
    (hcov : (∫ x, g x*S x ∂μ)=d) :
    d^2≤(∫ x, g x^2 ∂μ)-(∫ x, g x ∂μ)^2 := by
  have H := variance_nonneg (X:=fun x => g x-d*S x) (μ:=μ)
  rw [variance_fun_sub hg (hS.const_mul d),covariance_const_mul_right,
    variance_const_mul,variance_eq_sub hg,variance_eq_sub hS,covariance_eq_sub hg hS] at H
  simp only [Pi.mul_apply,Pi.pow_apply,hmean,hcov,mul_zero,sub_zero,zero_pow (by decide : 2≠0)] at H
  nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hsecond)]

theorem gaussian_tilted_cramer {V V' V'' g g' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : HasExpGrowth (fun x => Real.exp (V x)))
    (heV : HasExpGrowth V') (heV' : HasExpGrowth V'')
    (heg : HasExpGrowth g) (heg' : HasExpGrowth g')
    (hcV' : Continuous V'') (hcg' : Continuous g') (hconvex : ∀ x, 0≤V'' x) :
    (∫ x, g' x ∂(gaussianReal 0 1).tilted V)^2≤
      (∫ x, g x^2 ∂(gaussianReal 0 1).tilted V)-
        (∫ x, g x ∂(gaussianReal 0 1).tilted V)^2 := by
  let μ := (gaussianReal 0 1).tilted V
  have hcV := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have hcV1 := continuous_iff_continuousAt.mpr (fun x => (hV' x).continuousAt)
  have hcg := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted (he.integrable_gaussianMeasure (Real.continuous_exp.comp hcV))
  have hx : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hconst (c : ℝ) : HasExpGrowth (fun _ : ℝ => c) :=
    HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  let S : ℝ → ℝ := fun x => x-V' x
  have hs : HasExpGrowth S := hx.sub_real heV
  have hcS : Continuous S := continuous_id.sub hcV1
  have hS' (x : ℝ) : HasDerivAt S (1-V'' x) x := (hasDerivAt_id x).sub (hV' x)
  have hi (f : ℝ → ℝ) (hf : HasExpGrowth f) (hc : Continuous f) : Integrable f μ :=
    hf.integrable_gaussianTilt he hcV hc
  have hmean : (∫ x, S x ∂μ)=0 := by
    have H := gaussian_tilted_stein_growth hV (fun x => hasDerivAt_const x (1:ℝ)) he heV
      (hconst 1) (hconst 0) hcV1 continuous_const
    simp only [mul_one,one_mul,integral_zero,zero_add] at H
    rw [integral_sub (hi _ hx continuous_id) (hi _ heV hcV1),H,sub_self]
  have hscore : (∫ x, S x^2 ∂μ)=1-∫ x, V'' x ∂μ := by
    have H := gaussian_tilted_stein_growth hV hS' he heV hs
      ((hconst 1).sub_real heV') hcV1 (continuous_const.sub hcV')
    have HE (x : ℝ) : S x^2=x*S x-S x*V' x := by dsimp [S]; ring
    simp_rw [HE]
    rw [integral_sub (hi _ (hx.mul hs) (continuous_id.mul hcS))
      (hi _ (hs.mul heV) (hcS.mul hcV1)),H,add_sub_cancel_right,
      integral_sub (integrable_const 1) (hi _ heV' hcV'),integral_const,probReal_univ,one_smul]
  have hsecond : (∫ x, S x^2 ∂μ)≤1 := by
    rw [hscore]
    have HP : 0≤∫ x, V'' x ∂μ := integral_nonneg hconvex
    linarith
  have hcov : (∫ x, g x*S x ∂μ)=∫ x, g' x ∂μ := by
    have H := gaussian_tilted_stein_growth hV hg he heV heg heg' hcV1 hcg'
    have HE (x : ℝ) : g x*S x=x*g x-g x*V' x := by dsimp [S]; ring
    simp_rw [HE]
    rw [integral_sub (hi _ (hx.mul heg) (continuous_id.mul hcg))
      (hi _ (heg.mul heV) (hcg.mul hcV1)),H,add_sub_cancel_right]
  exact cramer_of_score (heg.memLp_two_gaussianTilt he hcV hcg)
    (hs.memLp_two_gaussianTilt he hcV hcS) hmean hsecond hcov

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

theorem scalarStepAverage_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) {m : ℝ} (hm : 0 ≤ m) (v x : ℝ) :
    v^2*(scalarStepAverage m v f (rootHessian 0 f) x)^2 ≤
      scalarStepAverage m v f (fun y => (rootGradient 0 f y)^2) x-
        (scalarStepAverage m v f (rootGradient 0 f) x)^2 := by
  have hdf (y : ℝ) : HasDerivAt f (rootGradient 0 f y) y :=
    (hf.1.differentiable (by norm_num) y).hasDerivAt
  have hdu (y : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f y) y := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 y
  have hcχ : Continuous (fun y : ℝ => rootHessian 0 f (x+v*y)) :=
    (rootHessian_continuous 0 hf).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hV (y : ℝ) : HasDerivAt (fun y => m*f (x+v*y)) (m*v*rootGradient 0 f (x+v*y)) y := by
    convert ((hdf (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x)).const_mul m using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hV' (y : ℝ) : HasDerivAt (fun y => m*v*rootGradient 0 f (x+v*y))
      (m*v^2*rootHessian 0 f (x+v*y)) y := by
    convert ((hdu (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x)).const_mul (m*v) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hg (y : ℝ) : HasDerivAt (fun y => rootGradient 0 f (x+v*y))
      (v*rootHessian 0 f (x+v*y)) y := by
    convert (hdu (x+v*y)).comp y (((hasDerivAt_id y).const_mul v).const_add x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  have hbu : HasExpGrowth (fun y => rootGradient 0 f (x+v*y)) :=
    HasExpGrowth.of_bounded zero_le_one (fun y => (h.bounds _).1)
  have hbχ : HasExpGrowth (fun y => rootHessian 0 f (x+v*y)) :=
    HasExpGrowth.of_bounded zero_le_one (fun y => (h.bounds _).2)
  have hconst (c : ℝ) : HasExpGrowth (fun _ : ℝ => c) :=
    HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  have hreg : BoundedDerivs (fun y => f (x+v*y)) :=
    (hf.translate x).compCLM (v • ContinuousLinearMap.id ℝ ℝ)
  have H := gaussian_tilted_cramer hV hV' hg (hreg.exp_growths m).1
    ((hconst (m*v)).mul hbu) ((hconst (m*v^2)).mul hbχ) hbu ((hconst v).mul hbχ)
    (continuous_const.mul hcχ) (continuous_const.mul hcχ)
    (fun y => mul_nonneg (mul_nonneg hm (sq_nonneg v)) (h _).1)
  rw [integral_const_mul,mul_pow] at H
  exact H

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

theorem BoundedScalar.const (c : ℝ) : BoundedScalar (fun _ => c) :=
  ⟨continuous_const,|c|,abs_nonneg _,fun _ => le_rfl⟩

theorem BoundedScalar.add {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x+h x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  obtain ⟨C,hC,hc⟩ := hh.bounded
  exact ⟨hg.continuous.add hh.continuous,B+C,add_nonneg hB hC,
    fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩

theorem BoundedScalar.const_mul {g : ℝ → ℝ} (hg : BoundedScalar g) (c : ℝ) :
    BoundedScalar (fun x => c*g x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨continuous_const.mul hg.continuous,|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem BoundedScalar.sub {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x-h x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hg.add (hh.const_mul (-1))

theorem BoundedScalar.sq {g : ℝ → ℝ} (hg : BoundedScalar g) :
    BoundedScalar (fun x => (g x)^2) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨hg.continuous.pow 2,B^2,sq_nonneg _,fun x => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb x) _

theorem ScalarSpinConvex.gradient_bounded {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) : BoundedScalar (rootGradient 0 f) :=
  ⟨rootGradient_continuous 0 hf,1,zero_le_one,fun x => (h.bounds x).1⟩

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

theorem scalarHierarchyAverage_const_mul {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x c : ℝ) :
    scalarHierarchyAverage n m v f (fun y => c*g y) x=c*scalarHierarchyAverage n m v f g x := by
  rw [scalarHierarchyAverage_integral hf (hg.const_mul c),scalarHierarchyAverage_integral hf hg,
    integral_const_mul]

theorem scalarHierarchyAverage_add {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y+h y) x=
      scalarHierarchyAverage n m v f g x+scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.add hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_add
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

theorem scalarHierarchyAverage_sub {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y-h y) x=
      scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.sub hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_sub
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

theorem scalarHierarchyAverage_mono {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (hle : ∀ x, g x ≤ h x)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x ≤ scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf hg,scalarHierarchyAverage_integral hf hh]
  exact integral_mono (scalarHierarchyAverage_integrable hf hg n m v x)
    (scalarHierarchyAverage_integrable hf hh n m v x) (fun z => hle _)

theorem scalarHierarchyAverage_nonneg {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hle : ∀ x, 0 ≤ g x) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    0 ≤ scalarHierarchyAverage n m v f g x := by
  rw [scalarHierarchyAverage_integral hf hg]
  exact integral_nonneg (fun z => hle _)

theorem scalarHierarchyAverage_sq {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    (scalarHierarchyAverage n m v f g x)^2 ≤ scalarHierarchyAverage n m v f (fun y => (g y)^2) x := by
  rw [scalarHierarchyAverage_integral hf hg,scalarHierarchyAverage_integral hf hg.sq]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  obtain ⟨B,_,hb⟩ := hg.bounded
  have H : MemLp (fun z => g (x+coordinateLinear n v z)) 2
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    MemLp.of_bound (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous)).aestronglyMeasurable
      B (ae_of_all _ (fun z => hb _))
  have HP := variance_nonneg (X:=fun z => g (x+coordinateLinear n v z))
    (μ:=hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0)
  rw [variance_eq_sub H] at HP
  exact sub_nonneg.mp HP

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

theorem scalarHierarchyAverage_observable_distance {f g a : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (ha : BoundedScalar a)
    {δ : ℝ} (_hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f a x| ≤ δ := by
  rw [← scalarHierarchyAverage_sub hf hg ha,
    scalarHierarchyAverage_integral hf (hg.sub ha)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (f:=fun z => g (x+coordinateLinear n v z)-a (x+coordinateLinear n v z))
    (C:=δ) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hga (x+coordinateLinear n v z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_tendsto_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hB : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := ε/(4*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/4 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/4 := by dsimp [h]; field_simp
  let C : ℝ≥0 := ⟨2*(B:ℝ)/h,div_nonneg (by positivity) hh.le⟩
  have hW := dyadicScalarAverage_tendsto_C1 β hα hmono hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (C:=C)
    (scalarWindowDerivative_bound hB hh) s t ht x
  have hc := Metric.cauchySeq_iff.mp hW.cauchySeq (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun m hm n hn => ?_⟩
  have he (j : ℕ) : |dyadicScalarAverage β α j s t f g x-
      dyadicScalarAverage β α j s t f (scalarWindow g h) x| ≤ ε/4 := by
    apply (scalarHierarchyAverage_observable_distance hf
      ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
      ⟨continuous_iff_continuousAt.mpr (fun z => (scalarWindow_hasDerivAt hgL.continuous h z).continuousAt),
        B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
      (mul_nonneg L.coe_nonneg hh.le) (fun z => ?_) _ _ _ x).trans hsmall
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have hd := hN m hm n hn
  simp only [Real.dist_eq] at hd ⊢
  have H₁ := abs_sub_le (dyadicScalarAverage β α m s t f g x)
    (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  have H₂ := abs_sub_le (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  rw [abs_sub_comm (dyadicScalarAverage β α n s t f (scalarWindow g h) x)] at H₂
  linarith [he m,he n]

theorem scalarCDFAverage_observable_distance (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B C L M : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (haM : LipschitzWith M a)
    (hB : ∀ z, |g z| ≤ B) (hC : ∀ z, |a z| ≤ C)
    {δ : ℝ} (hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β α s t f a x| ≤ δ := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haM hC s t ht x)).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩ ⟨haM.continuous,C,C.coe_nonneg,hC⟩ hδ hga _ _ _ x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindowDerivative_lipschitz_bound {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ L := by
  have H := hg.dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindow_lipschitz {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) : LipschitzWith L (scalarWindow g h) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarWindow_hasDerivAt hg.continuous h x).differentiableAt)
  intro x
  rw [(scalarWindow_hasDerivAt hg.continuous h x).deriv]
  exact_mod_cast scalarWindowDerivative_lipschitz_bound hg hh x

theorem scalarCDFAverage_eq_chainAverage_lipschitz {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {K B L : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (hB : ∀ z, |g z| ≤ B)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let h := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/2 := by dsimp [h]; field_simp
  have hd (z) : |g z-scalarWindow g h z| ≤ (L:ℝ)*h := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have H₁ := scalarCDFAverage_observable_distance β hα hmono hf hfK hgL
    (scalarWindow_lipschitz hgL hh) hB (scalarWindow_bound hgL.continuous hB hh)
    (mul_nonneg L.coe_nonneg hh.le) hd s t ht x
  have H₂ := scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
    ⟨(scalarWindow_lipschitz hgL hh).continuous,B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
    (mul_nonneg L.coe_nonneg hh.le) hd l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) x
  change |scalarTimeChainAverage β l f g x-scalarTimeChainAverage β l f (scalarWindow g h) x|≤_ at H₂
  have HE := scalarCDFAverage_eq_chainAverage hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (scalarWindowDerivative_lipschitz_bound hgL hh)
    β hα hmono l hm s t ht hdur hmodel x
  rw [HE] at H₁
  have H := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarTimeChainAverage β l f (scalarWindow g h) x) (scalarTimeChainAverage β l f g x)
  rw [abs_sub_comm (scalarTimeChainAverage β l f (scalarWindow g h) x)] at H
  linarith

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

theorem vectorIncrementChain_get (l : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain l f=vectorHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementChain_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f

theorem vectorIncrementAverage_get (l : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage l f g=vectorHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementAverage_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g

end Vector

theorem vectorIncrementAverage_real (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    vectorIncrementAverage l f g=scalarIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,scalarIncrementAverage,vectorIncrementChain_real,ih,vectorStepAverage_real]

theorem scalarIncrementAverage_ofFn (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=scalarHierarchyAverage n m v f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_ofFn,vectorHierarchyAverage_real]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightStats
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

theorem rawVariance_nonneg (l : List (ℝ × ℝ)) : 0 ≤ rawVariance l := by
  exact List.sum_nonneg (by intro a ha; obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha; exact sq_nonneg _)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeIncrementBridge
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

theorem rawTimeChain_mass (l : List (ℝ × ℝ≥0)) {P : ℝ → Prop} (hm : ∀ p∈l,P p.1) :
    ∀ p∈rawTimeChain l,P p.1 := by
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hm q hq

theorem rawTimeChain_sorted (l : List (ℝ × ℝ≥0)) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    (rawTimeChain l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [rawTimeChain,List.pairwise_map] using hs

theorem scalarIncrementChain_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f=scalarTimeChain β l f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change scalarStep p.1 (β*Real.sqrt (p.2:ℝ)) (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f)=_
    rw [ih]
    rfl

theorem scalarIncrementAverage_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l)) f g=scalarTimeChainAverage β l f g := by
  have he : scaleIncrementChain β (rawTimeChain l)=List.ofFn (fun i : Fin l.length => ((l.get i).1,β*Real.sqrt ((l.get i).2:ℝ))) := by
    simp only [scaleIncrementChain,rawTimeChain,List.map_map]
    conv_lhs => rw [← List.ofFn_get l,List.map_ofFn]
    rfl
  rw [he,scalarIncrementAverage_ofFn]
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
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

theorem quantile_knots_gap (k : ℕ) (Q : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    Fin.cons (α := fun _ => ℝ) 0 Q i.succ-Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc=cumulativeGapMap k Q i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rfl

theorem quantile_prefix_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) :
    ∃ l : List (ℝ × ℝ≥0),
      (chainDuration l:ℝ)=Q (Fin.last k) ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β f, scalarTimeChain β l f=scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) f := by
  let q := Fin.cons (α := fun _ => ℝ) 0 Q
  let hq := monotone_cons_zero_quantiles Q hQ h0
  let l := partitionTimeChain (k+1) q hq (quantileMass k)
  refine ⟨l,?_,?_,?_,?_⟩
  · have H := partitionTimeChain_duration (k+1) q hq (quantileMass k)
    simpa only [q,← Fin.succ_last,Fin.cons_succ,Fin.cons_zero,sub_zero] using H
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    change quantileMass k i ∈ Icc (0:ℝ) 1
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
      exact_mod_cast i.isLt.le
  · change TimeChainModels (quantileCDF k Q) (q 0) (partitionTimeChain (k+1) q hq (quantileMass k))
    apply partitionTimeChain_models
    intro i z hz
    exact quantileCDF_on_interval Q hQ i z hz
  · intro β f
    dsimp only [l,partitionTimeChain]
    rw [scalarTimeChain_ofFn]
    congr 2
    funext i
    simp only [NNReal.coe_mk, q]
    rw [quantile_knots_gap]
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFAtomicRepresentation
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

theorem quantile_full_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=1 ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β, scalarTimeChain β l scalarSpinTerminal 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ h0
  let t := NNReal.mk (1-Q (Fin.last k)) (sub_nonneg.mpr h1)
  refine ⟨l++[(1,t)],?_,?_,?_,?_⟩
  · apply NNReal.coe_injective
    simp only [chainDuration_append,chainDuration_cons,chainDuration_nil,add_zero,
      NNReal.coe_add,hd,t,NNReal.coe_mk,NNReal.coe_one]
    ring
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  · apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ
      simpa only [zero_add,hd] using hz.1
    · trivial
  · intro β
    rw [scalarTimeChain_append]
    simp only [scalarTimeChain]
    rw [he]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyCramer
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

theorem scalarHierarchy_cramer_data {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (x : ℝ) :
    let K := scalarHierarchyAverage n m v f (rootHessian 0 f) x
    let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarHierarchy n m v f) x)^2
    let H := rootHessian 0 (scalarHierarchy n m v f) x
    0 ≤ K ∧ K ≤ H ∧ H ≤ K+V ∧ (∑ i, (v i)^2)*K^2 ≤ V := by
  induction n generalizing f with
  | zero => simpa only [scalarHierarchyAverage,scalarHierarchy,Finset.univ_eq_empty,
      Finset.sum_empty,zero_mul,sub_self,add_zero,le_refl,and_true] using (h x).1
  | succ n ih =>
    let c := m (Fin.last n)
    let w := v (Fin.last n)
    let m' : Fin n → ℝ := fun i => m i.castSucc
    let v' : Fin n → ℝ := fun i => v i.castSucc
    let F := scalarStep c w f
    let E : (ℝ → ℝ) → ℝ := fun g => scalarHierarchyAverage n m' v' F g x
    let k := scalarStepAverage c w f (rootHessian 0 f)
    let u := scalarStepAverage c w f (rootGradient 0 f)
    let b := fun y => scalarStepAverage c w f (fun z => (rootGradient 0 f z)^2) y-(u y)^2
    let A := E k
    let B := E b
    let W := E (fun y => (rootGradient 0 F y)^2)-(rootGradient 0 (scalarHierarchy n m' v' F) x)^2
    have hF : BoundedDerivs F := scalarStep_regular hf _ _
    have hFc : ScalarSpinConvex F := h.scalarStep hf (hm _) _
    have hk : BoundedScalar k := (h.hessian_bounded hf).scalarStepAverage hf _ _
    have hu : BoundedScalar u := (h.gradient_bounded hf).scalarStepAverage hf _ _
    have he2 := (h.gradient_bounded hf).sq.scalarStepAverage hf c w
    have hb : BoundedScalar b := he2.sub hu.sq
    have hb0 (y : ℝ) : 0 ≤ b y := scalarStepAverage_variance_nonneg hf
      (rootGradient_continuous 0 hf) (fun z => (h.bounds z).1) c w y
    have hk0 (y : ℝ) : 0 ≤ k y := integral_nonneg (fun z => (h _).1)
    have hA : 0 ≤ A := scalarHierarchyAverage_nonneg hF hk hk0 n m' v' x
    have hB : 0 ≤ B := scalarHierarchyAverage_nonneg hF hb hb0 n m' v' x
    have hug : rootGradient 0 F=u := funext (scalarStep_rootGradient hf c w)
    have hχ : rootHessian 0 F=fun y => k y+c*b y := funext (scalarStep_rootHessian hf c w)
    have hEK : E (rootHessian 0 F)=A+c*B := by
      rw [hχ]
      exact (scalarHierarchyAverage_add hF hk (hb.const_mul c) n m' v' x).trans
        (congrArg (A+·) (scalarHierarchyAverage_const_mul hF hb n m' v' x c))
    have hEV : E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
        (rootGradient 0 (scalarHierarchy n m' v' F) x)^2=W+B := by
      have H := scalarHierarchyAverage_sub hF he2 hu.sq n m' v' x
      change B=E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-E (fun y => (u y)^2) at H
      dsimp [W]
      rw [hug]
      linarith
    have hbcr : w^2*A^2 ≤ B := by
      have H := scalarHierarchyAverage_mono hF (hk.sq.const_mul (w^2)) hb
        (fun y => scalarStepAverage_cramer hf h (hm _).1 w y) n m' v' x
      rw [scalarHierarchyAverage_const_mul hF hk.sq] at H
      have HJ := scalarHierarchyAverage_sq hF hk n m' v' x
      exact (mul_le_mul_of_nonneg_left HJ (sq_nonneg w)).trans H
    have I := ih hF hFc m' v' (fun i => hm _)
    change 0 ≤ E (rootHessian 0 F) ∧
      E (rootHessian 0 F) ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ E (rootHessian 0 F)+W ∧
      (∑ i, (v' i)^2)*(E (rootHessian 0 F))^2 ≤ W at I
    rw [hEK] at I
    change 0 ≤ A ∧ A ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ A+
        (E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
          (rootGradient 0 (scalarHierarchy n m' v' F) x)^2) ∧
      (∑ i, (v i)^2)*A^2 ≤ E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
          (rootGradient 0 (scalarHierarchy n m' v' F) x)^2
    rw [hEV,Fin.sum_univ_castSucc]
    change 0 ≤ A ∧ A ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ A+(W+B) ∧
      ((∑ i, (v' i)^2)+w^2)*A^2 ≤ W+B
    have hc0 := (hm (Fin.last n)).1
    have hc1 := (hm (Fin.last n)).2
    have hAB : A ≤ A+c*B := by dsimp [c]; nlinarith
    have hs0 : 0 ≤ ∑ i, (v' i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hsq : A^2 ≤ (A+c*B)^2 := pow_le_pow_left₀ hA hAB 2
    have HI := (mul_le_mul_of_nonneg_left hsq hs0).trans I.2.2.2
    refine ⟨hA,hAB.trans I.2.1,?_,?_⟩
    · dsimp [c] at I
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hB]
    · nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFCramer
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

theorem scalarCDFValue_rootGradient (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootGradient 0 (scalarCDFValue β α s t)=scalarCDFGradient β α s t := by
  funext x
  exact ((scalarCDFValue_regular β ha hm s t ht).1.differentiable (by norm_num) x |>.hasDerivAt).unique
    (scalarCDFValue_hasDerivAt β ha hm s t ht x)

theorem scalarCDFValue_rootHessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootHessian 0 (scalarCDFValue β α s t)=scalarCDFHessian β α s t := by
  funext x
  have H : HasDerivAt (rootGradient 0 (scalarCDFValue β α s t))
      (rootHessian 0 (scalarCDFValue β α s t) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 (scalarCDFValue_regular β ha hm s t ht) 0 x
  rw [scalarCDFValue_rootGradient β ha hm s t ht] at H
  exact H.unique (scalarCDFGradient_hasDerivAt β ha hm s t ht x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSquareSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitBoundedSquare_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∀ x,|f x|≤1) :
    LipschitzWith (2*K) (fun x => (f x)^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_mul,NNReal.coe_ofNat]
  have H := (abs_sq_sub_sq_le_two (hb x) (hb y)).trans
    (mul_le_mul_of_nonneg_left (show |f x-f y|≤(K:ℝ)*|x-y| from by
      simpa only [Real.dist_eq] using hf.dist_le_mul x y) (by norm_num))
  nlinarith

theorem scalarCDFHessian_square_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t≤1) :
    LipschitzWith (2*susceptibilityLipschitzConstant) (fun x => (scalarCDFHessian β α s t x)^2) :=
  unitBoundedSquare_lipschitz (scalarCDFHessian_lipschitz β ha hm s t ht)
    (scalarCDFHessian_abs_le_one β ha hm s t ht)

theorem scalarCDFHessian_square_bound (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |(scalarCDFHessian β α s t x)^2|≤1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (scalarCDFHessian_abs_le_one β ha hm s t ht x)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSuffixSemigroup
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

theorem quantile_suffix_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=Real.toNNReal (1-s) ∧
      (∀ p∈l, p.1∈Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have he : chainDuration l=Real.toNNReal s+Real.toNNReal (1-s) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1,Real.coe_toNNReal (1-s) (sub_nonneg.mpr hs.2),NNReal.coe_one]
    ring
  obtain ⟨_,l₂,_,h₂,_,hm₂,_,hs₂,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel _ _ he
  exact ⟨l₂,h₂,hm₂,by simpa only [zero_add,Real.coe_toNNReal s hs.1] using hs₂⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PositiveTimeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem positiveTimeChain_mem {l : List (ℝ × ℝ≥0)} {p : ℝ × ℝ≥0} (hp : p∈positiveTimeChain l) :
    p∈l ∧ 0<p.2 := by
  simpa only [positiveTimeChain,List.mem_filter,decide_eq_true_eq,ne_eq,pos_iff_ne_zero] using hp

theorem TimeChainModels.positiveTimeChain {α : ℝ → ℝ} {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : TimeChainModels α s (positiveTimeChain l) := by
  induction l generalizing s with
  | nil => trivial
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    by_cases hd : d=0
    · simpa [SK.Analytic.positiveTimeChain,hd] using ih ht
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true]
      exact ⟨hc,ih ht⟩

theorem TimeChainModels.sorted {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hpos : ∀ p∈l,0<p.2) : l.Pairwise (fun p q => p.1≤q.1) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hd : 0<(d:ℝ) := hpos (m,d) (List.mem_cons_self ..)
    have he : α s=m := hc s ⟨le_rfl,by linarith⟩
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rw [← he]
      exact (hα (le_add_of_nonneg_right d.coe_nonneg)).trans
        (ht.mass_bounds hα hq (hpos q (List.mem_cons_of_mem _ hq))).1
    · exact ih ht (fun q hq => hpos q (List.mem_cons_of_mem _ hq))

theorem quantile_interval_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), (chainDuration l:ℝ)=t-s ∧
      (∀ p∈l,p.1∈Icc (0:ℝ) 1) ∧ (∀ p∈l,0<p.2) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hst.trans ht⟩
  have hsplit : chainDuration l=Real.toNNReal (t-s)+Real.toNNReal (1-t) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith)]
    ring
  obtain ⟨l₁,_,hd₁,_,hm₁,_,hmodel₁,_,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm s hmodel _ _ hsplit
  refine ⟨positiveTimeChain l₁,?_,fun p hp => hm₁ p (positiveTimeChain_mem hp).1,
    fun p hp => (positiveTimeChain_mem hp).2,hmodel₁.positiveTimeChain⟩
  rw [chainDuration_positiveTimeChain,hd₁,Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

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

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarCompactAverage
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

theorem scalarPath_square_bound_convex (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f) :
    (∫ z, (coordinateLinear n v z)^2 ∂hierarchyPathLaw n m
      (fun z => f (coordinateLinear n v z)) 0) ≤
      2*(∑ i, (v i)^2)+4*(∑ i, (v i)^2)^2 := by
  have H := hierarchy_square_bound n m hm hmono (fun z => f (coordinateLinear n v z))
    (hf.compCLM (coordinateLinear n v)) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun z i => by
      rw [(scalar_comp_directional hf (coordinateLinear n v) z (coordinateAxis n i)).1,
        coordinateLinear_coordinateAxis,abs_mul]
      exact (mul_le_mul_of_nonneg_right (hc.bounds _).1 (abs_nonneg _)).trans_eq (one_mul _)) 0 v
  have he : (∑ i, |v i| * |v i|) = ∑ i, (v i)^2 :=
    Finset.sum_congr rfl (fun i _ => by rw [← sq_abs]; ring)
  rw [he] at H
  nlinarith

theorem scalarHierarchyAverage_compact_lower (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hg : BoundedScalar g) {T c : ℝ} (hT : 0≤T) (hV : ∑ i, (v i)^2 ≤ T)
    (hc0 : 0 ≤ c) (hg0 : ∀ x,0≤g x)
    (hgc : ∀ x, |x|≤1+2*T+4*T^2 → c≤g x) :
    c/2≤ scalarHierarchyAverage n m v f g 0 := by
  let μ := hierarchyPathLaw n m (fun z => f (coordinateLinear n v z)) 0
  let L := coordinateLinear n v
  let M := 2*T+4*T^2
  let R := 1+M
  have hM : 0≤M := by dsimp [M]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR2 : 2*M≤R^2 := by dsimp only [R]; nlinarith [sq_nonneg M]
  have hRdef : 1+2*T+4*T^2=R := by dsimp [R,M]; ring
  have he (x : ℝ) : c*(1-x^2/R^2)≤g x := by
    by_cases hx : |x|≤R
    · have H : 1-x^2/R^2≤1 := sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
      exact (mul_le_of_le_one_right hc0 H).trans (hgc x (hRdef ▸ hx))
    · have hsq : R^2≤x^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg x)).mpr (le_of_not_ge hx)
      have hdiv : 1≤x^2/R^2 := (one_le_div (sq_pos_of_pos hR)).mpr hsq
      exact (mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)).trans (hg0 x)
  have hF : BoundedDerivs (fun z => f (L z)) := hf.compCLM L
  let := hierarchyPathLaw_probability n m _ hF 0
  have hi : Integrable (fun z => (L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted (hierarchyPathLogDensity n m (fun z => f (L z))) from
      hierarchyPathLaw_eq_tilted n m _ hF 0]
    exact ((HasExpGrowth.linear L).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hF) (L.continuous.pow 2) 0
  have hig : Integrable (fun z => g (L z)) μ := by
    obtain ⟨B,hB,hb⟩ := hg.bounded
    exact hierarchyPathLaw_integrable n m _ _ hF (hg.continuous.comp L.continuous)
      (C:=B) (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (L z)) 0
  have H := integral_mono (((integrable_const (1:ℝ)).sub (hi.div_const (R^2))).const_mul c) hig
    (fun z => he (L z))
  change (∫ z, c*(1-(L z)^2/R^2) ∂μ)≤∫ z,g (L z) ∂μ at H
  simp only [integral_const_mul,integral_sub (integrable_const _) (hi.div_const _),
    integral_div,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hs : 0≤∑ i,(v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have HM : (∫ z, (L z)^2 ∂μ)≤M := (scalarPath_square_bound_convex n m v hm hmono hf hc).trans (by
    dsimp only [M]; nlinarith [sq_le_sq₀ hs hT |>.mpr hV])
  have Hd : (∫ z, (L z)^2 ∂μ)/R^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  rw [scalarHierarchyAverage_integral hf hg]
  simp only [zero_add]
  change c/2≤∫ z,g (L z) ∂μ
  nlinarith [mul_le_mul_of_nonneg_left Hd hc0]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarPathMoment
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

theorem scalarMagnetization_gap_envelope {R : ℝ} (hR : 0<R) (x : ℝ) :
    (1/(Real.cosh R)^2)*(1-x^2/R^2) ≤ 1-(scalarMagnetization x)^2 := by
  rw [← scalarMagnetization_derivative_identity]
  by_cases h : |x|≤R
  · have hc : Real.cosh x ≤ Real.cosh R := Real.cosh_le_cosh.mpr (by simpa only [abs_of_pos hR] using h)
    have hh : 1/(Real.cosh R)^2 ≤ 1/(Real.cosh x)^2 :=
      one_div_le_one_div_of_le (by positivity) (sq_le_sq₀ (Real.cosh_pos x).le (Real.cosh_pos R).le |>.mpr hc)
    have hsmall : 1-x^2/R^2 ≤ 1 := by
      have : 0 ≤ x^2/R^2 := by positivity
      linarith
    exact (mul_le_of_le_one_right (by positivity) hsmall).trans hh
  · have hr : R^2 ≤ x^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg x)).mpr (le_of_not_ge h)
    have hdiv : 1≤x^2/R^2 := (one_le_div (sq_pos_of_pos hR)).mpr hr
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)).trans (by positivity)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarPositiveHessian
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

theorem scalarPath_terminal_affine_shift (n : ℕ) (v : Fin n → ℝ) (x : ℝ) :
    (fun z => scalarSpinTerminal (x+coordinateLinear n v z))=
      affineLogPartition (fun b : Bool => spin b*x) (fun b => spin b • coordinateLinear n v) := by
  funext z
  simp only [affineLogPartition,Fintype.sum_bool,spin,scalarSpinTerminal,
    Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,smul_apply,smul_eq_mul,Real.cosh_eq]
  rw [show -x+ -(coordinateLinear n v z)= -(x+coordinateLinear n v z) by ring]
  congr 1
  ring

theorem scalarPath_square_bound_shift (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
    (∫ z, (coordinateLinear n v z)^2 ∂hierarchyPathLaw n m
      (fun z => scalarSpinTerminal (x+coordinateLinear n v z)) 0) ≤
      2*(∑ i, (v i)^2)+4*(∑ i, (v i)^2)^2 := by
  rw [scalarPath_terminal_affine_shift]
  have H := affineHierarchy_square_bound n m hm hmono (fun b : Bool => spin b*x)
    (fun b => spin b • coordinateLinear n v) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun b i => by cases b <;> simp [spin]) 0 v
  have he : (∑ i, |v i| * |v i|) = ∑ i, (v i)^2 :=
    Finset.sum_congr rfl (fun i _ => by rw [← sq_abs]; ring)
  rw [he] at H
  nlinarith

theorem scalarHierarchyAverage_square_gap_compact (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarHierarchyAverage n m v scalarSpinTerminal (fun z => (scalarMagnetization z)^2) x ≤
      1-1/(2*(Real.cosh (1+2*A^2+4*T+8*T^2))^2) := by
  let μ := hierarchyPathLaw n m (fun z => scalarSpinTerminal (x+coordinateLinear n v z)) 0
  let L := coordinateLinear n v
  let M := 2*A^2+4*T+8*T^2
  let R := 1+M
  have hM : 0≤M := by dsimp [M]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR2 : 2*M ≤ R^2 := by dsimp only [R]; nlinarith [sq_nonneg M]
  have hf : BoundedDerivs (fun z => scalarSpinTerminal (x+L z)) :=
    (scalarSpinTerminal_regular.translate x).compCLM L
  let := hierarchyPathLaw_probability n m _ hf 0
  have hi : Integrable (fun z => (L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted
      (hierarchyPathLogDensity n m (fun z => scalarSpinTerminal (x+L z))) from
        hierarchyPathLaw_eq_tilted n m _ hf 0]
    exact ((HasExpGrowth.linear L).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hf) (L.continuous.pow 2) 0
  have hie : Integrable (fun z => (x+L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted
      (hierarchyPathLogDensity n m (fun z => scalarSpinTerminal (x+L z))) from
        hierarchyPathLaw_eq_tilted n m _ hf 0]
    exact (((HasExpGrowth.const x).add (HasExpGrowth.linear L)).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hf) ((continuous_const.add L.continuous).pow 2) 0
  have hib : Integrable (fun z => (scalarMagnetization (x+L z))^2) μ :=
    hierarchyPathLaw_integrable n m _ _ hf
      (scalarMagnetization_lipschitz.continuous.comp (continuous_const.add L.continuous) |>.pow 2)
      (C:=1) (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one _) 0
  have H := integral_mono (((integrable_const (1:ℝ)).sub (hie.div_const (R^2))).const_mul (1/(Real.cosh R)^2))
    ((integrable_const (1:ℝ)).sub hib) (fun z => scalarMagnetization_gap_envelope hR (x+L z))
  change (∫ z, (1/(Real.cosh R)^2)*(1-(x+L z)^2/R^2) ∂μ) ≤ ∫ z, 1-(scalarMagnetization (x+L z))^2 ∂μ at H
  simp only [integral_const_mul,integral_sub (integrable_const _) (hie.div_const _),
    integral_sub (integrable_const _) hib,integral_div,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hs : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have HM : (∫ z, (L z)^2 ∂μ)≤2*T+4*T^2 :=
    (scalarPath_square_bound_shift n m v hm hmono x).trans (by
      nlinarith [sq_le_sq₀ hs hT |>.mpr hv])
  have HX := integral_mono hie ((integrable_const (2*x^2)).add (hi.const_mul 2))
    (fun z => by nlinarith [sq_nonneg (x-L z)] : ∀ z, (x+L z)^2≤2*x^2+2*(L z)^2)
  change (∫ z, (x+L z)^2 ∂μ) ≤ ∫ z, 2*x^2+2*(L z)^2 ∂μ at HX
  simp only [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at HX
  have hx2 : x^2≤A^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hA).mpr hx
  have HXM : (∫ z, (x+L z)^2 ∂μ)≤M := by dsimp only [M]; linarith
  have Hd : (∫ z, (x+L z)^2 ∂μ)/R^2 ≤ 1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  rw [scalarHierarchyAverage_eq_integral n m v (g:=fun z => (scalarMagnetization z)^2) scalarSpinTerminal_regular
    (scalarMagnetization_lipschitz.continuous.pow 2) zero_le_one (fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one z) x]
  have hRdef : 1+2*A^2+4*T+8*T^2=R := by dsimp [R,M]; ring
  rw [hRdef]
  change (∫ z, (scalarMagnetization (x+L z))^2 ∂μ) ≤ 1-1/(2*(Real.cosh R)^2)
  have hc : 0≤1/(Real.cosh R)^2 := by positivity
  have hh : 1/(2*(Real.cosh R)^2)=(1/(Real.cosh R)^2)/2 := by ring
  rw [hh]
  nlinarith [mul_le_mul_of_nonneg_left Hd hc]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSuffixSusceptibility
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

theorem scalarHierarchyAverage_const {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (n : ℕ) (m v : Fin n → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v f (fun _ => c) x=c := by
  rw [scalarHierarchyAverage_integral hf (BoundedScalar.const c)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHessianFloor
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

theorem scalarSusceptibilityFloor_pos (T A : ℝ) : 0 < scalarSusceptibilityFloor T A := by
  unfold scalarSusceptibilityFloor
  positivity

theorem scalarSpinTerminal_rootHessian (x : ℝ) :
    rootHessian 0 scalarSpinTerminal x=1-(scalarMagnetization x)^2 := by
  simpa [scalarHierarchy,Fin.sum_univ_succ,hierarchyAtom,
    scalarMomentSquare,one_mul] using scalarHierarchy_spin_hessian_overlap_sum 0
      (Fin.elim0) (Fin.elim0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x

theorem scalarSpinTerminal_spinConvex : ScalarSpinConvex scalarSpinTerminal := by
  intro x
  have H := (scalarHierarchy_spin_derivative_bounds 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) x).2
  exact ⟨H.1.le,H.2⟩

theorem scalarHierarchyAverage_terminal_hessian_floor (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤ scalarHierarchyAverage n m v scalarSpinTerminal
      (rootHessian 0 scalarSpinTerminal) x := by
  have hg : BoundedScalar scalarMagnetization :=
    ⟨scalarMagnetization_lipschitz.continuous,1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have he : rootHessian 0 scalarSpinTerminal=fun z => 1-(scalarMagnetization z)^2 :=
    funext scalarSpinTerminal_rootHessian
  rw [he,scalarHierarchyAverage_sub scalarSpinTerminal_regular (BoundedScalar.const 1) hg.sq,
    scalarHierarchyAverage_const scalarSpinTerminal_regular]
  have G := scalarHierarchyAverage_square_gap_compact n m v hm hmono hT hA hv hx
  change _≤1-scalarSusceptibilityFloor T A at G
  linarith

theorem scalarHierarchy_hessian_floor (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A ≤ rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x := by
  have H := (scalarHierarchy_cramer_data scalarSpinTerminal_regular scalarSpinTerminal_spinConvex n m v hm x).2.1
  have hg : BoundedScalar scalarMagnetization :=
    ⟨scalarMagnetization_lipschitz.continuous,1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have he : rootHessian 0 scalarSpinTerminal=fun z => 1-(scalarMagnetization z)^2 :=
    funext scalarSpinTerminal_rootHessian
  rw [he,scalarHierarchyAverage_sub scalarSpinTerminal_regular (BoundedScalar.const 1) hg.sq,
    scalarHierarchyAverage_const scalarSpinTerminal_regular] at H
  have G := scalarHierarchyAverage_square_gap_compact n m v hm hmono hT hA hv hx
  change _≤1-scalarSusceptibilityFloor T A at G
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHessianLoss
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

theorem scalarHierarchy_hessian_loss {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {a : ℝ} (ha : ∀ i, a≤ m i) (x : ℝ) :
    scalarHierarchyAverage n m v f (rootHessian 0 f) x+
      a*(scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 (scalarHierarchy n m v f) x)^2) ≤
      rootHessian 0 (scalarHierarchy n m v f) x := by
  induction n generalizing f with
  | zero => simp only [scalarHierarchyAverage,scalarHierarchy,sub_self,mul_zero,add_zero,le_refl]
  | succ n ih =>
    let c := m (Fin.last n)
    let w := v (Fin.last n)
    let m' : Fin n → ℝ := fun i => m i.castSucc
    let v' : Fin n → ℝ := fun i => v i.castSucc
    let F := scalarStep c w f
    let E : (ℝ → ℝ) → ℝ := fun g => scalarHierarchyAverage n m' v' F g x
    let k := scalarStepAverage c w f (rootHessian 0 f)
    let u := scalarStepAverage c w f (rootGradient 0 f)
    let b := fun y => scalarStepAverage c w f (fun z => (rootGradient 0 f z)^2) y-(u y)^2
    let A := E k
    let B := E b
    let W := E (fun y => (rootGradient 0 F y)^2)-(rootGradient 0 (scalarHierarchy n m' v' F) x)^2
    have hF : BoundedDerivs F := scalarStep_regular hf _ _
    have hFc : ScalarSpinConvex F := h.scalarStep hf (hm _) _
    have hk : BoundedScalar k := (h.hessian_bounded hf).scalarStepAverage hf _ _
    have hu : BoundedScalar u := (h.gradient_bounded hf).scalarStepAverage hf _ _
    have he2 := (h.gradient_bounded hf).sq.scalarStepAverage hf c w
    have hb : BoundedScalar b := he2.sub hu.sq
    have hb0 (y : ℝ) : 0 ≤ b y := scalarStepAverage_variance_nonneg hf
      (rootGradient_continuous 0 hf) (fun z => (h.bounds z).1) c w y
    have hB : 0 ≤ B := scalarHierarchyAverage_nonneg hF hb hb0 n m' v' x
    have hug : rootGradient 0 F=u := funext (scalarStep_rootGradient hf c w)
    have hχ : rootHessian 0 F=fun y => k y+c*b y := funext (scalarStep_rootHessian hf c w)
    have hEK : E (rootHessian 0 F)=A+c*B := by
      rw [hχ]
      exact (scalarHierarchyAverage_add hF hk (hb.const_mul c) n m' v' x).trans
        (congrArg (A+·) (scalarHierarchyAverage_const_mul hF hb n m' v' x c))
    have hEV : E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
        (rootGradient 0 (scalarHierarchy n m' v' F) x)^2=W+B := by
      have H := scalarHierarchyAverage_sub hF he2 hu.sq n m' v' x
      change B=E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-E (fun y => (u y)^2) at H
      dsimp [W]
      rw [hug]
      linarith
    have I := ih hF hFc m' v' (fun i => hm _) (fun i => ha _)
    change E (rootHessian 0 F)+a*W ≤ rootHessian 0 (scalarHierarchy n m' v' F) x at I
    rw [hEK] at I
    change A+a*(E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
      (rootGradient 0 (scalarHierarchy n m' v' F) x)^2) ≤ rootHessian 0 (scalarHierarchy n m' v' F) x
    rw [hEV]
    have hac : a ≤ c := ha _
    nlinarith [mul_nonneg (sub_nonneg.mpr hac) hB]

theorem scalarHierarchy_hessian_loss_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {a : ℝ} (ha0 : 0≤a) (ha : ∀ i, a≤ m i) (x : ℝ) :
    scalarHierarchyAverage n m v f (rootHessian 0 f) x+
      a*(∑ i, (v i)^2)*(scalarHierarchyAverage n m v f (rootHessian 0 f) x)^2 ≤
      rootHessian 0 (scalarHierarchy n m v f) x := by
  have H := scalarHierarchy_hessian_loss hf h n m v hm ha x
  have C := (scalarHierarchy_cramer_data hf h n m v hm x).2.2.2
  nlinarith [mul_le_mul_of_nonneg_left C ha0]

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

theorem scalarIncrementAverage_bounded (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) : BoundedScalar (scalarIncrementAverage l f g) := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_bounded hf hg _ _ _

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarJointLoss
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

theorem BoundedScalar.mul {f g : ℝ → ℝ} (hf : BoundedScalar f) (hg : BoundedScalar g) :
    BoundedScalar (fun x => f x*g x) := by
  obtain ⟨A,hA,hfA⟩ := hf.bounded
  obtain ⟨B,hB,hgB⟩ := hg.bounded
  exact ⟨hf.continuous.mul hg.continuous,A*B,mul_nonneg hA hB,fun x => by
    rw [abs_mul]; exact mul_le_mul (hfA x) (hgB x) (abs_nonneg _) hA⟩

theorem scalarIncrementAverage_mono (l : List (ℝ × ℝ)) {f g h : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hh : BoundedScalar h)
    (hle : ∀ x,g x≤h x) (x : ℝ) :
    scalarIncrementAverage l f g x≤ scalarIncrementAverage l f h x := by
  simp only [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_mono hf hg hh hle _ _ _ _

theorem scalarIncrementAverage_terminal_hessian_floor (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1))
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : rawVariance l≤T) {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤ scalarIncrementAverage l scalarSpinTerminal
      (rootHessian 0 scalarSpinTerminal) x := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_terminal_hessian_floor _ _ _
    (fun i => hm _ (List.get_mem _ _)) (mass_get_monotone hs) hT hA
    (by rw [sum_get_map l (fun p => p.2^2)]; exact hv) hx

theorem scalarIncrementChain_hessian_floor (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1))
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : rawVariance l≤T) {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A ≤ rootHessian 0 (scalarIncrementChain l scalarSpinTerminal) x := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_hessian_floor _ _ _
    (fun i => hm _ (List.get_mem _ _)) (mass_get_monotone hs) hT hA
    (by rw [sum_get_map l (fun p => p.2^2)]; exact hv) hx

theorem scalarIncrementAverage_joint_hessian_loss (l j k : List (ℝ × ℝ))
    (hl : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1)
    (hsl : l.Pairwise (fun p q => p.1≤q.1)) (hsjk : (j++k).Pairwise (fun p q => p.1≤q.1))
    {T a : ℝ} (hT : 0≤T) (ha : 0≤a) (hma : ∀ p∈j,a≤p.1)
    (hvl : rawVariance l≤T) (hvjk : rawVariance (j++k)≤T) :
    let F := scalarIncrementChain k scalarSpinTerminal
    let H := scalarIncrementChain j F
    let χ := rootHessian 0 H
    let K := scalarIncrementAverage j F (rootHessian 0 F)
    scalarIncrementAverage l H (fun x => χ x*K x) 0 ≤
      scalarIncrementAverage l H (fun x => (χ x)^2) 0-
        a*rawVariance j*(scalarSusceptibilityFloor T (1+2*T+4*T^2))^3/2 := by
  dsimp only
  let F := scalarIncrementChain k scalarSpinTerminal
  let H := scalarIncrementChain j F
  let χ := rootHessian 0 H
  let K := scalarIncrementAverage j F (rootHessian 0 F)
  let b := scalarSusceptibilityFloor T (1+2*T+4*T^2)
  have hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1 := fun p hp => hjk p (List.mem_append_left _ hp)
  have hk : ∀ p∈k,p.1∈Icc (0:ℝ) 1 := fun p hp => hjk p (List.mem_append_right _ hp)
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ scalarSpinTerminal_regular
  have hFc : ScalarSpinConvex F := scalarIncrementChain_spin_convex k hk
  have he : H=scalarIncrementChain (j++k) scalarSpinTerminal := (scalarIncrementChain_append _ _ _).symm
  have hH : BoundedDerivs H := scalarIncrementChain_regular _ hF
  have hHc : ScalarSpinConvex H := he ▸ scalarIncrementChain_spin_convex (j++k) hjk
  have hχ : BoundedScalar χ := hHc.hessian_bounded hH
  have hK : BoundedScalar K := scalarIncrementAverage_bounded _ hF (hFc.hessian_bounded hF)
  have hχ0 (x : ℝ) : 0≤χ x := (hHc x).1
  have hK0 (x : ℝ) : 0≤K x := scalarIncrementAverage_nonneg _ hF
    (hFc.hessian_bounded hF) (fun y => (hFc y).1) x
  have hb : 0<b := scalarSusceptibilityFloor_pos _ _
  have hχb (x : ℝ) (hx : |x|≤1+2*T+4*T^2) : b≤χ x := by
    dsimp [χ]; rw [he]
    exact scalarIncrementChain_hessian_floor _ hjk hsjk hT (by positivity) hvjk hx
  have hKb (x : ℝ) (hx : |x|≤1+2*T+4*T^2) : b≤K x := by
    have H₀ := scalarIncrementAverage_terminal_hessian_floor (j++k) hjk hsjk hT
      (by positivity) hvjk hx
    rw [scalarIncrementAverage_append] at H₀
    apply H₀.trans
    apply scalarIncrementAverage_mono j hF
      (scalarIncrementAverage_bounded k scalarSpinTerminal_regular
        (scalarSpinTerminal_spinConvex.hessian_bounded scalarSpinTerminal_regular))
      (hFc.hessian_bounded hF)
    intro y
    simpa only [scalarIncrementAverage_get,scalarIncrementChain_get,F] using
      (scalarHierarchy_cramer_data scalarSpinTerminal_regular scalarSpinTerminal_spinConvex
        k.length (fun i => (k.get i).1) (fun i => (k.get i).2)
        (fun i => hk _ (List.get_mem _ _)) y).2.1
  have hb3 : b^3/2≤ scalarIncrementAverage l H (fun x => χ x*(K x)^2) 0 := by
    rw [scalarIncrementAverage_get]
    apply scalarHierarchyAverage_compact_lower _ _ _
      (fun i => hl _ (List.get_mem _ _)) (mass_get_monotone hsl) hH hHc (hχ.mul hK.sq)
      hT (by rw [sum_get_map l (fun p => p.2^2)]; exact hvl) (by positivity)
      (fun x => mul_nonneg (hχ0 x) (sq_nonneg _))
    intro x hx
    have H₁ := hχb x hx
    have H₂ : b^2≤(K x)^2 := (sq_le_sq₀ hb.le (hK0 x)).mpr (hKb x hx)
    calc
      b^3=b*b^2 := by ring
      _ ≤ χ x*(K x)^2 := mul_le_mul H₁ H₂ (sq_nonneg _) (hχ0 x)
  have Hloss (x : ℝ) : K x+a*rawVariance j*(K x)^2≤χ x := by
    have G := scalarHierarchy_hessian_loss_cramer hF hFc j.length
      (fun i => (j.get i).1) (fun i => (j.get i).2)
      (fun i => hj _ (List.get_mem _ _)) ha (fun i => hma _ (List.get_mem _ _)) x
    rw [sum_get_map j (fun p => p.2^2)] at G
    simpa only [K,χ,H,scalarIncrementAverage_get,scalarIncrementChain_get,rawVariance] using G
  have HP := scalarIncrementAverage_mono l hH
    ((hχ.mul hK).add ((hχ.mul hK.sq).const_mul (a*rawVariance j))) hχ.sq
    (fun x => by nlinarith [mul_le_mul_of_nonneg_left (Hloss x) (hχ0 x)]) 0
  simp only [scalarIncrementAverage_get] at HP
  rw [scalarHierarchyAverage_add hH (hχ.mul hK) ((hχ.mul hK.sq).const_mul _),
    scalarHierarchyAverage_const_mul hH (hχ.mul hK.sq)] at HP
  simp only [← scalarIncrementAverage_get] at HP
  change scalarIncrementAverage l H (fun x => χ x*K x) 0+
    a*rawVariance j*scalarIncrementAverage l H (fun x => χ x*(K x)^2) 0≤
    scalarIncrementAverage l H (fun x => (χ x)^2) 0 at HP
  have Hmul := mul_le_mul_of_nonneg_left hb3 (mul_nonneg ha (rawVariance_nonneg j))
  dsimp only [b,χ,K,H,F] at HP Hmul
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainJointHessian
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

theorem timeChainJointHessian_loss (β : ℝ) (l j k : List (ℝ × ℝ≥0))
    (hl : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1)
    (hsl : l.Pairwise (fun p q => p.1≤q.1)) (hsjk : (j++k).Pairwise (fun p q => p.1≤q.1))
    {a : ℝ} (ha : 0≤a) (hma : ∀ p∈j,a≤p.1)
    (hvl : (chainDuration l:ℝ)≤1) (hvjk : (chainDuration (j++k):ℝ)≤1) :
    timeChainJointHessian β l j k ≤
      scalarTimeChainAverage β l (scalarTimeChain β (j++k) scalarSpinTerminal)
        (fun x => (rootHessian 0 (scalarTimeChain β (j++k) scalarSpinTerminal) x)^2) 0-
        a*(β^2*(chainDuration j:ℝ))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  let L := scaleIncrementChain β (rawTimeChain l)
  let J := scaleIncrementChain β (rawTimeChain j)
  let K := scaleIncrementChain β (rawTimeChain k)
  have heb : J++K=scaleIncrementChain β (rawTimeChain (j++k)) := by
    rw [rawTimeChain_append,scaleIncrementChain_append]
  have G := scalarIncrementAverage_joint_hessian_loss L J K
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hl))
    (heb ▸ scaleIncrementChain_mass β _ (rawTimeChain_mass _ hjk))
    (scaleIncrementChain_sorted β _ (rawTimeChain_sorted _ hsl))
    (heb ▸ scaleIncrementChain_sorted β _ (rawTimeChain_sorted _ hsjk))
    (T:=β^2) (sq_nonneg β) ha
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hma))
    (by dsimp [L]; rw [rawVariance_scale,rawVariance_rawTimeChain]; nlinarith [sq_nonneg β])
    (by rw [heb,rawVariance_scale,rawVariance_rawTimeChain]; nlinarith [sq_nonneg β])
  dsimp only at G
  simp only [L,J,K,rawVariance_scale,rawVariance_rawTimeChain,scalarIncrementChain_rawTimeChain,
    scalarIncrementAverage_rawTimeChain] at G
  simpa only [timeChainJointHessian,scalarTimeChain_append] using G

theorem timeChainJointHessian_cdf_loss (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1)
    (l j k : List (ℝ × ℝ≥0))
    (hdl : (chainDuration l:ℝ)=r) (hdj : (chainDuration j:ℝ)=q-r) (hdk : (chainDuration k:ℝ)=1-q)
    (hl : TimeChainModels α 0 l) (hj : TimeChainModels α r j) (hk : TimeChainModels α q k)
    (hml : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hmj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) (hmk : ∀ p∈k,p.1∈Icc (0:ℝ) 1)
    (hpl : ∀ p∈l,0<p.2) (hpj : ∀ p∈j,0<p.2) (hpk : ∀ p∈k,0<p.2) :
    timeChainJointHessian β l j k ≤ scalarCDFSusceptibilitySquareAverage β α r-
      α r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  have hdjk : (chainDuration (j++k):ℝ)=1-r := by
    rw [chainDuration_append,NNReal.coe_add,hdj,hdk]; ring
  have hjk : TimeChainModels α r (j++k) := hj.append (by simpa only [hdj,add_sub_cancel] using hk)
  have hmjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hmj p) (hmk p)
  have hpjk : ∀ p∈j++k,0<p.2 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hpj p) (hpk p)
  have G := timeChainJointHessian_loss β l j k hml hmjk (hl.sorted hm hpl) (hjk.sorted hm hpjk)
    (ha r).1 (fun p hp => (hj.mass_bounds hm hp (hpj p hp)).1)
    (by rw [hdl]; exact hrq.trans hq) (by rw [hdjk]; linarith)
  rw [hdj] at G
  let sr := Real.toNNReal (1-r)
  let tr := Real.toNNReal r
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have he : scalarTimeChain β (j++k) scalarSpinTerminal=scalarCDFValue β α r sr := by
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β ha hm (j++k) hmjk r sr hsr1 (NNReal.coe_injective (hdjk.trans hsr.symm)) hjk x).symm
  rw [he,scalarCDFValue_rootHessian β ha hm r sr hsr1] at G
  have hav := scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hm r sr hsr1) (scalarCDFValue_lipschitz β ha hm r sr hsr1)
    (scalarCDFHessian_square_lipschitz β ha hm r sr hsr1)
    (B:=1) (scalarCDFHessian_square_bound β ha hm r sr hsr1) β ha hm l hml 0 tr htr1
    (NNReal.coe_injective (hdl.trans htr.symm)) hl 0
  rw [← hav] at G
  exact G

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOn
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

theorem exists_quantile_TimeChainOn {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Nonempty (TimeChainOn (quantileCDF k Q) s t) := by
  obtain ⟨l,hd,hm,hp,hmodel⟩ := quantile_interval_chain β Q hQ hs hst ht
  exact ⟨⟨l,hd,hm,hp,hmodel⟩⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFUniformAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_abs_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x|≤B := by
  apply le_of_tendsto (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_abs_le hf hB _ _ _ _)

theorem scalarCDFAverage_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) :
    LipschitzWith (L+2*B*Real.toNNReal (Real.exp (2*(K:ℝ)))) (scalarCDFAverage β α s t f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht y)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_spatial_bound _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _)) (fun i j hij => ?_)
    hf hfK hgL hB x y
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hm n s t) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFConditionalSusceptibility_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith conditionalSusceptibilityLipschitz (scalarCDFConditionalSusceptibility β α r q) ∧
      ∀ x,|scalarCDFConditionalSusceptibility β α r q x|≤1 := by
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFAverage_lipschitz β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht
  refine ⟨?_,fun x => scalarCDFAverage_abs_le β ha hm
    (scalarCDFValue_regular β ha hm q _ hs) (scalarCDFValue_lipschitz β ha hm q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) r _ ht x⟩
  simpa only [scalarCDFConditionalSusceptibility,conditionalSusceptibilityLipschitz,NNReal.coe_one,mul_one] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem timeChainJointHessian_eq_cdf (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1)
    (l : TimeChainOn α 0 r) (j : TimeChainOn α r q) (k : TimeChainOn α q 1) :
    timeChainJointHessian β l.chain j.chain k.chain=scalarCDFJointSusceptibility β α r q := by
  let tr := Real.toNNReal r
  let tj := Real.toNNReal (q-r)
  let sr := Real.toNNReal (1-r)
  let sq := Real.toNNReal (1-q)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have htj : (tj:ℝ)=q-r := Real.coe_toNNReal _ (sub_nonneg.mpr hrq)
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hsq : (sq:ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have htj1 : tj≤1 := by rw [← NNReal.coe_le_coe,htj,NNReal.coe_one]; linarith
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have hsq1 : sq≤1 := by rw [← NNReal.coe_le_coe,hsq,NNReal.coe_one]; linarith
  have heF : scalarTimeChain β k.chain scalarSpinTerminal=scalarCDFValue β α q sq := by
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      k.chain k.mass q sq hsq1 (NNReal.coe_injective (k.duration.trans hsq.symm)) k.models x).symm
  have heH : scalarTimeChain β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)=scalarCDFValue β α r sr := by
    rw [← scalarTimeChain_append]
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      (j.append k).chain (j.append k).mass r sr hsr1
      (NNReal.coe_injective ((j.append k).duration.trans hsr.symm)) (j.append k).models x).symm
  have heK : scalarTimeChainAverage β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)
      (rootHessian 0 (scalarTimeChain β k.chain scalarSpinTerminal))=scalarCDFConditionalSusceptibility β α r q := by
    rw [heF,scalarCDFValue_rootHessian β ha hm q sq hsq1]
    funext x
    exact (scalarCDFAverage_eq_chainAverage_lipschitz
      (scalarCDFValue_regular β ha hm q sq hsq1) (scalarCDFValue_lipschitz β ha hm q sq hsq1)
      (scalarCDFHessian_lipschitz β ha hm q sq hsq1) (B:=1)
      (scalarCDFHessian_abs_le_one β ha hm q sq hsq1)
      β ha hm j.chain j.mass r tj htj1 (NNReal.coe_injective (j.duration.trans htj.symm)) j.models x).symm
  dsimp only [timeChainJointHessian]
  rw [heH,heK,scalarCDFValue_rootHessian β ha hm r sr hsr1]
  have hK := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  have hp := unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r sr hsr1) hK.1
    (scalarCDFHessian_abs_le_one β ha hm r sr hsr1) hK.2
  have hb (x) : |scalarCDFHessian β α r sr x*scalarCDFConditionalSusceptibility β α r q x|≤(1:ℝ≥0) := by
    rw [abs_mul,NNReal.coe_one]
    exact (mul_le_mul (scalarCDFHessian_abs_le_one β ha hm r sr hsr1 x) (hK.2 x)
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hm r sr hsr1) (scalarCDFValue_lipschitz β ha hm r sr hsr1) hp hb
    β ha hm l.chain l.mass 0 tr htr1
    (NNReal.coe_injective (by rw [l.duration,sub_zero,htr])) l.models 0).symm

theorem scalarCDFJointSusceptibility_quantile_loss_oai {n : ℕ} (β : ℝ) (Q : Fin (n+1) → ℝ)
    (hQ : Q∈admissibleQuantiles n) {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    scalarCDFJointSusceptibility β (quantileCDF n Q) r q ≤
      scalarCDFSusceptibilitySquareAverage β (quantileCDF n Q) r-
      quantileCDF n Q r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  obtain ⟨l⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) le_rfl hr (hrq.trans hq)
  obtain ⟨j⟩ := exists_quantile_TimeChainOn β Q hQ hr hrq hq
  obtain ⟨k⟩ := exists_quantile_TimeChainOn β Q hQ (hr.trans hrq) hq le_rfl
  have G := timeChainJointHessian_cdf_loss β (quantileCDF_bounds n Q) (quantileCDF_monotone n Q)
    hr hrq hq l.chain j.chain k.chain (by simpa only [sub_zero] using l.duration) j.duration k.duration
    l.models j.models k.models l.mass j.mass k.mass l.positive j.positive k.positive
  rw [timeChainJointHessian_eq_cdf β (quantileCDF_bounds n Q) (quantileCDF_monotone n Q) hr hrq hq l j k] at G
  exact G

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss_oai := @OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss_oai
