-- Prove2me | solution 1 for OAI.SK.Analytic.equalBlock_average_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:52.171256+00:00
-- url     : https://prove2.me/submissions/b88a01c0-0b81-4312-9dc0-67ff695b04b2

import Mathlib
import Definitions.Def_OAIQ036S004

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

theorem fiberGaussian_tilted_stein (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z ∂(fiberGaussian n x).tilted V) =
      ∫ z, fderiv ℝ V z (coordinateAxis n i) ∂(fiberGaussian n x).tilted V := by
  obtain ⟨hg,hg',hg''⟩ := hV.exp_growths 1
  simp only [one_mul] at hg hg' hg''
  have H := fiberGaussian_stein n (fun z => Real.exp (V z))
    (hV.1.exp.of_le (by norm_num)) hg hg' x i
  simp_rw [((hV.1.differentiable (by norm_num) _).hasFDerivAt.exp).fderiv,
    smul_apply,smul_eq_mul] at H
  simp only [integral_tilted_real_eq_div]
  congr 1
  rw [H]
  apply integral_congr_ae
  filter_upwards [] with z
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

theorem HasExpGrowth.memLp_two_tilted_fiberGaussian (n : ℕ)
    (V : ParameterSpace n → ℝ) (hV : BoundedDerivs V) {g : ParameterSpace n → ℝ}
    (hg : HasExpGrowth g) (hc : Continuous g) (x : ℝ) :
    MemLp g 2 ((fiberGaussian n x).tilted V) := by
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  simpa only [pow_two] using (hg.mul hg).integrable_tilted_fiberGaussian n V hV (hc.mul hc) x

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

theorem gaussian_tilted_coordinate_mean (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z ∂(fiberGaussian n x).tilted (fun z => p*F z)) =
      p*∫ z, directionalGradient F (coordinateAxis n i) z
        ∂(fiberGaussian n x).tilted (fun z => p*F z) := by
  rw [fiberGaussian_tilted_stein n _ (hF.const_mul p)]
  simp_rw [((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    smul_apply,smul_eq_mul]
  exact integral_const_mul _ _

theorem gaussian_tilted_cross_covariance (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i j : Fin n) :
    cov[directionalGradient F (coordinateAxis n i),coordinateProjection n j;
      (fiberGaussian n x).tilted (fun z => p*F z)] = gaussianResponse n F p x i j := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hg := directionalGradient_contDiff F hF.1 (coordinateAxis n i)
  obtain ⟨hg₀,hg₁⟩ := hF.directionalGradient_bounds (coordinateAxis n i)
  have hm (i : Fin n) : MemLp (directionalGradient F (coordinateAxis n i)) 2 μ :=
    (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (directionalGradient_contDiff F hF.1 _).continuous x
  have hy (j : Fin n) : MemLp (coordinateProjection n j) 2 μ :=
    (HasExpGrowth.linear _).memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (coordinateProjection n j).continuous x
  have H := fiberGaussian_tilted_weighted_stein n (fun z => p*F z)
    (directionalGradient F (coordinateAxis n i)) (hF.const_mul p) hg hg₀ hg₁ x j
  simp_rw [fderiv_directionalGradient F hF.1,
    ((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    ContinuousLinearMap.flip_apply,smul_apply,smul_eq_mul] at H
  have hmj := gaussian_tilted_coordinate_mean n F hF p x j
  change (∫ z, coordinateProjection n j z ∂μ) = _ at hmj
  change (∫ z, coordinateProjection n j z*directionalGradient F (coordinateAxis n i) z ∂μ) = _ at H
  rw [covariance_eq_sub (hm i) (hy j)]
  unfold gaussianResponse
  rw [covariance_eq_sub (hm i) (hm j)]
  simp only [Pi.mul_apply]
  change _ = (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)+_
  have he : (∫ z, directionalGradient F (coordinateAxis n i) z*
      (p*fderiv ℝ F z (coordinateAxis n j)) ∂μ) =
      p*∫ z, directionalGradient F (coordinateAxis n i) z*
        directionalGradient F (coordinateAxis n j) z ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext z
    unfold directionalGradient
    ring
  rw [he] at H
  have he₂ : (∫ z, directionalGradient F (coordinateAxis n i) z*coordinateProjection n j z ∂μ) =
      ∫ z, coordinateProjection n j z*directionalGradient F (coordinateAxis n i) z ∂μ := by
    congr 1; funext z; ring
  rw [he₂,H,hmj]
  ring

theorem gaussianResponse_isHermitian (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : ContDiff ℝ 2 F) (p x : ℝ) : (gaussianResponse n F p x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,gaussianResponse]
  rw [covariance_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

theorem gaussian_tilted_field_covariance (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i j : Fin n) :
    cov[coordinateProjection n i,coordinateProjection n j;
      (fiberGaussian n x).tilted (fun z => p*F z)] =
      (if i=j then 1 else 0)+p*gaussianResponse n F p x i j := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hm (i : Fin n) : MemLp (directionalGradient F (coordinateAxis n i)) 2 μ :=
    (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (directionalGradient_contDiff F hF.1 _).continuous x
  have hy (j : Fin n) : MemLp (coordinateProjection n j) 2 μ :=
    (HasExpGrowth.linear _).memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (coordinateProjection n j).continuous x
  have hg' : HasExpGrowth (fderiv ℝ (fun z => coordinateProjection n i z)) := by
    have he : fderiv ℝ (fun z => coordinateProjection n i z) = fun _ => coordinateProjection n i := by
      funext z; exact (coordinateProjection n i).fderiv
    rw [he]
    exact HasExpGrowth.of_bounded (norm_nonneg _) (fun _ => le_rfl)
  have H := fiberGaussian_tilted_weighted_stein n (fun z => p*F z)
    (coordinateProjection n i) (hF.const_mul p) (coordinateProjection n i).contDiff
    (HasExpGrowth.linear _) hg' x j
  simp_rw [(coordinateProjection n i).fderiv,
    ((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    smul_apply,smul_eq_mul,coordinateProjection_coordinateAxis] at H
  change (∫ z, coordinateProjection n j z*coordinateProjection n i z ∂μ) =
    (∫ _, (if i=j then 1 else 0 : ℝ) ∂μ)+
      ∫ z, coordinateProjection n i z*(p*fderiv ℝ F z (coordinateAxis n j)) ∂μ at H
  simp only [integral_const,probReal_univ,one_smul] at H
  have he : (∫ z, coordinateProjection n i z*(p*fderiv ℝ F z (coordinateAxis n j)) ∂μ) =
      p*∫ z, directionalGradient F (coordinateAxis n j) z*coordinateProjection n i z ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext z; unfold directionalGradient; ring
  rw [he] at H
  have hr := gaussian_tilted_cross_covariance n F hF p x j i
  change cov[directionalGradient F (coordinateAxis n j),coordinateProjection n i;μ] = _ at hr
  rw [covariance_eq_sub (hm j) (hy i)] at hr
  have hs : gaussianResponse n F p x j i = gaussianResponse n F p x i j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (gaussianResponse_isHermitian n F hF.1 p x).eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  rw [hs] at hr
  rw [covariance_eq_sub (hy i) (hy j)]
  simp only [Pi.mul_apply] at hr ⊢
  have hc : (∫ z, coordinateProjection n i z*coordinateProjection n j z ∂μ) =
      ∫ z, coordinateProjection n j z*coordinateProjection n i z ∂μ := by
    congr 1; funext z; ring
  rw [hc,H]
  have hj := gaussian_tilted_coordinate_mean n F hF p x j
  change (∫ z, coordinateProjection n j z ∂μ) = _ at hj
  rw [hj,← hr]
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAverage
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
section GaussianAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gaussianStep_curvature_domination {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {A : E × ℝ → ℝ} (hc : Continuous A) {C : ℝ} (hb : ∀ z, ‖A z‖ ≤ C)
    (m : ℝ) (u x : E)
    (hH : ∀ y, m*(A (x,y)-(prefixGradient f u (x,y))^2) ≤ prefixHessian f u u (x,y)) :
    m*(gaussianAverage m f A x-(fderiv ℝ (gaussianStep m f) x u)^2) ≤
      fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u := by
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,D,hD,hbH⟩ := prefixHessian_data hf u u
  have iA := integrable_gaussianStep_of_bounded hf m x
    (hc.comp (continuous_const.prodMk continuous_id)) (fun y => hb (x,y))
  have iH := integrable_gaussianStep_of_bounded hf m x
    (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have iGG := integrable_gaussianStep_of_bounded hf m x
    (g := fun y => prefixGradient f u (x,y)*prefixGradient f u (x,y))
    ((hcG.mul hcG).comp (continuous_const.prodMk continuous_id)) (C := B*B) (fun y => by
      rw [norm_mul]; exact mul_le_mul (hbG _) (hbG _) (norm_nonneg _) hB)
  have H := integral_mono ((iA.sub (by simpa only [pow_two] using iGG)).const_mul m) iH hH
  rw [integral_const_mul] at H
  simp only [Pi.sub_apply,Function.comp_apply,id_eq] at H
  have iA' : Integrable (fun y => A (x,y)) (gaussianStepLaw m f x) := iA
  rw [integral_sub iA' (by simpa only [pow_two] using iGG)] at H
  rw [fderiv_fderiv_gaussianStep_apply hf, fderiv_gaussianStep_apply hf]
  simp only [pow_two,gaussianAverage] at H ⊢
  nlinarith

theorem gaussianStep_variance_nonneg {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {A : E × ℝ → ℝ} (hc : Continuous A) {C : ℝ} (hb : ∀ z, ‖A z‖ ≤ C)
    (m : ℝ) (u x : E)
    (hA : ∀ y, 0 ≤ A (x,y)-(prefixGradient f u (x,y))^2) :
    0 ≤ gaussianAverage m f A x-(fderiv ℝ (gaussianStep m f) x u)^2 := by
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,hB,hbG⟩ := prefixGradient_data hf u
  have hcm : Continuous (fun y : ℝ => prefixGradient f u (x,y)) :=
    hcG.comp (continuous_const.prodMk continuous_id)
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound hcm.aestronglyMeasurable B (ae_of_all _ (fun y => hbG (x,y)))
  have iA := integrable_gaussianStep_of_bounded hf m x
    (hc.comp (continuous_const.prodMk continuous_id)) (fun y => hb (x,y))
  have iG := hmem.integrable_sq
  have Hi := integral_mono iG iA (fun y => sub_nonneg.mp (hA y))
  simp only [Function.comp_apply,id_eq] at Hi
  have Hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at Hv
  rw [fderiv_gaussianStep_apply hf]
  change 0 ≤ (∫ y, A (x,y) ∂μ)-(∫ y, prefixGradient f u (x,y) ∂μ)^2
  change 0 ≤ (∫ y, (prefixGradient f u (x,y))^2 ∂μ)-_ at Hv
  linarith

end GaussianAverage
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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeRecursion
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

section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadePressure_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) : BoundedDerivs (cascadePressure n m f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _)

theorem cascadeMoment_bounded_continuous (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (g : CascadeSpace E n → ℝ)
    (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) :
    Continuous (cascadeMoment n m f g) ∧ ∀ x, ‖cascadeMoment n m f g x‖ ≤ C := by
  induction n with
  | zero => exact ⟨hg,hb⟩
  | succ n ih =>
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous hf _ hg hC hb) (fun x => gaussianAverage_norm_le hf _ hb x)

theorem cascadePressure_gradient (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (x u : E) :
    fderiv ℝ (cascadePressure n m f) x u =
      cascadeMoment n m f (fun z => fderiv ℝ f z (cascadeLift n u)) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadePressure,ih (fun i => m i.castSucc) _ (hf.gaussianStep _)]
    simp_rw [fderiv_gaussianStep_apply hf]
    rfl

theorem cascade_curvature_domination (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (A : CascadeSpace E n → ℝ)
    (hA : Continuous A) {C upper lower : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖A z‖ ≤ C)
    (hmlu : lower ≤ upper) (hm : ∀ i, lower ≤ m i) (hmu : ∀ i, m i ≤ upper)
    (hmono : Monotone m) (u : E)
    (hV : ∀ z, 0 ≤ A z-(fderiv ℝ f z (cascadeLift n u))^2)
    (hH : ∀ z, upper*(A z-(fderiv ℝ f z (cascadeLift n u))^2) ≤
      fderiv ℝ (fderiv ℝ f) z (cascadeLift n u) (cascadeLift n u)) (x : E) :
    0 ≤ cascadeMoment n m f A x-(fderiv ℝ (cascadePressure n m f) x u)^2 ∧
    lower*(cascadeMoment n m f A x-(fderiv ℝ (cascadePressure n m f) x u)^2) ≤
      fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u := by
  induction n generalizing upper with
  | zero =>
    refine ⟨hV x,?_⟩
    exact (mul_le_mul_of_nonneg_right hmlu (hV x)).trans (hH x)
  | succ n ih =>
    let q := m (Fin.last n)
    let f' := gaussianStep q f
    let A' := gaussianAverage q f A
    have hv' (z : CascadeSpace E n) : 0 ≤ A' z-(fderiv ℝ f' z (cascadeLift n u))^2 :=
      gaussianStep_variance_nonneg hf hA hb q (cascadeLift n u) z (fun y => hV (z,y))
    have hh' (z : CascadeSpace E n) :
        q*(A' z-(fderiv ℝ f' z (cascadeLift n u))^2) ≤
          fderiv ℝ (fderiv ℝ f') z (cascadeLift n u) (cascadeLift n u) := by
      apply gaussianStep_curvature_domination hf hA hb q (cascadeLift n u) z
      intro y
      exact (mul_le_mul_of_nonneg_right (hmu (Fin.last n)) (hV (z,y))).trans (hH (z,y))
    exact ih (fun i => m i.castSucc) f' (hf.gaussianStep _) A'
      (gaussianAverage_continuous hf _ hA hC hb) (fun z => gaussianAverage_norm_le hf _ hb z)
      (hm (Fin.last n)) (fun i => hm i.castSucc) (fun i => hmono (Fin.le_last _))
      (fun i j hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij)) hv' hh'

end Cascade
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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ThermalMoments
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
section ThermalMoments
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem affineMoment_variance_nonneg (c : S → ℝ) (L : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (x : E) : 0 ≤ affineMoment c L (fun s => (g s)^2) x-(affineMoment c L g x)^2 := by
  let a := affineMoment c L g x
  have H : 0 ≤ ∑ s, affineGibbs c L x s*(g s-a)^2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (affineGibbs_pos c L x s).le (sq_nonneg _))
  have he : (∑ s, affineGibbs c L x s*(g s-a)^2) =
      affineMoment c L (fun s => (g s)^2) x-a^2 := by
    simp only [sub_sq]
    simp_rw [mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have h₁ : (∑ s, affineGibbs c L x s*(2*g s*a)) = 2*a*a := by
      calc
        _ = (∑ s, affineGibbs c L x s*g s)*(2*a) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
        _ = _ := by change a*(2*a) = _; ring
    have h₂ : (∑ s, affineGibbs c L x s*a^2) = a^2 := by
      rw [← Finset.sum_mul,affineGibbs_sum,one_mul]
    rw [h₁,h₂]
    dsimp only [affineMoment]
    ring
  rwa [he] at H

end ThermalMoments
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyMeanSquare n m U c j)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyMeanSquare_continuous n m U c hc j) (C := 1) _ x
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

theorem hierarchyMeanOverlap_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j ∈ Set.Icc (0 : ℝ) 1 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  refine ⟨integral_nonneg (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (1 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono (hierarchyMeanSquare_integrable n m U c hc j 0) (integrable_const 1)
        (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).2)
    _ = 1 := by simp

end MeanTower
end SK.Analytic
namespace SK.Analytic

theorem massFromAtoms_nonneg (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    0 ≤ massFromAtoms n w i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

theorem massFromAtoms_le_sum (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    massFromAtoms n w i ≤ ∑ j, w j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact hw j

theorem massFromAtoms_monotone (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (massFromAtoms n w) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left hj,ite_eq_left (hj.trans hik)]
  · rw [ite_eq_right hj]
    split_ifs
    · exact hw j
    · exact le_rfl
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockAtom_nonneg (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    0 ≤ blockAtom D N k t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

theorem blockAtom_sum (D N k : ℕ) : ∑ t, blockAtom D N k t = 1 := by
  unfold blockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem blockMass_valid (D N k : ℕ) :
    (∀ i, 0 ≤ blockMass D N k i) ∧ (∀ i, blockMass D N k i ≤ 1) ∧ Monotone (blockMass D N k) := by
  refine ⟨massFromAtoms_nonneg _ _ (blockAtom_nonneg D N k),?_,
    massFromAtoms_monotone _ _ (blockAtom_nonneg D N k)⟩
  intro i
  exact (massFromAtoms_le_sum _ _ (blockAtom_nonneg D N k) i).trans_eq (blockAtom_sum D N k)

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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem cascadeMoment_nonneg (n : ℕ) (m : Fin n → ℝ)
    (f g : CascadeSpace E n → ℝ) (hg : ∀ z, 0 ≤ g z) (x : E) :
    0 ≤ cascadeMoment n m f g x := by
  induction n with
  | zero => exact hg x
  | succ n ih =>
    apply ih
    intro z
    exact integral_nonneg (fun y => hg (z,y))

theorem cascadeMoment_const (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (a : ℝ) :
    cascadeMoment n m f (fun _ => a) = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun _ => a) = fun _ => a := by
      funext z
      let := gaussianStepLaw_probability hf (m (Fin.last n)) z
      simp only [gaussianAverage,integral_const,probReal_univ,one_smul]
    rw [cascadeMoment,h]
    exact ih _ _ (hf.gaussianStep _)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cascadeMoment_const_mul (n : ℕ) (m : Fin n → ℝ)
    (f g : CascadeSpace E n → ℝ) (a : ℝ) :
    cascadeMoment n m f (fun z => a*g z) = fun x => a*cascadeMoment n m f g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
        fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
      funext z; exact integral_const_mul a _
    rw [cascadeMoment,h,ih]
    rfl

theorem cascadeMoment_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f)
    (g : T → CascadeSpace E n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) :
    cascadeMoment n m f (fun z => ∑ t, g t z) =
      fun x => ∑ t, cascadeMoment n m f (g t) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
        fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
      funext z
      let := gaussianStepLaw_probability hf (m (Fin.last n)) z
      apply integral_finsetSum
      intro t _
      exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (C t) (ae_of_all _ (fun y => hb t (z,y)))
    rw [cascadeMoment,h]
    exact ih _ _ (hf.gaussianStep _) _
      (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
      (fun t z => gaussianAverage_norm_le hf _ (hb t) z)

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

theorem cascadeSpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) (s : S) :
    0 ≤ cascadeSpinWeight n m c L x s :=
  cascadeMoment_nonneg n m _ _ (fun z => (affineGibbs_pos c L z s).le) x

theorem cascadeSpinWeight_sum (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) :
    ∑ s, cascadeSpinWeight n m c L x s = 1 := by
  have H := congrFun (cascadeMoment_sum n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (fun s z => affineGibbs c L z s)
    (affineGibbs_continuous c L) (fun _ => 1) (by intro; norm_num)
    (fun s z => affineGibbs_norm_le_one c L z s)) x
  simp_rw [affineGibbs_sum] at H
  rw [cascadeMoment_const n m _ (affineLogPartition_boundedDerivs c L)] at H
  exact H.symm

theorem cascadeMoment_affineMoment (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (g : S → ℝ) (x : E) :
    cascadeMoment n m (affineLogPartition c L) (affineMoment c L g) x =
      ∑ s, cascadeSpinWeight n m c L x s*g s := by
  have H := congrFun (cascadeMoment_sum n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (fun s z => g s*affineGibbs c L z s)
    (fun s => continuous_const.mul (affineGibbs_continuous c L s)) (fun s => ‖g s‖)
    (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one c L z s) (norm_nonneg _)).trans_eq (mul_one _))) x
  simp_rw [cascadeMoment_const_mul] at H
  change cascadeMoment n m (affineLogPartition c L) (fun z => ∑ s, affineGibbs c L z s*g s) x = _
  simpa only [cascadeSpinWeight,mul_comm] using H

theorem cascadeSpinWeight_regular (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => cascadeSpinWeight n m c L x s) ∧
      ∀ x, ‖cascadeSpinWeight n m c L x s‖ ≤ 1 :=
  cascadeMoment_bounded_continuous n m _ (affineLogPartition_boundedDerivs c L) _
    (affineGibbs_continuous c L s) (by norm_num) (fun x => affineGibbs_norm_le_one c L x s)
end CascadeProbability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinCurvature
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
section SpinCurvature
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem cascadeAffine_gradient (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x u : E) :
    fderiv ℝ (cascadePressure n m (affineLogPartition c L)) x u =
      cascadeMoment n m (affineLogPartition c L)
        (affineMoment c L (fun s => L s (cascadeLift n u))) x := by
  rw [cascadePressure_gradient n m _ (affineLogPartition_boundedDerivs c L)]
  simp_rw [fderiv_affineLogPartition_apply]

theorem cascadeAffine_curvature (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) {lower : ℝ}
    (hl : lower ≤ 1) (hm : ∀ i, lower ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (x u : E) :
    let f := affineLogPartition c L
    let M := cascadeMoment n m f (affineMoment c L (fun s => L s (cascadeLift n u))) x
    let A := cascadeMoment n m f (affineMoment c L (fun s => (L s (cascadeLift n u))^2)) x
    0 ≤ A-M^2 ∧ lower*(A-M^2) ≤ fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u := by
  classical
  let g : S → ℝ := fun s => L s (cascadeLift n u)
  let C : ℝ := ∑ s, (g s)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hg (s : S) : ‖(g s)^2‖ ≤ C := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun t _ => sq_nonneg (g t)) (Finset.mem_univ s)
  have H := cascade_curvature_domination n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (affineMoment c L (fun s => (g s)^2))
    (affineMoment_continuous c L _) hC (affineMoment_norm_le c L _ hg) hl hm hmu hmono u
    (fun z => by rw [fderiv_affineLogPartition_apply]; exact affineMoment_variance_nonneg c L g z)
    (fun z => by
      rw [fderiv_fderiv_affineLogPartition_apply,fderiv_affineLogPartition_apply]
      simp only [one_mul,pow_two,g]
      exact le_rfl) x
  rw [cascadeAffine_gradient] at H
  exact H

end SpinCurvature
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSpinTrace
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

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
namespace SK.Analytic

section Trace
variable {I : Type} [Fintype I] [DecidableEq I]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix I I ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  let S := CFC.sqrt A
  have hS : Sᴴ = S := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSS : S*S = A := by simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  rw [trace_mul_cycle,hS,hSS] at h
  exact h

theorem trace_mul_mono_of_posSemidef {A B C : Matrix I I ℝ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) : (A*B).trace ≤ (A*C).trace := by
  have h := trace_mul_nonneg_of_posSemidef hA hBC
  rw [mul_sub,trace_sub] at h
  linarith

theorem posSemidef_trace_one_sub {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (A.trace • (1 : Matrix I I ℝ)-A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hd : (diagonal (fun i => A.trace-hA.isHermitian.eigenvalues i)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    rw [sub_nonneg,hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have he : diagonal (fun i => A.trace-hA.isHermitian.eigenvalues i) =
      A.trace • (1 : Matrix I I ℝ)- diagonal hA.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i=j <;> simp [hij]
  have H := hd.mul_mul_conjTranspose_same (U : Matrix I I ℝ)
  rw [he,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one] at H
  have hu : (U : Matrix I I ℝ)*(U : Matrix I I ℝ)ᴴ = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  rw [hu] at H
  have hs : (U : Matrix I I ℝ)*diagonal hA.isHermitian.eigenvalues*
      (U : Matrix I I ℝ)ᴴ = A := by
    simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id,
      id_eq,Matrix.star_eq_conjTranspose,U] using hA.isHermitian.spectral_theorem.symm
  rwa [hs] at H

theorem posSemidef_scalar_one_sub {A : Matrix I I ℝ} (hA : A.PosSemidef)
    {T : ℝ} (hT : A.trace ≤ T) : (T • (1 : Matrix I I ℝ)-A).PosSemidef := by
  have H := (posSemidef_trace_one_sub hA).add
    (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hT))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem trace_square_bound {C V : Matrix I I ℝ} {T a : ℝ}
    (hC : C.PosSemidef) (hV : V.PosSemidef)
    (hCT : (T • (1 : Matrix I I ℝ)-C).PosSemidef)
    (hCV : (V+a • (1 : Matrix I I ℝ)-C).PosSemidef)
    (htr : C.trace ≤ T) (ha : 0 ≤ a) :
    (C*C).trace ≤ T*V.trace+a*T := by
  have h₁ := trace_mul_mono_of_posSemidef hC hCV
  have h₂ := trace_mul_mono_of_posSemidef hV hCT
  simp only [mul_add,Matrix.mul_smul,mul_one,trace_add,trace_smul,smul_eq_mul] at h₁ h₂
  rw [trace_mul_comm V C] at h₂
  nlinarith [mul_le_mul_of_nonneg_left htr ha]

end Trace

section Covariance
variable {Ω I : Type} [MeasurableSpace Ω] [Fintype I]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [Fintype I] [IsFiniteMeasure μ] in
theorem covarianceMatrix_isHermitian (X : I → Ω → ℝ) :
    (covarianceMatrix X μ).IsHermitian := by
  ext i j
  simp only [covarianceMatrix,conjTranspose_apply,star_trivial,covariance_comm]

theorem covarianceMatrix_posSemidef (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    (covarianceMatrix X μ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨covarianceMatrix_isHermitian X,fun u => ?_⟩
  have hXu (i : I) : MemLp (fun ω => u i*X i ω) 2 μ := (hX i).const_mul _
  have he : (star u ⬝ᵥ covarianceMatrix X μ *ᵥ u) =
      cov[fun ω => ∑ i, u i*X i ω,fun ω => ∑ i, u i*X i ω;μ] := by
    rw [covariance_fun_sum_left hXu (memLp_finsetSum _ (fun i _ => hXu i))]
    simp_rw [covariance_fun_sum_right hXu (hXu _)]
    simp_rw [covariance_const_mul_left,covariance_const_mul_right]
    change (∑ i, u i * ∑ j, cov[X i, X j; μ]*u j) = _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,covariance_self (memLp_finsetSum _ (fun i _ => hXu i)).aemeasurable]
  exact variance_nonneg _ _

omit [Fintype I] in

theorem covarianceMatrix_residual (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (q : ℝ) :
    covarianceMatrix (fun i ω => X i ω-q*Y i ω) μ =
      covarianceMatrix X μ - q • (crossCovarianceMatrix X Y μ + crossCovarianceMatrix Y X μ) +
      q^2 • covarianceMatrix Y μ := by
  ext i j
  simp only [covarianceMatrix,crossCovarianceMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [covariance_fun_sub_fun_sub (hX i) ((hY i).const_mul q)
      (hX j) ((hY j).const_mul q)]
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  ring

variable [DecidableEq I]

theorem covariance_stein_bound (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (D C : Matrix I I ℝ) (Δ x : ℝ) (hΔ : 0 < Δ) (hx : 0 < x)
    (hD : D.IsHermitian) (hDC : (D-x • C).PosSemidef)
    (hXY : ∀ i j, cov[X i,Y j;μ] = Δ*D i j)
    (hYY : covarianceMatrix Y μ = Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) :
    (covarianceMatrix X μ+(Δ*x^2)⁻¹ • (1 : Matrix I I ℝ)-C).PosSemidef := by
  have hr := covarianceMatrix_posSemidef (fun i ω => X i ω-(Δ*x)⁻¹*Y i ω)
    (fun i => (hX i).sub ((hY i).const_mul _))
  rw [covarianceMatrix_residual X Y hX hY,hYY] at hr
  have hdij (i j) : D j i = D i j := by
    have H := congrArg (fun M : Matrix I I ℝ => M i j) hD.eq
    simpa only [conjTranspose_apply,star_trivial] using H
  have he : covarianceMatrix X μ - (Δ*x)⁻¹ •
      (crossCovarianceMatrix X Y μ + crossCovarianceMatrix Y X μ) +
      ((Δ*x)⁻¹)^2 • (Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) =
      covarianceMatrix X μ - x⁻¹ • D + (Δ*x^2)⁻¹ • (1 : Matrix I I ℝ) := by
    ext i j
    simp only [crossCovarianceMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hXY,covariance_comm (Y i),hdij]
    field_simp [hΔ.ne',hx.ne']
    ring
  rw [he] at hr
  have H := hr.add (hDC.smul (inv_nonneg.mpr hx.le))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp [hx.ne']
  ring

theorem conditional_covariance_trace_bound (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (D C : Matrix I I ℝ) (Δ x T : ℝ) (hΔ : 0 < Δ) (hx : 0 < x)
    (hD : D.IsHermitian) (hC : C.PosSemidef) (htr : C.trace ≤ T)
    (hDC : (D-x • C).PosSemidef)
    (hXY : ∀ i j, cov[X i,Y j;μ] = Δ*D i j)
    (hYY : covarianceMatrix Y μ = Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) :
    (C*C).trace ≤ T*(covarianceMatrix X μ).trace+T/(Δ*x^2) := by
  have H := trace_square_bound hC (covarianceMatrix_posSemidef X hX)
    (posSemidef_scalar_one_sub hC htr)
    (covariance_stein_bound X Y hX hY D C Δ x hΔ hx hD hDC hXY hYY)
    htr (by positivity : 0 ≤ (Δ*x^2)⁻¹)
  simpa only [div_eq_mul_inv,mul_comm ((Δ*x^2)⁻¹)] using H

end Covariance
end SK.Analytic
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
section FiniteCovariance
variable {S I : Type} [Fintype S] [Fintype I]

omit [Fintype I] in
theorem finiteMean_apply (p : S → ℝ) (v : S → I → ℝ) (i : I) :
    finiteMean p v i = ∑ s, p s*v s i := by simp only [finiteMean,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

omit [Fintype I] in
theorem finiteCovariance_apply (p : S → ℝ) (v : S → I → ℝ) (i j : I) :
    finiteCovariance p v i j = (∑ s, p s*v s i*v s j)-finiteMean p v i*finiteMean p v j := by
  simp only [finiteCovariance,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,mul_assoc]

omit [Fintype I] in

theorem finiteCovariance_centered (p : S → ℝ) (v : S → I → ℝ) (hp : ∑ s, p s = 1) :
    finiteCovariance p v = ∑ s, p s • vecMulVec (v s-finiteMean p v) (v s-finiteMean p v) := by
  ext i j
  rw [finiteCovariance_apply]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,Pi.sub_apply]
  have he (s : S) : p s*((v s i-finiteMean p v i)*(v s j-finiteMean p v j)) =
      p s*v s i*v s j-(p s*v s i)*finiteMean p v j-
        (p s*v s j)*finiteMean p v i+p s*(finiteMean p v i*finiteMean p v j) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul,← finiteMean_apply,hp,one_mul]
  ring

theorem finiteCovariance_posSemidef (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) : (finiteCovariance p v).PosSemidef := by
  rw [finiteCovariance_centered p v hs]
  apply Matrix.posSemidef_sum
  intro s _
  apply Matrix.PosSemidef.smul _ (hp s)
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v s-finiteMean p v)

theorem finiteMean_dotProduct (p : S → ℝ) (v : S → I → ℝ) (u : I → ℝ) :
    u ⬝ᵥ finiteMean p v = ∑ s, p s*(u ⬝ᵥ v s) := by
  simp only [finiteMean,dotProduct_sum,dotProduct_smul,smul_eq_mul]

theorem finiteCovariance_quadratic (p : S → ℝ) (v : S → I → ℝ) (u : I → ℝ) :
    u ⬝ᵥ finiteCovariance p v *ᵥ u =
      (∑ s, p s*(u ⬝ᵥ v s)^2)-(∑ s, p s*(u ⬝ᵥ v s))^2 := by
  simp only [finiteCovariance,Matrix.sub_mulVec,dotProduct_sub,Matrix.sum_mulVec,
    dotProduct_sum,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,dotProduct_smul,
    smul_eq_mul,op_smul_eq_mul,finiteMean_dotProduct]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [dotProduct_comm (v s) u]
    ring
  · rw [dotProduct_comm (finiteMean p v) u,finiteMean_dotProduct]
    ring

theorem finiteCovariance_trace_le [DecidableEq I] (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) :
    (finiteCovariance p v).trace ≤ (Fintype.card I : ℝ) := by
  calc
    _ ≤ ∑ _ : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      change finiteCovariance p v i i ≤ 1
      rw [finiteCovariance_apply]
      have he : ∑ s, p s*v s i*v s i ≤ 1 := by
        calc
          _ = ∑ s, p s*(v s i)^2 := by apply Finset.sum_congr rfl; intro s _; ring
          _ ≤ ∑ s, p s*1 := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
            ((sq_le_one_iff_abs_le_one _).mpr (hv s i)) (hp s))
          _ = 1 := by simpa only [mul_one] using hs
      nlinarith [sq_nonneg (finiteMean p v i)]
    _ = _ := by simp
end FiniteCovariance
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem directionalGradient_coordinateVector (n : ℕ) (F : ParameterSpace n → ℝ)
    (u : Fin n → ℝ) (z : ParameterSpace n) :
    directionalGradient F (coordinateVector n u) z = ∑ i, u i*directionalGradient F (coordinateAxis n i) z := by
  simp only [directionalGradient,coordinateVector,map_sum,map_smul,smul_eq_mul]

theorem hessian_tilted_integrable (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (u v : ParameterSpace n) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ F) z v u)
      ((fiberGaussian n x).tilted (fun z => p*F z)) := by
  have he : (fun z => fderiv ℝ (fderiv ℝ F) z v u) =
      fun z => fderiv ℝ (directionalGradient F u) z v := by
    funext z
    rw [fderiv_directionalGradient F hF.1]
    rfl
  rw [he]
  apply ((hF.directionalGradient_bounds u).2.derivative_eval v).integrable_tilted_fiberGaussian n _ (hF.const_mul p)
  exact ((directionalGradient_contDiff F hF.1 u).continuous_fderiv (by norm_num)).clm_apply continuous_const

section CovQuadratic
variable {Ω I : Type} [MeasurableSpace Ω] [Fintype I] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem covarianceMatrix_quadratic (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (u : I → ℝ) :
    u ⬝ᵥ covarianceMatrix X μ *ᵥ u =
      cov[fun z => ∑ i, u i*X i z,fun z => ∑ i, u i*X i z;μ] := by
  have hXu (i : I) : MemLp (fun z => u i*X i z) 2 μ := (hX i).const_mul _
  rw [covariance_fun_sum_left hXu (memLp_finsetSum _ (fun i _ => hXu i))]
  simp_rw [covariance_fun_sum_right hXu (hXu _)]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right]
  change (∑ i, u i * ∑ j, cov[X i, X j;μ]*u j) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end CovQuadratic

theorem gaussianResponse_quadratic (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ gaussianResponse n F p x *ᵥ u =
      (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateVector n u) (coordinateVector n u)
        ∂(fiberGaussian n x).tilted (fun z => p*F z)) +
      p*cov[directionalGradient F (coordinateVector n u),directionalGradient F (coordinateVector n u);
        (fiberGaussian n x).tilted (fun z => p*F z)] := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hM : gaussianResponse n F p x =
      (Matrix.of (fun i j => ∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)) +
      p • covarianceMatrix (fun i => directionalGradient F (coordinateAxis n i)) μ := by rfl
  rw [hM,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  congr 1
  · have hI (i j : Fin n) := hessian_tilted_integrable n F hF p x (coordinateAxis n i) (coordinateAxis n j)
    have he (z : ParameterSpace n) :
        fderiv ℝ (fderiv ℝ F) z (coordinateVector n u) (coordinateVector n u) =
        ∑ i, ∑ j, u i*(fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i)*u j) := by
      simp only [coordinateVector,map_sum,map_smul,_root_.sum_apply,
        _root_.smul_apply,smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [(hF.1.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (coordinateAxis n j) (coordinateAxis n i)]
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ((hI i j).mul_const _).const_mul _))]
    change (∑ i, u i*(∑ j, (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)*u j)) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => ((hI i j).mul_const _).const_mul _),Finset.mul_sum]
    simp only [integral_const_mul,integral_mul_const]
    rfl
  · congr 1
    rw [covarianceMatrix_quadratic _ (fun i =>
      (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
        (directionalGradient_contDiff F hF.1 _).continuous x)]
    have he : directionalGradient F (coordinateVector n u) = fun z => ∑ i, u i*directionalGradient F (coordinateAxis n i) z := by
      funext z
      exact directionalGradient_coordinateVector n F u z
    rw [he]
end SK.Analytic
namespace SK.Analytic
section MixtureCovariance
variable {Ω S : Type} [MeasurableSpace Ω] [Fintype S] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype S] [IsProbabilityMeasure μ] in
theorem integratedWeights_nonneg (P : Ω → S → ℝ) (hP : ∀ z s, 0 ≤ P z s) (s : S) :
    0 ≤ integratedWeights P μ s := integral_nonneg (fun z => hP z s)

theorem integratedWeights_sum (P : Ω → S → ℝ) (hP : ∀ s, Integrable (fun z => P z s) μ)
    (hS : ∀ z, ∑ s, P z s = 1) : ∑ s, integratedWeights P μ s = 1 := by
  unfold integratedWeights
  rw [← integral_finsetSum _ (fun s _ => hP s)]
  simp only [hS,integral_const,probReal_univ,one_smul]

omit [IsProbabilityMeasure μ] in
theorem integral_weighted_sum (P : Ω → S → ℝ) (hP : ∀ s, Integrable (fun z => P z s) μ) (a : S → ℝ) :
    (∫ z, ∑ s, P z s*a s ∂μ) = ∑ s, integratedWeights P μ s*a s := by
  rw [integral_finsetSum _ (fun s _ => (hP s).mul_const _)]
  simp only [integral_mul_const,integratedWeights]

theorem integratedWeights_total_variance (P : Ω → S → ℝ)
    (hP : ∀ s, MemLp (fun z => P z s) 2 μ) (a : S → ℝ) :
    (∫ z, (∑ s, P z s*(a s)^2)-(∑ s, P z s*a s)^2 ∂μ) +
      cov[fun z => ∑ s, P z s*a s,fun z => ∑ s, P z s*a s;μ] =
      (∑ s, integratedWeights P μ s*(a s)^2)-(∑ s, integratedWeights P μ s*a s)^2 := by
  have hPI (s : S) := (hP s).integrable (by norm_num)
  have hA : MemLp (fun z => ∑ s, P z s*a s) 2 μ :=
    memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hB : Integrable (fun z => ∑ s, P z s*(a s)^2) μ :=
    integrable_finsetSum _ (fun s _ => (hPI s).mul_const _)
  rw [integral_sub hB hA.integrable_sq,covariance_eq_sub hA hA]
  simp only [Pi.mul_apply]
  rw [integral_weighted_sum P hPI,integral_weighted_sum P hPI]
  have he : (∫ z, (∑ s, P z s*a s)^2 ∂μ) =
      ∫ z, (∑ s, P z s*a s)*(∑ s, P z s*a s) ∂μ := by simp only [pow_two]
  rw [he]
  ring
end MixtureCovariance
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeFieldCurvature
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem cascadeAffine_gradient_scaled (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (u : E) (a : ℝ)
    (g : S → ℝ) (hg : ∀ s, L s (cascadeLift n u) = a*g s) (z : E) :
    directionalGradient (cascadePressure n m (affineLogPartition c L)) u z =
      a*∑ s, cascadeSpinWeight n m c L z s*g s := by
  rw [directionalGradient,cascadeAffine_gradient,cascadeMoment_affineMoment]
  simp only [hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem cascadeAffine_curvature_scaled (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) {p : ℝ}
    (hl : p ≤ 1) (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (u : E) (a : ℝ) (g : S → ℝ) (hg : ∀ s, L s (cascadeLift n u) = a*g s) (z : E) :
    p*a^2*((∑ s, cascadeSpinWeight n m c L z s*(g s)^2) -
      (∑ s, cascadeSpinWeight n m c L z s*g s)^2) ≤
      fderiv ℝ (fderiv ℝ (cascadePressure n m (affineLogPartition c L))) z u u := by
  have H := (cascadeAffine_curvature n m c L hl hm hmu hmono z u).2
  simp_rw [cascadeMoment_affineMoment,hg] at H
  have h₁ : (∑ s, cascadeSpinWeight n m c L z s*(a*g s)^2) =
      a^2*∑ s, cascadeSpinWeight n m c L z s*(g s)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have h₂ : (∑ s, cascadeSpinWeight n m c L z s*(a*g s)) =
      a*∑ s, cascadeSpinWeight n m c L z s*g s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h₁,h₂] at H
  convert H using 1 <;> first | rfl | ring
end CascadeFieldCurvature

section CoordinateFields
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem cascade_coordinates_field (N n : ℕ)
    (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ) (a : ℝ)
    (v : S → Fin N → ℝ)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i)
    (u : Fin N → ℝ) (s : S) :
    L s (cascadeLift n (coordinateVector N u)) = a*(u ⬝ᵥ v s) := by
  rw [← cascadeLiftCLM_apply]
  simp only [coordinateVector,map_sum,map_smul,smul_eq_mul,cascadeLiftCLM_apply,hv,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end CoordinateFields
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section GaussianSpinResponse
variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in

theorem gaussianResponse_mixture_domination (N : ℕ) (F : ParameterSpace N → ℝ)
    (hF : BoundedDerivs F) (p a x : ℝ) (P : ParameterSpace N → S → ℝ)
    (v : S → Fin N → ℝ)
    (hP : ∀ s, MemLp (fun z => P z s) 2 ((fiberGaussian N x).tilted (fun z => p*F z)))
    (hPpos : ∀ z s, 0 ≤ P z s) (hPsum : ∀ z, ∑ s, P z s = 1)
    (hG : ∀ u z, directionalGradient F (coordinateVector N u) z =
      a*∑ s, P z s*(u ⬝ᵥ v s))
    (hH : ∀ u z, p*a^2*((∑ s, P z s*(u ⬝ᵥ v s)^2)-(∑ s, P z s*(u ⬝ᵥ v s))^2) ≤
      fderiv ℝ (fderiv ℝ F) z (coordinateVector N u) (coordinateVector N u)) :
    (gaussianResponse N F p x - (p*a^2) •
      finiteCovariance (integratedWeights P ((fiberGaussian N x).tilted (fun z => p*F z))) v).PosSemidef := by
  let μ := (fiberGaussian N x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability N _ (hF.const_mul p) x
  have hPI (s : S) : Integrable (fun z => P z s) μ := (hP s).integrable (by norm_num)
  have hC := finiteCovariance_posSemidef (integratedWeights P μ) v
    (integratedWeights_nonneg P hPpos) (integratedWeights_sum P hPI hPsum)
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(gaussianResponse_isHermitian N F hF.1 p x).sub (hC.isHermitian.smul (by simp [IsSelfAdjoint])),fun u => ?_⟩
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  rw [gaussianResponse_quadratic N F hF,finiteCovariance_quadratic]
  let A : ParameterSpace N → ℝ := fun z => ∑ s, P z s*(u ⬝ᵥ v s)
  have hA : MemLp A 2 μ := memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hB : Integrable (fun z => ∑ s, P z s*(u ⬝ᵥ v s)^2) μ :=
    integrable_finsetSum _ (fun s _ => (hPI s).mul_const _)
  have hv : Integrable (fun z => (∑ s, P z s*(u ⬝ᵥ v s)^2)-A z^2) μ := hB.sub hA.integrable_sq
  have HI := integral_mono (hv.const_mul (p*a^2))
    (hessian_tilted_integrable N F hF p x _ _) (hH u)
  rw [integral_const_mul] at HI
  have HT := integratedWeights_total_variance (μ := μ) P hP (fun s => u ⬝ᵥ v s)
  have he : directionalGradient F (coordinateVector N u) = fun z => a*A z := funext (hG u)
  rw [he,covariance_const_mul_left,covariance_const_mul_right]
  change 0 ≤ (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateVector N u) (coordinateVector N u) ∂μ) +
    p*(a*(a*cov[A,A;μ])) - (p*a^2)*
      ((∑ s, integratedWeights P μ s*(u ⬝ᵥ v s)^2)-(∑ s, integratedWeights P μ s*(u ⬝ᵥ v s))^2)
  change (∫ z, (∑ s, P z s*(u ⬝ᵥ v s)^2)-A z^2 ∂μ) + cov[A,A;μ] = _ at HT
  rw [← HT]
  nlinarith [HI]

theorem cascadeGaussianResponse_domination (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ)
    (p a x : ℝ) (hl : p ≤ 1) (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i) :
    let F := cascadePressure n m (affineLogPartition c L)
    let μ := (fiberGaussian N x).tilted (fun z => p*F z)
    let P := cascadeSpinWeight n m c L
    (gaussianResponse N F p x - (p*a^2) • finiteCovariance (integratedWeights P μ) v).PosSemidef := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  apply gaussianResponse_mixture_domination N F hF p a x (cascadeSpinWeight n m c L) v
  · intro s
    have hr := cascadeSpinWeight_regular n m c L s
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian N _ (hF.const_mul p) hr.1 x
  · exact cascadeSpinWeight_nonneg n m c L
  · exact cascadeSpinWeight_sum n m c L
  · intro u z
    exact cascadeAffine_gradient_scaled n m c L (coordinateVector N u) a _ (cascade_coordinates_field N n L a v hv u) z
  · intro u z
    exact cascadeAffine_curvature_scaled n m c L hl hm hmu hmono (coordinateVector N u) a _
      (cascade_coordinates_field N n L a v hv u) z
end GaussianSpinResponse
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section GaussianSpinTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem cascadeGaussian_conditional_trace (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ)
    (p a x : ℝ) (hp : 0 < p) (ha : 0 < a) (hl : p ≤ 1)
    (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i) :
    let F := cascadePressure n m (affineLogPartition c L)
    let μ := (fiberGaussian N x).tilted (fun z => p*F z)
    let P := cascadeSpinWeight n m c L
    let C := finiteCovariance (integratedWeights P μ) v
    let X := fun i z => finiteMean (P z) v i
    (C*C).trace ≤ (N : ℝ)*(covarianceMatrix X μ).trace+(N : ℝ)/(a^2*p^2) := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  let μ := (fiberGaussian N x).tilted (fun z => p*F z)
  let P := cascadeSpinWeight n m c L
  let C := finiteCovariance (integratedWeights P μ) v
  let X : Fin N → ParameterSpace N → ℝ := fun i z => finiteMean (P z) v i
  let Y : Fin N → ParameterSpace N → ℝ := fun i z => a*coordinateProjection N i z
  let D : Matrix (Fin N) (Fin N) ℝ := (a^2)⁻¹ • gaussianResponse N F p x
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  let := fiberGaussian_tilted_probability N _ (hF.const_mul p) x
  have hP (s : S) : MemLp (fun z => P z s) 2 μ := by
    have hr := cascadeSpinWeight_regular n m c L s
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian N _ (hF.const_mul p) hr.1 x
  have hPI (s : S) : Integrable (fun z => P z s) μ := (hP s).integrable (by norm_num)
  have hq₀ := integratedWeights_nonneg (μ := μ) P (cascadeSpinWeight_nonneg n m c L)
  have hq₁ := integratedWeights_sum (μ := μ) P hPI (cascadeSpinWeight_sum n m c L)
  have hC : C.PosSemidef := finiteCovariance_posSemidef _ v hq₀ hq₁
  have hCT : C.trace ≤ (N : ℝ) := by
    simpa only [Fintype.card_fin,C] using finiteCovariance_trace_le _ v hq₀ hq₁ hvb
  have hX (i : Fin N) : MemLp (X i) 2 μ := by
    change MemLp (fun z => finiteMean (P z) v i) 2 μ
    simp only [finiteMean_apply]
    exact memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hY (i : Fin N) : MemLp (Y i) 2 μ :=
    ((HasExpGrowth.linear (coordinateProjection N i)).memLp_two_tilted_fiberGaussian N _
      (hF.const_mul p) (coordinateProjection N i).continuous x).const_mul a
  have hG (i : Fin N) : directionalGradient F (coordinateAxis N i) = fun z => a*X i z := by
    funext z
    simpa only [X,P,finiteMean_apply] using cascadeAffine_gradient_scaled n m c L (coordinateAxis N i) a (fun s => v s i) (fun s => hv s i) z
  have hXG (i : Fin N) : X i = fun z => a⁻¹*directionalGradient F (coordinateAxis N i) z := by
    rw [hG]
    funext z
    simp only [inv_mul_cancel_left₀ ha.ne']
  have hD : D.IsHermitian := (gaussianResponse_isHermitian N F hF.1 p x).smul (by simp [IsSelfAdjoint])
  have hDC : (D-p • C).PosSemidef := by
    have H := (cascadeGaussianResponse_domination N n m c L p a x hl hm hmu hmono v hv).smul
      (inv_nonneg.mpr (sq_nonneg a))
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext i j
    simp only [D,C,F,P,μ,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp [ha.ne']
  have hXY (i j : Fin N) : cov[X i,Y j;μ] = a^2*D i j := by
    rw [hXG]
    change cov[fun z => a⁻¹*directionalGradient F (coordinateAxis N i) z,
      fun z => a*coordinateProjection N j z;μ] = _
    rw [covariance_const_mul_left,covariance_const_mul_right,gaussian_tilted_cross_covariance N F hF p x]
    simp only [D,Matrix.smul_apply,smul_eq_mul]
    field_simp [ha.ne']
  have hYY : covarianceMatrix Y μ = a^2 • (1 : Matrix (Fin N) (Fin N) ℝ)+((a^2)^2*p) • D := by
    ext i j
    change cov[fun z => a*coordinateProjection N i z,fun z => a*coordinateProjection N j z;μ] = _
    rw [covariance_const_mul_left,covariance_const_mul_right,gaussian_tilted_field_covariance N F hF p x]
    simp only [D,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    field_simp [ha.ne']
  exact conditional_covariance_trace_bound X Y hX hY D C (a^2) p N (sq_pos_of_pos ha) hp hD hC hCT hDC hXY hYY
end GaussianSpinTrace
end SK.Analytic

end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ReciprocalSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem sum_nat_reciprocal_squares_aux (k : ℕ) :
    (∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 2-2/((k+1 : ℕ) : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    have hk : (0 : ℝ) < (k+1 : ℕ) := by positivity
    have hl : (0 : ℝ) < (k+1+1 : ℕ) := by positivity
    have hi : 1/((k+1 : ℕ) : ℝ)^2 ≤ 2/((k+1 : ℕ) : ℝ)-2/((k+1+1 : ℕ) : ℝ) := by
      apply (le_sub_iff_add_le).2
      field_simp [ne_of_gt hk,ne_of_gt hl]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    linarith

theorem sum_nat_reciprocal_squares (k : ℕ) :
    (∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 2 :=
  (sum_nat_reciprocal_squares_aux k).trans (sub_le_self _ (by positivity))
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockMassValue
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

 theorem blockMass_eq_sum (D N k : ℕ) (i : Fin (blockDimension D N k)) :
    blockMass D N k i = ∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0 := by
  unfold blockMass massFromAtoms blockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b = t then
        (if t.val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem blockMass_at_field (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    blockMass D N k (fieldIndex D N k b i) = (b.val : ℝ)/((k+1 : ℕ) : ℝ) := by
  rw [blockMass_eq_sum]
  have hh (c : Fin (k+1)) : (blockLevel D N k c).val ≤ (fieldIndex D N k b i).val ↔ c < b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hc : b.val ≤ c.val := by omega
      have hc' := Nat.mul_le_mul_right N hc
      nlinarith [i.isLt]
    · intro h
      have hc := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun c : Fin (k+1) => c < b) = Finset.Iio b := by
    ext c
    simp
  rw [hs]
  simp only [Finset.sum_const,Fin.card_Iio,nsmul_eq_mul,div_eq_mul_inv]
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathWeight_const (n : ℕ) (p : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    hierarchyPathWeight n (fun _ => p) f z =
      Real.exp (p*(f z-hierarchyPressure n (fun _ => p) f (parameter n z))) := by
  induction n with
  | zero => simp [hierarchyPathWeight,hierarchyPressure,parameter]
  | succ n ih =>
    rw [hierarchyPathWeight,ih,← Real.exp_add]
    apply congrArg Real.exp
    change p*(f z-gaussianStep p f z.1)+p*(gaussianStep p f z.1-
      hierarchyPressure n (fun _ => p) (gaussianStep p f) (parameter n z.1)) = _
    change _ = p*(f z-hierarchyPressure n (fun _ => p) (gaussianStep p f) (parameter n z.1))
    ring

theorem parameter_ae_fiberGaussian (n : ℕ) (x : ℝ) :
    ∀ᵐ z ∂fiberGaussian n x, parameter n z = x := by
  induction n with
  | zero => simp [fiberGaussian,parameter]
  | succ n ih =>
    change ∀ᵐ z ∂(fiberGaussian n x).prod (gaussianReal 0 1), parameter n z.1 = x
    exact Measure.quasiMeasurePreserving_fst.ae ih

theorem hierarchyPathLaw_const (n : ℕ) (p : ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPathLaw n (fun _ => p) f x = (fiberGaussian n x).tilted (fun z => p*f z) := by
  let A := hierarchyPressure n (fun _ => p) f x
  have hweight : hierarchyPathWeight n (fun _ => p) f =ᵐ[fiberGaussian n x]
      (fun z => Real.exp (p*f z)/Real.exp (p*A)) := by
    filter_upwards [parameter_ae_fiberGaussian n x] with z hz
    rw [hierarchyPathWeight_const,hz,mul_sub,Real.exp_sub]
  have hZ : (∫ z, Real.exp (p*f z) ∂fiberGaussian n x) = Real.exp (p*A) := by
    have hn := (hierarchyPathWeight_normalized n (fun _ => p) f hf x).2
    rw [integral_congr_ae hweight,integral_div] at hn
    exact (div_eq_one_iff_eq (Real.exp_ne_zero _)).mp hn
  rw [hierarchyPathLaw,Measure.tilted,hZ]
  apply withDensity_congr_ae
  exact hweight.fun_comp ENNReal.ofReal

end SK.Analytic
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem gaussianStep_append (a b : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianStep p (fun z => f (parameterAppend a (b+1) z)) =
      fun z => gaussianStep p f (parameterAppend a b z) := by
  rfl

theorem gaussianAverage_append (a b : ℕ) (p : ℝ) (f g : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianAverage p (fun z => f (parameterAppend a (b+1) z)) (fun z => g (parameterAppend a (b+1) z)) =
      fun z => gaussianAverage p f g (parameterAppend a b z) := rfl

theorem hierarchyMomentLevel_last (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) : hierarchyMomentLevel n m f g (Fin.last n) = g := by
  cases n with
  | zero => rfl
  | succ n => simp only [hierarchyMomentLevel,Fin.lastCases_last]

theorem hierarchyMomentLevel_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f g : ParameterSpace (a+b) → ℝ) (z : CascadeSpace (ParameterSpace a) b) :
    hierarchyMomentLevel (a+b) m f g ⟨a,by omega⟩ (parameterAppend a b z) =
      cascadeMoment b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))
        (fun z => g (parameterAppend a b z)) (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero =>
    change hierarchyMomentLevel a m f g (Fin.last a) z = g z
    rw [hierarchyMomentLevel_last]
  | succ b ih =>
    change hierarchyMomentLevel ((a+b)+1) m f g (Fin.castSucc ⟨a,by omega⟩)
      (parameterAppend a b z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih]
    rw [cascadeMoment,gaussianStep_append,gaussianAverage_append]
    rfl

end SK.Analytic
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Translate
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parameterEmbed_eq (b : ℕ) (x : E) (z : ParameterSpace b) :
    parameterEmbed b x z = cascadeLift b x+parameterNoise (E := E) b z := by
  induction b with
  | zero => simp only [parameterEmbed,cascadeLift,parameterNoise,_root_.zero_apply,add_zero]
  | succ b ih =>
    change (parameterEmbed b x z.1,z.2) = (cascadeLift b x+parameterNoise (E := E) b z.1,0+z.2)
    rw [ih,zero_add]

theorem BoundedDerivs.parameterEmbed {b : ℕ} {f : CascadeSpace E b → ℝ}
    (hf : BoundedDerivs f) (x : E) : BoundedDerivs (fun z => f (parameterEmbed b x z)) := by
  simpa only [parameterEmbed_eq] using (hf.translate (cascadeLift b x)).compCLM (parameterNoise (E := E) b)

theorem parameterEmbed_continuous (b : ℕ) (x : E) : Continuous (parameterEmbed b x) := by
  have he : parameterEmbed b x = fun z => cascadeLift b x+parameterNoise (E := E) b z := funext (parameterEmbed_eq b x)
  rw [he]
  exact continuous_const.add (parameterNoise (E := E) b).continuous

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStep_parameterEmbed (b : ℕ) (p : ℝ) (f : CascadeSpace E (b+1) → ℝ) (x : E) :
    gaussianStep p (fun z => f (parameterEmbed (b+1) x z)) =
      fun z => gaussianStep p f (parameterEmbed b x z) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_parameterEmbed (b : ℕ) (p : ℝ) (f g : CascadeSpace E (b+1) → ℝ) (x : E) :
    gaussianAverage p (fun z => f (parameterEmbed (b+1) x z)) (fun z => g (parameterEmbed (b+1) x z)) =
      fun z => gaussianAverage p f g (parameterEmbed b x z) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cascadeMoment_parameterEmbed (b : ℕ) (m : Fin b → ℝ)
    (f g : CascadeSpace E b → ℝ) (x : E) (y : ℝ) :
    cascadeMoment b m f g x = hierarchyAverage b m (fun z => f (parameterEmbed b x z))
      (fun z => g (parameterEmbed b x z)) y := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [cascadeMoment,ih,hierarchyAverage,gaussianStep_parameterEmbed,gaussianAverage_parameterEmbed]

theorem cascadeMoment_const_integral (b : ℕ) (p : ℝ) (f g : CascadeSpace E b → ℝ)
    (hf : BoundedDerivs f) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (x : E) :
    cascadeMoment b (fun _ => p) f g x =
      ∫ z, g (parameterEmbed b x z) ∂(fiberGaussian b 0).tilted (fun z => p*f (parameterEmbed b x z)) := by
  have hg' : Continuous (fun z => g (parameterEmbed b x z)) := by
    simpa only [Function.comp_def] using hg.comp (parameterEmbed_continuous b x)
  rw [cascadeMoment_parameterEmbed b (fun _ => p) f g x 0]
  rw [hierarchyAverage_eq_integral b (fun _ => p) (fun z => f (parameterEmbed b x z))
    (hf.parameterEmbed x) (fun z => g (parameterEmbed b x z)) hg' hC (fun z => hb _) 0]
  rw [hierarchyPathLaw_const b p _ (hf.parameterEmbed x) 0]
end Translate
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyBlocks
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

theorem gaussianStep_blocks (a b c : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+(c+1))) → ℝ) :
    gaussianStep p (fun z => f (parameterBlocks a b (c+1) z)) =
      fun z => gaussianStep p f (parameterBlocks a b c z) := rfl

theorem gaussianAverage_blocks (a b c : ℕ) (p : ℝ) (f g : ParameterSpace (a+(b+(c+1))) → ℝ) :
    gaussianAverage p (fun z => f (parameterBlocks a b (c+1) z)) (fun z => g (parameterBlocks a b (c+1) z)) =
      fun z => gaussianAverage p f g (parameterBlocks a b c z) := rfl

theorem hierarchyMomentLevel_after_block (a b c : ℕ) (m : Fin (a+(b+c)) → ℝ)
    (f g : ParameterSpace (a+(b+c)) → ℝ) (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) :
    hierarchyMomentLevel (a+(b+c)) m f g ⟨a+b,by omega⟩ (parameterBlocks a b c z) =
      cascadeMoment c (fun i => m ⟨a+b+i,by omega⟩)
        (fun z => f (parameterBlocks a b c z)) (fun z => g (parameterBlocks a b c z))
        (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) c z) := by
  induction c with
  | zero =>
    change hierarchyMomentLevel (a+b) m f g (Fin.last (a+b)) (parameterAppend a b z) = g (parameterAppend a b z)
    rw [hierarchyMomentLevel_last]
  | succ c ih =>
    change hierarchyMomentLevel ((a+(b+c))+1) m f g (Fin.castSucc ⟨a+b,by omega⟩)
      (parameterBlocks a b c z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih,cascadeMoment,gaussianStep_blocks,gaussianAverage_blocks]
    have he : (⟨a+b+(Fin.last c).val,by omega⟩ : Fin (a+(b+(c+1)))) = Fin.last (a+(b+c)) := by
      apply Fin.ext
      exact Nat.add_assoc a b c
    rw [he]
    rfl

theorem hierarchyMomentLevel_before_block (a b c : ℕ) (m : Fin (a+(b+c)) → ℝ)
    (f g : ParameterSpace (a+(b+c)) → ℝ) (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) :
    hierarchyMomentLevel (a+(b+c)) m f g ⟨a,by omega⟩ (parameterBlocks a b c z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩)
        (cascadePressure c (fun i => m ⟨a+b+i,by omega⟩) (fun z => f (parameterBlocks a b c z)))
        (cascadeMoment c (fun i => m ⟨a+b+i,by omega⟩)
          (fun z => f (parameterBlocks a b c z)) (fun z => g (parameterBlocks a b c z)))
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) c z)) := by
  induction c with
  | zero =>
    exact hierarchyMomentLevel_split a b m f g z
  | succ c ih =>
    change hierarchyMomentLevel ((a+(b+c))+1) m f g (Fin.castSucc ⟨a,by omega⟩)
      (parameterBlocks a b c z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih,cascadePressure,cascadeMoment,gaussianStep_blocks,gaussianAverage_blocks]
    have he : (⟨a+b+(Fin.last c).val,by omega⟩ : Fin (a+(b+(c+1)))) = Fin.last (a+(b+c)) := by
      apply Fin.ext
      exact Nat.add_assoc a b c
    rw [he]
    rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAxis
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

theorem parameterAppend_noise_axis (a b : ℕ) (i : Fin b) :
    parameterAppend a b (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i)) =
      coordinateAxis (a+b) ⟨a+i.val,by omega⟩ := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [coordinateAxis_last]
      have he : (⟨a+(Fin.last b).val,by omega⟩ : Fin (a+(b+1))) = Fin.last (a+b) := by
        apply Fin.ext; simp
      rw [he]
      change _ = coordinateAxis ((a+b)+1) (Fin.last (a+b))
      rw [coordinateAxis_last]
      change (parameterAppend a b (parameterNoise (E := ParameterSpace a) b 0),1) = (0,1)
      rw [map_zero,map_zero]
    · rw [coordinateAxis_castSucc]
      have he : (⟨a+i.castSucc.val,by omega⟩ : Fin (a+(b+1))) = (⟨a+i.val,by omega⟩ : Fin (a+b)).castSucc := by
        rfl
      rw [he]
      change _ = coordinateAxis ((a+b)+1) (⟨a+i.val,by omega⟩ : Fin (a+b)).castSucc
      rw [coordinateAxis_castSucc]
      change (parameterAppend a b (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i)),0) = _
      rw [ih]

theorem parameterBlocks_noise_axis (a b d : ℕ) (i : Fin b) :
    parameterBlocks a b d (cascadeLift d (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i))) =
      coordinateAxis (a+(b+d)) ⟨a+i.val,by omega⟩ := by
  induction d with
  | zero => exact parameterAppend_noise_axis a b i
  | succ d ih =>
    change (parameterBlocks a b d (cascadeLift d (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i))),0) = _
    rw [ih]
    change _ = coordinateAxis ((a+(b+d))+1) (⟨a+i.val,by omega⟩ : Fin (a+(b+d))).castSucc
    rw [coordinateAxis_castSucc]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeRebase
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
section CascadeMap
variable {E F : Type}

theorem gaussianStep_cascadeMap (n : ℕ) (A : E → F) (p : ℝ)
    (f : CascadeSpace F (n+1) → ℝ) :
    gaussianStep p (fun z => f (cascadeMap (n+1) A z)) =
      fun z => gaussianStep p f (cascadeMap n A z) := rfl

theorem gaussianAverage_cascadeMap (n : ℕ) (A : E → F) (p : ℝ)
    (f g : CascadeSpace F (n+1) → ℝ) :
    gaussianAverage p (fun z => f (cascadeMap (n+1) A z)) (fun z => g (cascadeMap (n+1) A z)) =
      fun z => gaussianAverage p f g (cascadeMap n A z) := rfl

theorem cascadePressure_cascadeMap (n : ℕ) (A : E → F) (m : Fin n → ℝ)
    (f : CascadeSpace F n → ℝ) (x : E) :
    cascadePressure n m (fun z => f (cascadeMap n A z)) x = cascadePressure n m f (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadePressure,gaussianStep_cascadeMap,ih,cascadePressure]

theorem cascadeMoment_cascadeMap (n : ℕ) (A : E → F) (m : Fin n → ℝ)
    (f g : CascadeSpace F n → ℝ) (x : E) :
    cascadeMoment n m (fun z => f (cascadeMap n A z)) (fun z => g (cascadeMap n A z)) x =
      cascadeMoment n m f g (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadeMoment,gaussianStep_cascadeMap,gaussianAverage_cascadeMap,ih,cascadeMoment]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cascadeMap_affine (n : ℕ) (u : F) (A : E →L[ℝ] F) (z : CascadeSpace E n) :
    cascadeMap n (fun x => u+A x) z = cascadeLift n u+cascadeMapCLM n A z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cascadeMap n (fun x => u+A x) z.1,z.2) = (cascadeLift n u+cascadeMapCLM n A z.1,0+z.2)
    rw [ih,zero_add]

theorem cascadeMapCLM_lift (n : ℕ) (A : E →L[ℝ] F) (x : E) :
    cascadeMapCLM n A (cascadeLift n x) = cascadeLift n (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cascadeMapCLM n A (cascadeLift n x),0) = (cascadeLift n (A x),0)
    rw [ih]

variable {S : Type} [Fintype S]

theorem affineLogPartition_rebase (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ)
    (u : F) (A : E →L[ℝ] F) :
    affineLogPartition (rebaseConstants n c L u) (rebaseLinears n L A) =
      fun z => affineLogPartition c L (cascadeMap n (fun x => u+A x) z) := by
  funext z
  simp only [affineLogPartition,rebaseConstants,rebaseLinears,
    ContinuousLinearMap.comp_apply,cascadeMap_affine,map_add,add_assoc]

theorem affineGibbs_rebase (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ)
    (u : F) (A : E →L[ℝ] F) (z : CascadeSpace E n) (s : S) :
    affineGibbs (rebaseConstants n c L u) (rebaseLinears n L A) z s =
      affineGibbs c L (cascadeMap n (fun x => u+A x) z) s := by
  simp only [affineGibbs,rebaseConstants,rebaseLinears,
    ContinuousLinearMap.comp_apply,cascadeMap_affine,map_add,add_assoc]

theorem cascadePressure_rebase (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) (A : E →L[ℝ] F) (x : E) :
    cascadePressure n m (affineLogPartition (rebaseConstants n c L u) (rebaseLinears n L A)) x =
      cascadePressure n m (affineLogPartition c L) (u+A x) := by
  rw [affineLogPartition_rebase,cascadePressure_cascadeMap]

theorem cascadeSpinWeight_rebase (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) (A : E →L[ℝ] F) (x : E) (s : S) :
    cascadeSpinWeight n m (rebaseConstants n c L u) (rebaseLinears n L A) x s =
      cascadeSpinWeight n m c L (u+A x) s := by
  unfold cascadeSpinWeight
  rw [affineLogPartition_rebase]
  simp only [affineGibbs_rebase]
  exact cascadeMoment_cascadeMap n (fun x => u+A x) m (affineLogPartition c L) (fun z => affineGibbs c L z s) x
end CascadeMap
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
namespace SK.Analytic
open Matrix
section ReplicaOverlap
variable {S I : Type} [Fintype S] [Fintype I]

omit [Fintype I] in
theorem finiteMean_abs_le_one (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) (i : I) :
    |finiteMean p v i| ≤ 1 := by
  rw [finiteMean_apply]
  calc
    _ ≤ ∑ s, |p s*v s i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, p s*|v s i| := by simp only [abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ s, p s*1 := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hv s i) (hp s))
    _ = 1 := by simp only [mul_one,hs]

end ReplicaOverlap
end SK.Analytic

end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeBlockTrace
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
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeBlockTrace
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem cascadeMean_regular {I : Type} (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace E n →L[ℝ] ℝ) (v : S → I → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (i : I) :
    Continuous (fun z => finiteMean (cascadeSpinWeight n m c L z) v i) ∧
      ∀ z, ‖finiteMean (cascadeSpinWeight n m c L z) v i‖ ≤ 1 := by
  constructor
  · simp only [finiteMean_apply]
    exact continuous_finsetSum _ (fun s _ => (cascadeSpinWeight_regular n m c L s).1.mul continuous_const)
  · intro z
    exact finiteMean_abs_le_one _ v (cascadeSpinWeight_nonneg n m c L z)
      (cascadeSpinWeight_sum n m c L z) hv i

theorem cascadeBlock_trace (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (CascadeSpace E N) n →L[ℝ] ℝ)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (hl : p ≤ 1)
    (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, L s (cascadeLift n (parameterNoise (E := E) N (coordinateAxis N i))) = a*v s i)
    (x : E) :
    let F := cascadePressure n m (affineLogPartition c L)
    let P := cascadeSpinWeight n m c L
    let W := fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x
    let C := finiteCovariance W v
    let X := fun i z => finiteMean (P z) v i
    (C*C).trace ≤ (N : ℝ)*(∑ i, (cascadeMoment N (fun _ => p) F (fun z => (X i z)^2) x-
      (cascadeMoment N (fun _ => p) F (X i) x)^2))+(N : ℝ)/(a^2*p^2) := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  let P := cascadeSpinWeight n m c L
  let X : Fin N → CascadeSpace E N → ℝ := fun i z => finiteMean (P z) v i
  let c' := rebaseConstants n c L (cascadeLift N x)
  let L' := rebaseLinears n L (parameterNoise (E := E) N)
  let F' := cascadePressure n m (affineLogPartition c' L')
  let P' := cascadeSpinWeight n m c' L'
  let μ := (fiberGaussian N 0).tilted (fun z => p*F' z)
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  have hF' : BoundedDerivs F' := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c' L')
  let := fiberGaussian_tilted_probability N _ (hF'.const_mul p) 0
  have hFe (z : ParameterSpace N) : F' z = F (parameterEmbed N x z) := by
    rw [parameterEmbed_eq]
    exact cascadePressure_rebase n m c L (cascadeLift N x) (parameterNoise (E := E) N) z
  have hPe (z : ParameterSpace N) (s : S) : P' z s = P (parameterEmbed N x z) s := by
    rw [parameterEmbed_eq]
    exact cascadeSpinWeight_rebase n m c L (cascadeLift N x) (parameterNoise (E := E) N) z s
  have hM (g : CascadeSpace E N → ℝ) (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
      (hb : ∀ z, ‖g z‖ ≤ B) :
      cascadeMoment N (fun _ => p) F g x = ∫ z, g (parameterEmbed N x z) ∂μ := by
    rw [cascadeMoment_const_integral N p F g hF hg hB hb x]
    congr 1
    exact congrArg (fun h => (fiberGaussian N 0).tilted h) (funext fun z => congrArg (p*·) (hFe z).symm)
  have hW : (fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x) = integratedWeights P' μ := by
    funext s
    rw [hM _ (cascadeSpinWeight_regular n m c L s).1 (by norm_num : (0 : ℝ) ≤ 1)
      (cascadeSpinWeight_regular n m c L s).2]
    exact integral_congr_ae (ae_of_all _ (fun z => (hPe z s).symm))
  have hX (i : Fin N) : MemLp (fun z => finiteMean (P' z) v i) 2 μ := by
    have hr := cascadeMean_regular n m c' L' v hvb i
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian
      N _ (hF'.const_mul p) hr.1 0
  have hXe (i : Fin N) (z : ParameterSpace N) : finiteMean (P' z) v i = X i (parameterEmbed N x z) := by
    unfold X
    congr 2
    exact funext (hPe z)
  have hV : (covarianceMatrix (fun i z => finiteMean (P' z) v i) μ).trace =
      ∑ i, (cascadeMoment N (fun _ => p) F (fun z => (X i z)^2) x-
        (cascadeMoment N (fun _ => p) F (X i) x)^2) := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    change cov[fun z => finiteMean (P' z) v i,fun z => finiteMean (P' z) v i;μ] = _
    rw [covariance_eq_sub (hX i) (hX i)]
    have R := cascadeMean_regular n m c L v hvb i
    have hxc : Continuous (X i) := R.1
    have hxsc : Continuous (fun z => (X i z)^2) := hxc.pow 2
    rw [hM (fun z => (X i z)^2) hxsc (by norm_num : (0 : ℝ) ≤ 1) (fun z => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (R.2 z)),
      hM (X i) hxc (by norm_num : (0 : ℝ) ≤ 1) R.2]
    simp only [Pi.mul_apply,hXe,pow_two]
  have hv' (s : S) (i : Fin N) : L' s (cascadeLift n (coordinateAxis N i)) = a*v s i := by
    change L s (cascadeMapCLM n (parameterNoise (E := E) N) (cascadeLift n (coordinateAxis N i))) = _
    rw [cascadeMapCLM_lift]
    exact hv s i
  have H := cascadeGaussian_conditional_trace N n m c' L' p a 0 hp ha hl hm hmu hmono v hvb hv'
  change (finiteCovariance (integratedWeights P' μ) v*finiteCovariance (integratedWeights P' μ) v).trace ≤
    (N : ℝ)*(covarianceMatrix (fun i z => finiteMean (P' z) v i) μ).trace+(N : ℝ)/(a^2*p^2) at H
  rw [hV,← hW] at H
  exact H
end CascadeBlockTrace
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyBlockTrace
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
section CascadeRootMoment
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadeMoment_root (n : ℕ) (m : Fin n → ℝ) (f : CascadeSpace E n → ℝ)
    (hf : BoundedDerivs f) (g : E → ℝ) :
    cascadeMoment n m f (fun z => g (cascadeRoot (E := E) n z)) = g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : gaussianAverage (m (Fin.last n)) f (fun z => g (cascadeRoot (E := E) (n+1) z)) =
        fun z => g (cascadeRoot (E := E) n z) := by
      exact gaussianAverage_const_prefix hf _ (fun z => g (cascadeRoot (E := E) n z))
    rw [cascadeMoment,he]
    exact ih _ _ (hf.gaussianStep _)
end CascadeRootMoment

section HierarchyBlockTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinMean_after_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    hierarchySpinMean (a+(b+d)) m U v ⟨a+b,by omega⟩ (parameterBlocks a b d z) =
      ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
        (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap)
        (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z) s*v s := by
  unfold hierarchySpinMean
  rw [hierarchyMomentLevel_after_block]
  exact cascadeMoment_affineMoment d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
    (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) v _

theorem hierarchySpinMean_before_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    let F := cascadePressure d (fun i => m ⟨a+b+i,by omega⟩)
      (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    let X := fun x => ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s
    hierarchySpinMean (a+(b+d)) m U v ⟨a,by omega⟩ (parameterBlocks a b d z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩) F X
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z)) := by
  dsimp only
  unfold hierarchySpinMean
  rw [hierarchyMomentLevel_before_block]
  congr 1
  funext x
  exact cascadeMoment_affineMoment d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
    (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) v x

theorem hierarchyMeanSquare_before_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    let F := cascadePressure d (fun i => m ⟨a+b+i,by omega⟩)
      (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    let X := fun x => ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s
    hierarchyMomentLevel (a+(b+d)) m (affineLogPartition (fun _ => 0) U)
      (fun z => (hierarchySpinMean (a+(b+d)) m U v ⟨a+b,by omega⟩ z)^2)
      ⟨a,by omega⟩ (parameterBlocks a b d z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩) F (fun x => (X x)^2)
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z)) := by
  dsimp only
  rw [hierarchyMomentLevel_before_block]
  simp only [hierarchySpinMean_after_block]
  congr 1
  exact cascadeMoment_root d (fun i => m ⟨a+b+i,by omega⟩)
    (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    (affineLogPartition_boundedDerivs (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    (fun x => (∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s)^2)

theorem hierarchyBlock_conditional_trace (a N d : ℕ) (m : Fin (a+(N+d)) → ℝ)
    (U : S → ParameterSpace (a+(N+d)) →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin d, p ≤ m ⟨a+N+i,by omega⟩)
    (hmu : ∀ i : Fin d, m ⟨a+N+i,by omega⟩ ≤ 1)
    (hmono : Monotone (fun i : Fin d => m ⟨a+N+i,by omega⟩))
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, U s (parameterBlocks a N d (cascadeLift d
      (parameterNoise (E := ParameterSpace a) N (coordinateAxis N i)))) = scale*v s i)
    (z : ParameterSpace (a+(N+d))) :
    let C := finiteCovariance (hierarchySpinWeight (a+(N+d)) m U ⟨a,by omega⟩ z) v
    (C*C).trace ≤ (N : ℝ)*(∑ i, (
      hierarchyMomentLevel (a+(N+d)) m (affineLogPartition (fun _ => 0) U)
        (fun z => (hierarchySpinMean (a+(N+d)) m U (fun s => v s i) ⟨a+N,by omega⟩ z)^2) ⟨a,by omega⟩ z-
      (hierarchySpinMean (a+(N+d)) m U (fun s => v s i) ⟨a,by omega⟩ z)^2))+
      (N : ℝ)/(scale^2*p^2) := by
  obtain ⟨w,rfl⟩ := (parameterBlocks a N d).surjective z
  let L := fun s => (U s).comp (parameterBlocks a N d).toContinuousLinearMap
  let mf := fun i : Fin d => m ⟨a+N+i,by omega⟩
  let F := cascadePressure d mf (affineLogPartition (fun _ => 0) L)
  let P := cascadeSpinWeight d mf (fun _ => 0) L
  let x := cascadeRoot (E := ParameterSpace a) N
    (cascadeRoot (E := CascadeSpace (ParameterSpace a) N) d w)
  have he : (fun i : Fin N => m ⟨a+i,by omega⟩) = fun _ => p := funext hb
  have hW : hierarchySpinWeight (a+(N+d)) m U ⟨a,by omega⟩ (parameterBlocks a N d w) =
      fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x := by
    funext s
    unfold hierarchySpinWeight
    rw [hierarchyMomentLevel_before_block,he]
    rfl
  have hX (i : Fin N) := hierarchySpinMean_before_block a N d m U (fun s => v s i) w
  have hY (i : Fin N) := hierarchyMeanSquare_before_block a N d m U (fun s => v s i) w
  simp only [he] at hX hY
  have H := cascadeBlock_trace N d mf (fun _ => 0) L p scale hp ha hl hm hmu hmono v hvb hv x
  dsimp only at H ⊢
  rw [hW]
  simpa only [hX,hY,finiteMean_apply] using H
end HierarchyBlockTrace
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

end Probability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_CovarianceRegular
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
section CovarianceRegular
variable {S I : Type} [Fintype S]

theorem finiteCovariance_abs_le_two (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) (i j : I) :
    |finiteCovariance p v i j| ≤ 2 := by
  have hfirst : |∑ s, p s*v s i*v s j| ≤ 1 := by
    calc
      _ ≤ ∑ s, |p s*v s i*v s j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, p s := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul,abs_mul,abs_of_nonneg (hp s)]
        calc
          _ ≤ (p s*1)*1 := mul_le_mul (mul_le_mul_of_nonneg_left (hv s i) (hp s)) (hv s j)
            (abs_nonneg _) (by simpa using hp s)
          _ = p s := by ring
      _ = 1 := hs
  have hm := mul_le_mul (finiteMean_abs_le_one p v hp hs hv i)
    (finiteMean_abs_le_one p v hp hs hv j) (abs_nonneg (finiteMean p v j)) (by norm_num : (0 : ℝ) ≤ 1)
  rw [finiteCovariance_apply]
  calc
    _ ≤ |∑ s, p s*v s i*v s j|+|finiteMean p v i*finiteMean p v j| := abs_sub _ _
    _ ≤ 2 := by rw [abs_mul]; linarith

variable [Fintype I]

theorem matrix_trace_square_norm_bound (C : Matrix I I ℝ) (hC : ∀ i j, |C i j| ≤ 2) :
    ‖(C*C).trace‖ ≤ 4*(Fintype.card I : ℝ)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  calc
    _ ≤ ∑ i, ∑ j, ‖C i j*C j i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _ : I, ∑ _ : I, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      nlinarith [hC i j,hC j i,abs_nonneg (C i j),abs_nonneg (C j i)]
    _ = _ := by simp; ring

variable {Ω : Type} [TopologicalSpace Ω]

omit [Fintype I] in
theorem finiteMean_continuous (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (v : S → I → ℝ) (i : I) :
    Continuous (fun z => finiteMean (P z) v i) := by
  simp only [finiteMean_apply]
  exact continuous_finsetSum _ (fun s _ => (hP s).mul continuous_const)

omit [Fintype I] in
theorem finiteCovariance_continuous (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (v : S → I → ℝ) (i j : I) :
    Continuous (fun z => finiteCovariance (P z) v i j) := by
  simp only [finiteCovariance_apply]
  exact (continuous_finsetSum _ (fun s _ => ((hP s).mul continuous_const).mul continuous_const)).sub
    ((finiteMean_continuous P hP v i).mul (finiteMean_continuous P hP v j))

theorem traceSquare_continuous (C : Ω → Matrix I I ℝ) (hC : ∀ i j, Continuous (fun z => C z i j)) :
    Continuous (fun z => (C z*C z).trace) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => (hC i j).mul (hC j i)))
end CovarianceRegular

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyTraceRegular
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyTraceSquare_regular {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Continuous (hierarchyTraceSquare n m U v j) ∧
      ∀ z, ‖hierarchyTraceSquare n m U v j z‖ ≤ 4*(N : ℝ)^2 := by
  constructor
  · exact traceSquare_continuous _ (finiteCovariance_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) v)
  · intro z
    simpa only [hierarchyTraceSquare, Fintype.card_fin] using matrix_trace_square_norm_bound _
      (finiteCovariance_abs_le_two _ v (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z) hv)

theorem hierarchyTraceSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyTraceSquare n m U v j) (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) :=
  hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyTraceSquare_regular n m U v hv j).1 (hierarchyTraceSquare_regular n m U v hv j).2 x
end HierarchyTraceRegular

theorem hierarchyPathLaw_moment_integral (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x) =
      ∫ z, g z ∂hierarchyPathLaw n m f x := by
  have hr := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb j
  rw [← hierarchyAverage_eq_integral n m f hf _ hr.1 hC hr.2 x,
    ← hierarchyAverage_eq_integral n m f hf g hg hC hb x,hierarchyAverage_momentLevel]
  exact hf
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyTraceIntegral
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
section TraceIntegral
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyBlock_trace_integral (a N d : ℕ) (hN : 0 < N)
    (m : Fin (a+(N+d)) → ℝ) (U : S → ParameterSpace (a+(N+d)) →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin d, p ≤ m ⟨a+N+i,by omega⟩)
    (hmu : ∀ i : Fin d, m ⟨a+N+i,by omega⟩ ≤ 1)
    (hmono : Monotone (fun i : Fin d => m ⟨a+N+i,by omega⟩))
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, U s (parameterBlocks a N d (cascadeLift d
      (parameterNoise (E := ParameterSpace a) N (coordinateAxis N i)))) = scale*v s i) :
    (∫ z, hierarchyTraceSquare (a+(N+d)) m U v ⟨a,by omega⟩ z
      ∂hierarchyPathLaw (a+(N+d)) m (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap (a+(N+d)) m U (fun i s => v s i) ⟨a+N,by omega⟩-
      hierarchyMeanOverlap (a+(N+d)) m U (fun i s => v s i) ⟨a,by omega⟩+
      1/((N : ℝ)*scale^2*p^2) := by
  let n := a+(N+d)
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  let μ := hierarchyPathLaw n m f 0
  let := hierarchyPathLaw_probability n m f hf 0
  let j : Fin (n+1) := ⟨a,by dsimp [n]; omega⟩
  let l : Fin (n+1) := ⟨a+N,by dsimp [n]; omega⟩
  let M := fun (i : Fin N) (q : Fin (n+1)) => hierarchySpinMean n m U (fun s => v s i) q
  have hr (i : Fin N) (q : Fin (n+1)) : Continuous (M i q) ∧ ∀ z, ‖M i q z‖ ≤ 1 :=
    hierarchySpinMean_regular n m U (fun s => v s i) (by norm_num)
      (fun s => by simpa only [Real.norm_eq_abs] using hvb s i) q
  have hsq (i : Fin N) (q : Fin (n+1)) : ∀ z, ‖(M i q z)^2‖ ≤ 1 := by
    intro z
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ((hr i q).2 z)
  have hI (i : Fin N) (q : Fin (n+1)) : Integrable (fun z => (M i q z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf ((hr i q).1.pow 2) (hsq i q) 0
  let T := fun (i : Fin N) => hierarchyMomentLevel n m f (fun z => (M i l z)^2) j
  have hT (i : Fin N) : Integrable (T i) μ := by
    have h := hierarchyMomentLevel_bounded_continuous n m f (fun z => (M i l z)^2)
      hf ((hr i l).1.pow 2) (by norm_num : (0 : ℝ) ≤ 1) (hsq i l) j
    exact hierarchyPathLaw_integrable n m f _ hf h.1 h.2 0
  have hTI (i : Fin N) : (∫ z, T i z ∂μ) = ∫ z, (M i l z)^2 ∂μ :=
    hierarchyPathLaw_moment_integral n m f _ hf ((hr i l).1.pow 2) (by norm_num) (hsq i l) j 0
  have hpoint (z : ParameterSpace n) : hierarchyTraceSquare n m U v j z ≤
      (N : ℝ)*(∑ i, (T i z-(M i j z)^2))+(N : ℝ)/(scale^2*p^2) :=
    hierarchyBlock_conditional_trace a N d m U p scale hp ha hl hb hm hmu hmono v hvb hv z
  have hsum : Integrable (fun z => ∑ i : Fin N, (T i z-(M i j z)^2)) μ :=
    integrable_finsetSum _ (fun i _ => (hT i).sub (hI i j))
  have hint := integral_mono (hierarchyTraceSquare_integrable n m U v hvb j 0)
    (((integrable_finsetSum _ (fun i _ => (hT i).sub (hI i j))).const_mul (N : ℝ)).add
      (integrable_const ((N : ℝ)/(scale^2*p^2)))) hpoint
  have hexp (q : Fin (n+1)) :
      (∑ i, ∫ z, (M i q z)^2 ∂μ) = (N : ℝ)*hierarchyMeanOverlap n m U (fun i s => v s i) q := by
    unfold hierarchyMeanOverlap hierarchyMeanSquare normalizedSquare
    rw [integral_div,integral_finsetSum _ (fun i _ => hI i q)]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  change (∫ z, hierarchyTraceSquare n m U v j z ∂μ) ≤
    ∫ z, (N : ℝ)*(∑ i : Fin N, (T i z-(M i j z)^2))+(N : ℝ)/(scale^2*p^2) ∂μ at hint
  rw [integral_add (hsum.const_mul (N : ℝ))
    (integrable_const ((N : ℝ)/(scale^2*p^2))),integral_const_mul,
    integral_finsetSum (f := fun i z => T i z-(M i j z)^2) Finset.univ (fun i _ => (hT i).sub (hI i j))] at hint
  simp only [integral_sub (hT _) (hI _ j),hTI,Finset.sum_sub_distrib,hexp] at hint
  have hc : (∫ _ : ParameterSpace n, (N : ℝ)/(scale^2*p^2) ∂μ) = (N : ℝ)/(scale^2*p^2) := by simp
  rw [hc] at hint
  change (∫ z, hierarchyTraceSquare n m U v j z ∂μ)/(N : ℝ)^2 ≤ _
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    _ ≤ (N : ℝ)*(↑N*hierarchyMeanOverlap n m U (fun i s => v s i) l-
      ↑N*hierarchyMeanOverlap n m U (fun i s => v s i) j)+↑N/(scale^2*p^2) := hint
    _ = _ := by field_simp [ne_of_gt hn,ne_of_gt ha,ne_of_gt hp]; ring
end TraceIntegral
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchySegmentTrace
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
section SegmentTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySegment_trace_integral (n a N : ℕ) (haN : a+N ≤ n) (hN : 0 < N)
    (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin n, a+N ≤ i.val → p ≤ m i)
    (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s (i : Fin N), U s (coordinateAxis n ⟨a+i,by omega⟩) = scale*v s i) :
    (∫ z, hierarchyTraceSquare n m U v ⟨a,by omega⟩ z
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap n m U (fun i s => v s i) ⟨a+N,by omega⟩-
      hierarchyMeanOverlap n m U (fun i s => v s i) ⟨a,by omega⟩+
      1/((N : ℝ)*scale^2*p^2) := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le haN
  rw [Nat.add_assoc] at hd
  subst n
  apply hierarchyBlock_trace_integral a N d hN m U p scale hp ha hl hb
    (fun i => hm ⟨a+N+i,by omega⟩ (by simp))
    (fun i => hmu ⟨a+N+i,by omega⟩)
    (fun i j hij => hmono (by change a+N+i.val ≤ a+N+j.val; omega)) v hvb
  intro s i
  rw [parameterBlocks_noise_axis]
  exact hv s i
end SegmentTrace
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockTrace
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
section BlockTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem equalBlock_trace_integral (D N k : ℕ) (hN : 0 < N)
    (U : S → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (scale : Fin (k+1) → ℝ) (ha : ∀ b, 0 < scale b)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s b i, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = scale b*v s i)
    (j : Fin k) :
    (∫ z, hierarchyTraceSquare (blockDimension D N k) (blockMass D N k) U v (blockLevel D N k j.castSucc) z
      ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => v s i) (blockLevel D N k j.succ)-
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => v s i) (blockLevel D N k j.castSucc)+
      1/((N : ℝ)*(scale j.succ)^2*(((j.val+1 : ℕ) : ℝ)/((k+1 : ℕ) : ℝ))^2) := by
  let n := blockDimension D N k
  let a := D+(j.val+1)*N
  let p : ℝ := ((j.val+1 : ℕ) : ℝ)/((k+1 : ℕ) : ℝ)
  have hseg : a+N ≤ n := by
    dsimp [a,n,blockDimension]
    have h : (j.val+2)*N ≤ (k+1)*N := Nat.mul_le_mul_right N (by omega)
    nlinarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : (0 : ℝ) < ((k+1 : ℕ) : ℝ))).2
    exact_mod_cast (show j.val+1 ≤ k+1 by omega)
  have hb (i : Fin N) : blockMass D N k ⟨a+i,by omega⟩ = p := by
    simpa only [p,a,fieldIndex,Fin.val_succ] using blockMass_at_field D N k j.succ i
  have hm (i : Fin n) (hi : a+N ≤ i.val) : p ≤ blockMass D N k i := by
    rw [← hb ⟨0,hN⟩]
    exact (blockMass_valid D N k).2.2 (by change a+0 ≤ i.val; omega)
  have HV (s : S) (i : Fin N) : U s (coordinateAxis n ⟨a+i,by omega⟩) = scale j.succ*v s i :=
    hv s j.succ i
  have H := hierarchySegment_trace_integral n a N hseg hN (blockMass D N k) U p (scale j.succ)
    hp (ha j.succ) hp1 hb hm (blockMass_valid D N k).2.1 (blockMass_valid D N k).2.2 v hvb HV
  have he : (⟨a+N,by omega⟩ : Fin (n+1)) = blockLevel D N k j.succ := by
    apply Fin.ext
    simp only [blockLevel_val,Fin.val_succ,a]
    ring
  rw [he] at H
  exact H
end BlockTrace
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageTrace
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
section AverageTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem equalBlock_average_trace_oai (D N k : ℕ) (hN : 0 < N)
    (U : S → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s b i, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = Real.sqrt (Δ b)*v s i) :
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹ *
      ((∫ z, hierarchyTraceSquare (blockDimension D N k) (blockMass D N k) U v (blockLevel D N k j.castSucc) z
      ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2)) ≤
      1/((k+1 : ℕ) : ℝ)+2*((k+1 : ℕ) : ℝ)/((N : ℝ)*δ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  let A : ℝ := K^2/((N : ℝ)*δ)
  let r : Fin (k+1) → ℝ := fun j => hierarchyMeanOverlap n m U (fun i s => v s i) (blockLevel D N k j)
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hvb s i
  have hr0 : 0 ≤ r 0 := (hierarchyMeanOverlap_bounds n m U (fun i s => v s i) hc _).1
  have hr1 : r (Fin.last k) ≤ 1 := (hierarchyMeanOverlap_bounds n m U (fun i s => v s i) hc _).2
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpos b : 0 < Δ b := hδ.trans_le (hΔ b)
  have he (j : Fin k) : 1/((N : ℝ)*(Real.sqrt (Δ j.succ))^2*
      (((j.val+1 : ℕ) : ℝ)/K)^2) ≤ A*(1/((j.val+1 : ℕ) : ℝ)^2) := by
    rw [Real.sq_sqrt (hpos j.succ).le]
    have hJ : (0 : ℝ) < ((j.val+1 : ℕ) : ℝ) := by positivity
    calc
      _ ≤ 1/((N : ℝ)*δ*(((j.val+1 : ℕ) : ℝ)/K)^2) :=
        one_div_le_one_div_of_le (by positivity) (by gcongr; exact hΔ j.succ)
      _ = _ := by dsimp [A]; field_simp
  have H (j : Fin k) := (equalBlock_trace_integral D N k hN U (fun b => Real.sqrt (Δ b))
    (fun b => Real.sqrt_pos.2 (hpos b)) v hvb hv j).trans (add_le_add le_rfl (he j))
  have HS := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left (H j) (inv_nonneg.2 hK.le))
  change (∑ j : Fin k, K⁻¹*_) ≤ _
  apply HS.trans
  change (∑ j : Fin k, K⁻¹*(r j.succ-r j.castSucc+A*(1/((j.val+1 : ℕ) : ℝ)^2))) ≤ _
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have ht : (∑ j : Fin k, (r j.succ-r j.castSucc)) = r (Fin.last k)-r 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_succ r
    have h2 := Fin.sum_univ_castSucc r
    linarith
  rw [ht]
  have hb := mul_le_mul_of_nonneg_left (sum_nat_reciprocal_squares k) hA
  have hl : r (Fin.last k)-r 0+A*(∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 1+2*A := by linarith
  calc
    _ ≤ K⁻¹*(1+2*A) := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hK.le)
    _ = _ := by dsimp [A,K]; field_simp
end AverageTrace
end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.equalBlock_average_trace_oai := @OAI.SK.Analytic.equalBlock_average_trace_oai
