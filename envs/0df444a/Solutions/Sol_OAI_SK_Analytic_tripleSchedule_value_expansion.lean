-- Prove2me | solution 1 for OAI.SK.Analytic.tripleSchedule_value_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:21:10.225899+00:00
-- url     : https://prove2.me/submissions/46b1941f-9eef-429f-ae64-8c302c34e31a

import Mathlib
import Definitions.Def_OAIQ036S005
import Definitions.Def_OAIQ036S006

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_C1Taylor
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

theorem lipschitz_derivative_taylor {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {L : ℝ≥0} (hL : LipschitzWith L df)
    (x y : ℝ) : |f (x+y)-f x-df x*y| ≤ (L:ℝ)*y^2 := by
  let F : ℝ → ℝ := fun t => f (x+t*y)-df x*(t*y)
  have hD (t : ℝ) : HasDerivAt F ((df (x+t*y)-df x)*y) t := by
    convert ((hd (x+t*y)).comp t (((hasDerivAt_id t).mul_const y).const_add x)).sub
      (((hasDerivAt_id t).mul_const y).const_mul (df x)) using 1 <;> first | rfl | ring
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt) (C:=(L:ℝ)*y^2) (by
      intro t ht
      rw [Real.norm_eq_abs,abs_mul]
      have HL := hL.dist_le_mul (x+t*y) x
      simp only [Real.dist_eq,add_sub_cancel_left,abs_mul] at HL
      calc
        _ ≤ ((L:ℝ)*(|t| *|y|))*|y| := mul_le_mul_of_nonneg_right HL (abs_nonneg _)
        _ ≤ ((L:ℝ)*(1*|y|))*|y| := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by rw [abs_of_nonneg ht.1]; exact ht.2.le) (abs_nonneg _)) L.coe_nonneg) (abs_nonneg _)
        _ = _ := by rw [one_mul,mul_assoc,← pow_two,sq_abs])
  have heq : F 1-F 0=f (x+y)-f x-df x*y := by dsimp [F]; ring_nf
  rw [heq,Real.norm_eq_abs] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ExpExpansion
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

theorem exp_quadratic_remainder (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp |x| := by
  have H := Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) 2
  norm_num [Finset.sum_range_succ,← Complex.ofReal_exp,← Complex.ofReal_add,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs] at H
  have he : (↑(Real.exp x)-(1+(x:ℂ)))=((Real.exp x-(1+x):ℝ):ℂ) := by push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs] at H
  have HL := le_abs_self (Real.exp x-(1+x))
  linarith

theorem fourth_pow_le_exp_square {c : ℝ} (hc : 0 < c) (y : ℝ) :
    y^4 ≤ 2/c^2*Real.exp (c*y^2) := by
  have H := Real.pow_div_factorial_le_exp (c*y^2) (mul_nonneg hc.le (sq_nonneg y)) 2
  norm_num at H
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    y^4*c^2 ≤ 2*Real.exp (c*y^2) := by nlinarith
    _ = (2*Real.exp (c*y^2)) := rfl

theorem log_integral_exp_quadratic_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y Δ : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (hΔ : Integrable Δ μ)
    {c δ M : ℝ} (hc : 0 < c) (hδ : 4*δ^2 ≤ c)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ)
    (hM : (∫ z, Real.exp (c*(Y z)^2) ∂μ) ≤ M)
    (hb : ∀ᵐ z ∂μ, |Δ z| ≤ 2*δ^2*(Y z)^2) :
    Real.log (∫ z, Real.exp (Δ z) ∂μ) ≤ (∫ z, Δ z ∂μ)+
      (32/c^2)*δ^4*M := by
  have hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ :=
    ⟨Real.continuous_exp.comp_aestronglyMeasurable ((hY.pow 2).const_mul c),
      hE.hasFiniteIntegral⟩
  have hη : ∀ z, 2*δ^2*(Y z)^2 ≤ c/2*(Y z)^2 := by
    intro z
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hdom : ∀ᵐ z ∂μ, Real.exp (Δ z) ≤ Real.exp (c*(Y z)^2) := by
    filter_upwards [hb] with z hz
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (hz.trans (by
      have H := hη z
      nlinarith [mul_nonneg hc.le (sq_nonneg (Y z))]))
  have hi : Integrable (fun z => Real.exp (Δ z)) μ :=
    hE.mono' (Real.continuous_exp.comp_aestronglyMeasurable hΔ.aestronglyMeasurable) (by
      filter_upwards [hdom] with z hz
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hz)
  have hpos : 0 < (∫ z, Real.exp (Δ z) ∂μ) := integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun z => (Real.exp_pos (Δ z)).le)) hi |>.mpr (by simp [Function.support,Real.exp_ne_zero])
  have hr : ∀ᵐ z ∂μ, Real.exp (Δ z) ≤ 1+Δ z+
      (32/c^2)*δ^4*Real.exp (c*(Y z)^2) := by
    filter_upwards [hb] with z hz
    apply (exp_quadratic_remainder (Δ z)).trans
    apply add_le_add_right
    have hsq : (Δ z)^2 ≤ 4*δ^4*(Y z)^4 := by
      have H := pow_le_pow_left₀ (abs_nonneg (Δ z)) hz 2
      rw [sq_abs] at H
      nlinarith [H]
    have hp := fourth_pow_le_exp_square (half_pos hc) (Y z)
    have hexp : Real.exp |Δ z| ≤ Real.exp (c/2*(Y z)^2) :=
      Real.exp_le_exp.mpr (hz.trans (hη z))
    calc
      _ ≤ (4*δ^4*(Y z)^4)*Real.exp (c/2*(Y z)^2) :=
        mul_le_mul hsq hexp (Real.exp_nonneg _) (by positivity)
      _ ≤ (4*δ^4*(2/(c/2)^2*Real.exp (c/2*(Y z)^2)))*Real.exp (c/2*(Y z)^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_nonneg _)
      _ = (4*δ^4*(2/(c/2)^2))*(Real.exp (c/2*(Y z)^2)*Real.exp (c/2*(Y z)^2)) := by ring
      _ = _ := by
        rw [← Real.exp_add,show c/2*(Y z)^2+c/2*(Y z)^2=c*(Y z)^2 by ring]
        congr 1
        field_simp
        ring
  have H := integral_mono_ae hi ((integrable_const (1:ℝ)).add hΔ |>.add (hE.const_mul ((32/c^2)*δ^4))) hr
  simp only [Pi.add_apply] at H
  have Hsum := integral_add ((integrable_const (1:ℝ)).add hΔ) (hE.const_mul ((32/c^2)*δ^4))
  have Hsum2 := integral_add (integrable_const (1:ℝ)) hΔ
  simp only [Pi.add_apply] at Hsum Hsum2
  rw [Hsum,Hsum2,integral_const_mul] at H
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have HM := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (32/c^2)*δ^4)
  have HL := Real.log_le_sub_one_of_pos hpos
  linarith

end SK.Analytic

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

theorem exp_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E) :
    Real.exp (m*gaussianStep m f x)=∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1 := by
  by_cases hm : m=0
  · simp [hm]
  · rw [gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
    rw [mul_div_cancel₀ _ hm,Real.exp_log (integral_exp_pos (hf.exp_integrable m x))]

theorem gaussianAverage_exp_increment {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (m : ℝ) (x : E) :
    gaussianAverage m f (fun z => Real.exp (m*(g z-f z))) x=
      Real.exp (m*(gaussianStep m g x-gaussianStep m f x)) := by
  rw [gaussianAverage_exp_representation hf]
  simp only [smul_eq_mul]
  have he (y : ℝ) : Real.exp (m*f (x,y))*Real.exp (m*(g (x,y)-f (x,y)))=
      Real.exp (m*g (x,y)) := by rw [← Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [← exp_gaussianStep hg m x,← Real.exp_add]
  congr 1
  ring

theorem gaussianStep_increment_sandwich {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {m : ℝ} (hm : m∈Icc (0:ℝ) 1) (x : E) :
    gaussianAverage m f (fun z => g z-f z) x ≤ gaussianStep m g x-gaussianStep m f x ∧
    Real.exp (gaussianStep m g x-gaussianStep m f x) ≤
      gaussianAverage m f (fun z => Real.exp (g z-f z)) x := by
  let ν := gaussianStepLaw m f x
  let U := fun z => g z-f z
  have hU : BoundedDerivs U := by simpa only [neg_one_mul, ← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
  let := gaussianStepLaw_probability hf m x
  have hi : Integrable (fun y => U (x,y)) ν :=
    hU.hasExpGrowth.integrable_gaussianStepLaw hf hU.1.continuous m x
  have hiE (a : ℝ) : Integrable (fun y => Real.exp (a*U (x,y))) ν :=
    ((hU.exp_growths a).1).integrable_gaussianStepLaw hf
      (Real.continuous_exp.comp (continuous_const.mul hU.1.continuous)) m x
  have hi1 : Integrable (fun y => Real.exp (U (x,y))) ν := by simpa only [one_mul] using hiE 1
  have jensen (a : ℝ) : Real.exp (a*(∫ y, U (x,y) ∂ν)) ≤ ∫ y, Real.exp (a*U (x,y)) ∂ν := by
    have H := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall (fun _ => mem_univ _)) (hi.const_mul a) (hiE a)
    simpa only [integral_const_mul] using H
  by_cases hz : m=0
  · subst m
    have he : gaussianStep 0 g x-gaussianStep 0 f x=∫ y, U (x,y) ∂ν := by
      simp only [ν,gaussianStepLaw_zero,gaussianStep,ite_true]
      exact (integral_sub (hg.hasExpGrowth.integrable_gaussian_section hg.1.continuous x) (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)).symm
    rw [he]
    constructor
    · exact le_rfl
    · simpa only [one_mul, gaussianAverage, U, ν] using jensen 1
  · have hm0 : 0 < m := lt_of_le_of_ne hm.1 (Ne.symm hz)
    have hident : (∫ y, Real.exp (m*U (x,y)) ∂ν)=
        Real.exp (m*(gaussianStep m g x-gaussianStep m f x)) := gaussianAverage_exp_increment hf hg m x
    have hl := jensen m
    rw [hident,Real.exp_le_exp] at hl
    refine ⟨(mul_le_mul_iff_right₀ hm0).mp hl,?_⟩
    let J := ∫ y, Real.exp (U (x,y)) ∂ν
    have hJ : 0 < J := integral_exp_pos hi1
    have hp : (∫ y, Real.exp (m*U (x,y)) ∂ν) ≤ J^m := by
      have heq : (fun y => (Real.exp (U (x,y)))^m)=fun y => Real.exp (m*U (x,y)) := by
        funext y
        rw [← Real.exp_mul,mul_comm]
      have H := (Real.concaveOn_rpow hm.1 hm.2).le_map_integral
        (Real.continuous_rpow_const hm.1).continuousOn isClosed_Ici
        (Eventually.of_forall (fun y => (Real.exp_pos (U (x,y))).le)) hi1 (by
          change Integrable (fun y => (Real.exp (U (x,y)))^m) ν
          rw [heq]
          exact hiE m)
      simpa only [heq] using H
    rw [hident,Real.rpow_def_of_pos hJ,Real.exp_le_exp] at hp
    have hu : gaussianStep m g x-gaussianStep m f x ≤ Real.log J := by nlinarith
    have H := Real.exp_le_exp.mpr hu
    rw [Real.exp_log hJ] at H
    exact H
end

end SK.Analytic

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TiltedExponentialSquare
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

theorem tilted_linear_even_moment_bound (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) ≤
      (p.factorial:ℝ)*(4*(∑ i, (a i)^2)+B^2)^p := by
  let σ := ∑ i, (a i)^2
  have hσ : 0 ≤ σ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ 4*σ+B^2 := by positivity
  let := fiberGaussian_tilted_probability n V hV x
  induction p with
  | zero => simp
  | succ p ih =>
    have H := tilted_linear_even_moment_step n V hV x a hB hb p
    have hm : 0 ≤ 2*(2*p+1:ℕ)*σ+B^2 := by positivity
    have hp : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
    have hcoef : 2*(2*p+1:ℕ)*σ+B^2 ≤ (p+1:ℕ)*(4*σ+B^2) := by
      push_cast
      nlinarith [mul_nonneg hp (sq_nonneg B)]
    calc
      _ ≤ (2*(2*p+1:ℕ)*σ+B^2)*(∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) := by
        simpa only [Nat.mul_add,Nat.mul_one] using H
      _ ≤ (2*(2*p+1:ℕ)*σ+B^2)*((p.factorial:ℝ)*(4*σ+B^2)^p) := mul_le_mul_of_nonneg_left ih hm
      _ ≤ (p+1:ℕ)*(4*σ+B^2)*((p.factorial:ℝ)*(4*σ+B^2)^p) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]; ring

theorem tilted_linear_exp_square_bound (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B)
    {c : ℝ} (hc : 0 ≤ c) (hsmall : c*(4*(∑ i, (a i)^2)+B^2) ≤ 1/2) :
    Integrable (fun z => Real.exp (c*(coordinateLinear n a z)^2)) ((fiberGaussian n x).tilted V) ∧
    (∫ z, Real.exp (c*(coordinateLinear n a z)^2) ∂(fiberGaussian n x).tilted V) ≤ 2 := by
  let L := coordinateLinear n a
  let μ := (fiberGaussian n x).tilted V
  let C := 4*(∑ i, (a i)^2)+B^2
  let F (p : ℕ) := fun z => (c^p/(p.factorial:ℝ))*L z^(2*p)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hi (p) : Integrable (F p) μ :=
    (((HasExpGrowth.linear L).pow _).integrable_tilted_fiberGaussian n V hV (L.continuous.pow _) x).const_mul _
  have hFp (p) (z) : 0 ≤ F p z := by
    dsimp only [F]
    apply mul_nonneg (by positivity)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hnorm (p) : (∫ z, ‖F p z‖ ∂μ)=(∫ z, F p z ∂μ) := by
    apply integral_congr_ae; filter_upwards [] with z; exact Real.norm_of_nonneg (hFp p z)
  have hbound (p) : (∫ z, F p z ∂μ) ≤ (1/2:ℝ)^p := by
    rw [show F p=fun z => (c^p/(p.factorial:ℝ))*L z^(2*p) from rfl,integral_const_mul]
    have H := tilted_linear_even_moment_bound n V hV x a hB hb p
    calc
      _ ≤ (c^p/(p.factorial:ℝ))*((p.factorial:ℝ)*C^p) := mul_le_mul_of_nonneg_left H (by positivity)
      _ = (c*C)^p := by rw [mul_pow]; field_simp
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc hC) hsmall p
  have hsgeom : Summable (fun p : ℕ => (1/2:ℝ)^p) := summable_geometric_of_abs_lt_one (by norm_num)
  have hs : Summable (fun p => ∫ z, F p z ∂μ) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg (hFp p)) hbound hsgeom
  have hsN : Summable (fun p => ∫ z, ‖F p z‖ ∂μ) := by simpa only [hnorm] using hs
  have he (z) : (∑' p, F p z)=Real.exp (c*L z^2) := by
    rw [Real.exp_eq_exp_ℝ]
    convert (NormedSpace.expSeries_div_hasSum_exp (c*L z^2)).tsum_eq using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr
    intro p
    dsimp only [F]
    rw [mul_pow,pow_mul]
    ring
  have HE := integral_tsum_of_summable_integral_norm hi hsN
  simp_rw [he] at HE
  have h1 : 1 ≤ (∫ z, Real.exp (c*L z^2) ∂μ) := by
    rw [← HE]
    have H := hs.le_tsum 0 (fun p _ => integral_nonneg (hFp p))
    have hzero : (∫ z, F 0 z ∂μ)=1 := by
      let := fiberGaussian_tilted_probability n V hV x
      simp [F,μ]
    rwa [hzero] at H
  refine ⟨?_,?_⟩
  · by_contra hn
    rw [integral_undef hn] at h1
    norm_num at h1
  · change (∫ z, Real.exp (c*L z^2) ∂μ) ≤ 2
    rw [← HE]
    calc
      _ ≤ ∑' p : ℕ, (1/2:ℝ)^p := hs.tsum_le_tsum hbound hsgeom
      _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]; norm_num

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

theorem hierarchyAverage_mono_exp (n : ℕ) (m : Fin n → ℝ)
    {f g a : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (ha : Continuous a) (hgE : HasExpGrowth g) (haE : HasExpGrowth a)
    (hle : ∀ z, g z≤a z) (x : ℝ) : hierarchyAverage n m f g x≤hierarchyAverage n m f a x := by
  rw [hierarchyAverage_eq_integral_exp n m f hf g hg hgE x,
    hierarchyAverage_eq_integral_exp n m f hf a ha haE x]
  exact integral_mono (hgE.integrable_hierarchyPathLaw n m hf hg x)
    (haE.integrable_hierarchyPathLaw n m hf ha x) hle

theorem hierarchyPressure_increment_sandwich (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (x : ℝ) :
    hierarchyAverage n m f (fun z => g z-f z) x ≤
      hierarchyPressure n m g x-hierarchyPressure n m f x ∧
    Real.exp (hierarchyPressure n m g x-hierarchyPressure n m f x) ≤
      hierarchyAverage n m f (fun z => Real.exp (g z-f z)) x := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ n ih =>
    let p := m (Fin.last n)
    let F := gaussianStep p f
    let G := gaussianStep p g
    have hF : BoundedDerivs F := hf.gaussianStep p
    have hG : BoundedDerivs G := hg.gaussianStep p
    have hU : BoundedDerivs (fun z => g z-f z) := by
      simpa only [neg_one_mul,← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
    have hV : BoundedDerivs (fun z => G z-F z) := by
      simpa only [neg_one_mul,← sub_eq_add_neg] using hG.add (hF.const_mul (-1))
    have hUE : HasExpGrowth (fun z => Real.exp (g z-f z)) := by
      simpa only [one_mul] using (hU.exp_growths 1).1
    have hVE : HasExpGrowth (fun z => Real.exp (G z-F z)) := by
      simpa only [one_mul] using (hV.exp_growths 1).1
    have hUC : Continuous (fun z => Real.exp (g z-f z)) := Real.continuous_exp.comp hU.1.continuous
    have hVC : Continuous (fun z => Real.exp (G z-F z)) := Real.continuous_exp.comp hV.1.continuous
    have H := ih (fun i => m i.castSucc) (fun i => hm i.castSucc) hF hG
    constructor
    · refine (hierarchyAverage_mono_exp n (fun i => m i.castSucc) hF
        (gaussianAverage_continuous_of_expGrowth hf p hU.hasExpGrowth hU.1.continuous)
        hV.1.continuous (gaussianAverage_expGrowth hf p hU.hasExpGrowth) hV.hasExpGrowth
        (fun z => (gaussianStep_increment_sandwich hf hg (hm (Fin.last n)) z).1) x).trans H.1
    · refine H.2.trans (hierarchyAverage_mono_exp n (fun i => m i.castSucc) hF
        hVC (gaussianAverage_continuous_of_expGrowth hf p hUE hUC)
        hVE (gaussianAverage_expGrowth hf p hUE)
        (fun z => (gaussianStep_increment_sandwich hf hg (hm (Fin.last n)) z).2) x)

theorem hierarchyPressure_increment_integral_sandwich (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (x : ℝ) :
    (∫ z, g z-f z ∂hierarchyPathLaw n m f x) ≤
      hierarchyPressure n m g x-hierarchyPressure n m f x ∧
    hierarchyPressure n m g x-hierarchyPressure n m f x ≤
      Real.log (∫ z, Real.exp (g z-f z) ∂hierarchyPathLaw n m f x) := by
  have hU : BoundedDerivs (fun z => g z-f z) := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
  have hUE : HasExpGrowth (fun z => Real.exp (g z-f z)) := by
    simpa only [one_mul] using (hU.exp_growths 1).1
  have H := hierarchyPressure_increment_sandwich n m hm hf hg x
  rw [hierarchyAverage_eq_integral_exp n m f hf _ hU.1.continuous hU.hasExpGrowth x,
    hierarchyAverage_eq_integral_exp n m f hf (fun z => Real.exp (g z-f z)) (Real.continuous_exp.comp hU.1.continuous) hUE x] at H
  refine ⟨H.1,?_⟩
  have hi := hUE.integrable_hierarchyPathLaw n m hf (Real.continuous_exp.comp hU.1.continuous) x
  let := hierarchyPathLaw_probability n m f hf x
  have hp := integral_exp_pos hi
  exact (Real.le_log_iff_exp_le hp).mpr H.2

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

theorem hierarchy_exp_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c*(4*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2) ≤ 1/2) :
    Integrable (fun z => Real.exp (c*(coordinateLinear n a z)^2)) (hierarchyPathLaw n m f x) ∧
    (∫ z, Real.exp (c*(coordinateLinear n a z)^2) ∂hierarchyPathLaw n m f x) ≤ 2 := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  exact tilted_linear_exp_square_bound n _ (hierarchyPathLogDensity_regular n m hf) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (hierarchy_score_direction_bound n m hm hmono f hf C hC hF a) hc hsmall

end SK.Analytic

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorHierarchy
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
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hierarchyPressure_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f : E → ℝ) (c : ℝ → E) :
    hierarchyPressure n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchy n m v f (c x) := by
  induction n generalizing f with
  | zero => simp [hierarchyPressure,vectorHierarchy,parameter]
  | succ n ih =>
    have he : (fun z : ParameterSpace (n+1) =>
        f (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => f ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he,hierarchyPressure]
    change hierarchyPressure n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

end Vector

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

theorem vectorHierarchyAverage_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f g : F → ℝ) :
    vectorHierarchyAverage n m v (f ∘ L) (g ∘ L)=vectorHierarchyAverage n m (L ∘ v) f g ∘ L := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchyAverage,vectorStep_pullback,vectorStepAverage_pullback,ih]
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

theorem vectorHierarchy_div_scale (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (c : ℝ) (hc : c≠0) (f : E → ℝ) :
    vectorHierarchy n (fun i => m i/c) v (fun x => c*f x)=fun x => c*vectorHierarchy n m v f x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [vectorHierarchy,vectorStep_div_scale _ c hc,ih]; rfl

theorem vectorHierarchyAverage_div_scale (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (c : ℝ) (hc : c≠0) (f g : E → ℝ) :
    vectorHierarchyAverage n (fun i => m i/c) v (fun x => c*f x) g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchyAverage,vectorStep_div_scale _ c hc,vectorStepAverage_div_scale _ c hc,ih]
    rfl
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

theorem commonBranch_value (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) :
    vectorHierarchy n (fun i => m i/3) (fun i => ((v i,0),v i))
      (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ((x,0),x)=3*scalarHierarchy n m v f x := by
  have H := congrFun (vectorHierarchy_pullback commonBranchEmbedding n (fun i => m i/3) v
    (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2)) x
  have he : (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ∘ commonBranchEmbedding=fun x => 3*f x := by
    funext x; simp only [Function.comp_apply,commonBranchEmbedding_apply]; ring
  rw [he,vectorHierarchy_div_scale n m v 3 (by norm_num),vectorHierarchy_real] at H
  exact H.symm

theorem commonBranch_average (n : ℕ) (m v : Fin n → ℝ) (f b : ℝ → ℝ) (a : ℝ × ℝ → ℝ) (x : ℝ) :
    vectorHierarchyAverage n (fun i => m i/3) (fun i => ((v i,0),v i))
      (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2)
      (fun p => a p.1*b p.2) ((x,0),x)=scalarHierarchyAverage n m v f (fun y => a (y,0)*b y) x := by
  have H := congrFun (vectorHierarchyAverage_pullback commonBranchEmbedding n (fun i => m i/3) v
    (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) (fun p => a p.1*b p.2)) x
  have he : (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ∘ commonBranchEmbedding=fun x => 3*f x := by
    funext x; simp only [Function.comp_apply,commonBranchEmbedding_apply]; ring
  rw [he,vectorHierarchyAverage_div_scale n m v 3 (by norm_num),vectorHierarchyAverage_real] at H
  exact H.symm

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

theorem vectorStep_add_frozen {f : E → ℝ} (hf : BoundedDerivs f)
    (g : E → ℝ) (m : ℝ) (v : E) (hg : ∀ x (t : ℝ), g (x+t • v)=g x) :
    vectorStep m v (fun x => f x+g x)=fun x => vectorStep m v f x+g x := by
  let T : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ+
    (ContinuousLinearMap.snd ℝ E ℝ).smulRight v
  have H := gaussianStep_add_prefix (hf.compCLM T) g m
  simpa only [vectorStep,hg,Function.comp_def,T,add_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd'] using H

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

theorem tripleStep_coordinate {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : (Fin 3 → ℝ) → ℝ)
    (m : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) (hg : ∀ x (t : ℝ),g (x+t • v)=g x) :
    vectorStep m v (fun x => f (x i)+g x)=fun x => scalarStep m (v i) f (x i)+g x := by
  have H := vectorStep_add_frozen (hf.compCLM (tripleCoordinate i)) g m v hg
  change vectorStep m v (fun x => (f ∘ tripleCoordinate i) x+g x)=
    (fun x => vectorStep m v (f ∘ tripleCoordinate i) x+g x) at H
  rw [vectorStep_pullback,vectorStep_real] at H
  exact H

theorem tripleStep_axis0 {f g h : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    vectorStep m ![v,0,0] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarStep m v f (x 0)+g (x 1)+h (x 2) := by
  have H := tripleStep_coordinate hf (fun x => g (x 1)+h (x 2)) m ![v,0,0] 0
    (by intro x t; simp)
  simpa only [Matrix.cons_val_zero,add_assoc] using H

theorem tripleStep_axis1 {f g h : ℝ → ℝ} (hg : BoundedDerivs g) (m v : ℝ) :
    vectorStep m ![0,v,0] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => f (x 0)+scalarStep m v g (x 1)+h (x 2) := by
  have H := tripleStep_coordinate hg (fun x => f (x 0)+h (x 2)) m ![0,v,0] 1
    (by intro x t; simp)
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,add_comm,add_left_comm,add_assoc] using H

theorem tripleStep_axis2 {f g h : ℝ → ℝ} (hh : BoundedDerivs h) (m v : ℝ) :
    vectorStep m ![0,0,v] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => f (x 0)+g (x 1)+scalarStep m v h (x 2) := by
  have H := tripleStep_coordinate hh (fun x => f (x 0)+g (x 1)) m ![0,0,v] 2
    (by intro x t; simp)
  simpa [add_comm,add_left_comm,add_assoc] using H

theorem tripleTailBlock_value {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedDerivs g) (hh : BoundedDerivs h) (p : ℝ × ℝ) :
    vectorIncrementChain (tripleTailBlock p) (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarStep p.1 p.2 f (x 0)+scalarStep p.1 p.2 g (x 1)+scalarStep p.1 p.2 h (x 2) := by
  simp only [tripleTailBlock,vectorIncrementChain,tripleStep_axis2 hh,tripleStep_axis1 hg,tripleStep_axis0 hf]

theorem tripleTailSchedule_value {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedDerivs g) (hh : BoundedDerivs h) (l : List (ℝ × ℝ)) :
    vectorIncrementChain (tripleTailSchedule l) (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarIncrementChain l f (x 0)+scalarIncrementChain l g (x 1)+scalarIncrementChain l h (x 2) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [tripleTailSchedule,List.flatMap_cons,vectorIncrementChain_append]
    simp only [tripleTailSchedule] at ih
    rw [ih,tripleTailBlock_value (scalarIncrementChain_regular l hf)
      (scalarIncrementChain_regular l hg) (scalarIncrementChain_regular l hh)]
    rfl

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

theorem scalarIncrementChain_ofFn (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) :
    scalarIncrementChain (List.ofFn (fun i => (m i,v i))) f=scalarHierarchy n m v f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_ofFn,vectorHierarchy_real]

theorem scalarIncrementAverage_ofFn (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=scalarHierarchyAverage n m v f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_ofFn,vectorHierarchyAverage_real]

theorem scalarIncrementChain_get (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain l f=scalarHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_get,vectorHierarchy_real]

theorem scalarIncrementChain_append (l r : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain (l++r) f=scalarIncrementChain l (scalarIncrementChain r f) := by
  simp only [← vectorIncrementChain_real,vectorIncrementChain_append]

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

theorem mergedProductBranches_monotone (l : List (ℝ × E)) (r : List (ℝ × F))
    (hl : l.Pairwise (fun p q => p.1 ≤ q.1))
    (hr : r.Pairwise (fun p q => p.1 ≤ q.1)) :
    (mergedProductBranches l r).Pairwise (fun p q => productMass p ≤ productMass q) := by
  unfold mergedProductBranches
  have hl' : (l.map (Sum.inl : (ℝ × E) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by simpa [List.pairwise_map,productMass] using hl
  have hr' : (r.map (Sum.inr : (ℝ × F) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by
    rw [List.pairwise_map]
    exact hr.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  have ht : ∀ a b c : (ProductIncrement (E:=E) (F:=F)),
      decide (productMass a ≤ productMass b) = true →
      decide (productMass b ≤ productMass c) = true →
      decide (productMass a ≤ productMass c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htot : ∀ a b : (ProductIncrement (E:=E) (F:=F)),
      (decide (productMass a ≤ productMass b) || decide (productMass b ≤ productMass a)) = true := by
    intro a b
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  simpa only [decide_eq_true_eq] using List.pairwise_merge ht htot
    _ _ (by simpa only [decide_eq_true_eq] using hl') (by simpa only [decide_eq_true_eq] using hr')

end Vector
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSymmetricTaylor
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

theorem lipschitz_second_derivative_taylor {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    {L : ℝ≥0} (hL : LipschitzWith L ddf) (x y : ℝ) :
    |f (x+y)-f x-df x*y-ddf x*y^2/2| ≤ (L:ℝ)*|y|^3 := by
  let F : ℝ → ℝ := fun t => f (x+t*y)-df x*(t*y)-ddf x*(t*y)^2/2
  have hD (t : ℝ) : HasDerivAt F ((df (x+t*y)-df x-ddf x*(t*y))*y) t := by
    convert (((hd (x+t*y)).comp t (((hasDerivAt_id t).mul_const y).const_add x)).sub
      (((hasDerivAt_id t).mul_const y).const_mul (df x))).sub
      (((((hasDerivAt_id t).mul_const y).pow 2).const_mul (ddf x)).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt) (C:=(L:ℝ)*|y|^3) (by
      intro t ht
      rw [Real.norm_eq_abs,abs_mul]
      have HT := lipschitz_derivative_taylor hdd hL x (t*y)
      have htsq : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      calc
        _ ≤ ((L:ℝ)*(t*y)^2)*|y| := mul_le_mul_of_nonneg_right HT (abs_nonneg _)
        _ ≤ ((L:ℝ)*y^2)*|y| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
          nlinarith [sq_nonneg y,mul_le_mul_of_nonneg_right htsq (sq_nonneg y)]
        _ = _ := by rw [← sq_abs y]; ring)
  have he : F 1-F 0=f (x+y)-f x-df x*y-ddf x*y^2/2 := by dsimp [F]; ring_nf
  rw [he,Real.norm_eq_abs] at H
  exact H

theorem symmetricIncrement_quad_bound {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {K : ℝ≥0} (hK : LipschitzWith K df) (z h : ℝ) :
    |symmetricIncrement f z h| ≤ 2*(K:ℝ)*h^2 := by
  have hp := lipschitz_derivative_taylor hd hK z h
  have hn := lipschitz_derivative_taylor hd hK z (-h)
  rw [neg_sq] at hn
  have he : symmetricIncrement f z h=(f (z+h)-f z-df z*h)+(f (z+(-h))-f z-df z*(-h)) := by
    dsimp [symmetricIncrement]; ring_nf
  rw [he]
  calc
    _ ≤ |f (z+h)-f z-df z*h|+|f (z+(-h))-f z-df z*(-h)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem symmetricIncrement_cubic_remainder {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    {L : ℝ≥0} (hL : LipschitzWith L ddf) (z h : ℝ) :
    |symmetricIncrement f z h-ddf z*h^2| ≤ 2*(L:ℝ)*|h|^3 := by
  have hp := lipschitz_second_derivative_taylor hd hdd hL z h
  have hn := lipschitz_second_derivative_taylor hd hdd hL z (-h)
  simp only [abs_neg,neg_sq] at hn
  have he : symmetricIncrement f z h-ddf z*h^2=
      (f (z+h)-f z-df z*h-ddf z*h^2/2)+
      (f (z+(-h))-f z-df z*(-h)-ddf z*h^2/2) := by dsimp [symmetricIncrement]; ring_nf
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem scalarHierarchy_symmetricIncrement_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (z δ Y : ℝ) :
    |symmetricIncrement (scalarHierarchy n m v scalarSpinTerminal) z (δ*Y)| ≤ 2*δ^2*Y^2 ∧
    |symmetricIncrement (scalarHierarchy n m v scalarSpinTerminal) z (δ*Y)-
      δ^2*rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*Y^2| ≤
        2*(susceptibilityLipschitzConstant:ℝ)*|δ|^3*|Y|^3 := by
  constructor
  · have H := symmetricIncrement_quad_bound (scalarHierarchy_spin_hasDerivAt n m v)
      (scalarHierarchy_spin_gradient_lipschitz n m v hm) z (δ*Y)
    simpa only [NNReal.coe_one,mul_one,mul_pow,mul_assoc] using H
  · have H := symmetricIncrement_cubic_remainder (scalarHierarchy_spin_hasDerivAt n m v)
      (scalarHierarchy_spin_gradient_hasDerivAt n m v)
      (scalarHierarchy_spin_hessian_lipschitz n m v hm hmono) z (δ*Y)
    have he : rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*(δ*Y)^2=
        δ^2*rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*Y^2 := by ring
    rw [he,abs_mul,mul_pow] at H
    simpa only [mul_assoc] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_UniformExpansion
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

lemma abs_cube_le_one_add_fourth (y : ℝ) : |y|^3 ≤ 1+y^4 := by
  have hfour : y^4=|y|^4 := by calc
    y^4 = (y^2)^2 := by ring
    _ = (|y|^2)^2 := by rw [sq_abs]
    _ = |y|^4 := by ring
  rw [hfour]
  have ha := abs_nonneg y
  rcases le_total |y| 1 with h|h
  · have H := pow_le_pow_left₀ ha h 3
    norm_num at H
    nlinarith [pow_nonneg ha 4]
  · have H := mul_le_mul_of_nonneg_right h (pow_nonneg ha 3)
    nlinarith

lemma cube_integrable_of_exp_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) {c : ℝ} (hc : 0 < c)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ) :
    Integrable (fun z => |Y z|^3) μ ∧
    (∫ z, |Y z|^3 ∂μ) ≤ (1+2/c^2)*(∫ z, Real.exp (c*(Y z)^2) ∂μ) := by
  have hb (z) : |Y z|^3 ≤ (1+2/c^2)*Real.exp (c*(Y z)^2) := by
    have H := fourth_pow_le_exp_square hc (Y z)
    have HE := Real.one_le_exp (mul_nonneg hc.le (sq_nonneg (Y z)))
    have HY := abs_cube_le_one_add_fourth (Y z)
    nlinarith
  have hi : Integrable (fun z => |Y z|^3) μ :=
    (hE.const_mul (1+2/c^2)).mono' ((continuous_abs.comp_aestronglyMeasurable hY).pow 3) (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg (Y z)) 3)] using hb z))
  refine ⟨hi,?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi (hE.const_mul _) hb

theorem log_integral_exp_cubic_expansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y Δ A : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (hΔ : Integrable Δ μ)
    (hA : Integrable (fun z => A z*(Y z)^2) μ)
    {c δ M B : ℝ} (hc : 0 < c) (hδ : 4*δ^2 ≤ c) (hδ1 : |δ| ≤ 1) (hB : 0 ≤ B)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ)
    (hM : (∫ z, Real.exp (c*(Y z)^2) ∂μ) ≤ M)
    (hb : ∀ᵐ z ∂μ, |Δ z| ≤ 2*δ^2*(Y z)^2)
    (hr : ∀ᵐ z ∂μ, |Δ z-δ^2*A z*(Y z)^2| ≤ B*|δ|^3*|Y z|^3) :
    Real.log (∫ z, Real.exp (Δ z) ∂μ) ≤
      δ^2*(∫ z, A z*(Y z)^2 ∂μ)+
      ((B*(1+2/c^2)+32/c^2)*M)*|δ|^3 := by
  obtain ⟨hi,hI⟩ := cube_integrable_of_exp_square μ Y hY hc hE
  have hM0 : 0 ≤ M := (integral_nonneg (fun z => Real.exp_nonneg _)).trans hM
  have hpow : δ^4 ≤ |δ|^3 := by
    have H := mul_le_mul_of_nonneg_left hδ1 (pow_nonneg (abs_nonneg δ) 3)
    have he : δ^4=|δ|^4 := by
      calc
        δ^4 = (δ^2)^2 := by ring
        _ = (|δ|^2)^2 := by rw [sq_abs]
        _ = |δ|^4 := by ring
    rw [he]; nlinarith
  have HD : (∫ z, Δ z ∂μ) ≤ δ^2*(∫ z, A z*(Y z)^2 ∂μ)+
      (B*|δ|^3)*(∫ z, |Y z|^3 ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hA.const_mul _) (hi.const_mul _)]
    apply integral_mono_ae hΔ ((hA.const_mul _).add (hi.const_mul _))
    filter_upwards [hr] with z hz
    have H := le_abs_self (Δ z-δ^2*A z*(Y z)^2)
    simp only [Pi.add_apply]
    nlinarith
  have Hlog := log_integral_exp_quadratic_bound μ Y Δ hY hΔ hc hδ hE hM hb
  have HC : (∫ z, |Y z|^3 ∂μ) ≤ (1+2/c^2)*M :=
    hI.trans (mul_le_mul_of_nonneg_left hM (by positivity))
  have HH := mul_le_mul_of_nonneg_left HC (by positivity : 0 ≤ B*|δ|^3)
  have HP := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (32/c^2)*M)
  nlinarith

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

theorem tripleMiddleBoundary_regular {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (X Z : ParameterSpace n →L[ℝ] ℝ) : BoundedDerivs (tripleMiddleBoundary f X Z) :=
  (hf.compCLM X).add ((hf.compCLM Z).const_mul 2)

theorem tripleModifiedBoundary_regular {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (X Z Y : ParameterSpace n →L[ℝ] ℝ) (δ : ℝ) :
    BoundedDerivs (tripleModifiedBoundary f X Z Y δ) :=
  ((hf.compCLM X).add (hf.compCLM (Z+δ • Y))).add (hf.compCLM (Z-δ • Y))

theorem tripleMiddleBoundary_coordinate_bound {n : ℕ} {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hL : LipschitzWith 1 f) (X Z : ParameterSpace n →L[ℝ] ℝ) (i : Fin n) (z : ParameterSpace n) :
    |fderiv ℝ (tripleMiddleBoundary f X Z) z (coordinateAxis n i)| ≤
      |X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)| := by
  let F := f ∘ X
  let G := f ∘ Z
  have hF := (hf.compCLM X).1.differentiable (by norm_num)
  have hG := (hf.compCLM Z).1.differentiable (by norm_num)
  change |fderiv ℝ (fun z => F z+2*G z) z (coordinateAxis n i)| ≤ _
  dsimp only [F,G,Function.comp_def]
  rw [fderiv_fun_add (hF z) ((hG z).const_mul 2),fderiv_const_mul (hG z),
    add_apply,smul_apply,smul_eq_mul]
  calc
    _ ≤ |fderiv ℝ F z (coordinateAxis n i)|+|2*fderiv ℝ G z (coordinateAxis n i)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (scalar_composition_coordinate_bound hf hL X z _)
        (mul_le_mul_of_nonneg_left (scalar_composition_coordinate_bound hf hL Z z _) (by norm_num))

theorem tripleMiddle_recursive_expansion (n t : ℕ) (m : Fin n → ℝ) (p v : Fin t → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (hp : ∀ i, p i∈Icc (0:ℝ) 1) (hpmono : Monotone p)
    (X Z : ParameterSpace n →L[ℝ] ℝ) (a : Fin n → ℝ) (x : ℝ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 4*δ^2 ≤ c) (hδ1 : |δ| ≤ 1)
    (hsmall : c*(4*(∑ i, (a i)^2)+
      (2*∑ i, |a i| *(|X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)|))^2) ≤ 1/2) :
    let f := scalarHierarchy t p v scalarSpinTerminal
    let F := tripleMiddleBoundary f X Z
    let Y := coordinateLinear n a
    hierarchyPressure n m (tripleModifiedBoundary f X Z Y δ) x ≤
      hierarchyPressure n m F x+
      δ^2*(∫ z, rootHessian 0 f (Z z)*(Y z)^2 ∂hierarchyPathLaw n m F x)+
      ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/c^2)+32/c^2)*2)*|δ|^3 := by
  dsimp only
  let f := scalarHierarchy t p v scalarSpinTerminal
  let F := tripleMiddleBoundary f X Z
  let Y := coordinateLinear n a
  let G := tripleModifiedBoundary f X Z Y δ
  let μ := hierarchyPathLaw n m F x
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular t p v
  have hFL : LipschitzWith 1 f := scalarHierarchy_lipschitz t p v (fun i => (hp i).1)
    scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
  have hF : BoundedDerivs F := tripleMiddleBoundary_regular hf X Z
  have hG : BoundedDerivs G := tripleModifiedBoundary_regular hf X Z Y δ
  have hU : BoundedDerivs (fun z => G z-F z) := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hG.add (hF.const_mul (-1))
  let := hierarchyPathLaw_probability n m F hF x
  obtain ⟨hE,hM⟩ := hierarchy_exp_square_bound n m hm hmono F hF
    (fun i => |X (coordinateAxis n i)|+2*|Z (coordinateAxis n i)|) (by intro i; positivity)
    (fun z i => tripleMiddleBoundary_coordinate_bound hf hFL X Z i z) x a hc.le hsmall
  have hΔ : Integrable (fun z => G z-F z) μ :=
    hU.hasExpGrowth.integrable_hierarchyPathLaw n m hF hU.1.continuous x
  have hcA : Continuous (fun z : ParameterSpace n => rootHessian 0 f (Z z)) :=
    (scalarHierarchy_spin_hessian_lipschitz t p v hp hpmono).continuous.comp Z.continuous
  have hbA (z : ParameterSpace n) : ‖rootHessian 0 f (Z z)‖ ≤ 1 := by
    have H := scalarHierarchy_spin_derivative_bounds t p v hp (Z z)
    change |fderiv ℝ (fderiv ℝ f) (Z z) 1 1| ≤ 1
    rw [abs_of_pos H.2.1]
    exact H.2.2.trans (sub_le_self _ (sq_nonneg _))
  have hA : Integrable (fun z => rootHessian 0 f (Z z)*(Y z)^2) μ :=
    ((HasExpGrowth.of_bounded zero_le_one hbA).mul ((HasExpGrowth.linear Y).pow 2)).integrable_hierarchyPathLaw
      n m hF (hcA.mul (Y.continuous.pow 2)) x
  have he (z) : G z-F z=symmetricIncrement f (Z z) (δ*Y z) := by
    dsimp [F,G,tripleMiddleBoundary,tripleModifiedBoundary,symmetricIncrement]; ring
  have H := log_integral_exp_cubic_expansion μ Y (fun z => G z-F z)
    (fun z => rootHessian 0 f (Z z)) Y.continuous.aestronglyMeasurable hΔ hA hc hδ hδ1
    (by positivity : 0 ≤ 2*(susceptibilityLipschitzConstant:ℝ)) hE hM
    (ae_of_all _ (fun z => by rw [he]; exact (scalarHierarchy_symmetricIncrement_bounds t p v hp hpmono _ δ _).1))
    (ae_of_all _ (fun z => by rw [he]; exact (scalarHierarchy_symmetricIncrement_bounds t p v hp hpmono _ δ _).2))
  have HS := (hierarchyPressure_increment_integral_sandwich n m hm hF hG x).2
  change hierarchyPressure n m G x ≤ hierarchyPressure n m F x+_+_
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetained
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tripleRetainedCommon_image (δ : ℝ) (c : List (ℝ × ℝ)) :
    (tripleRetainedCommon c).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleCommonSchedule c := by
  simp [tripleRetainedCommon,tripleCommonSchedule,List.map_map,Function.comp_def]

theorem tripleRetainedMiddle_image (δ : ℝ) (l : List TripleMiddleIncrement) :
    (tripleRetainedMiddle l).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleMiddleSchedule δ l := by
  simp only [tripleRetainedMiddle,tripleMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  cases p <;> simp [productVector,tripleMiddleVector,tripleRetainedEmbedding_apply]

theorem retained_sum_coordinates (n : ℕ) (v : Fin n → TripleRetainedState) (z : ParameterSpace n) :
    (∑ i,coordinateProjection n i z • v i)=
      ((coordinateLinear n (fun i => (v i).1.1) z,coordinateLinear n (fun i => (v i).1.2) z),
        coordinateLinear n (fun i => (v i).2) z) := by
  apply Prod.ext
  · apply Prod.ext
    · simpa only [retainedSingleton,retainedNoise,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
        Prod.smul_fst,smul_eq_mul,coordinateLinear_apply,mul_comm] using
          map_sum retainedSingleton (fun i => coordinateProjection n i z • v i) Finset.univ
    · simpa only [retainedSingleton,retainedNoise,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',Prod.smul_fst,Prod.smul_snd,smul_eq_mul,coordinateLinear_apply,mul_comm] using
          map_sum retainedNoise (fun i => coordinateProjection n i z • v i) Finset.univ
  · simpa only [retainedPair,ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,coordinateLinear_apply,mul_comm] using
      map_sum retainedPair (fun i => coordinateProjection n i z • v i) Finset.univ

theorem tripleRetained_pressure (n : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (f : ℝ → ℝ) (δ : ℝ) :
    vectorHierarchy n m (fun i => tripleRetainedEmbedding δ (v i))
      (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2)) 0=
      hierarchyPressure n m (tripleModifiedBoundary f (coordinateLinear n (fun i => (v i).1.1))
        (coordinateLinear n (fun i => (v i).2)) (coordinateLinear n (fun i => (v i).1.2)) δ) 0 := by
  have H := congrFun (hierarchyPressure_vector_linear n m v
    (fun x : TripleRetainedState => f x.1.1+f (x.2+δ*x.1.2)+f (x.2-δ*x.1.2)) (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  have HT := congrFun (vectorHierarchy_pullback (tripleRetainedEmbedding δ) n m v
    (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2))) 0
  simp only [Function.comp_def,tripleRetainedEmbedding_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,map_zero] at HT
  unfold tripleModifiedBoundary
  simpa only [tripleRetainedEmbedding_apply] using HT.symm.trans H.symm

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

theorem list_commonBranch_value (c : List (ℝ × ℝ)) (f : ℝ → ℝ) (x : ℝ) :
    vectorIncrementChain (tripleRetainedCommon c)
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) ((x,0),x)=3*scalarIncrementChain c f x := by
  have H := commonBranch_value c.length (fun i => (c.get i).1) (fun i => (c.get i).2) f x
  rw [← vectorIncrementChain_ofFn,← scalarIncrementChain_ofFn] at H
  have h1 : List.ofFn (fun i : Fin c.length => ((c.get i).1/3,(((c.get i).2,0),(c.get i).2)))=
      tripleRetainedCommon c := by
    unfold tripleRetainedCommon
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=c.get) (g:=fun p : ℝ × ℝ => (p.1/3,((p.2,0),p.2)))).symm
  simpa only [h1,Prod.mk.eta,List.ofFn_get] using H

theorem list_commonBranch_average (c : List (ℝ × ℝ)) (f b : ℝ → ℝ) (a : ℝ × ℝ → ℝ) (x : ℝ) :
    vectorIncrementAverage (tripleRetainedCommon c)
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) (fun p => a p.1*b p.2) ((x,0),x)=
      scalarIncrementAverage c f (fun y => a (y,0)*b y) x := by
  have H := commonBranch_average c.length (fun i => (c.get i).1) (fun i => (c.get i).2) f b a x
  rw [← vectorIncrementAverage_ofFn,← scalarIncrementAverage_ofFn] at H
  have h1 : List.ofFn (fun i : Fin c.length => ((c.get i).1/3,(((c.get i).2,0),(c.get i).2)))=
      tripleRetainedCommon c := by
    unfold tripleRetainedCommon
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=c.get) (g:=fun p : ℝ × ℝ => (p.1/3,((p.2,0),p.2)))).symm
  simpa only [h1,Prod.mk.eta,List.ofFn_get] using H

theorem weightedBranch_value (w : List (ℝ × (ℝ × ℝ))) (f : ℝ → ℝ) :
    vectorIncrementChain w (fun p : ℝ × ℝ => f p.1)=fun p => scalarIncrementChain (weightedUnderlying w) f p.1 := by
  have H := vectorIncrementChain_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f
  rw [vectorIncrementChain_real] at H
  exact H

theorem tripleRetainedMiddle_value (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w)))
      (fun p : TripleRetainedState => f p.1.1+2*f p.2)=
      fun p => scalarIncrementChain (weightedUnderlying w) f p.1.1+2*scalarIncrementChain (weightedUnderlying w) f p.2 := by
  have hF : BoundedDerivs (fun q : ℝ × ℝ => f q.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchChain _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*f p.2)=_
  rw [productBranchChain_factor _ hF hf,
    mergedProductBranches_left,mergedProductBranches_right,weightedBranch_value,vectorIncrementChain_real]

theorem tripleRetainedMiddle_average (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) :
    vectorIncrementAverage (tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w)))
      (fun p : TripleRetainedState => f p.1.1+2*f p.2) (fun p => g p.2*p.1.2^2)=
      fun p => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) p.1*
        scalarIncrementAverage (weightedUnderlying w) f g p.2 := by
  have he : (fun p : TripleRetainedState => g p.2*p.1.2^2)=fun p => p.1.2^2*g p.2 := by funext p; ring
  rw [he]
  have hF : BoundedDerivs (fun q : ℝ × ℝ => f q.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  change productBranchAverage _ (fun p => (fun q : ℝ × ℝ => f q.1) p.1+2*f p.2) (fun p => (fun q : ℝ × ℝ => q.2^2) p.1*g p.2)=_
  rw [productBranchAverage_factor _ hF hf (fun q : ℝ × ℝ => q.2^2) g,
    mergedProductBranches_left,mergedProductBranches_right,vectorIncrementAverage_real]

theorem tripleRetainedPrefix_value (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    vectorIncrementChain (tripleRetainedPrefix c w) (fun p => f p.1.1+2*f p.2) 0=
      3*scalarIncrementChain (c++weightedUnderlying w) f 0 := by
  rw [tripleRetainedPrefix,vectorIncrementChain_append,tripleRetainedMiddle_value w hf,scalarIncrementChain_append]
  exact list_commonBranch_value c _ 0

theorem tripleRetainedPrefix_average (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) :
    vectorIncrementAverage (tripleRetainedPrefix c w) (fun p => f p.1.1+2*f p.2) (fun p => g p.2*p.1.2^2) 0=
      scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) f)
        (fun x => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (x,0)*
          scalarIncrementAverage (weightedUnderlying w) f g x) 0 := by
  rw [tripleRetainedPrefix,vectorIncrementAverage_append,tripleRetainedMiddle_value w hf,
    tripleRetainedMiddle_average w hf g]
  exact list_commonBranch_average c _ _ _ 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetainedExpansion
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tripleRetained_base_pressure (n : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState) (f : ℝ → ℝ) :
    vectorHierarchy n m v (fun x => f x.1.1+2*f x.2) 0=
      hierarchyPressure n m (tripleMiddleBoundary f (coordinateLinear n (fun i => (v i).1.1))
        (coordinateLinear n (fun i => (v i).2))) 0 := by
  have H := congrFun (hierarchyPressure_vector_linear n m v (fun x : TripleRetainedState => f x.1.1+2*f x.2)
    (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  exact H.symm

theorem tripleRetained_quadratic_average (n t : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (p b : Fin t → ℝ) (hp : ∀ i,p i∈Icc (0:ℝ) 1) (hpmono : Monotone p) :
    let f := scalarHierarchy t p b scalarSpinTerminal
    vectorHierarchyAverage n m v (fun x => f x.1.1+2*f x.2)
      (fun x => rootHessian 0 f x.2*x.1.2^2) 0=
      ∫ z, rootHessian 0 f (coordinateLinear n (fun i => (v i).2) z)*
        (coordinateLinear n (fun i => (v i).1.2) z)^2
        ∂hierarchyPathLaw n m (tripleMiddleBoundary f (coordinateLinear n (fun i => (v i).1.1))
          (coordinateLinear n (fun i => (v i).2))) 0 := by
  dsimp only
  let f := scalarHierarchy t p b scalarSpinTerminal
  let X := coordinateLinear n (fun i => (v i).1.1)
  let Z := coordinateLinear n (fun i => (v i).2)
  let Y := coordinateLinear n (fun i => (v i).1.2)
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular t p b
  have hF : BoundedDerivs (tripleMiddleBoundary f X Z) := tripleMiddleBoundary_regular hf X Z
  have hc : Continuous (fun z => rootHessian 0 f (Z z)) :=
    (scalarHierarchy_spin_hessian_lipschitz t p b hp hpmono).continuous.comp Z.continuous
  have hbnd : ∀ z, ‖rootHessian 0 f (Z z)‖≤1 := by
    intro z
    have H := scalarHierarchy_spin_derivative_bounds t p b hp (Z z)
    change |fderiv ℝ (fderiv ℝ f) (Z z) 1 1|≤1
    rw [abs_of_pos H.2.1]
    exact H.2.2.trans (sub_le_self _ (sq_nonneg _))
  have he : HasExpGrowth (fun z => rootHessian 0 f (Z z)*(Y z)^2) :=
    (HasExpGrowth.of_bounded zero_le_one hbnd).mul ((HasExpGrowth.linear Y).pow 2)
  have H := congrFun (hierarchyAverage_vector_linear n m v (fun x : TripleRetainedState => f x.1.1+2*f x.2)
    (fun x => rootHessian 0 f x.2*x.1.2^2) (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ hF _ (hc.mul (Y.continuous.pow 2)) he 0

theorem tripleRetained_expansion (n t : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (p b : Fin t → ℝ) (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (hp : ∀ i,p i∈Icc (0:ℝ) 1) (hpmono : Monotone p)
    {c δ : ℝ} (hc : 0 < c) (hδ : 4*δ^2 ≤ c) (hδ1 : |δ|≤1)
    (hsmall : c*(4*(∑ i,((v i).1.2)^2)+
      (2*∑ i, |(v i).1.2| *(|(v i).1.1|+2*|(v i).2|))^2)≤1/2) :
    let f := scalarHierarchy t p b scalarSpinTerminal
    vectorHierarchy n m (fun i => tripleRetainedEmbedding δ (v i))
      (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2)) 0≤
      vectorHierarchy n m v (fun x => f x.1.1+2*f x.2) 0+
      δ^2*vectorHierarchyAverage n m v (fun x => f x.1.1+2*f x.2)
        (fun x => rootHessian 0 f x.2*x.1.2^2) 0+
      ((2*(susceptibilityLipschitzConstant:ℝ)*(1+2/c^2)+32/c^2)*2)*|δ|^3 := by
  dsimp only
  rw [tripleRetained_pressure,tripleRetained_base_pressure,tripleRetained_quadratic_average n t m v p b hp hpmono]
  apply tripleMiddle_recursive_expansion n t m p b hm hmono hp hpmono _ _ _ 0 hc hδ hδ1
  simpa only [coordinateLinear_coordinateAxis] using hsmall

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleMass
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

theorem tripleCommonSchedule_mem_mass {c : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleCommonSchedule c) : ∃ q∈c,p.1=q.1/3 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨q,hq,rfl⟩

theorem tripleMiddleSchedule_mem_mass {δ : ℝ} {w : List (ℝ × (ℝ × ℝ))} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))) :
    ∃ q∈weightedUnderlying w,p.1=q.1 ∨ p.1=q.1/2 := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  simp only [mergedProductBranches,List.mem_merge,List.mem_map] at hs
  rcases hs with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
  · exact ⟨(q.1,q.2.1),List.mem_map.mpr ⟨q,hq,rfl⟩,Or.inl rfl⟩
  · exact ⟨q,hq,Or.inr rfl⟩

theorem tripleTailSchedule_mem_mass {t : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleTailSchedule t) : ∃ q∈t,p.1=q.1 := by
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> exact ⟨q,hq,rfl⟩

theorem tripleTailSchedule_monotone (t : List (ℝ × ℝ))
    (ht : t.Pairwise (fun p q => p.1≤q.1)) :
    (tripleTailSchedule t).Pairwise (fun p q => p.1≤q.1) := by
  induction t with
  | nil => simp [tripleTailSchedule]
  | cons a t ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp ht
    change (tripleTailBlock a++tripleTailSchedule t).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨?_,ih ht,?_⟩
    · simp [tripleTailBlock]
    · intro p hp q hq
      obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
      have hpa : p.1=a.1 := by
        simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl <;> rfl
      rw [hpa,hqb]
      exact ha b hb

theorem tripleSchedule_mass_bounds (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈tripleSchedule δ c w t,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  simp only [tripleSchedule,List.mem_append] at hp
  rcases hp with (hp|hp)|hp
  · obtain ⟨q,hq,hpq⟩ := tripleCommonSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleMiddleSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rcases hpq with hpq|hpq
    · simpa only [hpq] using H
    · rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleTailSchedule_mem_mass hp
    simpa only [hpq] using hm q (by simp [hq])

theorem tripleSchedule_monotone (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,0≤p.1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    (tripleSchedule δ c w t).Pairwise (fun p q => p.1≤q.1) := by
  obtain ⟨hcw,ht,hct⟩ := List.pairwise_append.mp hs
  obtain ⟨hc,hw,hcw⟩ := List.pairwise_append.mp hcw
  have hmid : (tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))).Pairwise
      (fun p q => p.1≤q.1) := by
    rw [tripleMiddleSchedule,List.pairwise_map]
    apply mergedProductBranches_monotone
    · simpa only [weightedUnderlying,List.pairwise_map] using hw
    · exact hw
  have hcom : (tripleCommonSchedule c).Pairwise (fun p q => p.1≤q.1) := by
    rw [tripleCommonSchedule,List.pairwise_map]
    exact hc.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  unfold tripleSchedule
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hcom,hmid,?_⟩,tripleTailSchedule_monotone t ht,?_⟩
  · intro p hp q hq
    obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
    obtain ⟨b,hb,hqb⟩ := tripleMiddleSchedule_mem_mass hq
    have H := hcw a ha b hb
    have Ha := hm a (by simp [ha])
    rw [hpa]
    rcases hqb with hqb|hqb <;> rw [hqb] <;> linarith
  · intro p hp q hq
    obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
    rw [hqb]
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
      have H := hct a (List.mem_append_left _ ha) b hb
      have Ha := hm a (by simp [ha])
      rw [hpa]; linarith
    · obtain ⟨a,ha,hpa⟩ := tripleMiddleSchedule_mem_mass hp
      have H := hct a (List.mem_append_right _ ha) b hb
      have Ha := hm a (by simp [ha])
      rcases hpa with hpa|hpa <;> rw [hpa] <;> linarith

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

theorem tripleRetainedPrefix_image (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    (tripleRetainedPrefix c w).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleSchedule δ c w [] := by
  simp only [tripleRetainedPrefix,List.map_append,tripleRetainedCommon_image,tripleRetainedMiddle_image,
    tripleSchedule,tripleTailSchedule,List.flatMap_nil,List.append_nil]

theorem tripleRetainedPrefix_mass (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈tripleRetainedPrefix c w,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  have H := tripleSchedule_mass_bounds 0 c w [] (by simpa only [List.append_nil] using hm)
  rw [← tripleRetainedPrefix_image] at H
  exact H (p.1,tripleRetainedEmbedding 0 p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem tripleRetainedPrefix_monotone (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++weightedUnderlying w,0≤p.1)
    (hs : (c++weightedUnderlying w).Pairwise (fun p q => p.1≤q.1)) :
    (tripleRetainedPrefix c w).Pairwise (fun p q => p.1≤q.1) := by
  have H := tripleSchedule_monotone 0 c w [] (by simpa only [List.append_nil] using hm)
    (by simpa only [List.append_nil] using hs)
  rw [← tripleRetainedPrefix_image,List.pairwise_map] at H
  exact H

theorem tripleRetainedMiddle_variance (l : List TripleMiddleIncrement) :
    ((tripleRetainedMiddle l).map (fun p => p.2.1.2^2)).sum=weightedVariance (productLeft l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases p <;> (simp only [tripleRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,
      List.sum_cons,productVector,productLeft,List.filterMap_cons,weightedVariance,List.map_cons,
      List.sum_cons] at ih ⊢; rw [ih] <;> simp)

theorem tripleRetainedMiddle_score (l : List TripleMiddleIncrement) :
    ((tripleRetainedMiddle l).map (fun p => |p.2.1.2| * (|p.2.1.1| + 2*|p.2.2|))).sum=
      weightedAbsCross (productLeft l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases p <;> (simp only [tripleRetainedMiddle,List.map_cons,List.map_map,Function.comp_def,
      List.sum_cons,productVector,productLeft,List.filterMap_cons,weightedAbsCross,List.map_cons,List.sum_cons,
      abs_zero,mul_zero,add_zero] at ih ⊢; rw [ih] <;> simp)

theorem tripleRetainedPrefix_variance (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    ((tripleRetainedPrefix c w).map (fun p => p.2.1.2^2)).sum=weightedVariance w := by
  simp only [tripleRetainedPrefix,List.map_append,List.sum_append,tripleRetainedMiddle_variance,
    mergedProductBranches_left,tripleRetainedCommon,List.map_map,Function.comp_def,zero_pow (by norm_num : 2≠0),
    ]
  simp

theorem tripleRetainedPrefix_score (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) :
    ((tripleRetainedPrefix c w).map (fun p => |p.2.1.2| * (|p.2.1.1| + 2*|p.2.2|))).sum=weightedAbsCross w := by
  simp only [tripleRetainedPrefix,List.map_append,List.sum_append,tripleRetainedMiddle_score,
    mergedProductBranches_left,tripleRetainedCommon,List.map_map,Function.comp_def,abs_zero,zero_mul,
    ]
  simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleFiniteExpansion
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

theorem tripleSchedule_value_expansion_oai (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    {a δ : ℝ} (ha : 0<a) (hδ : 4*δ^2≤a) (hδ1 : |δ|≤1)
    (hsmall : a*(4*weightedVariance w+(2*weightedAbsCross w)^2)≤1/2) :
    vectorIncrementChain (tripleSchedule δ c w t) (fun x => ∑ u,scalarSpinTerminal (x u)) 0≤
      3*scalarIncrementChain (c++weightedUnderlying w++t) scalarSpinTerminal 0+
      δ^2*tripleBaseQuadratic c w t+tripleExpansionConstant a*|δ|^3 := by
  let l := tripleRetainedPrefix c w
  have hm0 : ∀ p∈c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1 :=
    fun p hp => hm p (List.mem_append_left _ hp)
  have hm1 := tripleRetainedPrefix_mass c w hm0
  have hs1 := tripleRetainedPrefix_monotone c w (fun p hp => (hm0 p hp).1) (List.pairwise_append.mp hs).1
  have hmt : ∀ i : Fin t.length,(t.get i).1∈Icc (0:ℝ) 1 :=
    fun i => hm _ (List.mem_append_right _ (List.get_mem t i))
  have hst := mass_get_monotone (List.pairwise_append.mp hs).2.1
  have hsmall' : a*(4*(∑ i : Fin l.length,((l.get i).2.1.2)^2)+
      (2*∑ i : Fin l.length, |(l.get i).2.1.2| * (|(l.get i).2.1.1|+2*|(l.get i).2.2|))^2)≤1/2 := by
    rw [sum_get_map l (fun p => p.2.1.2^2),
      sum_get_map l (fun p => |p.2.1.2| * (|p.2.1.1|+2*|p.2.2|))]
    simpa only [l,tripleRetainedPrefix_variance,tripleRetainedPrefix_score] using hsmall
  have H := tripleRetained_expansion l.length t.length (fun i => (l.get i).1) (fun i => (l.get i).2)
    (fun i => (t.get i).1) (fun i => (t.get i).2) (fun i => hm1 _ (List.get_mem l i))
    (mass_get_monotone hs1) hmt hst ha hδ hδ1 hsmall'
  dsimp only at H
  rw [← scalarIncrementChain_get] at H
  have hmap : List.ofFn (fun i : Fin l.length => ((l.get i).1,tripleRetainedEmbedding δ (l.get i).2))=
      l.map (fun p => (p.1,tripleRetainedEmbedding δ p.2)) := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,tripleRetainedEmbedding δ p.2))).symm
  rw [← vectorIncrementChain_ofFn,hmap,← vectorIncrementChain_get,← vectorIncrementAverage_get] at H
  have hf := scalarIncrementChain_regular t scalarSpinTerminal_regular
  rw [tripleRetainedPrefix_value c w hf,tripleRetainedPrefix_average c w hf] at H
  have hid : tripleSchedule δ c w t=(l.map (fun p => (p.1,tripleRetainedEmbedding δ p.2)))++tripleTailSchedule t := by
    rw [tripleRetainedPrefix_image]
    simp only [tripleSchedule,tripleTailSchedule,List.flatMap_nil,List.append_nil]
  rw [hid,vectorIncrementChain_append]
  have he : (fun x : Fin 3 → ℝ => ∑ u,scalarSpinTerminal (x u))=
      fun x => scalarSpinTerminal (x 0)+scalarSpinTerminal (x 1)+scalarSpinTerminal (x 2) := by
    funext x; simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; exact (add_assoc _ _ _).symm
  rw [he,tripleTailSchedule_value scalarSpinTerminal_regular scalarSpinTerminal_regular scalarSpinTerminal_regular]
  simpa only [scalarIncrementChain_append,tripleBaseQuadratic,tripleExpansionConstant] using H

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.tripleSchedule_value_expansion_oai := @OAI.SK.Analytic.tripleSchedule_value_expansion_oai
