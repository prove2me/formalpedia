-- Prove2me | solution 1 for OAI.SK.Analytic.exists_block_adaptive_path
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:05:30.278219+00:00
-- url     : https://prove2.me/submissions/0ccb7975-46ce-4862-8ddd-a67fc5554cd3

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005
import Theorems.Thm_OAI_SK_Analytic_equalBlock_average_trace
import Theorems.Thm_OAI_SK_Analytic_sharedFieldEnergy_variance

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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateStein
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

section DirectionalSpinStein
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem spinGaussian_directional_stein (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (a : Fin n → ℝ) :
    (∫ sz, coordinateLinear n a sz.2*g sz.1 sz.2 ∂spinGaussianLaw n V 0) =
      (∫ sz, fderiv ℝ (g sz.1) sz.2 (coordinateVector n a) ∂spinGaussianLaw n V 0) +
      ∫ sz, g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateVector n a) ∂spinGaussianLaw n V 0 := by
  have hdV (s : S) : HasExpGrowth (fderiv ℝ (V s)) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV s
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => coordinateProjection n i z*g s z) hV
    (fun s => (HasExpGrowth.linear _).mul (hg s))
    (fun s => (coordinateProjection n i).continuous.mul (hc s).continuous)
  have hi₂ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => fderiv ℝ (g s) z (coordinateAxis n i)) hV
    (fun s => (hdg s).derivative_eval _)
    (fun s => ((hc s).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hi₃ (i : Fin n) := spinGaussian_integrable n V
    (fun s z => g s z*fderiv ℝ (V s) z (coordinateAxis n i)) hV
    (fun s => (hg s).mul ((hdV s).derivative_eval _))
    (fun s => (hc s).continuous.mul (((hV s).1.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun sz : S × ParameterSpace n => ∑ i, g sz.1 sz.2*(a i*
      fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i))) =
      fun sz => ∑ i, a i*(g sz.1 sz.2*fderiv ℝ (V sz.1) sz.2 (coordinateAxis n i)) := by
    funext sz
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [spinGaussian_weighted_stein n V g hV hc hg hdg,mul_add]

end DirectionalSpinStein
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

theorem TranslationInvariant.gaussianStep {f : E × ℝ → ℝ} {u : E}
    (hi : TranslationInvariant f (u,0)) (m : ℝ) : TranslationInvariant (gaussianStep m f) u := by
  intro z t
  have he (y : ℝ) : f (z+t • u,y) = f (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hi (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem affineLogPartition_translation {S : Type} [Fintype S]
    (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (u : E) (hu : ∀ s, L s u = 0) :
    TranslationInvariant (affineLogPartition c L) u := by
  intro z t
  simp only [affineLogPartition,map_add,map_smul,hu,smul_eq_mul,mul_zero,add_zero]

end Translation

theorem hierarchyLevel_invariant_of_tail (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ParameterSpace n) (hi : TranslationInvariant f u)
    (j : Fin (n+1)) (hz : TailZero n j u) : TranslationInvariant (hierarchyLevel n m f j) u := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simpa only [hierarchyLevel,Fin.lastCases_last] using hi
    simp only [TailZero,Fin.lastCases_castSucc] at hz
    have hz' : u.2 = 0 ∧ TailZero n j u.1 := hz
    have hui : u = (u.1,0) := Prod.ext rfl hz'.1
    have hi' : TranslationInvariant f (u.1,0) := hui ▸ hi
    have H := ih (fun i => m i.castSucc) _ u.1 (hi'.gaussianStep (m (Fin.last n))) j hz'.2
    intro z t
    simpa only [hierarchyLevel,Fin.lastCases_castSucc,Prod.fst_add,Prod.smul_fst] using H z.1 t

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

omit [MeasurableSpace S] [MeasurableSingletonClass S] in

theorem hierarchyPotential_directional_cancellation (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (u z : ParameterSpace n)
    (hU : ∀ s, U s u = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) u) (s : S) :
    fderiv ℝ (hierarchyPotential n m U s) z u =
      -hierarchyAtom n m 1 j * fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z u := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  change fderiv ℝ (fun z => U s z-hierarchyPenalty n m 1 f z) z u = _
  rw [fderiv_fun_sub (U s).differentiableAt (hp.1.differentiable (by norm_num) z)]
  simp only [sub_apply,ContinuousLinearMap.fderiv,hU,zero_sub]
  rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
  rw [Finset.sum_eq_single j]
  · ring
  · intro k _ hkj
    rcases hi k hkj with h | h
    · rw [h,zero_mul]
    · rw [h.fderiv_zero ((hierarchyLevel_boundedDerivs n m f hf k).1.differentiable (by norm_num)),mul_zero]
  · simp

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

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem HasExpGrowth.finsetSum {I : Type} (s : Finset I) (f : I → E → F)
    (hf : ∀ i ∈ s, HasExpGrowth (f i)) : HasExpGrowth (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using HasExpGrowth.const (E := E) (0 : F)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

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

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem HasExpGrowth.fderiv_sum {I : Type} (s : Finset I) (f : I → E → ℝ)
    (hc : ∀ i ∈ s, Differentiable ℝ (f i))
    (hd : ∀ i ∈ s, HasExpGrowth (fderiv ℝ (f i))) :
    HasExpGrowth (fderiv ℝ (fun z => ∑ i ∈ s, f i z)) := by
  have he : fderiv ℝ (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, fderiv ℝ (f i) z := by
    funext z
    exact (HasFDerivAt.fun_sum (fun i hi => (hc i hi z).hasFDerivAt)).fderiv
  rw [he]
  exact HasExpGrowth.finsetSum s _ hd

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem gradientSquareSum_regular {I : Type} [Fintype I] (F : E → ℝ)
    (hF : BoundedDerivs F) (u : I → E) :
    ContDiff ℝ 1 (gradientSquareSum F u) ∧ HasExpGrowth (gradientSquareSum F u) ∧
      HasExpGrowth (fderiv ℝ (gradientSquareSum F u)) := by
  have hc (i) := directionalGradient_contDiff F hF.1 (u i)
  have hg (i) := hF.directionalGradient_bounds (u i)
  refine ⟨ContDiff.sum (fun i _ => (hc i).mul (hc i)),?_,?_⟩
  · exact HasExpGrowth.finsetSum _ _ (fun i _ => (hg i).1.mul (hg i).1)
  · apply HasExpGrowth.fderiv_sum
    · intro i _; exact ((hc i).mul (hc i)).differentiable (by norm_num)
    · intro i _
      exact HasExpGrowth.fderiv_mul ((hc i).differentiable (by norm_num))
        ((hc i).differentiable (by norm_num)) (hg i).1 (hg i).1 (hg i).2 (hg i).2

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem TranslationInvariant.gradientSquareSum {I : Type} [Fintype I] {F : E → ℝ} {v : E}
    (hF : TranslationInvariant F v) (u : I → E) : TranslationInvariant (gradientSquareSum F u) v := by
  intro z t
  have shifted : (fun point => F (point + t • v)) = F := funext (fun point => hF point t)
  have derivative : fderiv ℝ F (z + t • v) = fderiv ℝ F z := by
    rw [← fderiv_comp_add_right (t • v), shifted]
  unfold SK.Analytic.gradientSquareSum SK.Analytic.directionalGradient
  rw [derivative]

end SmoothObservables

section SharedPrefix
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyGaussian_shared_stein (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hc : ∀ s, ContDiff ℝ 1 (g s)) (hg : ∀ s, HasExpGrowth (g s))
    (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (a : Fin n → ℝ) (j : Fin (n+1))
    (hU : ∀ s, U s (coordinateVector n a) = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n a))
    (hig : ∀ s, TranslationInvariant (g s) (coordinateVector n a)) :
    (∫ sz, coordinateLinear n a sz.2*g sz.1 sz.2 ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ sz,
        g sz.1 sz.2*fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j)
          sz.2 (coordinateVector n a) ∂hierarchyGaussianLaw n m U := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  have H := spinGaussian_directional_stein n (hierarchyPotential n m U) g
    (hierarchyPotential_boundedDerivs n m U) hc hg hdg a
  have hz (sz : S × ParameterSpace n) :
      fderiv ℝ (g sz.1) sz.2 (coordinateVector n a) = 0 :=
    (hig sz.1).fderiv_zero ((hc sz.1).differentiable (by norm_num)) sz.2
  simp_rw [hz,integral_zero,zero_add] at H
  rw [H]
  simp_rw [hierarchyPotential_directional_cancellation n m U j _ _ hU hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with sz
  ring

end SharedPrefix
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

theorem hierarchyMomentLevel_tower (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (j l : Fin (n+1)) (hjl : j ≤ l) :
    hierarchyMomentLevel n m f (hierarchyMomentLevel n m f g l) j =
      hierarchyMomentLevel n m f g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hjl
    refine Fin.lastCases (fun hjl => ?_) (fun j hjl => ?_) j
    · have hl : l = Fin.last (n+1) := le_antisymm (Fin.le_last l) hjl
      subst l
      simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hjl
      refine Fin.lastCases (fun _ => ?_) (fun l hjl => ?_) l
      · simp only [hierarchyMomentLevel,Fin.lastCases_last]
      · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf]
        funext z
        exact congrFun (ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j l hjl) z.1

end SK.Analytic

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_moment_orthogonality (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (j l : Fin (n+1)) (hjl : j ≤ l) (x : ℝ) :
    let A := hierarchyMomentLevel n m f g j
    let B := hierarchyMomentLevel n m f g l
    (∫ z, (B z-A z)^2 ∂hierarchyPathLaw n m f x) =
      (∫ z, (B z)^2 ∂hierarchyPathLaw n m f x)-
      ∫ z, (A z)^2 ∂hierarchyPathLaw n m f x := by
  dsimp only
  let A := hierarchyMomentLevel n m f g j
  let B := hierarchyMomentLevel n m f g l
  let μ := hierarchyPathLaw n m f x
  have hA := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb j
  have hB := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb l
  have bounded (u v : ParameterSpace n → ℝ) (hu : ∀ z, ‖u z‖ ≤ C) (hv : ∀ z, ‖v z‖ ≤ C)
      (z) : ‖u z*v z‖ ≤ C*C := by
    rw [norm_mul]
    exact mul_le_mul (hu z) (hv z) (norm_nonneg _) hC
  have ihAA : Integrable (fun z => A z*A z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hA.1.mul hA.1) (bounded A A hA.2 hA.2) x
  have ihBB : Integrable (fun z => B z*B z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hB.1.mul hB.1) (bounded B B hB.2 hB.2) x
  have ihAB : Integrable (fun z => A z*B z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hA.1.mul hB.1) (bounded A B hA.2 hB.2) x
  have ht := hierarchyPathLaw_prefix_mul n m f B g hf hB.1 hg hC hC hB.2 hb j x
  rw [hierarchyMomentLevel_tower n m f g hf j l hjl] at ht
  change (∫ z, A z*B z ∂μ) = ∫ z, A z*A z ∂μ at ht
  change (∫ z, (B z-A z)^2 ∂μ) = (∫ z, (B z)^2 ∂μ)-∫ z, (A z)^2 ∂μ
  have he : (fun z => (B z-A z)^2) = fun z => B z*B z-(2*(A z*B z))+A z*A z := by
    funext z
    ring
  rw [he]
  have ha := integral_add (μ := μ)
    (f := fun z => B z*B z-2*(A z*B z)) (g := fun z => A z*A z)
    (ihBB.sub (ihAB.const_mul 2)) ihAA
  rw [ha]
  have hs := integral_sub (μ := μ)
    (f := fun z => B z*B z) (g := fun z => 2*(A z*B z)) ihBB (ihAB.const_mul 2)
  rw [hs,integral_const_mul,ht]
  simp only [pow_two]
  ring

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

theorem hierarchyMomentLevel_family {I : Type} (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (g : I → ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (F : (I → ℝ) → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => F (fun i => hierarchyMomentLevel n m f (g i) j z)) j =
      fun z => F (fun i => hierarchyMomentLevel n m f (g i) j z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      let G : ParameterSpace n → ℝ := fun z => F (fun i =>
        hierarchyMomentLevel n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
          (gaussianAverage (m (Fin.last n)) f (g i)) j z)
      change (fun z : ParameterSpace (n+1) => hierarchyMomentLevel n (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) f) (gaussianAverage (m (Fin.last n)) f (fun z => G z.1)) j z.1) =
        fun z : ParameterSpace (n+1) => G z.1
      rw [gaussianAverage_const_prefix hf]
      funext z
      exact congrFun (ih (fun i => m i.castSucc) _ (fun i => gaussianAverage (m (Fin.last n)) f (g i))
        (hf.gaussianStep _) j) z.1

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

theorem hierarchyMomentLevel_fixed_family {I : Type} (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (g : I → ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (j : Fin (n+1))
    (hg : ∀ i, hierarchyMomentLevel n m f (g i) j = g i) (F : (I → ℝ) → ℝ) :
    hierarchyMomentLevel n m f (fun z => F (fun i => g i z)) j = fun z => F (fun i => g i z) := by
  have H := hierarchyMomentLevel_family n m f g hf F j
  simpa only [hg] using H

theorem hierarchyMomentLevel_fixed_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1))
    (hg : hierarchyMomentLevel n m f g j = g) (hh : hierarchyMomentLevel n m f h j = h) :
    hierarchyMomentLevel n m f (fun z => g z*h z) j = fun z => g z*h z := by
  let G : Bool → ParameterSpace n → ℝ := fun b => if b then g else h
  have hr (b : Bool) : hierarchyMomentLevel n m f (G b) j = G b := by
    cases b <;> assumption
  exact hierarchyMomentLevel_fixed_family n m f G hf j hr (fun a => a true*a false)

section SharedSpinTest
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyGaussian_integrable (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hg : ∀ s, HasExpGrowth (g s)) (hc : ∀ s, Continuous (g s)) :
    Integrable (fun sz => g sz.1 sz.2) (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussian_integrable n _ g (hierarchyPotential_boundedDerivs n m U) hg hc

theorem hierarchyGaussian_memLp_two (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hg : ∀ s, HasExpGrowth (g s)) (hc : ∀ s, Continuous (g s)) :
    MemLp (fun sz => g sz.1 sz.2) 2 (hierarchyGaussianLaw n m U) := by
  have hI := hierarchyGaussian_integrable n m U g hg hc
  rw [memLp_two_iff_integrable_sq hI.aestronglyMeasurable]
  simpa only [pow_two] using hierarchyGaussian_integrable n m U (fun s z => g s z*g s z)
    (fun s => (hg s).mul (hg s)) (fun s => (hc s).mul (hc s))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in

theorem hierarchyLevel_shared_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (j : Fin (n+1))
    (u v : ParameterSpace n) (hu : TailZero n j u) (hv : PrefixZero n j v)
    (hU : ∀ s, U s u = c s) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z (u+v) =
      hierarchySpinMean n m U c j z := by
  rw [map_add]
  have H := (hierarchyLevel_invariant_of_prefix n m _ v j hv).fderiv_zero
    ((hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j).1.differentiable (by norm_num)) z
  rw [H,add_zero]
  exact congrFun (hierarchyLevel_spinMean n m U c j u hu hU) z

theorem hierarchyGaussian_retained_stein (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (h : ParameterSpace n → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hc : ∀ s, ‖c s‖ ≤ C) (hb : ∀ z, ‖h z‖ ≤ D)
    (hcont : ContDiff ℝ 1 h) (hdh : HasExpGrowth (fderiv ℝ h))
    (a : Fin n → ℝ) (j l : Fin (n+1)) (hjl : j ≤ l)
    (u v : ParameterSpace n) (ha : coordinateVector n a = u+v)
    (hu : TailZero n j u) (hv : PrefixZero n j v) (huc : ∀ s, U s u = c s)
    (hU : ∀ s, U s (coordinateVector n a) = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n a))
    (hih : TranslationInvariant h (coordinateVector n a))
    (hf : hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U) h l = h) :
    (∫ sz, coordinateLinear n a sz.2*(c sz.1*h sz.2) ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ z,
        (hierarchySpinMean n m U c j z*hierarchySpinMean n m U c l z)*h z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let f := affineLogPartition (fun _ => 0) U
  have hfr := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hgb := HasExpGrowth.of_bounded hD hb
  have hs := hierarchyGaussian_shared_stein n m U (fun s z => c s*h z)
    (fun _ => contDiff_const.mul hcont)
    (fun s => (HasExpGrowth.const (c s)).mul hgb)
    (fun s => by
      have he : fderiv ℝ (fun z : ParameterSpace n => c s*h z) =
          fun z => c s • fderiv ℝ h z := by
        funext z
        exact ((hcont.differentiable (by norm_num) z).hasFDerivAt.const_mul (c s)).fderiv
      rw [he]
      exact (HasExpGrowth.const (c s)).smul hdh)
    a j hU hi (fun s z t => congrArg (fun r => c s*r) (hih z t))
  have Hder (z : ParameterSpace n) : fderiv ℝ (hierarchyLevel n m f j) z (coordinateVector n a) =
      hierarchySpinMean n m U c j z := by
    rw [ha]
    exact hierarchyLevel_shared_gradient n m U c j u v hu hv huc z
  dsimp only [f] at Hder
  simp_rw [Hder] at hs
  rw [hs]
  congr 1
  let A := hierarchySpinMean n m U c j
  let B := hierarchySpinMean n m U c l
  have hA := hierarchySpinMean_regular n m U c hC hc j
  have hB := hierarchySpinMean_regular n m U c hC hc l
  have hAc : Continuous A := hA.1
  have hAb : ∀ z, ‖A z‖ ≤ C := hA.2
  have hhp : ∀ z, ‖h z*A z‖ ≤ D*C := by
    intro z
    rw [norm_mul]
    exact mul_le_mul (hb z) (hAb z) (norm_nonneg _) hD
  have hfixA : hierarchyMomentLevel n m f A l = A :=
    hierarchyMomentLevel_retained n m f _ hfr j l hjl
  have hfix := hierarchyMomentLevel_fixed_mul n m f h A hfr l hf hfixA
  have hmarg := hierarchyGaussian_terminal_marginal n m U c (fun z => h z*A z)
    (hcont.continuous.mul hAc) (hgb.mul (HasExpGrowth.of_bounded hC hAb))
  have ht := hierarchyPathLaw_fixed_mul n m f (affineMoment (fun _ => 0) U c)
    (fun z => h z*A z) hfr (affineMoment_continuous (fun _ => 0) U c)
    (hcont.continuous.mul hAc) hC (mul_nonneg hD hC)
    (affineMoment_norm_le (fun _ => 0) U c hc) hhp l hfix 0
  calc
    _ = ∫ sz, c sz.1*(h sz.2*A sz.2) ∂hierarchyGaussianLaw n m U := by
      apply integral_congr_ae
      filter_upwards [] with sz
      ring
    _ = ∫ z, affineMoment (fun _ => 0) U c z*(h z*A z) ∂hierarchyPathLaw n m f 0 := hmarg
    _ = ∫ z, (h z*A z)*affineMoment (fun _ => 0) U c z ∂hierarchyPathLaw n m f 0 := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = ∫ z, (h z*A z)*B z ∂hierarchyPathLaw n m f 0 := ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
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

theorem TailZero.add {n : ℕ} {j : Fin (n+1)} {u v : ParameterSpace n}
    (hu : TailZero n j u) (hv : TailZero n j v) : TailZero n j (u+v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    revert hu hv
    refine Fin.lastCases (fun _ _ => by simp only [TailZero,Fin.lastCases_last]) (fun j hu hv => ?_) j
    simp only [TailZero,Fin.lastCases_castSucc] at hu hv ⊢
    exact ⟨by simp only [Prod.snd_add,hu.1,hv.1,add_zero],ih hu.2 hv.2⟩

theorem TailZero.smul {n : ℕ} {j : Fin (n+1)} {u : ParameterSpace n}
    (hu : TailZero n j u) (c : ℝ) : TailZero n j (c • u) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    revert hu
    refine Fin.lastCases (fun _ => by simp only [TailZero,Fin.lastCases_last]) (fun j hu => ?_) j
    simp only [TailZero,Fin.lastCases_castSucc] at hu ⊢
    exact ⟨by simp only [Prod.smul_snd,hu.1,smul_zero],ih hu.2⟩

theorem PrefixZero.add {n : ℕ} {j : Fin (n+1)} {u v : ParameterSpace n}
    (hu : PrefixZero n j u) (hv : PrefixZero n j v) : PrefixZero n j (u+v) := by
  induction n with
  | zero => change u = 0 at hu; change v = 0 at hv; simp [hu,hv,PrefixZero]
  | succ n ih =>
    revert hu hv
    refine Fin.lastCases (fun hu hv => ?_) (fun j hu hv => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hu hv ⊢
      rw [hu,hv,add_zero]
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hu hv ⊢
      exact ih hu hv

theorem PrefixZero.smul {n : ℕ} {j : Fin (n+1)} {u : ParameterSpace n}
    (hu : PrefixZero n j u) (c : ℝ) : PrefixZero n j (c • u) := by
  induction n with
  | zero => change u = 0 at hu; simp [hu,PrefixZero]
  | succ n ih =>
    revert hu
    refine Fin.lastCases (fun hu => ?_) (fun j hu => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hu ⊢
      rw [hu,smul_zero]
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hu ⊢
      exact ih hu

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

theorem hierarchyLevel_pair_invariance (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (i₁ i₂ : Fin n) (c₁ c₂ : ℝ) (hi : i₁ ≤ i₂)
    (ht : TranslationInvariant f (c₁ • coordinateAxis n i₁+c₂ • coordinateAxis n i₂))
    (j : Fin (n+1)) (hj : j.val ≤ i₁.val ∨ i₂.val < j.val) :
    TranslationInvariant (hierarchyLevel n m f j) (c₁ • coordinateAxis n i₁+c₂ • coordinateAxis n i₂) := by
  rcases hj with hj | hj
  · apply hierarchyLevel_invariant_of_prefix
    exact ((prefixZero_coordinateAxis n i₁ j hj).smul c₁).add
      ((prefixZero_coordinateAxis n i₂ j (hj.trans hi)).smul c₂)
  · apply hierarchyLevel_invariant_of_tail n m f _ ht
    exact ((tailZero_coordinateAxis n i₁ j ((show i₁.val ≤ i₂.val from hi).trans_lt hj)).smul c₁).add
      ((tailZero_coordinateAxis n i₂ j hj).smul c₂)

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

theorem normalizedDot_self {N : ℕ} (a : Fin N → ℝ) :
    normalizedDot a a = normalizedSquare a := by simp [normalizedDot,normalizedSquare,pow_two]

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

theorem normalizedDot_sub_right {N : ℕ} (a b c : Fin N → ℝ) :
    normalizedDot a (fun i => b i-c i) = normalizedDot a b-normalizedDot a c := by
  simp only [normalizedDot,mul_sub,Finset.sum_sub_distrib,sub_div]

theorem normalizedDot_comm {N : ℕ} (a b : Fin N → ℝ) : normalizedDot a b = normalizedDot b a := by
  simp only [normalizedDot,mul_comm]

theorem mean_cross_replacement {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |normalizedDot a b-normalizedSquare a| ≤ Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  rw [← normalizedDot_self,← normalizedDot_sub_right]
  calc
    _ ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
      abs_normalizedDot_le _ _
    _ ≤ 1*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
    _ = _ := one_mul _

theorem mean_square_replacement {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |normalizedSquare b-normalizedSquare a| ≤ 2*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  have he : normalizedSquare b-normalizedSquare a =
      normalizedDot b (fun i => b i-a i)+normalizedDot a (fun i => b i-a i) := by
    rw [normalizedDot_sub_right,normalizedDot_sub_right,normalizedDot_self,normalizedDot_self,
      normalizedDot_comm b a]
    ring
  rw [he]
  have H (c : Fin N → ℝ) (hc : ∀ i, |c i| ≤ 1) :
      |normalizedDot c (fun i => b i-a i)| ≤ Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
    calc
      _ ≤ Real.sqrt (normalizedSquare c)*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
        abs_normalizedDot_le _ _
      _ ≤ 1*Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
        mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one c hc))
          (Real.sqrt_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ |normalizedDot b (fun i => b i-a i)|+|normalizedDot a (fun i => b i-a i)| := abs_add_le _ _
    _ ≤ Real.sqrt (normalizedSquare (fun i => b i-a i))+Real.sqrt (normalizedSquare (fun i => b i-a i)) :=
      add_le_add (H b hb) (H a ha)
    _ = _ := by ring

theorem mean_variance_replacement {N : ℕ} (a b : Fin N → ℝ) (r : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |(normalizedDot a b-r)*normalizedSquare b-
      (normalizedSquare a-r)*normalizedSquare a| ≤
      3*Real.sqrt (normalizedSquare (fun i => b i-a i)) := by
  have hA := normalizedSquare_le_one a ha
  have hA₀ := normalizedSquare_nonneg a
  have hB := normalizedSquare_le_one b hb
  have hB₀ := normalizedSquare_nonneg b
  have hAr : |normalizedSquare a-r| ≤ 1 := abs_le.2 ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have he : (normalizedDot a b-r)*normalizedSquare b-
      (normalizedSquare a-r)*normalizedSquare a =
      (normalizedDot a b-normalizedSquare a)*normalizedSquare b+
      (normalizedSquare a-r)*(normalizedSquare b-normalizedSquare a) := by ring
  rw [he]
  calc
    _ ≤ |(normalizedDot a b-normalizedSquare a)*normalizedSquare b|+
        |(normalizedSquare a-r)*(normalizedSquare b-normalizedSquare a)| := abs_add_le _ _
    _ = |normalizedDot a b-normalizedSquare a| *normalizedSquare b+
        |normalizedSquare a-r| *|normalizedSquare b-normalizedSquare a| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hB₀]
    _ ≤ Real.sqrt (normalizedSquare (fun i => b i-a i))*1+
        1*(2*Real.sqrt (normalizedSquare (fun i => b i-a i))) := by
      exact add_le_add
        (mul_le_mul (mean_cross_replacement a b ha) hB hB₀ (Real.sqrt_nonneg _))
        (mul_le_mul hAr (mean_square_replacement a b ha hb) (abs_nonneg _) (by norm_num))
    _ = _ := by ring
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanSquare
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_fixed {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
      (hierarchyMeanSquare n m U c j) j = hierarchyMeanSquare n m U c j := by
  exact hierarchyMomentLevel_family n m _ (fun i => affineMoment (fun _ => 0) U (c i))
    (affineLogPartition_boundedDerivs (fun _ => 0) U) normalizedSquare j

theorem hierarchyMeanSquare_eq_gradient {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s) :
    hierarchyMeanSquare n m U c j = fun z => (N : ℝ)⁻¹ *
      gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u z := by
  funext z
  simp only [hierarchyMeanSquare,normalizedSquare,gradientSquareSum,
    hierarchyLevel_spinMean n m U _ j _ (hu _) (hU _),← pow_two]
  ring

theorem hierarchyMeanSquare_regular {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s) :
    ContDiff ℝ 1 (hierarchyMeanSquare n m U c j) ∧
      HasExpGrowth (hierarchyMeanSquare n m U c j) ∧
      HasExpGrowth (fderiv ℝ (hierarchyMeanSquare n m U c j)) := by
  rw [hierarchyMeanSquare_eq_gradient n m U c j u hu hU]
  have H := gradientSquareSum_regular
    (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j)
    (hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j) u
  refine ⟨contDiff_const.mul H.1,(HasExpGrowth.const _).mul H.2.1,?_⟩
  have he : fderiv ℝ (fun z => (N : ℝ)⁻¹ *
      gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u z) =
      fun z => (N : ℝ)⁻¹ • fderiv ℝ
        (gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u) z := by
    funext z
    exact ((H.1.differentiable (by norm_num) z).hasFDerivAt.const_mul _).fderiv
  rw [he]
  exact (HasExpGrowth.const _).smul H.2.2

theorem hierarchyMeanSquare_invariant {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1))
    (u : Fin N → ParameterSpace n) (hu : ∀ i, TailZero n j (u i)) (hU : ∀ i s, U s (u i) = c i s)
    (v : ParameterSpace n) (hv : TranslationInvariant
      (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) v) :
    TranslationInvariant (hierarchyMeanSquare n m U c j) v := by
  rw [hierarchyMeanSquare_eq_gradient n m U c j u hu hU]
  intro z t
  dsimp only
  rw [(hv.gradientSquareSum u) z t]
end MeanSquare

section MeanSquareStein
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyMeanSquare_stein {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (hc : ∀ i s, ‖c i s‖ ≤ 1)
    (a : Fin N → Fin n → ℝ) (j l : Fin (n+1)) (hjl : j ≤ l)
    (u v : Fin N → ParameterSpace n) (ha : ∀ i, coordinateVector n (a i) = u i+v i)
    (hu : ∀ i, TailZero n j (u i)) (hv : ∀ i, PrefixZero n j (v i))
    (huc : ∀ i s, U s (u i) = c i s) (hU : ∀ i s, U s (coordinateVector n (a i)) = 0)
    (hi : ∀ i k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n (a i)))
    (ul : Fin N → ParameterSpace n) (hul : ∀ i, TailZero n l (ul i))
    (hulc : ∀ i s, U s (ul i) = c i s)
    (hil : ∀ i, TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) l)
      (coordinateVector n (a i))) (i : Fin N) :
    (∫ sz, coordinateLinear n (a i) sz.2*(c i sz.1*hierarchyMeanSquare n m U c l sz.2)
      ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ z,
        (hierarchySpinMean n m U (c i) j z*hierarchySpinMean n m U (c i) l z)*
          hierarchyMeanSquare n m U c l z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  have Hr := hierarchyMeanSquare_regular n m U c l ul hul hulc
  have hb (z : ParameterSpace n) : ‖hierarchyMeanSquare n m U c l z‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc l z).1]
    exact (hierarchyMeanSquare_bounds n m U c hc l z).2
  exact hierarchyGaussian_retained_stein n m U (c i) _ (C := 1) (D := 1)
    (by norm_num) (by norm_num) (hc i) hb Hr.1 Hr.2.2 (a i) j l hjl
    (u i) (v i) (ha i) (hu i) (hv i) (huc i) (hU i) (hi i)
    (hierarchyMeanSquare_invariant n m U c l ul hul hulc _ (hil i))
    (hierarchyMeanSquare_fixed n m U c l)
end MeanSquareStein
end SK.Analytic
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

theorem hierarchyMean_increment_identity {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j l : Fin (n+1)) (hjl : j ≤ l) :
    (∫ z, normalizedSquare (fun i => hierarchySpinMean n m U (c i) l z-
        hierarchySpinMean n m U (c i) j z)
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) =
      hierarchyMeanOverlap n m U c l-hierarchyMeanOverlap n m U c j := by
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  let μ := hierarchyPathLaw n m f 0
  have hr (i : Fin N) (k : Fin (n+1)) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) k
  have hI (i : Fin N) (k : Fin (n+1)) : Integrable (fun z => (hierarchySpinMean n m U (c i) k z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf ((hr i k).1.pow 2) (C := 1)
      (fun z => by dsimp only [Pi.pow_apply]; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ((hr i k).2 z)) 0
  have hInc (i : Fin N) : Integrable (fun z => (hierarchySpinMean n m U (c i) l z-
      hierarchySpinMean n m U (c i) j z)^2) μ := by
    apply hierarchyPathLaw_integrable n m f _ hf (((hr i l).1.sub (hr i j).1).pow 2) (C := 4) _ 0
    intro z
    have h := (norm_sub_le (hierarchySpinMean n m U (c i) l z) (hierarchySpinMean n m U (c i) j z)).trans
      (add_le_add ((hr i l).2 z) ((hr i j).2 z))
    dsimp only [Pi.pow_apply,Pi.sub_apply]
    rw [norm_pow]
    nlinarith [norm_nonneg (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)]
  have horth (i : Fin N) := hierarchyPathLaw_moment_orthogonality n m f (affineMoment (fun _ => 0) U (c i))
    hf (affineMoment_continuous (fun _ => 0) U (c i)) (by norm_num : (0 : ℝ) ≤ 1)
    (affineMoment_norm_le (fun _ => 0) U (c i) (hc i)) j l hjl 0
  change (∫ z, (∑ i, (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)^2)/(N : ℝ) ∂μ) =
    (∫ z, (∑ i, (hierarchySpinMean n m U (c i) l z)^2)/(N : ℝ) ∂μ)-
      (∫ z, (∑ i, (hierarchySpinMean n m U (c i) j z)^2)/(N : ℝ) ∂μ)
  rw [integral_div,integral_div,integral_div,
    integral_finsetSum _ (fun i _ => hInc i),
    integral_finsetSum _ (fun i _ => hI i l),integral_finsetSum _ (fun i _ => hI i j)]
  have he : (∑ i, ∫ z, (hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z)^2 ∂μ) =
      ∑ i, ((∫ z, (hierarchySpinMean n m U (c i) l z)^2 ∂μ)-
      (∫ z, (hierarchySpinMean n m U (c i) j z)^2 ∂μ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact horth i
  rw [he,Finset.sum_sub_distrib,sub_div]

theorem hierarchyMeanOverlap_mono {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) : Monotone (hierarchyMeanOverlap n m U c) := by
  intro j l hjl
  have H := integral_nonneg (μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)
    (f := fun z => normalizedSquare (fun i => hierarchySpinMean n m U (c i) l z-hierarchySpinMean n m U (c i) j z))
    (fun z => normalizedSquare_nonneg _)
  rw [hierarchyMean_increment_identity n m U c hc j l hjl] at H
  exact sub_nonneg.mp H
end MeanTower
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

theorem blockLevel_injective (D N k : ℕ) (hN : 0 < N) :
    Function.Injective (blockLevel D N k) := by
  intro a b hab
  apply Fin.ext
  have h := congrArg Fin.val hab
  simp only [blockLevel_val] at h
  exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel h))

theorem fieldIndex_lt_level (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    (fieldIndex D N k b i).val < (blockLevel D N k b).val := by
  simp only [fieldIndex_val,blockLevel_val]
  nlinarith [i.isLt]

theorem fieldIndex_mono_block (D N k : ℕ) (a b : Fin (k+1)) (hab : a ≤ b) (i : Fin N) :
    fieldIndex D N k a i ≤ fieldIndex D N k b i := by
  change D+a.val*N+i.val ≤ D+b.val*N+i.val
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right N hab) D) i.val

theorem blockLevel_mono (D N k : ℕ) : Monotone (blockLevel D N k) := by
  intro a b hab
  change D+(a.val+1)*N ≤ D+(b.val+1)*N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right N (Nat.add_le_add_right hab 1)) D

theorem blockAtom_sum (D N k : ℕ) : ∑ t, blockAtom D N k t = 1 := by
  unfold blockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem blockAtom_at (D N k : ℕ) (hN : 0 < N) (b : Fin (k+1)) :
    blockAtom D N k (blockLevel D N k b) = ((k+1 : ℕ) : ℝ)⁻¹ := by
  unfold blockAtom
  have he (a : Fin (k+1)) : blockLevel D N k a = blockLevel D N k b ↔ a=b :=
    (blockLevel_injective D N k hN).eq_iff
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem blockAtom_zero_off (D N k : ℕ) (t : Fin (blockDimension D N k+1))
    (ht : ∀ b, blockLevel D N k b ≠ t) : blockAtom D N k t = 0 := by
  simp only [blockAtom,ht,ite_false,Finset.sum_const_zero]

theorem hierarchyAtom_blockMass (D N k : ℕ) (t : Fin (blockDimension D N k+1)) :
    hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 t = blockAtom D N k t := by
  rw [← blockAtom_sum D N k]
  exact hierarchyAtom_massFromAtoms _ _ t

theorem blockLevel_outside_pair (D N k : ℕ) (j : Fin k) (i : Fin N) (b : Fin (k+1))
    (hb : b ≠ j.castSucc) :
    (blockLevel D N k b).val ≤ (fieldIndex D N k j.castSucc i).val ∨
      (fieldIndex D N k j.succ i).val < (blockLevel D N k b).val := by
  have hjb : b.val ≠ j.val := by intro h; apply hb; exact Fin.ext h
  simp only [blockLevel_val,fieldIndex_val,Fin.val_castSucc,Fin.val_succ]
  rcases lt_or_gt_of_ne hjb with h | h
  · left
    have hh : (b.val+1)*N ≤ j.val*N := Nat.mul_le_mul_right N h
    omega
  · right
    have hh : (j.val+1)*N ≤ b.val*N := Nat.mul_le_mul_right N h
    nlinarith [i.isLt]

theorem blockLevel_prefix_second (D N k : ℕ) (j : Fin k) (i : Fin N) :
    (blockLevel D N k j.castSucc).val ≤ (fieldIndex D N k j.succ i).val := by
  simp only [blockLevel_val,fieldIndex_val,Fin.val_castSucc,Fin.val_succ]
  omega
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem coordinateVector_pair (n : ℕ) (p q : Fin n) (a b : ℝ) :
    coordinateVector n (pairCoefficients n p q a b) = a • coordinateAxis n p+b • coordinateAxis n q := by
  simp only [coordinateVector,pairCoefficients,add_smul,Finset.sum_add_distrib,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coordinateLinear_pair (n : ℕ) (p q : Fin n) (a b : ℝ) (z : ParameterSpace n) :
    coordinateLinear n (pairCoefficients n p q a b) z =
      a*coordinateProjection n p z+b*coordinateProjection n q z := by
  simp only [coordinateLinear_apply,pairCoefficients,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

section BlockSpin
variable {N D k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem retainedFieldDirection_spin (b : Fin (k+1)) (i : Fin N) (s : Config N) :
    U s (retainedFieldDirection D N k Δ b i) = spin (s i) := by
  simp only [retainedFieldDirection,map_smul,smul_eq_mul,hU]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (hΔ b)),one_mul]

theorem sharedField_termination (j : Fin k) (i : Fin N) (s : Config N) :
    U s (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) = 0 := by
  rw [sharedFieldCoefficients,coordinateVector_pair,map_add]
  rw [neg_smul,map_neg]
  change U s (retainedFieldDirection D N k Δ j.castSucc i) -
    U s (retainedFieldDirection D N k Δ j.succ i) = 0
  rw [retainedFieldDirection_spin U Δ hΔ hU,retainedFieldDirection_spin U Δ hΔ hU,sub_self]

theorem sharedField_level_invariant (j : Fin k) (i : Fin N) (b : Fin (k+1)) (hb : b ≠ j.castSucc) :
    TranslationInvariant (hierarchyLevel (blockDimension D N k) (blockMass D N k)
      (affineLogPartition (fun _ => 0) U) (blockLevel D N k b))
      (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) := by
  have ht := affineLogPartition_translation (fun _ => 0) U _ (sharedField_termination U Δ hΔ hU j i)
  rw [sharedFieldCoefficients,coordinateVector_pair] at ht ⊢
  exact hierarchyLevel_pair_invariance _ _ _ _ _ _ _
    (fieldIndex_mono_block D N k _ _ (by exact Nat.le_succ _) i) ht _
    (blockLevel_outside_pair D N k j i b hb)

theorem sharedField_atom_cancellation (j : Fin k) (i : Fin N)
    (t : Fin (blockDimension D N k+1)) (ht : t ≠ blockLevel D N k j.castSucc) :
    hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 t = 0 ∨
      TranslationInvariant (hierarchyLevel (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) U) t)
        (coordinateVector (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i)) := by
  by_cases hb : ∃ b, blockLevel D N k b = t
  · obtain ⟨b,rfl⟩ := hb
    right
    apply sharedField_level_invariant U Δ hΔ hU j i b
    intro h
    exact ht (congrArg (blockLevel D N k) h)
  · left
    rw [hierarchyAtom_blockMass]
    exact blockAtom_zero_off D N k t (not_exists.mp hb)

theorem blockMeanSquare_stein (j : Fin k) (i : Fin N) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    (∫ sz, coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*
      (c i sz.1*hierarchyMeanSquare n m U c L sz.2) ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 J * ∫ z,
        (hierarchySpinMean n m U (c i) J z*hierarchySpinMean n m U (c i) L z)*
          hierarchyMeanSquare n m U c L z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let u := retainedFieldDirection D N k Δ j.castSucc
  let v := fun i => -retainedFieldDirection D N k Δ j.succ i
  have hJL : blockLevel D N k j.castSucc ≤ blockLevel D N k j.succ :=
    blockLevel_mono D N k (show j.castSucc ≤ j.succ from Nat.le_succ _)
  have hu (i : Fin N) : TailZero n (blockLevel D N k j.castSucc) (u i) :=
    (tailZero_coordinateAxis n _ _ (fieldIndex_lt_level D N k j.castSucc i)).smul _
  have hv (i : Fin N) : PrefixZero n (blockLevel D N k j.castSucc) (v i) := by
    simpa only [v,retainedFieldDirection,neg_smul] using
      (prefixZero_coordinateAxis n _ _ (blockLevel_prefix_second D N k j i)).smul (-(Real.sqrt (Δ j.succ))⁻¹)
  have hul (i : Fin N) : TailZero n (blockLevel D N k j.succ) (u i) :=
    (tailZero_coordinateAxis n _ _ ((fieldIndex_lt_level D N k j.castSucc i).trans_le hJL)).smul _
  apply hierarchyMeanSquare_stein n (blockMass D N k) U (fun i s => spin (s i))
    (by intro i s; cases s i <;> norm_num [spin])
    (sharedFieldCoefficients D N k Δ j) _ _ hJL u v
    (by intro i; dsimp only [n]; simp only [sharedFieldCoefficients,coordinateVector_pair,u,v,retainedFieldDirection,neg_smul])
    hu hv (retainedFieldDirection_spin U Δ hΔ hU j.castSucc)
    (sharedField_termination U Δ hΔ hU j)
    (sharedField_atom_cancellation U Δ hΔ hU j)
    u hul (retainedFieldDirection_spin U Δ hΔ hU j.castSucc) _ i
  intro i
  apply sharedField_level_invariant U Δ hΔ hU j i j.succ
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_succ,Fin.val_castSucc] at hh
  omega
end BlockSpin
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

end FiniteCovariance
end SK.Analytic

end
end
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

theorem blockExponent_field {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) (s : Config N) :
    blockExponent I a v s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = v b*spin (s i) := by
  simp only [blockExponent,spinExponent,coordinateLinear_coordinateAxis,blockCoefficients_field,
    blockInteraction_field,spinMonomial,Finset.prod_singleton]

theorem blockExponent_expansion {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (s : Config N) (z : ParameterSpace (blockDimension D N k)) :
    blockExponent I a v s z =
      (∑ t : Fin D, a t*spinMonomial s (I t)*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) t) z)+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*spin (s i)*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  unfold blockExponent spinExponent
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*
    spinMonomial s {(finProdFinEquiv.symm t).2}*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,spinMonomial,Finset.prod_singleton,
    fieldIndex_eq_natAdd]

theorem blockFieldEnergy_exponent {D N k : ℕ} (I : Fin D → Finset (Fin N)) (v : Fin (k+1) → ℝ)
    (sz : Config N × ParameterSpace (blockDimension D N k)) :
    blockFieldEnergy v sz = blockExponent I (fun _ => 0) (fun b => v b/(N : ℝ)) sz.1 sz.2 := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,blockFieldEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section PathMarginal
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
theorem hierarchyGaussian_probability (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) : IsProbabilityMeasure (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussianLaw_probability n _ (hierarchyPotential_boundedDerivs n m U)

theorem hierarchyGaussian_path_marginal (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (h : ParameterSpace n → ℝ)
    (hc : Continuous h) (hg : HasExpGrowth h) :
    (∫ sz, h sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, h z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  have H := hierarchyGaussian_terminal_marginal n m U (fun _ => 1) h hc hg
  simpa only [affineMoment,mul_one,affineGibbs_sum,one_mul] using H
end PathMarginal

theorem sharedFieldEnergy_expansion (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k)
    (sz : Config N × ParameterSpace (blockDimension D N k)) :
    sharedFieldEnergy D N k Δ j sz =
      (∑ i, coordinateLinear (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i) sz.2*spin (sz.1 i))/(N : ℝ) := by
  unfold sharedFieldEnergy blockFieldEnergy
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sharedBlockWeights,pairCoefficients,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,sharedFieldCoefficients,coordinateLinear_pair]

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Integrals
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
theorem integral_normalized_sum_identity {N : ℕ} (A : Fin N → Ω → ℝ) (B : Fin N → Ω' → ℝ)
    (w : ℝ) (hA : ∀ i, Integrable (A i) μ) (hB : ∀ i, Integrable (B i) ν)
    (hid : ∀ i, (∫ z, A i z ∂μ) = -w*(∫ z, B i z ∂ν)) :
    (∫ z, (∑ i, A i z)/(N : ℝ) ∂μ) = -w*(∫ z, (∑ i, B i z)/(N : ℝ) ∂ν) := by
  rw [integral_div,integral_div,integral_finsetSum _ (fun i _ => hA i),
    integral_finsetSum _ (fun i _ => hB i)]
  simp only [hid,← Finset.mul_sum,mul_div_assoc]
end Integrals

section BlockMean
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem blockField_coordinate_mean (j : Fin k) (i : Fin N) :
    (∫ sz, coordinateLinear (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i) sz.2*
      spin (sz.1 i) ∂hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) =
      -hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 (blockLevel D N k j.castSucc) *
        ∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) U (fun s => spin (s i))
          (blockLevel D N k j.castSucc) z)^2
        ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let J := blockLevel D N k j.castSucc
  let u := retainedFieldDirection D N k Δ j.castSucc i
  let v := -retainedFieldDirection D N k Δ j.succ i
  have hu : TailZero n J u :=
    (tailZero_coordinateAxis n _ _ (fieldIndex_lt_level D N k j.castSucc i)).smul _
  have hv : PrefixZero n J v := by
    simpa only [v,retainedFieldDirection,neg_smul] using
      (prefixZero_coordinateAxis n _ _ (blockLevel_prefix_second D N k j i)).smul (-(Real.sqrt (Δ j.succ))⁻¹)
  have ha : coordinateVector n (sharedFieldCoefficients D N k Δ j i) = u+v := by
    dsimp only [n]
    simp only [sharedFieldCoefficients,coordinateVector_pair,u,v,retainedFieldDirection,neg_smul]
  have hf : hierarchyMomentLevel n (blockMass D N k) (affineLogPartition (fun _ => 0) U)
      (fun _ => (1 : ℝ)) J = fun _ => 1 := by
    exact hierarchyMomentLevel_family n (blockMass D N k) _ (fun (_ : Unit) (_ : ParameterSpace n) => (0 : ℝ))
      (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun _ => 1) J
  have H := hierarchyGaussian_retained_stein n (blockMass D N k) U (fun s => spin (s i))
    (fun _ => 1) (C := 1) (D := 1) (by norm_num) (by norm_num)
    (by intro s; cases s i <;> norm_num [spin]) (by intro z; norm_num) contDiff_const
    (by have he : fderiv ℝ (fun _ : ParameterSpace n => (1 : ℝ)) = fun _ => 0 := by
          funext z
          exact fderiv_const_apply 1
        rw [he]
        exact HasExpGrowth.const (E := ParameterSpace n) (0 : ParameterSpace n →L[ℝ] ℝ))
    (sharedFieldCoefficients D N k Δ j i) J J le_rfl u v ha hu hv
    (retainedFieldDirection_spin U Δ hΔ hU j.castSucc i)
    (sharedField_termination U Δ hΔ hU j i)
    (sharedField_atom_cancellation U Δ hΔ hU j i)
    (by intro z t; rfl) hf
  simpa only [mul_one,← pow_two] using H

theorem sharedFieldEnergy_mean (hN : 0 < N) (j : Fin k) :
    (∫ sz, sharedFieldEnergy D N k Δ j sz
      ∂hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) =
      -((k+1 : ℕ) : ℝ)⁻¹ *
        hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => spin (s i))
          (blockLevel D N k j.castSucc) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let J := blockLevel D N k j.castSucc
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hA (i : Fin N) : Integrable
      (fun sz => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*c i sz.1)
      (hierarchyGaussianLaw n m U) := by
    apply hierarchyGaussian_integrable n m U (fun s z => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) z*c i s)
    · intro s
      exact (HasExpGrowth.linear _).mul (HasExpGrowth.const _)
    · intro s
      exact (coordinateLinear n _).continuous.mul continuous_const
  have hB (i : Fin N) : Integrable
      (fun z => (hierarchySpinMean n m U (c i) J z)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
    have hr := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) J
    apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
      (hr.1.pow 2) (C := 1) _ 0
    intro z
    dsimp only [Pi.pow_apply]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hr.2 z)
  have H := integral_normalized_sum_identity _ _ (hierarchyAtom n m 1 J) hA hB
    (blockField_coordinate_mean U Δ hΔ hU j)
  simp only [sharedFieldEnergy_expansion]
  change _ = -((k+1 : ℕ) : ℝ)⁻¹ * ∫ z, (∑ i, (hierarchySpinMean n m U (c i) J z)^2)/(N : ℝ)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  rw [H]
  rw [show hierarchyAtom n m 1 J = ((k+1 : ℕ) : ℝ)⁻¹ by
    exact (hierarchyAtom_blockMass D N k J).trans (blockAtom_at D N k hN j.castSucc)]
end BlockMean
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section BoundedMeanObservable
variable {S : Type} [Fintype S] [Nonempty S]
theorem hierarchyMeanSquare_norm_le_one {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    ‖hierarchyMeanSquare n m U c j z‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

variable [MeasurableSpace S] [MeasurableSingletonClass S]
theorem hierarchyMeanSquare_joint_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    Integrable (fun sz => hierarchyMeanSquare n m U c j sz.2) (hierarchyGaussianLaw n m U) := by
  exact hierarchyGaussian_integrable n m U (fun _ => hierarchyMeanSquare n m U c j)
    (fun _ => HasExpGrowth.of_bounded (by norm_num) (hierarchyMeanSquare_norm_le_one n m U c hc j))
    (fun _ => hierarchyMeanSquare_continuous n m U c hc j)
end BoundedMeanObservable

section BlockTest
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem sharedFieldEnergy_meanSquare_test (hN : 0 < N) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    (∫ sz, sharedFieldEnergy D N k Δ j sz*hierarchyMeanSquare n m U c L sz.2
      ∂hierarchyGaussianLaw n m U) = -((k+1 : ℕ) : ℝ)⁻¹ *
        ∫ z, normalizedDot (fun i => hierarchySpinMean n m U (c i) J z)
          (fun i => hierarchySpinMean n m U (c i) L z)*hierarchyMeanSquare n m U c L z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let J := blockLevel D N k j.castSucc
  let L := blockLevel D N k j.succ
  let M := hierarchyMeanSquare n m U c L
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hMc : Continuous M := hierarchyMeanSquare_continuous n m U c hc L
  have hMb : ∀ z, ‖M z‖ ≤ 1 := hierarchyMeanSquare_norm_le_one n m U c hc L
  have hMg : HasExpGrowth M := HasExpGrowth.of_bounded (by norm_num) hMb
  have hmreg (b : Fin (n+1)) (i : Fin N) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) b
  have hA (i : Fin N) : Integrable
      (fun sz => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*(c i sz.1*M sz.2))
      (hierarchyGaussianLaw n m U) := by
    apply hierarchyGaussian_integrable n m U (fun s z => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) z*(c i s*M z))
    · intro s
      exact (HasExpGrowth.linear _).mul ((HasExpGrowth.const _).mul hMg)
    · intro s
      exact (coordinateLinear n _).continuous.mul (continuous_const.mul hMc)
  have hB (i : Fin N) : Integrable
      (fun z => (hierarchySpinMean n m U (c i) J z*hierarchySpinMean n m U (c i) L z)*M z)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
    apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
      (((hmreg J i).1.mul (hmreg L i).1).mul hMc) (C := 1) _ 0
    intro z
    simp only [Pi.mul_apply,norm_mul]
    have hp := mul_le_mul ((hmreg J i).2 z) ((hmreg L i).2 z) (norm_nonneg _) zero_le_one
    have hq := mul_le_mul hp (hMb z) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1*1)
    simpa only [one_mul] using hq
  have hId (i : Fin N) := blockMeanSquare_stein U Δ hΔ hU j i
  dsimp only at hId
  have H := integral_normalized_sum_identity _ _ (hierarchyAtom n m 1 J) hA hB hId
  have hAtom : hierarchyAtom n m 1 J = ((k+1 : ℕ) : ℝ)⁻¹ :=
    (hierarchyAtom_blockMass D N k J).trans (blockAtom_at D N k hN j.castSucc)
  rw [hAtom] at H
  simpa only [sharedFieldEnergy_expansion,normalizedDot,
    div_mul_eq_mul_div,Finset.sum_mul,mul_assoc] using H
end BlockTest
end SK.Analytic

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

theorem centered_bounded_test [IsProbabilityMeasure μ]
    (Y B : Ω → ℝ) (hY : MemLp Y 2 μ) (hB : AEStronglyMeasurable B μ)
    (hb : ∀ᵐ z ∂μ, |B z| ≤ 1) :
    |(∫ z, Y z*B z ∂μ)-(∫ z, Y z ∂μ)*(∫ z, B z ∂μ)| ≤
      Real.sqrt ((∫ z, (Y z)^2 ∂μ)-(∫ z, Y z ∂μ)^2) := by
  have hB₂ : MemLp B 2 μ := (memLp_const (1 : ℝ)).mono' hB hb
  have hB₁ := hB₂.integrable (by norm_num)
  have hc := hY.sub (memLp_const (∫ z, Y z ∂μ))
  have H := abs_integral_mul_le_sqrt_of_bound (μ := μ)
    (fun z => Y z-∫ z, Y z ∂μ) B hc hB hb
  have hl : (∫ z, (Y z-∫ z, Y z ∂μ)*B z ∂μ) =
      (∫ z, Y z*B z ∂μ)-(∫ z, Y z ∂μ)*(∫ z, B z ∂μ) := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun z => Y z*B z) (g := fun z => (∫ z, Y z ∂μ)*B z)
      (hY.integrable_mul hB₂) (hB₁.const_mul _),integral_const_mul]
  rw [hl] at H
  have hr : (∫ z, (Y z-∫ z, Y z ∂μ)^2 ∂μ) =
      (∫ z, (Y z)^2 ∂μ)-(∫ z, Y z ∂μ)^2 := by
    rw [← variance_eq_integral hY.aemeasurable]
    exact variance_eq_sub hY
  rwa [hr] at H
end Cauchy
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section JointBlockLp
variable {D N k : ℕ}
theorem sharedFieldEnergy_memLp_two
    (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (Δ : Fin (k+1) → ℝ) (j : Fin k) :
    MemLp (sharedFieldEnergy D N k Δ j) 2
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) := by
  let w := sharedBlockWeights k Δ j
  let I : Fin D → Finset (Fin N) := fun _ => ∅
  have he : sharedFieldEnergy D N k Δ j = fun sz =>
      blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ)) sz.1 sz.2 :=
    funext (blockFieldEnergy_exponent I w)
  rw [he]
  let L : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ :=
    blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ))
  have hg (s : Config N) : HasExpGrowth (fun z => L s z) := HasExpGrowth.linear (L s)
  have hc (s : Config N) : Continuous (fun z => L s z) := (L s).continuous
  exact hierarchyGaussian_memLp_two (blockDimension D N k) (blockMass D N k) U (fun s z => L s z) hg hc
end JointBlockLp

section CenteredBlockTest
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem sharedFieldEnergy_centered_test (hN : 0 < N) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    |(∫ z, normalizedDot (fun i => hierarchySpinMean n m U (c i) J z)
          (fun i => hierarchySpinMean n m U (c i) L z)*hierarchyMeanSquare n m U c L z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)-
      hierarchyMeanOverlap n m U c J * hierarchyMeanOverlap n m U c L| ≤
      ((k+1 : ℕ) : ℝ)*Real.sqrt (ProbabilityTheory.variance (sharedFieldEnergy D N k Δ j)
        (hierarchyGaussianLaw n m U)) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let L := blockLevel D N k j.succ
  let μ := hierarchyGaussianLaw n m U
  let M := hierarchyMeanSquare n m U c L
  let := hierarchyGaussian_probability n m U
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hMb : ∀ z, ‖M z‖ ≤ 1 := hierarchyMeanSquare_norm_le_one n m U c hc L
  have hY := sharedFieldEnergy_memLp_two U Δ j
  have hM := hierarchyMeanSquare_joint_integrable n m U c hc L
  have H := centered_bounded_test (μ := μ) (sharedFieldEnergy D N k Δ j) (fun sz => M sz.2)
    hY hM.aestronglyMeasurable (by filter_upwards [] with sz; exact hMb sz.2)
  have hp : (∫ sz, M sz.2 ∂μ) = hierarchyMeanOverlap n m U c L :=
    hierarchyGaussian_path_marginal n m U M (hierarchyMeanSquare_continuous n m U c hc L)
      (HasExpGrowth.of_bounded (by norm_num) hMb)
  have hv := variance_eq_sub hY
  dsimp only [Pi.pow_apply] at hv
  rw [← hv] at H
  rw [hp] at H
  have hmean := sharedFieldEnergy_mean U Δ hΔ hU hN j
  have htest := sharedFieldEnergy_meanSquare_test U Δ hΔ hU hN j
  dsimp only at htest
  rw [hmean,htest] at H
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hK : 0 < K := by dsimp only [K]; positivity
  have he (I r s : ℝ) : -K⁻¹*I-(-K⁻¹*r)*s = -K⁻¹*(I-r*s) := by ring
  rw [he,abs_mul,abs_neg,abs_inv,abs_of_pos hK] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  rw [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] at H'
  exact H'
end CenteredBlockTest
end SK.Analytic
namespace SK.Analytic
section SqrtIntegral
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_sqrt_le_sqrt_integral (d : Ω → ℝ) (hd : Integrable d μ) (hpos : ∀ z, 0 ≤ d z) :
    (∫ z, Real.sqrt (d z) ∂μ) ≤ Real.sqrt (∫ z, d z ∂μ) := by
  have hsm : AEStronglyMeasurable (fun z => Real.sqrt (d z)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hd.aestronglyMeasurable
  have hsq : (fun z => (Real.sqrt (d z))^2) = d := funext (fun z => Real.sq_sqrt (hpos z))
  have h₂ : MemLp (fun z => Real.sqrt (d z)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsm,hsq]
    exact hd
  have H := abs_integral_mul_le_sqrt_of_bound (μ := μ) (fun z => Real.sqrt (d z)) (fun _ => 1)
    h₂ aestronglyMeasurable_const (by filter_upwards [] with z; norm_num)
  simp only [mul_one] at H
  rw [hsq] at H
  exact (le_abs_self _).trans H
end SqrtIntegral

section MeanVariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalizedSquare_le_const {N : ℕ} (a : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) : normalizedSquare a ≤ C^2 := by
  by_cases hN : N=0
  · simp [normalizedSquare,hN,sq_nonneg C]
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (div_le_iff₀ hn).2
  calc
    (∑ i, (a i)^2) ≤ ∑ _ : Fin N, C^2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ha i,sq_abs (a i),abs_nonneg (a i)]
    _ = C^2*(N : ℝ) := by simp [mul_comm]

theorem normalizedSquare_measurable {N : ℕ} (a : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) : Measurable (fun z => normalizedSquare (a z)) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => (ha i).pow_const 2)

theorem normalizedDot_measurable {N : ℕ} (a b : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hb : ∀ i, Measurable (fun z => b z i)) :
    Measurable (fun z => normalizedDot (a z) (b z)) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => (ha i).mul (hb i))

theorem normalizedSquare_memLp {N : ℕ} (a : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z i, |a z i| ≤ C) :
    MemLp (fun z => normalizedSquare (a z)) 2 μ := by
  apply (memLp_const (C^2)).mono' (normalizedSquare_measurable a ha).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (normalizedSquare_nonneg _)]
  exact normalizedSquare_le_const (a z) C hC (hb z)

theorem abs_normalizedDot_le_one {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) : |normalizedDot a b| ≤ 1 := by
  have h₁ : Real.sqrt (normalizedSquare a) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
  have h₂ : Real.sqrt (normalizedSquare b) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one b hb)
  exact (abs_normalizedDot_le a b).trans (by nlinarith [Real.sqrt_nonneg (normalizedSquare a),Real.sqrt_nonneg (normalizedSquare b)])

theorem mean_variance_from_test {N : ℕ} (a b : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hb : ∀ i, Measurable (fun z => b z i))
    (ha₁ : ∀ z i, |a z i| ≤ 1) (hb₁ : ∀ z i, |b z i| ≤ 1) :
    let M := fun z => normalizedSquare (a z)
    let T := fun z => normalizedSquare (b z)
    let r := ∫ z, M z ∂μ
    ProbabilityTheory.variance M μ ≤
      |(∫ z, normalizedDot (a z) (b z)*T z ∂μ)-r*(∫ z, T z ∂μ)|+
        3*Real.sqrt (∫ z, normalizedSquare (fun i => b z i-a z i) ∂μ) := by
  let M := fun z => normalizedSquare (a z)
  let T := fun z => normalizedSquare (b z)
  let Q := fun z => normalizedDot (a z) (b z)
  let d := fun z => normalizedSquare (fun i => b z i-a z i)
  let r := ∫ z, M z ∂μ
  have hM : MemLp M 2 μ := normalizedSquare_memLp a ha 1 (by norm_num) ha₁
  have hT : MemLp T 2 μ := normalizedSquare_memLp b hb 1 (by norm_num) hb₁
  have hQ : MemLp Q 2 μ := by
    apply (memLp_const (1 : ℝ)).mono' (normalizedDot_measurable a b ha hb).aestronglyMeasurable
    filter_upwards [] with z
    exact abs_normalizedDot_le_one (a z) (b z) (ha₁ z) (hb₁ z)
  have hd : Integrable d μ := by
    apply (normalizedSquare_memLp (fun z i => b z i-a z i)
      (fun i => (hb i).sub (ha i)) 2 (by norm_num) ?_).integrable (by norm_num)
    intro z i
    exact (abs_sub (b z i) (a z i)).trans (by linarith [ha₁ z i,hb₁ z i])
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨integral_nonneg (fun z => normalizedSquare_nonneg _),?_⟩
    calc
      r ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono (hM.integrable (by norm_num)) (integrable_const 1)
        (fun z => normalizedSquare_le_one _ (ha₁ z))
      _ = 1 := by simp
  let F := fun z => (Q z-r)*T z
  let G := fun z => (M z-r)*M z
  have hF : Integrable F μ := (hQ.sub (memLp_const r)).integrable_mul hT
  have hG : Integrable G μ := (hM.sub (memLp_const r)).integrable_mul hM
  have hFid : (∫ z, F z ∂μ) = (∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ) := by
    simp only [F,sub_mul]
    rw [integral_sub (f := fun z => Q z*T z) (g := fun z => r*T z) (hQ.integrable_mul hT) ((hT.integrable (by norm_num)).const_mul r),integral_const_mul]
  have hGid : (∫ z, G z ∂μ) = ProbabilityTheory.variance M μ := by
    simp only [G,sub_mul]
    rw [integral_sub (f := fun z => M z*M z) (g := fun z => r*M z) (hM.integrable_mul hM) ((hM.integrable (by norm_num)).const_mul r),integral_const_mul]
    rw [variance_eq_sub hM]
    simp only [pow_two,Pi.mul_apply,r]
  have hsqrt : Integrable (fun z => Real.sqrt (d z)) μ := by
    have hm : AEStronglyMeasurable (fun z => Real.sqrt (d z)) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hd.aestronglyMeasurable
    have h₂ : MemLp (fun z => Real.sqrt (d z)) 2 μ := by
      rw [memLp_two_iff_integrable_sq hm]
      have he : (fun z => (Real.sqrt (d z))^2) = d := by
        funext z
        exact Real.sq_sqrt (normalizedSquare_nonneg _)
      rw [he]
      exact hd
    exact h₂.integrable (by norm_num)
  have Herr : |(∫ z, F z ∂μ)-(∫ z, G z ∂μ)| ≤ 3*Real.sqrt (∫ z, d z ∂μ) := by
    rw [← integral_sub hF hG]
    calc
      _ ≤ ∫ z, |F z-G z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => F z-G z)
      _ ≤ ∫ z, 3*Real.sqrt (d z) ∂μ := integral_mono (hF.sub hG).norm (hsqrt.const_mul 3)
        (fun z => mean_variance_replacement (a z) (b z) r (ha₁ z) (hb₁ z) hr)
      _ = 3*(∫ z, Real.sqrt (d z) ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_sqrt_le_sqrt_integral d hd (fun z => normalizedSquare_nonneg _)) (by norm_num)
  rw [hFid,hGid] at Herr
  have H := (abs_le.mp Herr).1
  dsimp only
  change ProbabilityTheory.variance M μ ≤ |(∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ)|+3*Real.sqrt (∫ z, d z ∂μ)
  linarith [le_abs_self ((∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ))]
end MeanVariance
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockMeanSquare_variance {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    ProbabilityTheory.variance (hierarchyMeanSquare n m U c J)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) ≤
      ((k+1 : ℕ) : ℝ)*Real.sqrt (((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ))+
        3*Real.sqrt (hierarchyMeanOverlap n m U c L-hierarchyMeanOverlap n m U c J) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let J := blockLevel D N k j.castSucc
  let L := blockLevel D N k j.succ
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hr (b : Fin (n+1)) (i : Fin N) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) b
  have H := mean_variance_from_test (μ := μ)
    (fun z i => hierarchySpinMean n m U (c i) J z)
    (fun z i => hierarchySpinMean n m U (c i) L z)
    (fun i => (hr J i).1.measurable) (fun i => (hr L i).1.measurable)
    (fun z i => (hr J i).2 z) (fun z i => (hr L i).2 z)
  dsimp only at H
  have hJL : J ≤ L := blockLevel_mono D N k (show j.castSucc ≤ j.succ from Nat.le_succ _)
  have hinc := hierarchyMean_increment_identity n m U c hc J L hJL
  rw [hinc] at H
  have ht := sharedFieldEnergy_centered_test U Δ hΔ
    (blockExponent_field I a (fun b => Real.sqrt (Δ b))) hN j
  dsimp only at ht
  have hvar := sharedFieldEnergy_variance I a Δ hΔ j
  have hK : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact H.trans (add_le_add (ht.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) hK)) le_rfl)
end SK.Analytic

namespace SK.Analytic

theorem sum_sqrt_increments_le {k : ℕ} (r : Fin (k+1) → ℝ)
    (hr : Monotone r) (hr0 : 0 ≤ r 0) (hr1 : r (Fin.last k) ≤ 1) :
    (∑ j : Fin k, Real.sqrt (r j.succ-r j.castSucc)) ≤ Real.sqrt (k : ℝ) := by
  have hnon (j : Fin k) : 0 ≤ r j.succ-r j.castSucc := sub_nonneg.mpr (hr (Nat.le_succ _))
  have ht : (∑ j : Fin k, (r j.succ-r j.castSucc)) = r (Fin.last k)-r 0 := by
    rw [Finset.sum_sub_distrib]
    have H := Fin.sum_univ_succ r
    have G := Fin.sum_univ_castSucc r
    linarith
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin k => Real.sqrt (r j.succ-r j.castSucc)) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  simp_rw [Real.sq_sqrt (hnon _)] at H
  rw [ht] at H
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have H' : (∑ j : Fin k, Real.sqrt (r j.succ-r j.castSucc))^2 ≤ (k : ℝ) := by nlinarith
  exact (Real.le_sqrt (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)) hk).mpr H'
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockMeanSquare_average_variance {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹ *
      ProbabilityTheory.variance (hierarchyMeanSquare n m U c (blockLevel D N k j.castSucc))
        (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) ≤
      (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ)) + 3*Real.sqrt (k : ℝ)/((k+1 : ℕ) : ℝ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let r : Fin (k+1) → ℝ := fun j => hierarchyMeanOverlap n m U c (blockLevel D N k j)
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by
    dsimp only [c]; cases s i <;> norm_num [spin]
  have hm : Monotone r := fun i j hij => hierarchyMeanOverlap_mono n m U c hc (blockLevel_mono D N k hij)
  have hr0 : 0 ≤ r 0 := (hierarchyMeanOverlap_bounds n m U c hc _).1
  have hr1 : r (Fin.last k) ≤ 1 := (hierarchyMeanOverlap_bounds n m U c hc _).2
  have hsum := sum_sqrt_increments_le r hm hr0 hr1
  have hpos (b) : 0 < Δ b := hδ.trans_le (hΔ b)
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hK : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hbound (j : Fin k) : ((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ) ≤ 2/((N : ℝ)*δ) := by
    calc
      _ ≤ (δ⁻¹+δ⁻¹)/(N : ℝ) := div_le_div_of_nonneg_right
        (add_le_add (inv_anti₀ hδ (hΔ _)) (inv_anti₀ hδ (hΔ _))) hN'.le
      _ = _ := by field_simp; ring
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left
      ((blockMeanSquare_variance hN I a Δ hpos j).trans
        (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound j)) hK.le) le_rfl))
      (inv_nonneg.mpr hK.le))
  change (∑ j : Fin k, K⁻¹ * _ ) ≤ _
  apply H.trans
  change (∑ j : Fin k, K⁻¹*(K*Real.sqrt (2/((N : ℝ)*δ)) + 3*Real.sqrt (r j.succ-r j.castSucc))) ≤ _
  have he (t s : ℝ) : K⁻¹*(K*t+3*s) = t+(K⁻¹*3)*s := by
    rw [mul_add,← mul_assoc,inv_mul_cancel₀ (show K ≠ 0 from hK.ne'),one_mul]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left hsum (show 0 ≤ K⁻¹*3 by positivity)
  dsimp only [K] at hs ⊢
  simp only [div_eq_mul_inv]
  nlinarith
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

theorem finiteReplicaMoment_dot (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t) = finiteMean p v ⬝ᵥ finiteMean p v := by
  simp only [finiteMean,finiteReplicaMoment,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [dotProduct_comm (v t) (v s)]
  ring

theorem finiteReplicaMoment_square (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2) =
      ∑ i, ∑ j, (finiteCovariance p v i j+finiteMean p v i*finiteMean p v j)^2 := by
  simp only [finiteCovariance_apply,sub_add_cancel]
  have h (s t : S) : (v s ⬝ᵥ v t)^2 = ∑ i, ∑ j, (v s i*v t i)*(v s j*v t j) := by
    unfold dotProduct
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [finiteReplicaMoment,h,Finset.mul_sum,pow_two]
  calc
    _ = ∑ s, ∑ i, ∑ j, ∑ t, p s*p t*(v s i*v t i*(v s j*v t j)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ s, ∑ t, p s*p t*(v s i*v t i*(v s j*v t j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring

theorem finiteReplica_variance_identity (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∑ s, p s = 1) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-finiteMean p v ⬝ᵥ finiteMean p v)^2) =
      ((finiteCovariance p v)*(finiteCovariance p v)).trace+
        2*(finiteMean p v ⬝ᵥ (finiteCovariance p v)*ᵥ finiteMean p v) := by
  let C := finiteCovariance p v
  let m := finiteMean p v
  have hsymm (i j : I) : C i j = C j i := by
    simp only [C,finiteCovariance_apply]
    congr 1
    · apply Finset.sum_congr rfl; intro s _; ring
    · ring
  have hsquare : finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-m ⬝ᵥ m)^2) =
      finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2)-(m ⬝ᵥ m)^2 := by
    have he (s t : S) : p s*p t*(v s ⬝ᵥ v t-m ⬝ᵥ m)^2 =
        p s*p t*(v s ⬝ᵥ v t)^2-2*(p s*p t*(v s ⬝ᵥ v t))*(m ⬝ᵥ m)+
          p s*p t*(m ⬝ᵥ m)^2 := by ring
    unfold finiteReplicaMoment
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,hp,mul_one,one_mul]
    change finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2)-
      2*finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t)*(m ⬝ᵥ m)+(m ⬝ᵥ m)^2 = _
    rw [finiteReplicaMoment_dot]
    dsimp only [m,finiteReplicaMoment]
    ring
  rw [hsquare,finiteReplicaMoment_square]
  change (∑ i, ∑ j, (C i j+m i*m j)^2)-(m ⬝ᵥ m)^2 = _
  have he (i j : I) : (C i j+m i*m j)^2 = C i j*C j i+2*(m i*C i j*m j)+(m i*m j)^2 := by rw [hsymm j i]; ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hmm : (∑ i, ∑ j, (m i*m j)^2) = (m ⬝ᵥ m)^2 := by
    simp only [dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hmm]
  have hquad : (∑ i, ∑ j, m i*C i j*m j) = m ⬝ᵥ C*ᵥ m := by
    simp only [dotProduct,mulVec,Finset.mul_sum,mul_assoc]
  rw [hquad]
  change ((C*C).trace+2*(m ⬝ᵥ C*ᵥ m)+(m ⬝ᵥ m)^2)-(m ⬝ᵥ m)^2 = _
  ring

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

theorem quadratic_le_sqrt_trace (C : Matrix I I ℝ) (hC : C.IsHermitian) (u : I → ℝ) :
    u ⬝ᵥ C*ᵥ u ≤ Real.sqrt ((C*C).trace)*(u ⬝ᵥ u) := by
  have hs (i j : I) : C j i = C i j := by simpa only [star_trivial] using hC.apply i j
  have ht : (C*C).trace = ∑ z : I×I, (C z.1 z.2)^2 := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,hs,pow_two]
  have hq : u ⬝ᵥ C*ᵥ u = ∑ z : I×I, C z.1 z.2*(u z.1*u z.2) := by
    simp only [dotProduct,mulVec,Finset.mul_sum,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have huu : (∑ z : I×I, (u z.1*u z.2)^2) = (u ⬝ᵥ u)^2 := by
    simp only [Fintype.sum_prod_type,dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : I×I => C z.1 z.2) (fun z => u z.1*u z.2)
  rw [huu,← ht,← hq] at hc
  have ht₀ : 0 ≤ (C*C).trace := by rw [ht]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu₀ : 0 ≤ u ⬝ᵥ u := by unfold dotProduct; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have H := Real.le_sqrt_of_sq_le hc
  rwa [Real.sqrt_mul ht₀,Real.sqrt_sq_eq_abs,abs_of_nonneg hu₀] at H

theorem finiteReplica_variance_le (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-finiteMean p v ⬝ᵥ finiteMean p v)^2) ≤
      ((finiteCovariance p v)*(finiteCovariance p v)).trace+
        2*(Fintype.card I : ℝ)*Real.sqrt (((finiteCovariance p v)*(finiteCovariance p v)).trace) := by
  rw [finiteReplica_variance_identity p v hs]
  have hq := quadratic_le_sqrt_trace (finiteCovariance p v) (finiteCovariance_posSemidef p v hp hs).isHermitian (finiteMean p v)
  have hm : finiteMean p v ⬝ᵥ finiteMean p v ≤ (Fintype.card I : ℝ) := by
    unfold dotProduct
    calc
      _ ≤ ∑ _ : I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [pow_two] using (sq_le_one_iff_abs_le_one _).mpr (finiteMean_abs_le_one p v hp hs hv i)
      _ = _ := by simp
  have H := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (((finiteCovariance p v)*(finiteCovariance p v)).trace))
  nlinarith
end ReplicaOverlap
end SK.Analytic

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

theorem finiteReplicaMoment_sub_square (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t)^2)-2*r*finiteReplicaMoment p g+r^2 := by
  have he : (fun s t => (g s t-r)^2) = fun s t => (g s t)^2+(-2*r)*g s t+r^2 := by
    funext s t; ring
  rw [he,finiteReplicaMoment_add,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,finiteReplicaMoment_const p hp]
  ring

theorem finiteReplicaMoment_variance_split (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t-finiteReplicaMoment p g)^2)+(finiteReplicaMoment p g-r)^2 := by
  rw [finiteReplicaMoment_sub_square p hp,finiteReplicaMoment_sub_square p hp]
  ring

theorem finiteReplicaMoment_normalizedDot {N : ℕ} (p : S → ℝ) (v : S → Fin N → ℝ) :
    finiteReplicaMoment p (fun s t => normalizedDot (v s) (v t)) = normalizedSquare (finiteMean p v) := by
  have he : (fun s t => normalizedDot (v s) (v t)) = fun s t => (N : ℝ)⁻¹*(v s ⬝ᵥ v t) := by
    funext s t; simp only [normalizedDot,dotProduct,div_eq_mul_inv]; ring
  rw [he,finiteReplicaMoment_const_mul,finiteReplicaMoment_dot]
  simp only [normalizedSquare,dotProduct,pow_two,div_eq_mul_inv,mul_comm]

theorem finiteCovariance_trace_square_nonneg {I : Type} [Fintype I]
    (p : S → ℝ) (v : S → I → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) :
    0 ≤ ((finiteCovariance p v)*(finiteCovariance p v)).trace := by
  have h := (finiteCovariance_posSemidef p v hp hs).isHermitian
  simpa only [h.eq] using (Matrix.posSemidef_conjTranspose_mul_self (finiteCovariance p v)).trace_nonneg

theorem finiteReplica_normalized_variance_le {N : ℕ} (hN : 0 < N)
    (p : S → ℝ) (v : S → Fin N → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (hv : ∀ s i, |v s i| ≤ 1) :
    finiteReplicaMoment p (fun s t => (normalizedDot (v s) (v t)-normalizedSquare (finiteMean p v))^2) ≤
      ((finiteCovariance p v)*(finiteCovariance p v)).trace/(N : ℝ)^2+
      2*Real.sqrt (((finiteCovariance p v)*(finiteCovariance p v)).trace/(N : ℝ)^2) := by
  let T := ((finiteCovariance p v)*(finiteCovariance p v)).trace
  let m := finiteMean p v
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 ≤ T := finiteCovariance_trace_square_nonneg p v hp hs
  have he : (fun s t => (normalizedDot (v s) (v t)-normalizedSquare m)^2) =
      fun s t => ((N : ℝ)^2)⁻¹*(v s ⬝ᵥ v t-m ⬝ᵥ m)^2 := by
    funext s t
    simp only [normalizedDot,normalizedSquare,dotProduct,pow_two,div_eq_mul_inv]
    ring
  rw [he,finiteReplicaMoment_const_mul]
  have H := mul_le_mul_of_nonneg_left (finiteReplica_variance_le p v hp hs hv)
    (inv_nonneg.2 (sq_nonneg (N : ℝ)))
  apply H.trans_eq
  simp only [Fintype.card_fin]
  rw [Real.sqrt_div hT,Real.sqrt_sq hn.le]
  change ((N : ℝ)^2)⁻¹*(T+2*(N : ℝ)*Real.sqrt T) = T/(N : ℝ)^2+2*(Real.sqrt T/(N : ℝ))
  field_simp [ne_of_gt hn]
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
section HierarchyReplica
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_eq_finiteMean {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U (fun i s => v s i) j z = normalizedSquare (finiteMean (hierarchySpinWeight n m U j z) v) := by
  simp only [hierarchyMeanSquare,hierarchySpinMean_eq_sum]
  congr 1
  funext i
  exact (finiteMean_apply _ _ i).symm

theorem hierarchyOverlap_integrand_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let Q := finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t)-r)^2)
    0 ≤ Q ∧ Q ≤ 4 := by
  dsimp only
  refine ⟨finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _),?_⟩
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have hdot := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have hr := hierarchyMeanOverlap_bounds n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j
  have ha : |normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j| ≤ 2 := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
  have hb := abs_nonneg (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)
  nlinarith [sq_abs (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)]

theorem hierarchyOverlapError_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    0 ≤ hierarchyOverlapError n m U v j ∧ hierarchyOverlapError n m U v j ≤ 4 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc := finiteReplicaMoment_continuous (hierarchySpinWeight n m U j)
    (fun s => (hierarchySpinWeight_regular n m U j s).1)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
  have hi := Integrable.of_bound (μ := hierarchyPathLaw n m f 0) hc.aestronglyMeasurable 4
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
      exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
  refine ⟨integral_nonneg (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (4 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono hi (integrable_const 4) (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
    _ = 4 := by simp
end HierarchyReplica
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplicaBound
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
section IntegralTrace
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_variance_trace_bound (M Q T : Ω → ℝ)
    (hM : AEMeasurable M μ) (hc : Integrable (fun z => (M z-∫ x, M x ∂μ)^2) μ)
    (hQ : Integrable Q μ) (hT : Integrable T μ) (hT0 : ∀ z, 0 ≤ T z)
    (hp : ∀ z, Q z ≤ (M z-∫ x, M x ∂μ)^2+T z+2*Real.sqrt (T z)) :
    (∫ z, Q z ∂μ) ≤ ProbabilityTheory.variance M μ+(∫ z, T z ∂μ)+2*Real.sqrt (∫ z, T z ∂μ) := by
  have hsm : AEStronglyMeasurable (fun z => Real.sqrt (T z)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hT.aestronglyMeasurable
  have hsq : (fun z => (Real.sqrt (T z))^2) = T := funext (fun z => Real.sq_sqrt (hT0 z))
  have hs2 : MemLp (fun z => Real.sqrt (T z)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsm,hsq]
    exact hT
  have HI := integral_mono (g := fun z => (M z-∫ x, M x ∂μ)^2+T z+2*Real.sqrt (T z)) hQ
    ((hc.add hT).add ((hs2.integrable (by norm_num)).const_mul 2)) hp
  have hs := integral_sqrt_le_sqrt_integral T hT hT0
  rw [integral_add (f := fun z => (M z-∫ x, M x ∂μ)^2+T z) (g := fun z => 2*Real.sqrt (T z))
    (hc.add hT) ((hs2.integrable (by norm_num)).const_mul 2),
    integral_add hc hT,integral_const_mul,← variance_eq_integral hM] at HI
  linarith
end IntegralTrace

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplicaBound
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyOverlap_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  apply Integrable.of_bound (finiteReplicaMoment_continuous _
    (fun s => (hierarchySpinWeight_regular n m U j s).1) _).aestronglyMeasurable 4
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
    exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2

theorem hierarchyMeanSquare_centered_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => (hierarchyMeanSquare n m U (fun i s => v s i) j z-
      hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  let M := hierarchyMeanSquare n m U (fun i s => v s i) j
  let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hv s i
  have hM : Continuous M := hierarchyMeanSquare_continuous n m U _ hc j
  have hr := hierarchyMeanOverlap_bounds n m U _ hc j
  refine Integrable.of_bound (f := fun z => (M z-r)^2) ?_ 1 ?_
  · exact ((hM.sub continuous_const).pow 2).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖(M z-r)^2‖ ≤ 1
    have hz := hierarchyMeanSquare_bounds n m U _ hc j z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),sq_le_one_iff_abs_le_one]
    exact abs_le.2 ⟨by linarith [hr.1,hr.2,hz.1,hz.2],
      by linarith [hr.1,hr.2,hz.1,hz.2]⟩

theorem hierarchyOverlap_integrand_le {N : ℕ} (hN : 0 < N) (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    let M := hierarchyMeanSquare n m U (fun i s => v s i) j z
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let T := hierarchyTraceSquare n m U v j z/(N : ℝ)^2
    finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-r)^2) ≤ (M-r)^2+T+2*Real.sqrt T := by
  dsimp only
  rw [finiteReplicaMoment_variance_split _ (hierarchySpinWeight_sum n m U j z),finiteReplicaMoment_normalizedDot,
    hierarchyMeanSquare_eq_finiteMean]
  have H := finiteReplica_normalized_variance_le hN _ v
    (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z) hv
  dsimp only [hierarchyTraceSquare]
  linarith

theorem hierarchyOverlapError_le {N : ℕ} (hN : 0 < N) (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
    let B := (∫ z, hierarchyTraceSquare n m U v j z ∂μ)/(N : ℝ)^2
    hierarchyOverlapError n m U v j ≤
      ProbabilityTheory.variance (hierarchyMeanSquare n m U (fun i s => v s i) j) μ+B+2*Real.sqrt B := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hv s i
  have H := integral_variance_trace_bound (μ := μ)
    (hierarchyMeanSquare n m U (fun i s => v s i) j)
    (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2))
    (fun z => hierarchyTraceSquare n m U v j z/(N : ℝ)^2)
    (hierarchyMeanSquare_continuous n m U _ hc j).measurable.aemeasurable
    (hierarchyMeanSquare_centered_integrable n m U v hv j)
    (hierarchyOverlap_integrable n m U v hv j)
    ((hierarchyTraceSquare_integrable n m U v hv j 0).div_const _)
    (fun z => div_nonneg (finiteCovariance_trace_square_nonneg _ v
      (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)) (sq_nonneg _))
    (hierarchyOverlap_integrand_le hN n m U v hv j)
  rw [integral_div] at H
  exact H
end HierarchyReplicaBound
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageReplica
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

theorem uniform_subprobability_sqrt (k : ℕ) (B : Fin k → ℝ) (hB : ∀ j, 0 ≤ B j) :
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹*Real.sqrt (B j)) ≤
      Real.sqrt (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹*B j) := by
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg (fun j _ => hB j)
  have HC := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin k => Real.sqrt (B j)) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at HC
  simp_rw [Real.sq_sqrt (hB _)] at HC
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  change (K⁻¹*(∑ j, Real.sqrt (B j)))^2 ≤ K⁻¹*(∑ j, B j)
  have hkk : (k : ℝ) ≤ K := by dsimp [K]; norm_num
  have HH := mul_le_mul_of_nonneg_left (HC.trans (mul_le_mul_of_nonneg_left hkk hsum)) (sq_nonneg K⁻¹)
  have hc : K⁻¹^2*((∑ j, B j)*K) = K⁻¹*(∑ j, B j) := by
    field_simp [ne_of_gt hK]
  rw [hc] at HH
  nlinarith

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem block_average_overlap_explicit {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let v : Config N → Fin N → ℝ := fun s i => spin (s i)
    let E := 1/((k+1 : ℕ) : ℝ)+2*((k+1 : ℕ) : ℝ)/((N : ℝ)*δ)
    (∑ j : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j)) ≤
      (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/((k+1 : ℕ) : ℝ)+E+2*Real.sqrt E+4/((k+1 : ℕ) : ℝ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let v : Config N → Fin N → ℝ := fun s i => spin (s i)
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  let E : ℝ := 1/K+2*K/((N : ℝ)*δ)
  let B : Fin k → ℝ := fun j => (∫ z, hierarchyTraceSquare n m U v (blockLevel D N k j.castSucc) z ∂μ)/(N : ℝ)^2
  let V : Fin k → ℝ := fun j => ProbabilityTheory.variance
    (hierarchyMeanSquare n m U (fun i s => v s i) (blockLevel D N k j.castSucc)) μ
  have hv (s : Config N) (i : Fin N) : |v s i| ≤ 1 := by dsimp [v]; cases s i <;> norm_num [spin]
  have hK : 0 < K := by dsimp [K]; positivity
  have hB j : 0 ≤ B j := div_nonneg (integral_nonneg (fun z => finiteCovariance_trace_square_nonneg _ v
    (hierarchySpinWeight_nonneg n m U _ z) (hierarchySpinWeight_sum n m U _ z))) (sq_nonneg _)
  have HT : (∑ j, K⁻¹*B j) ≤ E := equalBlock_average_trace D N k hN U Δ hδ hΔ v hv
    (fun s b i => blockExponent_field I a (fun b => Real.sqrt (Δ b)) b i s)
  have HV : (∑ j, K⁻¹*V j) ≤ (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K :=
    blockMeanSquare_average_variance hN I a Δ hδ hΔ
  have HS : (∑ j, K⁻¹*Real.sqrt (B j)) ≤ Real.sqrt E :=
    (uniform_subprobability_sqrt k B hB).trans (Real.sqrt_le_sqrt HT)
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left (hierarchyOverlapError_le hN n m U v hv (blockLevel D N k j.castSucc)) (inv_nonneg.2 hK.le))
  change (∑ j : Fin k, K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j.castSucc)) ≤
    ∑ j, K⁻¹*(V j+B j+2*Real.sqrt (B j)) at H
  have he : (∑ j, K⁻¹*(V j+B j+2*Real.sqrt (B j))) =
      (∑ j, K⁻¹*V j)+(∑ j, K⁻¹*B j)+2*(∑ j, K⁻¹*Real.sqrt (B j)) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at H
  have HL := mul_le_mul_of_nonneg_left (hierarchyOverlapError_bounds n m U v hv (blockLevel D N k (Fin.last k))).2
    (inv_nonneg.2 hK.le)
  dsimp only
  rw [Fin.sum_univ_castSucc]
  change (∑ j : Fin k, K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j.castSucc))+
    K⁻¹*hierarchyOverlapError n m U v (blockLevel D N k (Fin.last k)) ≤ _
  change _ ≤ (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K+E+2*Real.sqrt E+4/K
  calc
    _ ≤ ((k : ℝ)*Real.sqrt (2/((N : ℝ)*δ))+3*Real.sqrt (k : ℝ)/K)+E+2*Real.sqrt E+K⁻¹*4 := by linarith
    _ = _ := by ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_OverlapBoundArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
namespace SK.Analytic

theorem overlap_error_arithmetic {k v : ℝ} (hk : 1 ≤ k) (hv : 0 < v)
    (hkv : k/Real.sqrt v ≤ 1) :
    let E := 1/(k+1)+2*(k+1)/v
    k*Real.sqrt (2/v)+3*Real.sqrt k/(k+1)+E+2*Real.sqrt E+4/(k+1) ≤
      20*(k/Real.sqrt v+1/Real.sqrt k) := by
  have hk0 : 0 < k := by linarith
  have hrk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hrv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hksq : k^2 ≤ v := by
    have hh := (div_le_one hrv).1 hkv
    nlinarith [Real.sq_sqrt hv.le]
  have hroot : Real.sqrt k ≤ k := by
    nlinarith [Real.sq_sqrt hk0.le]
  have hK : 0 < k+1 := by linarith
  have hE : 1/(k+1)+2*(k+1)/v ≤ 5/k := by
    have h1 := one_div_le_one_div_of_le hk0 (show k ≤ k+1 by linarith)
    have h2 : 2*(k+1)/v ≤ 4/k := by
      calc
        _ ≤ 2*(2*k)/(k^2) := div_le_div₀ (by positivity) (by nlinarith) (sq_pos_of_pos hk0) hksq
        _ = _ := by field_simp; ring
    calc
      _ ≤ 1/k+4/k := add_le_add h1 h2
      _ = _ := by ring
  have hEsqrt : Real.sqrt (1/(k+1)+2*(k+1)/v) ≤ 3/Real.sqrt k := by
    calc
      _ ≤ Real.sqrt (9/k) := Real.sqrt_le_sqrt (hE.trans (div_le_div_of_nonneg_right (by norm_num) hk0.le))
      _ = _ := by rw [Real.sqrt_div (by norm_num)]; norm_num
  have hfirst : k*Real.sqrt (2/v) ≤ 2*(k/Real.sqrt v) := by
    rw [Real.sqrt_div (by norm_num)]
    have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2 : ℝ)]
    have H := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htwo hrv.le) hk0.le
    calc
      _ ≤ k*(2/Real.sqrt v) := H
      _ = _ := by ring
  have hmean : 3*Real.sqrt k/(k+1) ≤ 3/Real.sqrt k := by
    apply (div_le_div_iff₀ hK hrk).2
    nlinarith [Real.sq_sqrt hk0.le]
  have hEfinal : 1/(k+1)+2*(k+1)/v ≤ 5/Real.sqrt k :=
    hE.trans (div_le_div_of_nonneg_left (by norm_num) hrk hroot)
  have hlast : 4/(k+1) ≤ 4/Real.sqrt k :=
    div_le_div_of_nonneg_left (by norm_num) hrk (hroot.trans (by linarith))
  dsimp only
  have ha : 0 ≤ k/Real.sqrt v := by positivity
  have hb : 0 ≤ 1/Real.sqrt k := by positivity
  simp only [div_eq_mul_inv] at hEsqrt hfirst hmean hEfinal hlast ha hb ⊢
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageOverlap
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

theorem block_average_overlap_concentration {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b)
    (hsmall : (k : ℝ)/Real.sqrt ((N : ℝ)*δ) ≤ 1) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let v : Config N → Fin N → ℝ := fun s i => spin (s i)
    (∑ j : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j)) ≤
      20*((k : ℝ)/Real.sqrt ((N : ℝ)*δ)+1/Real.sqrt (k : ℝ)) := by
  have H := block_average_overlap_explicit hN I a Δ hδ hΔ
  have A := overlap_error_arithmetic (k := (k : ℝ)) (v := (N : ℝ)*δ)
    (by exact_mod_cast Nat.succ_le_iff.mpr hk) (by positivity) hsmall
  simp only [Nat.cast_add,Nat.cast_one] at H
  simpa only [Nat.cast_add,Nat.cast_one] using H.trans A
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAdaptiveOverlap
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

theorem blockCoefficients_contDiff {D N k : ℕ} (a : Fin D → ℝ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) =>
      blockCoefficients (N := N) (fun i => p.1*a i) (fun b => β*p.2 b)) := by
  apply contDiff_pi.mpr
  intro t
  refine Fin.addCases (fun i => ?_) (fun i => ?_) t
  · simp only [blockCoefficients,Fin.addCases_left]
    exact contDiff_fst.mul contDiff_const
  · simp only [blockCoefficients,Fin.addCases_right]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ _).comp contDiff_snd)

theorem blockAdaptiveOverlap_contDiff {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) : ContDiff ℝ 2 (blockAdaptiveOverlap (k := k) I a β) := by
  apply contDiff_pi.mpr
  intro j
  exact (spinHierarchyOverlap_contDiff (blockDimension D N k) (blockMass D N k)
    (blockInteraction I) (fun i s => spin (s i)) (fun i s => by cases s i <;> norm_num [spin])
    (blockLevel D N k j)).comp (blockCoefficients_contDiff a β)

theorem blockAdaptiveOverlap_bounds {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) (j : Fin (k+1)) :
    blockAdaptiveOverlap I a β p j ∈ Set.Icc (0:ℝ) 1 :=
  hierarchyMeanOverlap_bounds _ _ _ _ (fun i s => by cases s i <;> norm_num [spin]) _

theorem blockAdaptiveOverlap_monotone {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) :
    Monotone (blockAdaptiveOverlap I a β p) :=
  (hierarchyMeanOverlap_mono _ _ _ _ (fun i s => by cases s i <;> norm_num [spin])).comp
    (blockLevel_mono D N k)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveODERegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem lipschitzWith_sqrt_max (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨(2*Real.sqrt ε)⁻¹, by positivity⟩ (fun x : ℝ => Real.sqrt (max ε x)) := by
  have h : LipschitzOnWith ⟨(2*Real.sqrt ε)⁻¹, by positivity⟩ Real.sqrt (Ici ε) := by
    apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (Real.hasDerivAt_sqrt (ne_of_gt (hε.trans_le hx))).hasDerivWithinAt)
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖1/(2*Real.sqrt x)‖ ≤ (2*Real.sqrt ε)⁻¹
    rw [one_div]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (by norm_num))
  have hm := LipschitzWith.id.const_max ε
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Real.sqrt (max ε x)) (Real.sqrt (max ε y)) ≤ (2*Real.sqrt ε)⁻¹*dist x y
  calc
    _ ≤ (2*Real.sqrt ε)⁻¹ * dist (max ε x) (max ε y) :=
      h.dist_le_mul _ (show ε ≤ max ε x from le_max_left ε x)
        _ (show ε ≤ max ε y from le_max_left ε y)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using hm.dist_le_mul x y) (by positivity)

theorem lipschitzWith_pi_of_uniform {X : Type} [PseudoMetricSpace X] {ι : Type} [Fintype ι]
    {K : ℝ≥0} {f : X → ι → ℝ} (hf : ∀ i, LipschitzWith K (fun x => f x i)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_pi_le_iff (by positivity)).mpr (fun i => (hf i).dist_le_mul x y)

theorem positiveGapScales_lipschitz (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K, LipschitzWith K (positiveGapScales k ε) := by
  have h := lipschitzWith_pi_of_uniform (ι := Fin (k+1))
    (fun j => (lipschitzWith_sqrt_max ε hε).comp (LipschitzWith.eval j))
  exact ⟨_,h.comp (cumulativeGapMap k).lipschitz⟩

theorem regular_positiveGapScales {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (ε : ℝ) (hε : 0 < ε) :
    LocallyLipschitz (fun p : ℝ × (Fin (k+1) → ℝ) => R (p.1,positiveGapScales k ε p.2)) := by
  obtain ⟨K,hK⟩ := positiveGapScales_lipschitz k ε hε
  exact hR.locallyLipschitz.comp
    (LipschitzWith.prod_fst.prodMk (hK.comp LipschitzWith.prod_snd)).locallyLipschitz
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveODEExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem exists_floored_adaptive_path {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (hRb : ∀ p j, R p j ∈ Icc (0:ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) (q₀ : Fin (k+1) → ℝ) :
    ∃ q : ℝ → (Fin (k+1) → ℝ), q 0 = q₀ ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt q
        (R (Real.sqrt (1-t),positiveGapScales k ε (q t))) (Icc (0:ℝ) 1) t := by
  let G := fun p : ℝ × (Fin (k+1) → ℝ) => R (p.1,positiveGapScales k ε p.2)
  have hG : LocallyLipschitz G := regular_positiveGapScales R hR ε hε
  obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.prod (isCompact_closedBall q₀ 1)) hG.locallyLipschitzOn
  have hs (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Real.sqrt (1-t) ∈ Icc (0:ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg _,?_⟩
    apply Real.sqrt_le_one.mpr
    linarith [ht.1]
  let F := fun t q => G (Real.sqrt (1-t),q)
  have hf : IsPicardLindelof F (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) q₀ 1 0 1 K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [F,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
        hK.dist_le_mul (Real.sqrt (1-t),x) ⟨hs t ht,hx⟩
          (Real.sqrt (1-t),y) ⟨hs t ht,hy⟩
    · intro x _
      exact (hG.continuous.comp ((Real.continuous_sqrt.comp
        (continuous_const.sub continuous_id)).prodMk continuous_const)).continuousOn
    · intro t _ x _
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
      intro j
      rw [Real.norm_eq_abs,abs_of_nonneg (hRb _ j).1]
      exact (hRb _ j).2
    · norm_num
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem monotoneOn_unit_of_deriv_nonneg {f g : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt f (g t) (Icc (0:ℝ) 1) t)
    (hg : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ g t) : MonotoneOn f (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (fun t ht => (hf t ht).continuousWithinAt)
  · intro t ht
    exact (hf t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact hg t (interior_subset ht)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptivePositivePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem exists_positive_adaptive_path {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (hRb : ∀ p j, R p j ∈ Icc (0:ℝ) 1) (hRm : ∀ p, Monotone (R p))
    (η : ℝ) (hη : 0 < η) :
    ∃ q : ℝ → (Fin (k+1) → ℝ),
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt q
        (R (Real.sqrt (1-t),fun j => Real.sqrt (cumulativeGapMap k (q t) j))) (Icc (0:ℝ) 1) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q t) j) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, q t j ≤ ((j.val:ℝ)+1)*η+t) := by
  let q₀ : Fin (k+1) → ℝ := fun j => ((j.val:ℝ)+1)*η
  let ε := η/2
  obtain ⟨q,hq0,hq⟩ := exists_floored_adaptive_path R hR hRb ε (by dsimp [ε]; positivity) q₀
  let v := fun t => R (Real.sqrt (1-t),positiveGapScales k ε (q t))
  have hGap0 (j : Fin (k+1)) : cumulativeGapMap k q₀ j = η := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [q₀]
    · simp only [cumulativeGapMap_succ,q₀,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
  have hGapD (j : Fin (k+1)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun u => cumulativeGapMap k (q u) j)
        (cumulativeGapMap k (v t) j) (Icc (0:ℝ) 1) t := by
    exact ((ContinuousLinearMap.proj j).comp (cumulativeGapMap k)).hasFDerivAt.comp_hasDerivWithinAt t (hq t ht)
  have hGapV (t : ℝ) (j : Fin (k+1)) : 0 ≤ cumulativeGapMap k (v t) j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (hRb _ 0).1
    · change 0 ≤ v t i.succ-v t i.castSucc
      exact sub_nonneg.mpr (hRm _ (Fin.castSucc_le_succ i))
  have hGap (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j : Fin (k+1)) :
      η ≤ cumulativeGapMap k (q t) j := by
    have H := monotoneOn_unit_of_deriv_nonneg (hGapD j) (fun t _ => hGapV t j)
      (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    change cumulativeGapMap k (q 0) j ≤ cumulativeGapMap k (q t) j at H
    rwa [hq0,hGap0] at H
  have hscales (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      positiveGapScales k ε (q t) = fun j => Real.sqrt (cumulativeGapMap k (q t) j) := by
    funext j
    rw [positiveGapScales,max_eq_right]
    exact (by dsimp [ε]; linarith : ε ≤ η).trans (hGap t ht j)
  refine ⟨q,hq0,?_,hGap,?_⟩
  · intro t ht
    simpa only [hscales t ht] using hq t ht
  · intro t ht j
    have hD (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
        HasDerivWithinAt (fun s => s-q s j) (1-v u j) (Icc (0:ℝ) 1) u := by
      exact (hasDerivWithinAt_id u _).sub
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) j).hasFDerivAt.comp_hasDerivWithinAt u (hq u hu))
    have H := monotoneOn_unit_of_deriv_nonneg hD (fun u _ => sub_nonneg.mpr (hRb _ j).2)
      (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    change 0-q 0 j ≤ t-q t j at H
    rw [hq0] at H
    change 0-((j.val:ℝ)+1)*η ≤ t-q t j at H
    linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAdaptivePath
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

theorem exists_block_adaptive_path_oai {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ q : ℝ → (Fin (k+1) → ℝ),
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q
        (blockAdaptiveOverlap I a β (Real.sqrt (1-u),fun j => Real.sqrt (cumulativeGapMap k (q u) j)))
          (Set.Icc (0:ℝ) 1) u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1,
        let U := blockExponent I (fun i => Real.sqrt (1-u)*a i)
          (fun b => β*Real.sqrt (cumulativeGapMap k (q u) b))
        (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
          hierarchyOverlapError (blockDimension D N k) (blockMass D N k) U
            (fun s i => spin (s i)) (blockLevel D N k j)) ≤
          20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))) := by
  obtain ⟨q,h0,hD,hgap,hupper⟩ := exists_positive_adaptive_path (k := k)
    (blockAdaptiveOverlap I a β) ((blockAdaptiveOverlap_contDiff I a β).of_le (by norm_num))
    (blockAdaptiveOverlap_bounds I a β) (blockAdaptiveOverlap_monotone I a β) η hη
  refine ⟨q,h0,hD,hgap,hupper,?_⟩
  intro u hu
  have hs (b : Fin (k+1)) :
      Real.sqrt (β^2*cumulativeGapMap k (q u) b) = β*Real.sqrt (cumulativeGapMap k (q u) b) := by
    rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,abs_of_nonneg hβ.le]
  have H := block_average_overlap_concentration hN hk I (fun i => Real.sqrt (1-u)*a i)
    (fun b => β^2*cumulativeGapMap k (q u) b) (by positivity : 0 < β^2*η)
    (fun b => mul_le_mul_of_nonneg_left (hgap u hu b) (sq_nonneg β)) hsmall
  simpa only [hs] using H
end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.exists_block_adaptive_path_oai := @OAI.SK.Analytic.exists_block_adaptive_path_oai
