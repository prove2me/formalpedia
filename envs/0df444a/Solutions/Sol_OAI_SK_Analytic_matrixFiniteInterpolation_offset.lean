-- Prove2me | solution 1 for OAI.SK.Analytic.matrixFiniteInterpolation_offset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:08:10.109906+00:00
-- url     : https://prove2.me/submissions/77f55173-4bc2-49ef-835d-5a4b38e99bea

import Mathlib
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005

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

theorem blockLevel_injective (D N k : ℕ) (hN : 0 < N) :
    Function.Injective (blockLevel D N k) := by
  intro a b hab
  apply Fin.ext
  have h := congrArg Fin.val hab
  simp only [blockLevel_val] at h
  exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right hN (Nat.add_left_cancel h))

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
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaEdgeIdentity
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

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedHierarchyProbability
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

theorem weightedHierarchyWeight_regular (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (s : S) :
    Continuous (fun z => weightedHierarchyWeight n m c U j z s) ∧
      ∀ z, ‖weightedHierarchyWeight n m c U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs c U)
    (affineGibbs_continuous c U s) (by norm_num) (fun z => affineGibbs_norm_le_one c U z s) j

theorem weightedHierarchyWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (z : ParameterSpace n) (s : S) :
    0 ≤ weightedHierarchyWeight n m c U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => (affineGibbs_pos c U z s).le) j z

theorem weightedHierarchyWeight_sum (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    ∑ s, weightedHierarchyWeight n m c U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition c U)
    (affineLogPartition_boundedDerivs c U) (fun s z => affineGibbs c U z s)
    (affineGibbs_continuous c U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one c U z s) j
  have he : (fun z => ∑ s, affineGibbs c U z s) = fun _ => 1 := funext (affineGibbs_sum c U)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs c U)] at H
  exact (congrFun H z).symm

theorem weightedHierarchyMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z =
      ∑ s, weightedHierarchyWeight n m c U j z s*g s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition c U)
    (affineLogPartition_boundedDerivs c U) (fun s z => g s*affineGibbs c U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous c U s))
    (fun s => ‖g s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one c U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition c U)
    (fun z => ∑ s, affineGibbs c U z s*g s) j z = _
  simpa only [weightedHierarchyWeight,mul_comm] using congrFun H z

theorem weightedHierarchyReplica_integrable (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) :
    Integrable (fun z => finiteReplicaMoment (weightedHierarchyWeight n m c U j z) K)
      (hierarchyPathLaw n m (affineLogPartition c U) 0) := by
  classical
  let B := ∑ s, ∑ t, ‖K s t‖
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs c U)
    (finiteReplicaMoment_continuous _ (fun s => (weightedHierarchyWeight_regular n m c U j s).1) K)
    (C:=B)
  intro z
  unfold finiteReplicaMoment
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  simp only [norm_mul]
  have hs := (weightedHierarchyWeight_regular n m c U j s).2 z
  have ht := (weightedHierarchyWeight_regular n m c U j t).2 z
  have H := mul_le_mul hs ht (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right H (norm_nonneg _)).trans_eq (by ring)

theorem weightedHierarchyReplica_const (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (a : ℝ) :
    weightedHierarchyReplica n m c U j (fun _ _ => a) = a := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs c U) 0
  simp only [weightedHierarchyReplica,finiteReplicaMoment_const _ (weightedHierarchyWeight_sum n m c U j _),integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem weightedHierarchyReplica_mono (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) {K L : S → S → ℝ}
    (h : ∀ s t, K s t ≤ L s t) :
    weightedHierarchyReplica n m c U j K ≤ weightedHierarchyReplica n m c U j L :=
  integral_mono (weightedHierarchyReplica_integrable n m c U j K)
    (weightedHierarchyReplica_integrable n m c U j L)
    (fun z => finiteReplicaMoment_mono _ (weightedHierarchyWeight_nonneg n m c U j z) K L h)

theorem weightedHierarchyReplica_sum {I : Type} [Fintype I] (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : I → S → S → ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => ∑ i, K i s t) =
      ∑ i, weightedHierarchyReplica n m c U j (K i) := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_sum]
  exact integral_finsetSum _ (fun i _ => weightedHierarchyReplica_integrable n m c U j (K i))

omit [Nonempty S] in
theorem weightedHierarchyReplica_const_mul (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) (a : ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => a*K s t) =
      a*weightedHierarchyReplica n m c U j K := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_const_mul,integral_const_mul]

theorem weightedHierarchyReplica_separable_square (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (g : S → ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => g s*g t) =
      ∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition c U) 0 := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_separable_square,weightedHierarchyMean_eq_sum]

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedTerminalMean
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

omit [Nonempty S] in
theorem affineMoment_sum {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] (c : S → ℝ) (U : S → E →L[ℝ] ℝ) (g : I → S → ℝ) (z : E) :
    affineMoment c U (fun s => ∑ i, g i s) z = ∑ i, affineMoment c U (g i) z := by
  simp only [affineMoment,Finset.mul_sum]
  exact Finset.sum_comm

theorem weightedHierarchyTerminalMean_integrable (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) :
    Integrable (affineMoment c U g) (hierarchyPathLaw n m (affineLogPartition c U) 0) := by
  classical
  exact hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs c U)
    (affineMoment_continuous c U g)
    (affineMoment_norm_le c U g (fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s))) 0

theorem weightedHierarchyTerminalMean_const (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (a : ℝ) :
    weightedHierarchyTerminalMean n m c U (fun _ => a) = a := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs c U) 0
  simp only [weightedHierarchyTerminalMean,affineMoment,← Finset.sum_mul,affineGibbs_sum,one_mul]
  simp

theorem weightedHierarchyTerminalMean_mono (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) {g h : S → ℝ} (hgh : ∀ s, g s ≤ h s) :
    weightedHierarchyTerminalMean n m c U g ≤ weightedHierarchyTerminalMean n m c U h := by
  apply integral_mono (weightedHierarchyTerminalMean_integrable n m c U g)
    (weightedHierarchyTerminalMean_integrable n m c U h)
  intro z
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hgh s) (affineGibbs_pos c U z s).le)

theorem weightedHierarchyTerminalMean_sum {I : Type} [Fintype I] (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : I → S → ℝ) :
    weightedHierarchyTerminalMean n m c U (fun s => ∑ i, g i s) =
      ∑ i, weightedHierarchyTerminalMean n m c U (g i) := by
  simp only [weightedHierarchyTerminalMean,affineMoment_sum]
  exact integral_finsetSum _ (fun i _ => weightedHierarchyTerminalMean_integrable n m c U (g i))

omit [Nonempty S] in
theorem weightedHierarchyTerminalMean_const_mul (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (a : ℝ) :
    weightedHierarchyTerminalMean n m c U (fun s => a*g s) =
      a*weightedHierarchyTerminalMean n m c U g := by
  simp only [weightedHierarchyTerminalMean,affineMoment_const_mul,integral_const_mul]

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

theorem weightedHierarchy_coordinate_covariance (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s) :
    (∫ z, coordinateProjection n i z*affineMoment c U g z
      ∂hierarchyPathLaw n m (affineLogPartition c U) 0) =
      a*((∫ z, affineMoment c U (fun s => (g s)^2) z
        ∂hierarchyPathLaw n m (affineLogPartition c U) 0)-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
          (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
            ∂hierarchyPathLaw n m (affineLogPartition c U) 0) else 0) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let A := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f 0
  let V (z : ParameterSpace n) := f z-hierarchyPenalty n m 1 f z
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf 0
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
    (HasExpGrowth.of_bounded hB hGb) (HasExpGrowth.of_bounded hC hC') 0 i
  dsimp only [V] at H
  simp_rw [← hierarchyPathLaw_integral_tilt n m f hf 0] at H
  have hA (j : Fin (n+1)) := hierarchyMomentLevel_bounded_continuous n m f G hf hG.continuous hB hGb j
  have hi (j : Fin (n+1)) : Integrable (fun z => G z*A j z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hG.continuous.mul (hA j).1)
      (fun z => by simp only [Pi.mul_apply,norm_mul]; exact mul_le_mul (hGb z) ((hA j).2 z) (norm_nonneg _) hB) 0
  have hi2 : Integrable (fun z => affineMoment c U (fun s => (g s)^2) z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (affineMoment_continuous _ _ _)
      (affineMoment_norm_le c U _ (fun s => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)) 0
  have hprod (j : Fin (n+1)) :
      (∫ z, G z*A j z ∂μ) = ∫ z, (A j z)^2 ∂μ := by
    have H := hierarchyPathLaw_fixed_mul n m f G (A j) hf hG.continuous (hA j).1 hB hB
      hGb (hA j).2 j (hierarchyMomentLevel_retained n m f G hf j j le_rfl) 0
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
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteStatePressureCurve
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

omit [Fintype S] [Nonempty S] in
theorem observableCoefficientBilinear_apply (d : ℕ) (O : Fin d → S → ℝ)
    (s : S) (a : Fin d → ℝ) :
    observableCoefficientBilinear d O s a = observableExponent d O a s := by
  simp only [observableCoefficientBilinear,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,observableExponent,coordinateLinear,smul_smul]

theorem observableTerminal_paramRegular (d : ℕ) (O : Fin d → S → ℝ) (c : S → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (observableExponent d O z.1) z.2) := by
  apply paramRegular_log_finite_exp (fun s z => c s+observableExponent d O z.1 s z.2)
  intro s
  apply (paramRegular_const (c s)).add
  simpa only [observableCoefficientBilinear_apply] using
    paramRegular_bilinear (observableCoefficientBilinear d O s)

theorem observableTerminal_parameterDerivative (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a v : Fin d → ℝ) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (observableExponent d O w.1) w.2) (a,z) (v,0) =
      affineMoment c (observableExponent d O a) (fun s => observableExponent d O v s z) z := by
  rw [← parameterFDeriv_at_field ((observableTerminal_paramRegular d O c).1.differentiable (by norm_num)) a v z]
  let L : S → (Fin d → ℝ) →L[ℝ] ℝ := fun s => (observableCoefficientBilinear d O s).flip z
  have he : (fun a : Fin d → ℝ => affineLogPartition c (observableExponent d O a) z) =
      affineLogPartition c L := by
    funext a
    simp only [affineLogPartition,L,ContinuousLinearMap.flip_apply,observableCoefficientBilinear_apply]
  rw [he,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,L,ContinuousLinearMap.flip_apply,observableCoefficientBilinear_apply]

omit [Fintype S] [Nonempty S] in
theorem observableExponent_single (d : ℕ) (O : Fin d → S → ℝ)
    (i : Fin d) (s : S) (z : ParameterSpace d) :
    observableExponent d O (Pi.single i 1) s z = O i s*coordinateProjection d i z := by
  classical
  simp [observableExponent,coordinateLinear_apply,Pi.single_apply]

theorem observablePressure_parameterDerivative_single (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition c (observableExponent d O a)) 0) a (Pi.single i 1) =
      ∫ z, coordinateProjection d i z*affineMoment c (observableExponent d O a) (O i) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0 := by
  classical
  have hP := hierarchyPressure_paramRegular d m _ (observableTerminal_paramRegular d O c)
  rw [parameterFDeriv_at_field (hP.1.differentiable (by norm_num)),
    hierarchyPressure_parameterDerivative d m _ (observableTerminal_paramRegular d O c)]
  simp only [observableTerminal_parameterDerivative,observableExponent_single]
  have he : (fun z : ParameterSpace d => affineMoment c (observableExponent d O a)
      (fun s => O i s*coordinateProjection d i z) z) = fun z =>
        coordinateProjection d i z*affineMoment c (observableExponent d O a) (O i) z := by
    funext z
    simp only [affineMoment,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he]
  apply hierarchyAverage_eq_integral_exp d m _ (affineLogPartition_boundedDerivs _ _)
  · exact (coordinateProjection d i).continuous.mul (affineMoment_continuous _ _ _)
  · let B := ∑ s, ‖O i s‖
    have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact (HasExpGrowth.linear _).mul (HasExpGrowth.of_bounded hB
      (affineMoment_norm_le c _ (O i) (fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s))))

theorem observablePressure_coefficient_variation (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition c (observableExponent d O a)) 0) a (Pi.single i 1) =
      a i*((∫ z, affineMoment c (observableExponent d O a) (fun s => (O i s)^2) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0)-
        ∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j*
          (∫ z, (hierarchyMomentLevel d m (affineLogPartition c (observableExponent d O a))
            (affineMoment c (observableExponent d O a) (O i)) j z)^2
              ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0) else 0) := by
  rw [observablePressure_parameterDerivative_single]
  apply weightedHierarchy_coordinate_covariance
  intro s
  simp only [observableExponent,coordinateLinear_coordinateAxis]

theorem observablePressure_hasDerivAt_curve (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (m : Fin d → ℝ) (a : ℝ → Fin d → ℝ) {t : ℝ} {a' : Fin d → ℝ}
    (ha : HasDerivAt a a' t) :
    HasDerivAt (fun u => hierarchyPressure d m (affineLogPartition c (observableExponent d O (a u))) 0)
      (∑ i : Fin d, a' i*(a t i*((∫ z, affineMoment c (observableExponent d O (a t)) (fun s => (O i s)^2) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O (a t))) 0)-
        ∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j*
          (∫ z, (hierarchyMomentLevel d m (affineLogPartition c (observableExponent d O (a t)))
            (affineMoment c (observableExponent d O (a t)) (O i)) j z)^2
              ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O (a t))) 0) else 0))) t := by
  have hp := hierarchyPressure_paramRegular d m _ (observableTerminal_paramRegular d O c)
  have hd := (parameter_contDiff_at_field hp.1 (0:ℝ)).differentiable (by norm_num)
  have H := (hd (a t)).hasFDerivAt.comp_hasDerivAt t ha
  apply H.congr_deriv
  symm
  conv_rhs => rw [pi_eq_sum_univ' a',map_sum]
  simp only [map_smul,smul_eq_mul,observablePressure_coefficient_variation]

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteCovarianceInterpolation
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

theorem hierarchyAtom_nonneg_of_monotone (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hm : ∀ i, m i ∈ Icc (0:ℝ) u) (hmono : Monotone m)
    (j : Fin (n+1)) : 0 ≤ hierarchyAtom n m u j := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyAtom,Fin.lastCases_last] using sub_nonneg.mpr (hm (Fin.last n)).2
    · simp only [hierarchyAtom,Fin.lastCases_castSucc]
      apply ih _ _ (hm (Fin.last n)).1
      · intro i
        exact ⟨(hm i.castSucc).1,hmono (Fin.le_last _)⟩
      · intro i l hil
        exact hmono (by simpa using hil)

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem weightedCovarianceExpression_eq (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (O : Fin n → S → ℝ) (b : Fin n → ℝ) :
    (∑ i : Fin n, b i*(weightedHierarchyTerminalMean n m c U (fun s => (O i s)^2)-
      ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (fun s t => O i s*O i t) else 0)) =
      weightedHierarchyTerminalMean n m c U (fun s => ∑ i, b i*(O i s)^2)-
        ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
          weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j) := by
  classical
  simp only [mul_sub,Finset.sum_sub_distrib,weightedHierarchyTerminalMean_sum,
    weightedHierarchyTerminalMean_const_mul,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change _ = hierarchyAtom n m 1 j*weightedHierarchyReplica n m c U j
    (fun s t => ∑ i : Fin n, if i.val < j.val then b i*(O i s*O i t) else 0)
  rw [weightedHierarchyReplica_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < j.val
  · simp only [ite_eq_left h,weightedHierarchyReplica_const_mul]
    ring
  · simp only [ite_eq_right h,mul_zero,weightedHierarchyReplica_const]

theorem observablePressure_hasDerivAt_covariance (n : ℕ) (O : Fin n → S → ℝ)
    (c : S → ℝ) (m : Fin n → ℝ) (a : ℝ → Fin n → ℝ) {t : ℝ} {a' : Fin n → ℝ}
    (ha : HasDerivAt a a' t) :
    HasDerivAt (fun u => hierarchyPressure n m (affineLogPartition c (observableExponent n O (a u))) 0)
      (weightedHierarchyTerminalMean n m c (observableExponent n O (a t))
        (fun s => ∑ i, (a' i*a t i)*(O i s)^2)-
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c (observableExponent n O (a t)) j
          (partialObservableCovariance n O (fun i => a' i*a t i) j)) t := by
  have H := observablePressure_hasDerivAt_curve n O c m a ha
  apply H.congr_deriv
  rw [← weightedCovarianceExpression_eq]
  simp only [weightedHierarchyTerminalMean,weightedHierarchyReplica_separable_square]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedCovariance_bound (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (O : Fin n → S → ℝ) (b : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (D : ℝ) (C : Fin (n+1) → ℝ)
    (hdiag : ∀ s, (∑ i, b i*(O i s)^2) ≤ D)
    (hkernel : ∀ j, hierarchyAtom n m 1 j≠0 → ∀ s t, -C j ≤ partialObservableCovariance n O b j s t) :
    weightedHierarchyTerminalMean n m c U (fun s => ∑ i, b i*(O i s)^2)-
      (∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j)) ≤
      D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j := by
  have hD := weightedHierarchyTerminalMean_mono n m c U hdiag
  rw [weightedHierarchyTerminalMean_const] at hD
  have H : (∑ j : Fin (n+1), hierarchyAtom n m 1 j*(-C j)) ≤
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : hierarchyAtom n m 1 j=0
    · simp only [hj,zero_mul,le_refl]
    · have hC := weightedHierarchyReplica_mono n m c U j (hkernel j hj)
      rw [weightedHierarchyReplica_const] at hC
      exact mul_le_mul_of_nonneg_left hC (hierarchyAtom_nonneg_of_monotone n m 1 (by norm_num) hm hmono j)
  simp only [mul_neg,Finset.sum_neg_distrib] at H
  linarith

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteCovarianceComparison
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

omit [Fintype S] [Nonempty S] in
theorem interpolationCoefficient_continuous (n : ℕ) (I : Fin n → Bool) :
    Continuous (interpolationCoefficient n I) := by
  apply continuous_pi
  intro i
  simp only [interpolationCoefficient]
  split_ifs
  · exact Real.continuous_sqrt
  · exact Real.continuous_sqrt.comp (continuous_const.sub continuous_id)

omit [Fintype S] [Nonempty S] in
theorem interpolationCoefficient_hasDerivAt (n : ℕ) (I : Fin n → Bool)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ∃ a' : Fin n → ℝ, HasDerivAt (interpolationCoefficient n I) a' t ∧
      ∀ i, a' i*interpolationCoefficient n I t i=interpolationRate n I i := by
  let a' : Fin n → ℝ := fun i => if I i then 1/(2*Real.sqrt t) else -(1/(2*Real.sqrt (1-t)))
  refine ⟨a',?_,?_⟩
  · apply hasDerivAt_pi.mpr
    intro i
    dsimp only [a',interpolationCoefficient]
    split_ifs
    · exact Real.hasDerivAt_sqrt ht.1.ne'
    · simpa only [id_eq,Pi.sub_apply,zero_sub,neg_div] using
        (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt (by linarith [ht.2] : 1-t≠0))
  · intro i
    dsimp only [a',interpolationCoefficient,interpolationRate]
    split_ifs
    · have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht.1).ne'
      field_simp
    · have hs : Real.sqrt (1-t)≠0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
      field_simp

theorem observablePressure_covariance_comparison (n : ℕ) (O : Fin n → S → ℝ)
    (c : S → ℝ) (m : Fin n → ℝ) (I : Fin n → Bool)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (D : ℝ) (C : Fin (n+1) → ℝ)
    (hdiag : ∀ s, (∑ i, interpolationRate n I i*(O i s)^2) ≤ D)
    (hkernel : ∀ j, hierarchyAtom n m 1 j≠0 → ∀ s t, -C j ≤ partialObservableCovariance n O (interpolationRate n I) j s t) :
    hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I 1))) 0 ≤
      hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I 0))) 0+
      D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j := by
  let f : ℝ → ℝ := fun t =>
    hierarchyPressure n m (affineLogPartition c (observableExponent n O (interpolationCoefficient n I t))) 0
  let K := D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j
  let d : ℝ → ℝ := fun t =>
    weightedHierarchyTerminalMean n m c (observableExponent n O (interpolationCoefficient n I t))
      (fun s => ∑ i, interpolationRate n I i*(O i s)^2)-
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c (observableExponent n O (interpolationCoefficient n I t)) j
          (partialObservableCovariance n O (interpolationRate n I) j)
  have hc : Continuous f := by
    have H := parameter_contDiff_at_field
      (hierarchyPressure_paramRegular n m _ (observableTerminal_paramRegular n O c)).1 (0:ℝ)
    exact H.continuous.comp (interpolationCoefficient_continuous n I)
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : HasDerivAt f (d t) t := by
    obtain ⟨a',ha,he⟩ := interpolationCoefficient_hasDerivAt n I ht
    simpa only [he] using observablePressure_hasDerivAt_covariance n O c m (interpolationCoefficient n I) ha
  have hB (t : ℝ) : d t≤K := weightedCovariance_bound n m c _ O (interpolationRate n I)
    hm hmono D C hdiag hkernel
  have H : f 1-K≤f 0 := by
    have HM : AntitoneOn (fun t => f t-K*t) (Icc (0:ℝ) 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
        (hc.sub (continuous_const.mul continuous_id)).continuousOn
        (fun t ht => ((hd t (by simpa only [interior_Icc] using ht)).sub
          ((hasDerivAt_id t).const_mul K)).hasDerivWithinAt)
        (fun t _ => by simpa only [mul_one] using sub_nonpos.mpr (hB t))
    simpa using HM (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤1)
  change f 1 ≤ f 0+D+_
  dsimp only [K] at H
  linarith

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockObservable
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

variable {S : Type}

theorem blockObservable_covariance {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s t : S) :
    (∑ i, interpolationRate (blockDimension D N k) (blockInterpolationChoice D N k) i*
      (blockObservable H F i s*blockObservable H F i t))=
      (1/2:ℝ)*(∑ i, H i s*H i t)-(1/2:ℝ)*(∑ b, ∑ i, F b i s*F b i t) := by
  rw [Fin.sum_univ_add]
  simp only [interpolationRate,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,Bool.false_eq_true,ite_true,ite_false]
  rw [← finProdFinEquiv.sum_comp (fun u : Fin ((k+1)*N) =>
    -(1/2:ℝ)*(F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 s*
      F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 t))]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← Finset.mul_sum]
  ring

theorem blockObservable_partial_covariance {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (b : Fin (k+1)) (s t : S) :
    partialObservableCovariance (blockDimension D N k) (blockObservable H F)
      (interpolationRate (blockDimension D N k) (blockInterpolationChoice D N k))
      (blockLevel D N k b) s t=
      (1/2:ℝ)*(∑ i, H i s*H i t)-
        (1/2:ℝ)*(∑ a, if a≤b then ∑ i, F a i s*F a i t else 0) := by
  unfold partialObservableCovariance
  rw [Fin.sum_univ_add]
  have hd (i : Fin D) : (Fin.castAdd ((k+1)*N) i).val < (blockLevel D N k b).val := by
    simp only [Fin.val_castAdd,blockLevel_val]
    omega
  simp only [hd,ite_true,interpolationRate,blockInterpolationChoice,blockObservable,
    Fin.addCases_left,Fin.addCases_right,Bool.false_eq_true,ite_false]
  rw [← finProdFinEquiv.sum_comp (fun u : Fin ((k+1)*N) =>
    if (Fin.natAdd D u).val < (blockLevel D N k b).val then
      -(1/2:ℝ)*(F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 s*
        F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 t) else 0)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← fieldIndex_eq_natAdd,
    fieldIndex_lt_blockLevel_iff,← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_ite_irrel,Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [neg_mul,mul_zero,Finset.sum_const_zero,Finset.sum_neg_distrib,← Finset.mul_sum,neg_zero]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedBlockMass
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

theorem weightedBlockAtom_nonneg (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (t : Fin (blockDimension D N k+1)) :
    0  ≤  weightedBlockAtom D N k w t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact hw b
  · exact le_rfl

theorem weightedBlockAtom_sum (D N k : ℕ) (w : Fin (k+1) → ℝ) :
    ∑ t, weightedBlockAtom D N k w t=∑ b, w b := by
  unfold weightedBlockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockMass_valid (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    (∀ i, weightedBlockMass D N k w i∈Icc (0:ℝ) 1) ∧ Monotone (weightedBlockMass D N k w) := by
  refine ⟨fun i => ⟨massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg D N k w hw) i,?_⟩,
    massFromAtoms_monotone _ _ (weightedBlockAtom_nonneg D N k w hw)⟩
  exact (massFromAtoms_le_sum _ _ (weightedBlockAtom_nonneg D N k w hw) i).trans_eq
    ((weightedBlockAtom_sum D N k w).trans hs)

theorem hierarchyAtom_weightedBlockMass (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hs : ∑ b, w b=1) (t : Fin (blockDimension D N k+1)) :
    hierarchyAtom (blockDimension D N k) (weightedBlockMass D N k w) 1 t=
      weightedBlockAtom D N k w t := by
  rw [← hs,← weightedBlockAtom_sum D N k w]
  exact hierarchyAtom_massFromAtoms _ _ t

theorem weightedBlockAtom_sum_mul (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (f : Fin (blockDimension D N k+1) → ℝ) :
    (∑ j, weightedBlockAtom D N k w j*f j)=∑ b, w b*f (blockLevel D N k b) := by
  simp only [weightedBlockAtom,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockAtom_ne_zero (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (j : Fin (blockDimension D N k+1)) (hj : weightedBlockAtom D N k w j≠0) :
    ∃ b, blockLevel D N k b=j := by
  by_contra h
  push Not at h
  exact hj (by simp only [weightedBlockAtom,h,ite_false,Finset.sum_const_zero])

theorem weightedBlockAtom_at (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hN : 0<N) (b : Fin (k+1)) :
    weightedBlockAtom D N k w (blockLevel D N k b)=w b := by
  unfold weightedBlockAtom
  simp only [(blockLevel_injective D N k hN).eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockCovarianceComparison
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

theorem blockObservable_compare {D N k : ℕ} (hN : 0<N)
    (H : Fin D → S → ℝ) (F : Fin (k+1) → Fin N → S → ℝ) (c : S → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0≤w b) (hs : ∑ b, w b=1)
    (A : ℝ) (C : Fin (k+1) → ℝ)
    (hdiag : ∀ s, (1/2:ℝ)*(∑ i, (H i s)^2)-(1/2:ℝ)*(∑ b, ∑ i, (F b i s)^2) ≤ A)
    (hkernel : ∀ b s t, -C b ≤ (1/2:ℝ)*(∑ i, H i s*H i t)-
      (1/2:ℝ)*(∑ a, if a≤b then ∑ i, F a i s*F a i t else 0)) :
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))) 0 ≤
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 0))) 0+
      A+∑ b, w b*C b := by
  have hm := weightedBlockMass_valid D N k w hw hs
  have HH := observablePressure_covariance_comparison (blockDimension D N k) (blockObservable H F) c
    (weightedBlockMass D N k w) (blockInterpolationChoice D N k) hm.1 hm.2 A (weightedBlockAtom D N k C)
    (fun s => by simpa only [pow_two,blockObservable_covariance] using hdiag s)
    (fun j hj s t => by
      rw [hierarchyAtom_weightedBlockMass D N k w hs] at hj
      obtain ⟨b,rfl⟩ := weightedBlockAtom_ne_zero D N k w j hj
      rw [weightedBlockAtom_at D N k C hN,blockObservable_partial_covariance]
      exact hkernel b s t)
  simp_rw [hierarchyAtom_weightedBlockMass D N k w hs] at HH
  rw [weightedBlockAtom_sum_mul] at HH
  simpa only [weightedBlockAtom_at D N k C hN] using HH

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixCovarianceAlgebra
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

section FiniteGram
variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

theorem finite_linear_covariance (F : I → A → ℝ) (x y : A → ℝ) :
    (∑ i, (∑ a, F i a*x a)*(∑ b, F i b*y b))=
      ∑ a, ∑ b, (∑ i, F i a*F i b)*x a*y b := by
  classical
  simp only [Fintype.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring
end FiniteGram

theorem matrixFieldFeature_covariance {N d r : ℕ} (β : ℝ) (B : Fin r → Fin d → ℝ)
    (X Y : Fin N → Fin d → ℝ) :
    (∑ p : Fin N × Fin r, matrixFieldFeature N d r β B X p*matrixFieldFeature N d r β B Y p)=
      ((N:ℝ)*β^2)*∑ a, ∑ b, factorCovariance d r B a b*replicaCrossOverlap N d X Y a b := by
  by_cases hN : N=0
  · subst N
    simp [matrixFieldFeature]
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  simp only [matrixFieldFeature,Fintype.sum_prod_type]
  have he (i : Fin N) (u : Fin r) :
      (β*(∑ a, B u a*X i a))*(β*(∑ b, B u b*Y i b))=
        β^2*((∑ a, B u a*X i a)*(∑ b, B u b*Y i b)) := by ring
  simp_rw [he,← Finset.mul_sum,finite_linear_covariance]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (i : Fin N) (b : Fin d) => _)]
  simp only [replicaCrossOverlap,factorCovariance,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  simp only [Finset.mul_sum,mul_assoc]
  simp_rw [← Finset.mul_sum]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraKernel
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

theorem matrixSquare_sub (d : ℕ) (R Q : Fin d → Fin d → ℝ) :
    matrixSquare d (fun a b => R a b-Q a b)=matrixSquare d R-2*matrixInner d Q R+matrixSquare d Q := by
  simp only [matrixSquare,matrixInner,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrixSquare_nonneg (d : ℕ) (R : Fin d → Fin d → ℝ) : 0  ≤  matrixSquare d R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem matrixCovariance_lower (d : ℕ) (R Q : Fin d → Fin d → ℝ) :
    -matrixSquare d Q  ≤  matrixSquare d R-2*matrixInner d Q R := by
  have H := matrixSquare_nonneg d (fun a b => R a b-Q a b)
  rw [matrixSquare_sub] at H
  linarith

theorem factorPath_inner (d r k : ℕ) (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (j : Fin (k+1)) (R : Fin d → Fin d → ℝ) :
    matrixInner d (factorPath d r k B j) R=
      ∑ l, if l ≤ j then matrixInner d (factorCovariance d r (B l)) R else 0 := by
  simp only [matrixInner,factorPath,Finset.sum_mul,ite_mul,zero_mul]
  calc
    _ = ∑ a, ∑ l, ∑ b, if l ≤ j then factorCovariance d r (B l) a b*R a b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, if l ≤ j then factorCovariance d r (B l) a b*R a b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp only [Finset.sum_const_zero]

section
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem matrixFieldObservables_covariance {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (l : Fin (k+1)) (s t : S) :
    (∑ u, matrixFieldObservables N d r k β B X l u s*matrixFieldObservables N d r k β B X l u t)=
      ((N:ℝ)*β^2)*matrixInner d (factorCovariance d r (B l)) (replicaCrossOverlap N d (X s) (X t)) := by
  unfold matrixFieldObservables
  rw [← finProdFinEquiv.sum_comp]
  simpa only [Equiv.symm_apply_apply,matrixInner] using matrixFieldFeature_covariance β (B l) (X s) (X t)

omit [Fintype S] [Nonempty S] in
theorem matrixFieldObservables_prefix {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (j : Fin (k+1)) (s t : S) :
    (∑ l, if l ≤ j then ∑ u, matrixFieldObservables N d r k β B X l u s*
      matrixFieldObservables N d r k β B X l u t else 0)=
      ((N:ℝ)*β^2)*matrixInner d (factorPath d r k B j) (replicaCrossOverlap N d (X s) (X t)) := by
  simp_rw [matrixFieldObservables_covariance,factorPath_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraOffset
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

variable {S : Type} [Fintype S] [Nonempty S]

theorem matrixFiniteInterpolation_offset_oai {M N d r k : ℕ} (hN : 0<N) (hr : 0 < r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (H : Fin M → S → ℝ) (C : ℝ)
    (hcov : ∀ s t, (∑ u, H u s*H u t)=
      ((N:ℝ)*β^2/2)*matrixSquare d (replicaCrossOverlap N d (X s) (X t))-C)
    (D : Fin d → Fin d → ℝ) (hself : ∀ s, replicaCrossOverlap N d (X s) (X s)=D)
    (c : S → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    let n:=blockDimension M (N*r) k
    let F:=matrixFieldObservables N d r k β B X
    let m:=weightedBlockMass M (N*r) k w
    let I:=blockInterpolationChoice M (N*r) k
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 1))) 0 ≤
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 0))) 0+
      ((N:ℝ)*β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
        ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let K : ℝ := (N:ℝ)*β^2/4
  have hK : 0 ≤ K := by positivity
  have HC := blockObservable_compare (Nat.mul_pos hN hr) H
    (matrixFieldObservables N d r k β B X) c w hw hs
    (K*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D)-C/2)
    (fun j => K*matrixSquare d (factorPath d r k B j)+C/2)
    (fun s => by
      simp only [pow_two]
      rw [hcov]
      have HF := matrixFieldObservables_prefix β B X (Fin.last k) s s
      simp only [Fin.le_last,ite_true] at HF
      rw [HF,hself s]
      dsimp only [K]
      ring_nf
      exact le_rfl)
    (fun j s t => by
      rw [hcov,matrixFieldObservables_prefix]
      have HK := mul_le_mul_of_nonneg_left (matrixCovariance_lower d (replicaCrossOverlap N d (X s) (X t))
        (factorPath d r k B j)) hK
      dsimp only [K] at HK ⊢
      nlinarith)
  have he : (∑ j, w j*(K*matrixSquare d (factorPath d r k B j)+C/2))=
      K*∑ j, w j*matrixSquare d (factorPath d r k B j)+C/2 := by
    simp_rw [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at HC
  dsimp only
  convert HC using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [K]
  ring

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.matrixFiniteInterpolation_offset_oai := @OAI.SK.Analytic.matrixFiniteInterpolation_offset_oai
