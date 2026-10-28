-- Prove2me | solution 1 for OAI.SK.Analytic.scalarCDFParisi_origin_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:15:16.194349+00:00
-- url     : https://prove2.me/submissions/b997cc45-3a77-4dec-92c4-9de8a751c809

import Mathlib
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_scalarCDFPotential_minimum_bound

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

theorem gaussian_abs_pow_integrable (n : ℕ) :
    Integrable (fun z : ℝ => |z|^n) (gaussianReal 0 1) := by
  have H := (memLp_id_gaussianReal' (μ:=0) (v:=1) (n:ℝ≥0∞) (by simp)).integrable_norm_pow'
  simpa only [id_eq,Real.norm_eq_abs] using H

theorem gaussian_second_moment : (∫ z : ℝ, z^2 ∂gaussianReal 0 1)=1 := by
  have H := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (by fun_prop)] at H
  simpa using H

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

end GaussianGrowth

section LinearGrowth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasExpGrowth.linear (L : E →L[ℝ] ℝ) : HasExpGrowth L := by
  apply (HasExpGrowth.norm_id (E := E)).congr_bound (norm_nonneg L)
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using L.le_opNorm x

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
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
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

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianRotation
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

theorem gaussianPair_fst : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_fst.hasLaw

theorem gaussianPair_snd : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_snd.hasLaw

theorem gaussianPair_independent : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd gaussianPair := by
  exact (indepFun_iff_hasLaw_prodMk_prod gaussianPair_fst gaussianPair_snd).2 HasLaw.id

theorem gaussianPair_gaussian : HasGaussianLaw (fun p : ℝ × ℝ => p) gaussianPair :=
  gaussianPair_independent.hasGaussianLaw gaussianPair_fst.hasGaussianLaw gaussianPair_snd.hasGaussianLaw

theorem gaussianMix_gaussian (a b : ℝ) : HasGaussianLaw (gaussianMix a b) gaussianPair :=
  gaussianPair_gaussian.map_fun (gaussianMixCLM a b)

theorem gaussianMix_mean (a b : ℝ) : (∫ p, gaussianMix a b p ∂gaussianPair)=0 := by
  unfold gaussianMix
  rw [integral_add (gaussianPair_fst.hasGaussianLaw.integrable.const_mul a)
    (gaussianPair_snd.hasGaussianLaw.integrable.const_mul b),integral_const_mul,integral_const_mul]
  have hf := gaussianPair_fst.integral_comp (continuous_id.aestronglyMeasurable)
  have hs := gaussianPair_snd.integral_comp (continuous_id.aestronglyMeasurable)
  simp only [Function.comp_def,id_eq,integral_id_gaussianReal] at hf hs
  rw [hf,hs]; ring

theorem gaussianMix_covariance (a b c d : ℝ) :
    cov[gaussianMix a b,gaussianMix c d;gaussianPair]=a*c+b*d := by
  have hcross : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=0 :=
    gaussianPair_independent.covariance_eq_zero gaussianPair_fst.hasGaussianLaw.memLp_two
      gaussianPair_snd.hasGaussianLaw.memLp_two
  have hf : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.fst;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_fst.aemeasurable]
    have H := gaussianPair_fst.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  have hs : cov[(Prod.snd : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_snd.aemeasurable]
    have H := gaussianPair_snd.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  unfold gaussianMix
  rw [SK.covariance_linear_combination gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two,hf,hs,hcross,covariance_comm Prod.snd,hcross]
  ring

theorem gaussianMix_law (a b : ℝ) (hab : a^2+b^2=1) :
    HasLaw (gaussianMix a b) (gaussianReal 0 1) gaussianPair := by
  have hg := gaussianMix_gaussian a b
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,gaussianMix_mean,← covariance_self hg.aemeasurable,
    gaussianMix_covariance]
  have he : a*a+b*b=1 := by nlinarith [hab]
  rw [he]; norm_num

theorem gaussianRotate_law (θ : ℝ) : HasLaw (gaussianRotate θ) gaussianPair gaussianPair := by
  have hg : HasGaussianLaw (gaussianRotate θ) gaussianPair :=
    gaussianPair_gaussian.map_fun ((gaussianMixCLM (Real.cos θ) (Real.sin θ)).prod
      (gaussianMixCLM (-Real.sin θ) (Real.cos θ)))
  have hi := hg.indepFun_of_covariance_eq_zero (by rw [gaussianMix_covariance]; ring)
  exact hi.hasLaw_prod
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem gaussianRotate_inverse (θ : ℝ) (p : ℝ × ℝ) :
    gaussianRotate (-θ) (gaussianRotate θ p)=p := by
  ext <;> simp only [gaussianRotate,gaussianMix,Real.cos_neg,Real.sin_neg]
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.1 := by ring
      _=p.1 := by rw [Real.sin_sq_add_cos_sq]; ring
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.2 := by ring
      _=p.2 := by rw [Real.sin_sq_add_cos_sq]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCovariance
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

theorem gaussianPair_integrable_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) : Integrable f gaussianPair := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_integrable_linear_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hB : ∀ p, |f p| ≤ B*(|p.1|+|p.2|)+C) : Integrable f gaussianPair := by
  have hi := ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
    gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul B).add (integrable_const C)
  apply hi.mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_rotation_derivative {f g dg : ℝ → ℝ}
    (hf : Continuous f) (hd : ∀ x, HasDerivAt g (dg x) x) (hc : Continuous dg)
    {B D C : ℝ} (hB : 0 ≤ B) (_hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdg : ∀ x, |g x| ≤ D) (hdc : ∀ x, |dg x| ≤ C) (θ : ℝ) :
    HasDerivAt (fun a => ∫ p, f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p) ∂gaussianPair)
      (∫ p, f p.1*dg (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair) θ := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm (a : ℝ) (p : ℝ × ℝ) :
      |gaussianMix (-Real.sin a) (Real.cos a) p| ≤ |p.1|+|p.2| := by
    unfold gaussianMix
    calc
      _ ≤ |-Real.sin a*p.1|+|Real.cos a*p.2| := abs_add_le _ _
      _ ≤ |p.1|+|p.2| := by
        simp only [abs_mul,abs_neg]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
  have hi : Integrable (fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) gaussianPair := by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using
      ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
        gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul (B*C))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=θ)
    (F:=fun a p => f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p))
    (F':=fun a p => f p.1*dg (gaussianMix (Real.cos a) (Real.sin a) p)*gaussianMix (-Real.sin a) (Real.cos a) p)
    (bound:=fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) (by simp) _ _ _ _ hi _).2
  · exact Eventually.of_forall (fun a => (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · apply gaussianPair_integrable_bounded (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop)))
    intro p; simp only [Function.comp_def,Pi.mul_apply,abs_mul]; exact mul_le_mul (hb _) (hdg _) (abs_nonneg _) hB
  · exact (((hf.comp continuous_fst).mul (hc.comp (by unfold gaussianMix; fun_prop))).mul
      (by unfold gaussianMix; fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun p a _ => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hb _) (hdc _) (abs_nonneg _) hB) (hm a p)
        (abs_nonneg _) (mul_nonneg hB hC))
  · exact ae_of_all _ (fun p a _ => by
      have H := (hd (gaussianMix (Real.cos a) (Real.sin a) p)).comp a
        (((Real.hasDerivAt_cos a).mul_const p.1).add ((Real.hasDerivAt_sin a).mul_const p.2))
      simpa only [gaussianMix,mul_assoc,Function.comp_def,Pi.add_apply] using H.const_mul (f p.1))

theorem gaussianPair_rotation_stein {f df k : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df) (hk : Continuous k)
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) (hkd : ∀ x, |k x| ≤ D) (θ : ℝ) :
    (∫ p, f p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair)=
      -Real.sin θ*(∫ p, df p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p) ∂gaussianPair) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let A : ℝ × ℝ → ℝ := fun p => f (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1*p.2
  let A' : ℝ × ℝ → ℝ := fun p => df (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1
  have hAc : Continuous A := by dsimp [A,gaussianMix]; fun_prop
  have hA'c : Continuous A' := by dsimp [A',gaussianMix]; fun_prop
  have heq (p : ℝ × ℝ) : gaussianMix (Real.cos θ) (-Real.sin θ) (gaussianRotate θ p)=p.1 := by
    have H := congrArg Prod.fst (gaussianRotate_inverse θ p)
    simpa only [gaussianRotate,Real.cos_neg,Real.sin_neg] using H
  have hA : (fun p => A (gaussianRotate θ p))=(fun p => f p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)*gaussianMix (-Real.sin θ) (Real.cos θ) p) := by
    funext p; dsimp only [A]; rw [heq]; rfl
  have hA' : (fun p => A' (gaussianRotate θ p))=(fun p => df p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)) := by
    funext p; dsimp only [A']; rw [heq]; rfl
  have HA := (gaussianRotate_law θ).integral_comp hAc.aestronglyMeasurable
  have HA' := (gaussianRotate_law θ).integral_comp hA'c.aestronglyMeasurable
  simp only [Function.comp_def] at HA HA'
  rw [← hA,← hA',HA,HA']
  have hAi : Integrable A gaussianPair := by
    apply gaussianPair_integrable_linear_bounded hAc (B:=B*D) (C:=0)
    intro p
    dsimp [A]; rw [abs_mul,abs_mul]
    calc
      _ ≤ B*D*|p.2| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hb _) (hkd _) (abs_nonneg _) hB) (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hB hD,abs_nonneg p.1]
  have hA'i : Integrable A' gaussianPair := by
    apply gaussianPair_integrable_bounded hA'c
    intro p
    dsimp [A']; rw [abs_mul]
    exact mul_le_mul (hdf _) (hkd _) (abs_nonneg _) hC
  rw [show gaussianPair=(gaussianReal 0 1).prod (gaussianReal 0 1) from rfl,
    integral_prod _ hAi,integral_prod _ hA'i,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    have hfc : Continuous (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hdfc : Continuous (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hfint : Integrable (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) :=
      (integrable_const B).mono' hfc.aestronglyMeasurable (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb _))
    have hdint : Integrable (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply (integrable_const (|Real.sin θ| *C)).mono' hdfc.aestronglyMeasurable
      exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_mul,abs_neg]; exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _))
    have hzint : Integrable (fun z : ℝ => z*f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply ((HasExpGrowth.norm_id (E:=ℝ)).integrable_gaussianMeasure continuous_norm (μ:=gaussianReal 0 1) |>.mul_const B).mono'
        (continuous_id.mul hfc).aestronglyMeasurable
      exact ae_of_all _ (fun z => by simp only [Real.norm_eq_abs,Pi.mul_apply,id_eq,abs_mul]; exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _))
    have H := gaussian_integral_mul_eq_integral_deriv _ _ (fun z => by
      simpa only [mul_comm,Function.comp_def,Pi.sub_apply,id_eq,mul_one,one_mul,zero_sub] using (hd (Real.cos θ*y-Real.sin θ*z)).comp z
        ((hasDerivAt_const z (Real.cos θ*y)).sub ((hasDerivAt_id z).const_mul (Real.sin θ)))) hfint hdint hzint
    dsimp only [A,A',gaussianMix]
    simp only [neg_mul,← sub_eq_add_neg]
    calc
      _=k y*(∫ z : ℝ, z*f (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]; congr 1; funext z; ring
      _=k y*(∫ z : ℝ, -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by rw [H]
      _=_ := by rw [integral_const_mul,integral_mul_const]; ring)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianAngle_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    Continuous (gaussianAngle f g) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  apply continuousAt_of_dominated (bound:=fun _ : ℝ × ℝ => B*C)
  · exact Eventually.of_forall (fun a => ((hf.comp continuous_fst).mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB))
  · exact integrable_const _
  · exact ae_of_all _ (fun p => (continuous_const.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).continuousAt)

theorem gaussian_integrable_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f (gaussianReal 0 1) := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem gaussian_integrable_sq_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Integrable (fun x => f x^2) (gaussianReal 0 1) :=
  gaussian_integrable_bounded (hf.pow 2) (fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x))

theorem gaussianAngle_zero (f : ℝ → ℝ) (hf : Continuous f) :
    gaussianAngle f f 0=∫ x, f x^2 ∂gaussianReal 0 1 := by
  have H := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  simpa only [gaussianAngle,gaussianMix,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,
    add_zero,pow_two,Function.comp_def,Pi.mul_apply] using H

theorem gaussianAngle_pi_half {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    gaussianAngle f g (Real.pi/2)=(∫ x, f x ∂gaussianReal 0 1)*(∫ x, g x ∂gaussianReal 0 1) := by
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*g p.2) gaussianPair :=
    gaussianPair_integrable_bounded (by fun_prop) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB)
  simp only [gaussianAngle,gaussianMix,Real.cos_pi_div_two,Real.sin_pi_div_two,
    zero_mul,one_mul,zero_add,gaussianPair]
  rw [integral_prod _ hi]
  simp only [integral_const_mul,integral_mul_const]

theorem gaussianAngle_le_square {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (θ : ℝ) :
    gaussianAngle f f θ ≤ ∫ x, f x^2 ∂gaussianReal 0 1 := by
  have hfc : Continuous (fun p : ℝ × ℝ => f p.1) := hf.comp continuous_fst
  have hgc : Continuous (fun p : ℝ × ℝ => f (gaussianMix (Real.cos θ) (Real.sin θ) p)) :=
    hf.comp (by unfold gaussianMix; fun_prop)
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*f (gaussianMix (Real.cos θ) (Real.sin θ) p)) gaussianPair :=
    gaussianPair_integrable_bounded (hfc.mul hgc) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hB)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hf2 := gaussianPair_integrable_bounded (hfc.pow 2) (fun p => hb2 p.1)
  have hg2 := gaussianPair_integrable_bounded (hgc.pow 2) (fun p => hb2 _)
  have H := integral_mono (hi.const_mul 2) (hf2.add hg2)
    (fun p => by dsimp; nlinarith [sq_nonneg (f p.1-f (gaussianMix (Real.cos θ) (Real.sin θ) p))])
  simp only [Pi.add_apply,Pi.pow_apply] at hf2 hg2 H
  have Hplus := integral_add hf2 hg2
  simp only [Pi.pow_apply] at Hplus
  rw [integral_const_mul,Hplus] at H
  have HA := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  have HB := (gaussianMix_law (Real.cos θ) (Real.sin θ)
    (by nlinarith [Real.sin_sq_add_cos_sq θ])).integral_comp (hf.pow 2).aestronglyMeasurable
  simp only [Function.comp_def,Pi.pow_apply] at HA HB
  rw [HA,HB] at H
  exact (by change _ ≤ _; unfold gaussianAngle; linarith)

theorem gaussian_variance_pos {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x ∂gaussianReal 0 1)^2 < ∫ x, f x^2 ∂gaussianReal 0 1 := by
  let a : ℝ := ∫ x, f x ∂gaussianReal 0 1
  have hint := gaussian_integrable_bounded hf hb
  have hi2 := gaussian_integrable_sq_bounded hf hB hb
  have his : Integrable (fun x => (f x-a)^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hf.sub continuous_const) (B:=B+|a|) (by positivity)
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) (le_refl _)))
  have hp : 0<∫ x, (f x-a)^2 ∂gaussianReal 0 1 := by
    apply lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (f x-a)))
    intro he
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x-a)) his).mp he.symm
    have hv := hz.filter_mono (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0)≠0)).ae_le
    have heq := MeasureTheory.Measure.eq_of_ae_eq hv ((hf.sub continuous_const).pow 2) continuous_const
    apply hne
    refine ⟨a,fun x => ?_⟩
    have H := congrFun heq x
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp H)
  have he : (∫ x, (f x-a)^2 ∂gaussianReal 0 1)=
      (∫ x, f x^2 ∂gaussianReal 0 1)-a^2 := by
    simp_rw [show ∀ x, (f x-a)^2=f x^2-2*a*f x+a^2 by intro x; ring]
    have Hplus := integral_add (hi2.sub (hint.const_mul (2*a))) (integrable_const (a^2))
    have Hsub := integral_sub hi2 (hint.const_mul (2*a))
    simp only [Pi.sub_apply] at Hplus Hsub
    rw [Hplus,Hsub,integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    dsimp only [a]; ring
  rw [he] at hp
  exact sub_pos.mp hp

end SK.Analytic

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
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFDerivativeConvergence
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

theorem uniform_derivative_convergence {F D : ℕ → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x) (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ n, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f atTop) : TendstoUniformly D d atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ] with n hn x
  have hb (z : ℝ) : |F n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD n z).sub (hd z)) ((hLip n).sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

theorem scalarCDFValue_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) 0 1)
      (scalarCDFValue β α 0 1) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm 0 1 le_rfl x
  have HE : (∫ z in (0:ℝ)..0+(1:ℝ≥0), |αn n z-α z|)=cdfDistance (αn n) α := by
    simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc,cdfDistance]
  rw [HE] at H
  rw [Real.dist_eq,abs_sub_comm]
  exact H.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) 0 1)
      (scalarCDFHessian β α 0 1) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) 0 1 le_rfl x)
    (scalarCDFGradient_hasDerivAt β hα hαm 0 1 le_rfl)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) 0 1 le_rfl)
    (scalarCDFHessian_lipschitz β hα hαm 0 1 le_rfl)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) 0 1 le_rfl x)
    (scalarCDFValue_hasDerivAt β hα hαm 0 1 le_rfl)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) 0 1 le_rfl)
    (scalarCDFGradient_lipschitz β hα hαm 0 1 le_rfl)
    (scalarCDFValue_tendstoUniformly β hα hαm hn hnm hD)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSemigroup
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

theorem scalarCDFOperator_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : LipschitzWith L g)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) {ε : ℝ} (hfg : ∀ x, |f x-g x|≤ε) (x : ℝ) :
    |scalarCDFOperator β α s t f x-scalarCDFOperator β α s t g x|≤ε := by
  apply le_of_tendsto (((dyadicScalar_general_uniform hf hK β hα hm s t ht).tendsto_at x).sub
    ((dyadicScalar_general_uniform hg hL β hα hm s t ht).tendsto_at x)).abs
  exact Eventually.of_forall (fun n => dyadicScalar_uniform_nonexpansive hf hg β hα n s t hfg x)

theorem scalarCDFValue_semigroup_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFValue β (quantileCDF k Q) 0 1=
      scalarCDFOperator β (quantileCDF k Q) 0 (Real.toNNReal q)
        (scalarCDFValue β (quantileCDF k Q) q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal (1-q) (sub_nonneg.mpr hq.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r≤1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have hsplit : chainDuration l=t+r := by rw [hd]; apply NNReal.coe_injective; rw [NNReal.coe_add,ht,hr,NNReal.coe_one]; ring
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel t r hsplit
  have htail : scalarCDFValue β (quantileCDF k Q) q r=scalarTimeChain β l₂ scalarSpinTerminal := by
    funext x
    apply scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l₂ hm₂ q r hr1 h₂
    simpa only [zero_add,ht] using hs₂
  funext x
  change scalarCDFOperator β (quantileCDF k Q) 0 1 scalarSpinTerminal x=
    scalarCDFOperator β (quantileCDF k Q) 0 t (scalarCDFValue β (quantileCDF k Q) q r) x
  rw [htail,scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l hm 0 1 le_rfl hd hmodel,
    scalarCDFOperator_eq_chain (scalarTimeChain_regular scalarSpinTerminal_regular β l₂)
      (scalarTimeChain_lipschitz scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β l₂ (fun p hp => (hm₂ p hp).1))
      β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l₁ hm₁ 0 t ht1 h₁ hs₁]
  exact (congrFun (he scalarSpinTerminal scalarSpinTerminal_regular) x).symm

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

theorem scalarCDFOperator_semigroup_of_chain {f : ℝ → ℝ}
    (hf : BoundedDerivs f) {K : ℝ≥0} (hK : LipschitzWith K f)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t r : ℝ≥0) (htr : t+r ≤ 1) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1) (hd : chainDuration l=t+r)
    (hmodel : TimeChainModels α s l) :
    scalarCDFOperator β α s (t+r) f=
      scalarCDFOperator β α s t (scalarCDFOperator β α (s+t) r f) := by
  have ht : t ≤ 1 := (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ r from bot_le)).trans htr
  have hr : r ≤ 1 := (le_add_of_nonneg_left (show (0:ℝ≥0) ≤ t from bot_le)).trans htr
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β α l hm s hmodel t r hd
  have htail : scalarCDFOperator β α (s+t) r f=scalarTimeChain β l₂ f := by
    funext x
    exact scalarCDFOperator_eq_chain hf hK β ha hmono l₂ hm₂ (s+t) r hr h₂ hs₂ x
  funext x
  rw [htail,scalarCDFOperator_eq_chain hf hK β ha hmono l hm s (t+r) htr hd hmodel,
    scalarCDFOperator_eq_chain (scalarTimeChain_regular hf β l₂)
      (scalarTimeChain_lipschitz hf hK β l₂ (fun p hp => (hm₂ p hp).1))
      β ha hmono l₁ hm₁ s t ht h₁ hs₁]
  exact (congrFun (he f hf) x).symm

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

theorem scalarCDFValue_suffix_semigroup_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s q : ℝ} (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β (quantileCDF k Q) s (Real.toNNReal (1-s))=
      scalarCDFOperator β (quantileCDF k Q) s (Real.toNNReal (q-s))
        (scalarCDFValue β (quantileCDF k Q) q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hb : t+r=Real.toNNReal (1-s) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,ht,hr,Real.coe_toNNReal _ (by linarith)]
    ring
  have htr : t+r ≤ 1 := by rw [← NNReal.coe_le_coe,NNReal.coe_add,ht,hr,NNReal.coe_one]; linarith
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hsq.trans hq⟩
  have H := scalarCDFOperator_semigroup_of_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) s t r htr l hm (hd.trans hb.symm) hmodel
  rw [hb,show s+(t:ℝ)=q by rw [ht]; ring] at H
  exact H

theorem scalarCDFValue_suffix_semigroup (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β α s (Real.toNNReal (1-s))=
      scalarCDFOperator β α s (Real.toNNReal (q-s))
        (scalarCDFValue β α q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  let u := Real.toNNReal (1-s)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hu : (u:ℝ)=1-s := Real.coe_toNNReal _ (sub_nonneg.mpr (hsq.trans hq))
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; linarith
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith
  have hu1 : u ≤ 1 := by rw [← NNReal.coe_le_coe,hu,NNReal.coe_one]; linarith
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hb (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD : Tendsto (fun n => cdfDistance (a n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α ha h1
  funext x
  have hvalue (n : ℕ) {b : ℝ} {v : ℝ≥0} (hb0 : 0 ≤ b) (hv1 : b+v ≤ 1) (hv : v ≤ 1) (z : ℝ) :
      |scalarCDFValue β (a n) b v z-scalarCDFValue β α b v z| ≤ scalarTimeMassConstant β*cdfDistance (a n) α :=
    (scalarCDFValue_cdf_lipschitz β (hb n) (hm n) ha α.mono b v hv z).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hb0 hv1)
        (scalarTimeMassConstant_nonneg β))
  have herr (n : ℕ) : |scalarCDFValue β α s u x-
      scalarCDFOperator β α s t (scalarCDFValue β α q r) x| ≤
      (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
    have E := hvalue n (hs.trans hsq) (v:=r) (by rw [hr]; linarith) hr1
    have H₁ := scalarCDFOperator_uniform_nonexpansive
      (scalarCDFValue_regular β (hb n) (hm n) q r hr1) (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β (hb n) (hm n) q r hr1) (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      β (hb n) (hm n) s t ht1 E x
    have H₂ := (scalarCDFOperator_cdf_lipschitz (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1) β (hb n) (hm n) ha α.mono s t ht1 x).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hs (by rw [ht]; linarith))
        (scalarTimeMassConstantK_nonneg β 1))
    have H₀ := hvalue n hs (v:=u) (by rw [hu]; linarith) hu1 x
    rw [abs_sub_comm] at H₀
    have he := congrFun (scalarCDFValue_suffix_semigroup_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hs hsq hq) x
    calc
      _  ≤  |scalarCDFValue β α s u x-scalarCDFValue β (a n) s u x|+
          |scalarCDFValue β (a n) s u x-scalarCDFOperator β α s t (scalarCDFValue β α q r) x| := abs_sub_le _ _ _
      _  ≤  scalarTimeMassConstant β*cdfDistance (a n) α+
          (scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
        apply add_le_add H₀
        change |scalarCDFValue β (quantileCDF n (uniformCDFQuantiles n α)) s (Real.toNNReal (1-s)) x-_| ≤ _
        rw [he]
        exact (abs_sub_le _ _ _).trans ((add_le_add H₁ H₂).trans_eq (by ring))
      _ = _ := by ring
  have H := ge_of_tendsto (hD.const_mul (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1))
    (Eventually.of_forall herr)
  simp only [mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFHeatPrefix
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

theorem gaussianHeat_hasDerivAt {f df : ℝ → ℝ} (hf : BoundedDerivs f)
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {C : ℝ} (hb : ∀ x, |df x|  ≤  C) (v x : ℝ) :
    HasDerivAt (gaussianHeat v f) (gaussianHeat v df x) x := by
  let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=x)
    (F:=fun a z => f (a+v*z)) (F':=fun a z => df (a+v*z)) (bound:=fun _ : ℝ => C)
    (by simp) _ _ _ _ (integrable_const C) _).2
  · exact Eventually.of_forall (fun a => (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact ((hf.translate x).compCLM L).hasExpGrowth.integrable_gaussianMeasure
      ((hf.translate x).compCLM L).1.continuous
  · exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun z a _ => by simpa only [Real.norm_eq_abs] using hb (a+v*z))
  · exact ae_of_all _ (fun z a _ => by
      convert (hd (a+v*z)).comp a ((hasDerivAt_id a).add_const (v*z)) using 1 <;> first | rfl | simp)

theorem scalarCDFOperator_zero_on {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (hz : ∀ z∈Ico s (s+t), α z=0) :
    scalarCDFOperator β α s t f=gaussianHeat (β*Real.sqrt (t:ℝ)) f := by
  funext x
  rw [scalarCDFOperator_eq_chain hf hK β ha hm [(0,t)] (by simp) s t ht (by simp)
    (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChain,scalarTimeStep,scalarStep,gaussianStep,gaussianHeat]

theorem scalarCDFAverage_zero_on {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hc : Continuous dg)
    {K B C : ℝ≥0} (hK : LipschitzWith K f)
    (hB : ∀ y, |g y|  ≤  B) (hC : ∀ y, |dg y|  ≤  C)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (hz : ∀ z∈Ico s (s+t), α z=0) (x : ℝ) :
    scalarCDFAverage β α s t f g x=gaussianHeat (β*Real.sqrt (t:ℝ)) g x := by
  rw [scalarCDFAverage_eq_chainAverage hf hg hc hK hB hC β ha hm [(0,t)] (by simp)
    s t ht (by simp) (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChainAverage,scalarHierarchyAverage,scalarStepAverage,gaussianAverage,
    gaussianStepLaw,gaussianHeat]

theorem scalarCDFGradient_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0 ≤ s) (hsq : s ≤ q) (hq : q ≤ 1) (hz : ∀ z∈Ico s q, α z=0) :
    scalarCDFGradient β α s (Real.toNNReal (1-s))=
      gaussianHeat (β*Real.sqrt (q-s)) (scalarCDFGradient β α q (Real.toNNReal (1-q))) := by
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu : Real.toNNReal (1-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have he := scalarCDFValue_suffix_semigroup β α ha h1 hs hsq hq
  rw [scalarCDFOperator_zero_on (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_lipschitz β ha α.mono q _ hr) β ha α.mono s _ ht
    (by simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hsq),add_sub_cancel] using hz),
    Real.coe_toNNReal _ (sub_nonneg.mpr hsq)] at he
  funext x
  have HD := scalarCDFValue_hasDerivAt β ha α.mono s _ hu x
  rw [he] at HD
  exact HD.unique (gaussianHeat_hasDerivAt (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_hasDerivAt β ha α.mono q _ hr)
    (scalarCDFGradient_lipschitz β ha α.mono q _ hr).continuous
    (fun y => (scalarCDF_derivative_bounds β ha α.mono q _ hr y).1) _ x)

theorem scalarCDFOverlap_heat_prefix (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) (hz : ∀ z∈Ico 0 q, α z=0) :
    scalarCDFOverlap β α q=∫ z, (scalarCDFGradient β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1 := by
  have ht : Real.toNNReal q ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; exact hq.2
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hq.1]
  obtain ⟨hd,hc,hB,hC⟩ := scalarCDFGradient_sq_regular β ha hm q _ hr
  unfold scalarCDFOverlap
  rw [scalarCDFAverage_zero_on (B:=1) (C:=2) (scalarCDFValue_regular β ha hm q _ hr) hd hc
    (scalarCDFValue_lipschitz β ha hm q _ hr) hB hC β ha hm 0 _ ht
    (by simpa only [zero_add,Real.coe_toNNReal _ hq.1] using hz)]
  simp only [gaussianHeat,Real.coe_toNNReal _ hq.1,zero_add]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCramer
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

theorem gaussian_covariance_derivative {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, z*f z ∂gaussianReal 0 1)=∫ z, df z ∂gaussianReal 0 1 := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  apply gaussian_integral_mul_eq_integral_deriv f df hd
    (gaussian_integrable_bounded hf hb) (gaussian_integrable_bounded hc hdf)
  apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
    ((continuous_id.mul hf).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
    simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))

theorem gaussian_cramer_variance {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, df z ∂gaussianReal 0 1)^2 ≤
      (∫ z, f z^2 ∂gaussianReal 0 1)-(∫ z, f z ∂gaussianReal 0 1)^2 := by
  let m := ∫ z, f z ∂gaussianReal 0 1
  let d := ∫ z, df z ∂gaussianReal 0 1
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hi := gaussian_integrable_bounded hf hb
  have h2 := gaussian_integrable_sq_bounded hf hB hb
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable le_rfl
  have hz2 : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
    simpa only [sq_abs] using gaussian_abs_pow_integrable 2
  have hfz : Integrable (fun z : ℝ => z*f z) (gaussianReal 0 1) := by
    apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
      ((continuous_id.mul hf).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
      simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))
  have heq (z : ℝ) : (f z-m-d*z)^2 =
      f z^2-2*m*f z+m^2-2*d*(z*f z)+2*m*d*z+d^2*z^2 := by ring
  have H : 0 ≤ ∫ z, (f z-m-d*z)^2 ∂gaussianReal 0 1 := integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [heq] at H
  have hA := integral_sub h2 (hi.const_mul (2*m))
  have hB' := integral_add (h2.sub (hi.const_mul (2*m))) (integrable_const (m^2))
  have hC' := integral_sub ((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2)))
    (hfz.const_mul (2*d))
  have hD' := integral_add (((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))) (hz.const_mul (2*m*d))
  have hE' := integral_add ((((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))).add (hz.const_mul (2*m*d))) (hz2.const_mul (d^2))
  simp only [Pi.add_apply,Pi.sub_apply] at hA hB' hC' hD' hE'
  rw [hE',hD',hC',hB',hA] at H
  rw [integral_const_mul (2*m*d) (fun z : ℝ => z),
    show (∫ z : ℝ, z ∂gaussianReal 0 1)=0 from integral_id_gaussianReal] at H
  simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,
    gaussian_second_moment,mul_zero,add_zero,mul_one,
    gaussian_covariance_derivative hd hc hb hdf] at H
  dsimp [m,d] at H ⊢
  nlinarith

theorem gaussianHeat_variance_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a x : ℝ) : a^2*(gaussianHeat a df x)^2 ≤
      gaussianHeat a (fun y => f y^2) x-(gaussianHeat a f x)^2 := by
  have HD (z : ℝ) : HasDerivAt (fun z => f (x+a*z)) (a*df (x+a*z)) z := by
    convert (hd (x+a*z)).comp z (((hasDerivAt_id z).const_mul a).const_add x) using 1 <;>
      first | rfl | ring
  have H := gaussian_cramer_variance HD (by fun_prop) hB (fun z => hb (x+a*z))
    (C:=|a| * C) (fun z => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hdf (x+a*z)) (abs_nonneg a))
  rw [integral_const_mul] at H
  simpa only [mul_pow,gaussianHeat] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianHeatVariance
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

theorem gaussianHeat_abs_le {f : ℝ → ℝ} {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    (a x : ℝ) : |gaussianHeat a f x| ≤ B := by
  have H := norm_integral_le_of_norm_le (μ:=gaussianReal 0 1) (f:=fun z => f (x+a*z)) (integrable_const B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb (x+a*z)))
  simpa only [gaussianHeat,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using H

theorem gaussianHeat_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => gaussianHeat p.1 f p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B)
  · exact Eventually.of_forall (fun a => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb (a.2+a.1*z)))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => (hf.comp (by fun_prop)).continuousAt)

theorem gaussianHeat_variance_integral_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a b c : ℝ) (he : c^2=b^2+a^2) :
    a^2*(∫ z, (gaussianHeat a df (b*z))^2 ∂gaussianReal 0 1) ≤
      (∫ z, f (c*z)^2 ∂gaussianReal 0 1)-
        (∫ z, (gaussianHeat a f (b*z))^2 ∂gaussianReal 0 1) := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hdheat := gaussianHeat_continuous hc hdf
  have hfheat := gaussianHeat_continuous hf hb
  have hf2heat := gaussianHeat_continuous (hf.pow 2) hb2
  have hi1 : Integrable (fun z => (gaussianHeat a df (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hdheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hC (fun z => gaussianHeat_abs_le hdf a _)
  have hi2 : Integrable (fun z => gaussianHeat a (fun y => f y^2) (b*z)) (gaussianReal 0 1) :=
    gaussian_integrable_bounded (hf2heat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) (fun z => gaussianHeat_abs_le hb2 a _)
  have hi3 : Integrable (fun z => (gaussianHeat a f (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hfheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hB (fun z => gaussianHeat_abs_le hb a _)
  have H := integral_mono (hi1.const_mul (a^2)) (hi2.sub hi3)
    (fun z => gaussianHeat_variance_lower hd hc hB hb hdf a (b*z))
  have HI := integral_sub hi2 hi3
  simp only [Pi.sub_apply] at H
  rw [integral_const_mul,HI] at H
  have HC := integral_gaussian_sum (hf.pow 2)
    (HasExpGrowth.of_bounded (sq_nonneg B) (fun x => by
      simpa only [Real.norm_eq_abs,Pi.pow_apply] using hb2 x)) b a c he
  change (∫ z, gaussianHeat a (fun y => f y^2) (b*z) ∂gaussianReal 0 1)=_ at HC
  rw [HC] at H
  exact H

theorem gaussianHeat_sq_average_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => ∫ z, (gaussianHeat p.1 f (p.2*z))^2 ∂gaussianReal 0 1) := by
  have hh := gaussianHeat_continuous hf hb
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B^2)
  · exact Eventually.of_forall (fun a => ((hh.comp (show Continuous (fun z : ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (gaussianHeat_abs_le hb a.1 (a.2*z))))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => ((hh.comp (show Continuous (fun a : ℝ × ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).continuousAt)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianAngle_hasDerivAt {f df g dg : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (df x) x) (hfc : Continuous df)
    (hdg : ∀ x, HasDerivAt g (dg x) x) (hgc : Continuous dg)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |df x| ≤ C)
    (hd : ∀ x, |g x| ≤ D) (he : ∀ x, |dg x| ≤ E) (θ : ℝ) :
    HasDerivAt (gaussianAngle f g) (-Real.sin θ*gaussianAngle df dg θ) θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hdf x).continuousAt)
  have H := gaussianPair_rotation_derivative hf hdg hgc hB hD hE hb hd he θ
  rw [gaussianPair_rotation_stein hdf hfc hgc hB hC hE hb hc he θ] at H
  exact H

theorem gaussian_variance_angle_identity {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2=
      ∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=Real.pi/2)
    (fun θ _ => gaussianAngle_hasDerivAt hd hc hd hc hB hC hB hC hb hdf hb hdf θ)
    ((Real.continuous_sin.neg.mul hdc).intervalIntegrable _ _)
  simp_rw [neg_mul] at H
  rw [intervalIntegral.integral_neg, gaussianAngle_zero f hf,
    gaussianAngle_pi_half hf hf hB hb hb] at H
  nlinarith

theorem gaussian_strict_poincare_of_derivative_nonconstant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, df x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  let A : ℝ := ∫ x, df x^2 ∂gaussianReal 0 1
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have hpos : 0<∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ) := by
    apply intervalIntegral.integral_pos (by positivity)
      ((Real.continuous_sin.mul (continuous_const.sub hdc)).continuousOn)
    · intro θ hθ
      exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,Real.pi_pos]))
        (sub_nonneg.mpr (gaussianAngle_le_square hc hC hdf θ))
    · refine ⟨Real.pi/2,⟨by positivity,le_rfl⟩,?_⟩
      change 0 < Real.sin (Real.pi/2)*(A-gaussianAngle df df (Real.pi/2))
      rw [Real.sin_pi_div_two,one_mul,gaussianAngle_pi_half hc hc hC hdf hdf]
      exact sub_pos.mpr (by simpa only [A,pow_two] using gaussian_variance_pos hc hC hdf hne)
  have H := gaussian_variance_angle_identity hd hc hB hC hb hdf
  have heq : (∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ))=
      A-(∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ) := by
    simp_rw [mul_sub]
    have HS := intervalIntegral.integral_sub (μ:=volume)
      ((Real.continuous_sin.mul (continuous_const (y:=A))).intervalIntegrable 0 (Real.pi/2))
      ((Real.continuous_sin.mul hdc).intervalIntegrable 0 (Real.pi/2))
    simp only [Pi.mul_apply] at HS
    rw [HS,intervalIntegral.integral_mul_const,
      integral_sin,Real.cos_zero,Real.cos_pi_div_two]
    ring
  rw [heq,← H] at hpos
  exact sub_pos.mp hpos

theorem bounded_derivative_constant_imp_constant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (hc : ∃ c, ∀ x, df x=c) : ∃ c, ∀ x, f x=c := by
  obtain ⟨c,hc⟩ := hc
  have hder (x : ℝ) : HasDerivAt (fun y => f y-c*y) 0 x := by
    convert (hd x).sub ((hasDerivAt_id x).const_mul c) using 1 <;> first | rfl | simp_all
  have heq (x : ℝ) : f x=c*x+f 0 := by
    have H := is_const_of_deriv_eq_zero (fun y => (hder y).differentiableAt)
      (fun y => (hder y).deriv) x 0
    linarith
  have hz : c=0 := by
    by_contra hn
    have H := (abs_le.mp (hb ((2*B+1)/c))).2
    rw [heq] at H
    have hm : c*((2*B+1)/c)=2*B+1 := by field_simp
    rw [hm] at H
    have H0 := (abs_le.mp (hb 0)).1
    linarith
  refine ⟨f 0,fun x => ?_⟩
  simpa only [hz,zero_mul,zero_add] using heq x

theorem gaussian_strict_poincare {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  apply gaussian_strict_poincare_of_derivative_nonconstant hd hc hB hC hb hdf
  intro h
  exact hne (bounded_derivative_constant_imp_constant hd hB hb h)

end SK.Analytic

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
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFEndpoint
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

theorem scalarCDFGradient_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) : scalarCDFGradient β α s t 0=0 := by
  have H := (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at 0
  have he (n : ℕ) : rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) 0=0 := by
    simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
    exact scalarHierarchy_spin_gradient_zero _ _ _
  simp only [he] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

theorem scalarCDFOverlap_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) : scalarCDFOverlap β α 0=0 := by
  have HR := scalarCDFGradient_sq_regular β hα hmono 0 1 le_rfl
  have HE := scalarCDFAverage_eq_chainAverage
    (scalarCDFValue_regular β hα hmono 0 1 le_rfl) HR.1 HR.2.1
    (scalarCDFValue_lipschitz β hα hmono 0 1 le_rfl) (B:=1) HR.2.2.1 (C:=2) HR.2.2.2 β hα hmono
    [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFOverlap,sub_zero,Real.toNNReal_one,Real.toNNReal_zero,
    scalarTimeChainAverage,List.length_nil,scalarHierarchyAverage,scalarCDFGradient_zero β hα hmono 0 1 le_rfl,zero_pow (by decide : 2≠0)] using HE

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

theorem scalarHierarchy_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (x : ℝ) :
    let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarHierarchy n m v f) x)^2
    (∑ i, (v i)^2)*(max (rootHessian 0 (scalarHierarchy n m v f) x-V) 0)^2 ≤ V := by
  have H := scalarHierarchy_cramer_data hf h n m v hm x
  dsimp only at H ⊢
  have hmax : max (rootHessian 0 (scalarHierarchy n m v f) x-
      (scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 (scalarHierarchy n m v f) x)^2)) 0 ≤
      scalarHierarchyAverage n m v f (rootHessian 0 f) x := by
    apply max_le
    · linarith [H.2.2.1]
    · exact H.1
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) hmax 2)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans H.2.2.2

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

theorem scalarCDFValue_spinConvex (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : ScalarSpinConvex (scalarCDFValue β α s t) := by
  intro x
  rw [scalarCDFValue_rootGradient β ha hm s t ht,scalarCDFValue_rootHessian β ha hm s t ht]
  exact (scalarCDF_derivative_bounds β ha hm s t ht x).2

theorem chain_coefficients_variance (β : ℝ) (l : List (ℝ × ℝ≥0)) :
    (∑ i : Fin l.length, (β*Real.sqrt ((l.get i).2:ℝ))^2)=β^2*(chainDuration l:ℝ) := by
  simp only [mul_pow,Real.sq_sqrt (NNReal.coe_nonneg _),← Finset.mul_sum]
  congr 1
  induction l with
  | nil => simp [chainDuration]
  | cons p l ih => simpa [Fin.sum_univ_succ,chainDuration] using congrArg ((p.2:ℝ)+·) ih

theorem scalarTimeChain_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hc : ScalarSpinConvex f) (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1) (x : ℝ) :
    let V := scalarTimeChainAverage β l f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarTimeChain β l f) x)^2
    β^2*(chainDuration l:ℝ)*(max (rootHessian 0 (scalarTimeChain β l f) x-V) 0)^2 ≤ V := by
  have H := scalarHierarchy_cramer hf hc l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) (fun i => hm _ (List.get_mem _ _)) x
  dsimp only at H ⊢
  rw [chain_coefficients_variance] at H
  simpa only [scalarTimeChainAverage,scalarTimeChain_eq_hierarchy] using H

theorem scalarCDFOverlap_cramer_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    β^2*q*(max (scalarCDFHessian β (quantileCDF k Q) 0 1 0-scalarCDFOverlap β (quantileCDF k Q) q) 0)^2 ≤
      scalarCDFOverlap β (quantileCDF k Q) q := by
  let α := quantileCDF k Q
  have ha := quantileCDF_bounds k Q
  have hm := quantileCDF_monotone k Q
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr hq.2
  have hr1 : r ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr (by simp only [NNReal.coe_one]; linarith [hq.1])
  obtain ⟨l,hd,hl,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have htr : chainDuration l=t+r := by
    rw [hd]; apply NNReal.coe_injective
    rw [NNReal.coe_add,ht,hr,NNReal.coe_one]; ring
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β α l hl 0 hmodel t r htr
  let f := scalarCDFValue β α q r
  have hf : BoundedDerivs f := scalarCDFValue_regular β ha hm q r hr1
  have hfc : ScalarSpinConvex f := scalarCDFValue_spinConvex β ha hm q r hr1
  have hLip := scalarCDFValue_lipschitz β ha hm q r hr1
  have hroot : scalarTimeChain β l₁ f=scalarCDFValue β α 0 1 := by
    funext x
    rw [← scalarCDFOperator_eq_chain hf hLip β ha hm l₁ hm₁ 0 t ht1 h₁ hs₁ x]
    exact (congrFun (scalarCDFValue_semigroup_quantile β Q hQ hq) x).symm
  have htest := scalarCDFGradient_sq_regular β ha hm q r hr1
  have hav : scalarTimeChainAverage β l₁ f (fun y => (rootGradient 0 f y)^2) 0=
      scalarCDFOverlap β α q := by
    change scalarTimeChainAverage β l₁ (scalarCDFValue β α q r) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm q r hr1]
    exact (scalarCDFAverage_eq_chainAverage hf htest.1 htest.2.1 hLip
      (B:=1) htest.2.2.1 (C:=2) htest.2.2.2 β ha hm l₁ hm₁ 0 t ht1 h₁ hs₁ 0).symm
  have H := scalarTimeChain_cramer hf hfc β l₁ hm₁ 0
  dsimp only at H
  rw [h₁,ht,hav,hroot,scalarCDFValue_rootGradient β ha hm 0 1 le_rfl,
    scalarCDFValue_rootHessian β ha hm 0 1 le_rfl,scalarCDFGradient_zero β ha hm 0 1 le_rfl,
    zero_pow (by decide : 2≠0),sub_zero] at H
  exact H

theorem scalarCDFOverlap_cramer (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    β^2*q*(max (scalarCDFHessian β α 0 1 0-scalarCDFOverlap β α q) 0)^2 ≤ scalarCDFOverlap β α q := by
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hn (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hnm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have Hχ := (scalarCDFHessian_tendstoUniformly β ha α.mono hn hnm hD).tendsto_at 0
  have HΓ := (scalarCDFOverlap_tendstoUniformlyOn β ha α.mono hn hnm hD).tendsto_at hq
  have HL := ((Hχ.sub HΓ).max (tendsto_const_nhds (x := (0:ℝ)))).pow 2 |>.const_mul (β^2*q)
  exact le_of_tendsto_of_tendsto HL HΓ (Eventually.of_forall (fun n =>
    scalarCDFOverlap_cramer_quantile β (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α h1) hq))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_OverlapModulus
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

theorem cdfGradientTest_continuous {β : ℝ} {α : ℝ → ℝ}
    (hΓ : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (cdfGradientTest β α) :=
  continuous_id.sub ((continuousOn_iff_continuous_domRestrict.mp hΓ).comp continuous_projIcc)

theorem cdfGradientTest_eq {β : ℝ} {α : ℝ → ℝ} {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    cdfGradientTest β α s=s-scalarCDFOverlap β α s := by
  simp only [cdfGradientTest,projIcc_of_mem _ hs]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_SignedCDFTransport
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

theorem unitCDF_mul_indicator (q : ℝ) (f : ℝ → ℝ) :
    (fun x => unitCDF q x*f x)=(Ici q).indicator f := by
  funext x
  simp only [unitCDF,Set.indicator_apply,mem_Ici]
  split_ifs <;> simp

theorem unitCDF_mul_integral (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ x in Icc (0:ℝ) 1, unitCDF q x*f x)=∫ x in q..1, f x := by
  rw [unitCDF_mul_indicator,setIntegral_indicator measurableSet_Ici]
  have he : Icc (0:ℝ) 1∩Ici q=Icc q 1 := by
    ext x
    simp only [mem_inter_iff,mem_Icc,mem_Ici]
    constructor
    · intro H; exact ⟨H.2,H.1.2⟩
    · intro H; exact ⟨⟨hq.1.trans H.1,H.2⟩,H.1⟩
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hq.2]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFMinimizer
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

theorem supported_probability_cdf_one (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) : cdf (μ : Measure ℝ) 1=1 := by
  have H : (μ : Measure ℝ) (Iic 1)=1 := le_antisymm prob_le_one
    (by rw [← hμ]; exact measure_mono Icc_subset_Iic_self)
  rw [cdf_eq_real,Measure.real,H,ENNReal.toReal_one]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSupportDuality
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

theorem supported_probability_ae (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) :
    ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0:ℝ) 1 := by
  rw [ae_iff]
  change (μ : Measure ℝ) (Icc (0:ℝ) 1)ᶜ=0
  rw [measure_compl measurableSet_Icc (by simp [hμ]),hμ,measure_univ,tsub_self]

theorem integral_unitCDF_probability (μ : ProbabilityMeasure ℝ) (s c : ℝ) :
    (∫ t, unitCDF t s*c ∂(μ : Measure ℝ))=cdf (μ : Measure ℝ) s*c := by
  have E : (fun t => unitCDF t s*c)=(Iic s).indicator (fun _ => c) := by
    funext t
    simp only [unitCDF,indicator_apply,mem_Iic]
    split_ifs <;> simp
  rw [E,integral_indicator measurableSet_Iic,setIntegral_const,cdf_eq_real,smul_eq_mul]

theorem supported_cdf_integral_duality (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc (0:ℝ) 1)) :
    (∫ s in Icc (0:ℝ) 1, cdf (μ : Measure ℝ) s*g s)=
      ∫ q, (∫ s in q..1, g s) ∂(μ : Measure ℝ) := by
  have E : (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)=
      {p : ℝ×ℝ | p.1≤p.2}.indicator (fun p => g p.2) := by
    funext p
    simp only [unitCDF,indicator_apply,mem_ofPred_eq]
    split_ifs <;> simp
  have HI : Integrable (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)
      ((μ : Measure ℝ).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [E]
    exact (hg.comp_snd (μ : Measure ℝ)).indicator (measurableSet_le measurable_fst measurable_snd)
  have H := integral_integral_swap (f:=fun q s => unitCDF q s*g s) HI
  simp_rw [integral_unitCDF_probability] at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards [supported_probability_ae μ hμ] with q hq
  exact unitCDF_mul_integral q hq g

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_SupportMinima
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

theorem supported_continuous_integrable (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) : Integrable f (μ : Measure ℝ) := by
  have H := hf.integrableOn_Icc (μ:=(μ : Measure ℝ))
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem (supported_probability_ae μ hμ)] at H
  exact H

theorem support_minima_of_integral_le (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ} (hf : Continuous f)
    (hmin : ∀ q∈Icc (0:ℝ) 1, (∫ x, f x ∂(μ : Measure ℝ))≤f q) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧ f q=(∫ x, f x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1, f q≤f r := by
  let C := ∫ x, f x ∂(μ : Measure ℝ)
  have HI := supported_continuous_integrable μ hμ hf.continuousOn
  have Hn : ∀ᵐ x ∂(μ : Measure ℝ), 0≤f x-C := by
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact sub_nonneg.mpr (hmin x hx)
  have Hz : ∫ x, (f x-C) ∂(μ : Measure ℝ)=0 := by
    rw [integral_sub HI (integrable_const C),integral_const,probReal_univ,one_smul]
    exact sub_self _
  have He : ∀ᵐ x ∂(μ : Measure ℝ), f x=C := by
    have H := (integral_eq_zero_iff_of_nonneg_ae Hn (HI.sub (integrable_const C))).mp Hz
    filter_upwards [H] with x hx
    exact sub_eq_zero.mp hx
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    (isClosed_eq hf continuous_const) He
  have HD := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  intro q hq
  have Hq : f q=C := HS hq
  exact ⟨HD hq,Hq,fun r hr => Hq ▸ hmin r hr⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFPotential
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

theorem scalarCDFPotential_eq {β : ℝ} {α : ℝ → ℝ} {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFPotential β α q=∫ s in q..1, (scalarCDFOverlap β α s-s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.2] at hs
  dsimp only
  rw [cdfGradientTest_eq ⟨hq.1.trans hs.1,hs.2⟩]
  ring

theorem scalarCDFPotential_hasDerivAt {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) (q : ℝ) :
    HasDerivAt (scalarCDFPotential β α) (cdfGradientTest β α q) q := by
  have Hc := (cdfGradientTest_continuous hc).neg
  have H := intervalIntegral.integral_hasDerivAt_left
    (Hc.intervalIntegrable q 1) Hc.stronglyMeasurable.stronglyMeasurableAtFilter Hc.continuousAt
  convert H using 1 <;> first | rfl | exact Subsingleton.elim _ _ | simp only [Pi.neg_apply, neg_neg]

theorem scalarCDFPotential_continuous {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (scalarCDFPotential β α) :=
  continuous_iff_continuousAt.mpr (fun q => (scalarCDFPotential_hasDerivAt hc q).continuousAt)

theorem scalarCDFParisi_support_minima {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧
      scalarCDFPotential β (cdf (μ : Measure ℝ)) q=
        (∫ x, scalarCDFPotential β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1,
        scalarCDFPotential β (cdf (μ : Measure ℝ)) q≤ scalarCDFPotential β (cdf (μ : Measure ℝ)) r := by
  let α := cdf (μ : Measure ℝ)
  have ha : ∀ z, α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 := supported_probability_cdf_one μ hμ
  have HC := scalarCDFOverlap_continuousOn β α ha h1
  apply support_minima_of_integral_le μ hμ (scalarCDFPotential_continuous HC)
  intro q hq
  have HG : ContinuousOn (fun s => scalarCDFOverlap β α s-s) (Icc (0:ℝ) 1) := HC.sub continuousOn_id
  have HD := supported_cdf_integral_duality μ hμ HG.integrableOn_Icc
  have HE : (∫ x, scalarCDFPotential β α x ∂(μ : Measure ℝ))=
      (∫ x, (∫ s in x..1, scalarCDFOverlap β α s-s) ∂(μ : Measure ℝ)) := by
    apply integral_congr_ae
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact scalarCDFPotential_eq hx
  rw [HE,← HD]
  exact scalarCDFPotential_minimum_bound hβ α ha h1 hmin hq

theorem scalarCDFParisi_overlap_on_interior_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) (hq : q∈Ioo (0:ℝ) 1) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have Hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hqs).2.2
  have HL : IsLocalMin (scalarCDFPotential β (cdf (μ : Measure ℝ))) q := by
    filter_upwards [Icc_mem_nhds hq.1 hq.2] with r hr
    exact Hm r hr
  have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
  have HE := HL.hasDerivAt_eq_zero (scalarCDFPotential_hasDerivAt HC q)
  rw [cdfGradientTest_eq ⟨hq.1.le,hq.2.le⟩] at HE
  exact (sub_eq_zero.mp HE).symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFHeatContact
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

theorem scalarCDFOverlap_heat_increment_lower (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0) :
    β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s))
      (scalarCDFHessian β α q (Real.toNNReal (1-q))) (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)  ≤
      scalarCDFOverlap β α q-scalarCDFOverlap β α s := by
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr
  have hc := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |scalarCDFHessian β α q (Real.toNNReal (1-q)) x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  have he : (β*Real.sqrt q)^2=(β*Real.sqrt s)^2+(β*Real.sqrt (q-s))^2 := by
    simp only [mul_pow,Real.sq_sqrt (hs.trans hsq),Real.sq_sqrt hs,Real.sq_sqrt (sub_nonneg.mpr hsq)]
    ring
  have H := gaussianHeat_variance_integral_lower hu hc zero_le_one zero_le_one hb hdf
    (β*Real.sqrt (q-s)) (β*Real.sqrt s) (β*Real.sqrt q) he
  have HG := scalarCDFGradient_heat_prefix β α ha h1 hs hsq hq
    (fun z hz' => hz z ⟨hs.trans hz'.1,hz'.2⟩)
  rw [scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs.trans hsq,hq⟩ hz,
    scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs,hsq.trans hq⟩
      (fun z hz' => hz z ⟨hz'.1,hz'.2.trans_le hsq⟩),HG]
  simpa only [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hsq)] using H

theorem scalarCDFHeatContact_chi_sq_gt (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    1 < β^2*(∫ z, (scalarCDFHessian β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1) := by
  let f : ℝ → ℝ := scalarCDFGradient β α q (Real.toNNReal (1-q))
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hd (x : ℝ) : HasDerivAt f (df x) x := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr x
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) : |f x|  ≤  1 := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |df x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (f x)]
  have hmean : (∫ z, f (k*z) ∂gaussianReal 0 1)=0 := by
    have H := congrFun (scalarCDFGradient_heat_prefix β α ha h1 le_rfl hq0.le hq1 hz) 0
    rw [scalarCDFGradient_zero β ha α.mono 0 _ (by simp)] at H
    simpa only [gaussianHeat,sub_zero,zero_add,f,k] using H.symm
  have hsecond : (∫ z, f (k*z)^2 ∂gaussianReal 0 1)=q := by
    simpa only [f,k,scalarCDFOverlap_heat_prefix β ha α.mono ⟨hq0.le,hq1⟩ hz] using hcontact
  have hnonconstant : ¬∃ c, ∀ z, f (k*z)=c := by
    rintro ⟨c,hc⟩
    simp only [hc,integral_const,probReal_univ,one_smul] at hmean hsecond
    rw [hmean,zero_pow (by decide)] at hsecond
    exact hq0.ne' hsecond.symm
  have HD (z : ℝ) : HasDerivAt (fun z => f (k*z)) (k*df (k*z)) z := by
    convert (hd (k*z)).comp z ((hasDerivAt_id z).const_mul k) using 1 <;> first | rfl | ring
  have HP := gaussian_strict_poincare HD (by fun_prop) zero_le_one (abs_nonneg k)
    (fun z => hb (k*z)) (fun z => by
      rw [abs_mul]; simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdf (k*z)) (abs_nonneg k)) hnonconstant
  rw [hmean,hsecond,zero_pow (by decide),sub_zero] at HP
  simp_rw [mul_pow] at HP
  rw [integral_const_mul] at HP
  have hk : k^2=β^2*q := by dsimp [k]; rw [mul_pow,Real.sq_sqrt hq0.le]
  rw [hk] at HP
  change 1 < β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1)
  nlinarith

theorem not_min_of_contact_increment {G Γ J : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ s∈Icc (0:ℝ) 1, HasDerivAt G (s-Γ s) s) (hJ : Continuous J)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hcontact : Γ q=q) (hJq : 1 < J q)
    (hi : ∀ s∈Icc (0:ℝ) q, (q-s)*J s ≤ Γ q-Γ s) :
    ¬∀ r∈Icc (0:ℝ) 1, G q ≤ G r := by
  obtain ⟨ε,hε,hεJ⟩ := Metric.eventually_nhds_iff.mp (hJ.continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hJq))
  let δ := min (q/2) (ε/2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδq : δ  ≤  q/2 := min_le_left _ _
  have hδε : δ  ≤  ε/2 := min_le_right _ _
  let r := q-δ
  have hr0 : 0  ≤  r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  have hpos {s : ℝ} (hs : s∈Ioo r q) : 0 < s-Γ s := by
    have hs0 : 0  ≤  s := hr0.trans hs.1.le
    have hsJ : 1 < J s := by
      apply hεJ
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
      dsimp [r] at hs
      linarith [hs.1]
    have H := hi s ⟨hs0,hs.2.le⟩
    rw [hcontact] at H
    have HH := mul_lt_mul_of_pos_left hsJ (sub_pos.mpr hs.2)
    nlinarith
  have hstrict := strictMonoOn_of_deriv_pos (convex_Icc r q) hG.continuousOn
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s ⟨hr0.trans hs.1.le,hs.2.le.trans hq1⟩).deriv]
      exact hpos hs)
  intro hmin
  exact (not_lt_of_ge (hmin r ⟨hr0,hrq.le.trans hq1⟩))
    (hstrict ⟨le_rfl,hrq.le⟩ ⟨hrq.le,le_rfl⟩ hrq)

theorem heat_increment_coefficient_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (β q : ℝ) :
    Continuous (fun s : ℝ => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) f
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)) := by
  have hp : Continuous (fun s : ℝ => (β*Real.sqrt (q-s),β*Real.sqrt s)) :=
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).prodMk
      (continuous_const.mul Real.continuous_sqrt)
  exact continuous_const.mul ((gaussianHeat_sq_average_continuous hf hB hb).comp hp)

theorem scalarCDFPotential_not_min_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    ¬∀ r∈Icc (0:ℝ) 1, scalarCDFPotential β α q ≤ scalarCDFPotential β α r := by
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hdf (x : ℝ) : |df x| ≤ 1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  let J : ℝ → ℝ := fun s => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
    (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)
  have hJ : Continuous J := heat_increment_coefficient_continuous hc zero_le_one hdf β q
  have hJq : 1 < J q := by
    have HJ : J q=β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1) := by
      simp [J,gaussianHeat,k]
    rw [HJ]
    exact scalarCDFHeatContact_chi_sq_gt β α ha h1 hq0 hq1 hz hcontact
  have hΓ := scalarCDFOverlap_continuousOn β α ha h1
  apply not_min_of_contact_increment (scalarCDFPotential_continuous hΓ)
    (fun s hs => by simpa only [cdfGradientTest_eq hs] using scalarCDFPotential_hasDerivAt hΓ s)
    hJ hq0 hq1 hcontact hJq
  intro s hs
  have H := scalarCDFOverlap_heat_increment_lower β α ha h1 hs.1 hs.2 hq1 hz
  have HE : (q-s)*J s=β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1) := by dsimp [J]; ring
  rw [HE]
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSupportContact
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

theorem derivative_nonpos_at_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 1) (hm : ∀ r∈Icc (0:ℝ) 1, f 1≤f r) : d≤0 := by
  have H := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto H
  have HP : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 0 < r :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [HP,self_mem_nhdsWithin] with r hr0 hr1
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm r ⟨hr0.le,hr1.le⟩))
    (sub_nonpos.mpr hr1.le)

theorem scalarCDFParisi_overlap_on_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have hs := scalarCDFParisi_support_minima hβ μ hμ hmin q hqs
  have ha (x : ℝ) : cdf (μ : Measure ℝ) x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  by_cases hq0 : q=0
  · subst q
    exact scalarCDFOverlap_zero β ha (cdf (μ : Measure ℝ)).mono
  by_cases hq1 : q=1
  · subst q
    have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ)) ha
      (supported_probability_cdf_one μ hμ)
    have HD := derivative_nonpos_at_right_minimum (scalarCDFPotential_hasDerivAt HC 1) hs.2.2
    rw [cdfGradientTest_eq ⟨zero_le_one,le_rfl⟩] at HD
    have HB := scalarCDFOverlap_nonneg_le_one β ha (cdf (μ : Measure ℝ)).mono
      (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
    linarith [HB.2]
  · exact scalarCDFParisi_overlap_on_interior_support hβ μ hμ hmin hqs
      ⟨lt_of_le_of_ne hs.1.1 (Ne.symm hq0),lt_of_le_of_ne hs.1.2 hq1⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFZeroSupport
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

theorem cdf_zero_below_least_support (μ : ProbabilityMeasure ℝ) {q z : ℝ}
    (hq : IsLeast (μ : Measure ℝ).support q) (hz : z<q) :
    cdf (μ : Measure ℝ) z=0 := by
  have H : (μ : Measure ℝ) (Iic z)=0 := by
    apply measure_mono_null (t:=(μ : Measure ℝ).supportᶜ) _ (μ : Measure ℝ).measure_compl_support
    intro x hx hs
    exact (not_le_of_gt hz) (le_trans (hq.2 hs) hx)
  rw [cdf_eq_real,measureReal_def,H,ENNReal.toReal_zero]

theorem scalarCDFParisi_zero_mem_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    (0:ℝ)∈(μ : Measure ℝ).support := by
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  have HC : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support HS
  obtain ⟨q,hq⟩ := HC.exists_isLeast ((μ : Measure ℝ).nonempty_support (by
    intro H
    have H1 := measure_univ (μ:=(μ : Measure ℝ))
    simp only [H,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H1))
  have hbound := HS hq.1
  have he : q=0 := by
    by_contra H
    have hq0 : 0<q := lt_of_le_of_ne hbound.1 (Ne.symm H)
    have hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hq.1).2.2
    exact scalarCDFPotential_not_min_heat_prefix β (cdf (μ : Measure ℝ))
      (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
      hq0 hbound.2 (fun z hz => cdf_zero_below_least_support μ hq hz.2)
      (scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq.1) hm
  simpa only [he] using hq.1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOriginStability
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

theorem origin_coefficient_le_of_min {G Γ J : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ s∈Icc (0:ℝ) 1, HasDerivAt G (s-Γ s) s) (hJ : Continuous J)
    (hi : ∀ s∈Icc (0:ℝ) 1, s*J s ≤ Γ s)
    (hmin : ∀ r∈Icc (0:ℝ) 1, G 0 ≤ G r) : J 0 ≤ 1 := by
  by_contra H
  have hJ0 : 1 < J 0 := lt_of_not_ge H
  obtain ⟨ε,hε,hεJ⟩ := Metric.eventually_nhds_iff.mp (hJ.continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hJ0))
  let δ := min (1/2:ℝ) (ε/2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδε : δ ≤ ε/2 := min_le_right _ _
  have hneg {s : ℝ} (hs : s∈Ioo (0:ℝ) δ) : s-Γ s < 0 := by
    have hsJ : 1 < J s := by
      apply hεJ
      rw [Real.dist_eq,sub_zero,abs_of_pos hs.1]
      linarith [hs.2]
    have H := hi s ⟨hs.1.le,hs.2.le.trans hδ1⟩
    nlinarith [mul_lt_mul_of_pos_left hsJ hs.1]
  have hstrict := strictAntiOn_of_deriv_neg (convex_Icc (0:ℝ) δ) hG.continuousOn
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s ⟨hs.1.le,hs.2.le.trans hδ1⟩).deriv]
      exact hneg hs)
  exact (not_lt_of_ge (hmin δ ⟨hδ.le,hδ1⟩))
    (hstrict ⟨le_rfl,hδ.le⟩ ⟨hδ.le,le_rfl⟩ hδ)

theorem scalarCDFParisi_origin_stability_oai {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    β^2*(scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0)^2 ≤ 1 := by
  let α := cdf (μ : Measure ℝ)
  have ha (z : ℝ) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ hμ
  have hΓ := scalarCDFOverlap_continuousOn β α ha h1
  let χ := scalarCDFHessian β α 0 1 0
  let J (s : ℝ) := β^2*(max (χ-(s-cdfGradientTest β α s)) 0)^2
  have hJ : Continuous J := continuous_const.mul
    ((continuous_const.sub (continuous_id.sub (cdfGradientTest_continuous hΓ))).max continuous_const |>.pow 2)
  have H := origin_coefficient_le_of_min (scalarCDFPotential_continuous hΓ)
    (fun s hs => by simpa only [cdfGradientTest_eq hs] using scalarCDFPotential_hasDerivAt hΓ s) hJ
    (fun s hs => by
      have H := scalarCDFOverlap_cramer β α ha h1 hs
      dsimp [J]
      rw [cdfGradientTest_eq hs,sub_sub_cancel]
      nlinarith)
    ((scalarCDFParisi_support_minima hβ μ hμ hmin 0
      (scalarCDFParisi_zero_mem_support hβ μ hμ hmin)).2.2)
  have hχ : 0 ≤ χ := (scalarCDF_derivative_bounds β ha α.mono 0 1 le_rfl 0).2.1
  simpa only [J,cdfGradientTest_eq (show (0:ℝ)∈Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩),
    scalarCDFOverlap_zero β ha α.mono,sub_zero,sub_self,max_eq_left hχ] using H

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.scalarCDFParisi_origin_stability_oai := @OAI.SK.Analytic.scalarCDFParisi_origin_stability_oai
