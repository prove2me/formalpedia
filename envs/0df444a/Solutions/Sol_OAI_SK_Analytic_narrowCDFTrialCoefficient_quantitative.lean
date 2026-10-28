-- Prove2me | solution 1 for OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:08:33.454992+00:00
-- url     : https://prove2.me/submissions/40d4992a-810b-40fa-9f07-8a38f0067e15

import Mathlib
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_scalarCDFJointSusceptibility_quantile_loss

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

theorem unitBoundedProduct_abs_le {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) : |a*b|≤1 := by
  rw [abs_mul]
  calc
    _ ≤ 1*1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    _ = _ := by ring

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

theorem unitBoundedProduct_tendstoUniformly {F G : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hG : ∀ n x,|G n x|≤1) (hf : ∀ x,|f x|≤1)
    (hF : TendstoUniformly F f atTop) (hU : TendstoUniformly G g atTop) :
    TendstoUniformly (fun n x => F n x*G n x) (fun x => f x*g x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε/2) (by positivity),
    Metric.tendstoUniformly_iff.mp hU (ε/2) (by positivity)] with n hn hm x
  have H := unitBoundedProduct_sub (a:=F n x) (d:=g x) (hG n x) (hf x)
  have Hf := hn x
  have Hg := hm x
  simp only [Real.dist_eq] at Hf Hg ⊢
  rw [abs_sub_comm] at Hf Hg ⊢
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzCDFStability
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

theorem scalarCDFAverage_cdf_stability_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z∈Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((L:ℝ)+2*(B:ℝ)^2)*h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*d ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε/2 := by dsimp [d]; field_simp
  have hga (z) : |g z-scalarWindow g d z| ≤ (L:ℝ)*d := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hd z
  have Hα := scalarCDFAverage_observable_distance β hα hαm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hγ := scalarCDFAverage_observable_distance β hγ hγm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hc := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm hf
    (scalarWindow_hasDerivAt hgL.continuous d) (scalarWindowDerivative_continuous hgL.continuous d)
    hfK (scalarWindow_bound hgL.continuous hB hd) (scalarWindowDerivative_lipschitz_bound hgL hd)
    s t ht x h hh
  have H₁ := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarCDFAverage β α s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  have H₂ := abs_sub_le (scalarCDFAverage β α s t f (scalarWindow g d) x)
    (scalarCDFAverage β γ s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  rw [abs_sub_comm (scalarCDFAverage β γ s t f (scalarWindow g d) x)] at H₂
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzTerminalStability
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

theorem scalarCDFAverage_terminal_stability_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B A C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (haA : LipschitzWith A a) (hbC : LipschitzWith C b)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    {ε δ : ℝ} (hε : 0≤ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haA haB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hg hgL hbC hbB s t ht x)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_) hf hg hε hfg haA.continuous hbC.continuous B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t) i j hij
  · exact le_rfl

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

theorem scalarIncrementAverage_append (l r : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (l++r) f g=scalarIncrementAverage l (scalarIncrementChain r f) (scalarIncrementAverage r f g) := by
  simp only [← vectorIncrementAverage_real,← vectorIncrementChain_real,vectorIncrementAverage_append]

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

theorem ScalarSpinConvex.scalarHierarchy {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) :
    ScalarSpinConvex (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact h
  | succ n ih => exact ih (h.scalarStep hf (hm _) _) (scalarStep_regular hf _ _) _ _ (fun i => hm _)

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

theorem scalarCDFValue_spinConvex (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : ScalarSpinConvex (scalarCDFValue β α s t) := by
  intro x
  rw [scalarCDFValue_rootGradient β ha hm s t ht,scalarCDFValue_rootHessian β ha hm s t ht]
  exact (scalarCDF_derivative_bounds β ha hm s t ht x).2

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

theorem scalarIncrementAverage_bounded (l : List (ℝ × ℝ)) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) : BoundedScalar (scalarIncrementAverage l f g) := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_bounded hf hg _ _ _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFIntervalConvergence
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

theorem scalarCDFValue_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm s t ht x
  have HE := cdfDistance_subinterval_le (hnm n) hαm hs hst
  have HB := H.trans (mul_le_mul_of_nonneg_left HE (scalarTimeMassConstant_nonneg β))
  rw [Real.dist_eq,abs_sub_comm]
  exact HB.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) s t)
      (scalarCDFHessian β α s t) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFGradient_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFHessian_lipschitz β hα hαm s t ht)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFValue_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFGradient_lipschitz β hα hαm s t ht)
    (scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD s t ht hs hst)

theorem scalarCDFAverage_tendsto_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFAverage β (αn n) s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound
  rw [Real.dist_eq]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

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

theorem unitBoundedSquare_tendstoUniformly {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n x,|F n x|≤1) (hf : ∀ x,|f x|≤1)
    (hU : TendstoUniformly F f atTop) :
    TendstoUniformly (fun n x => (F n x)^2) (fun x => (f x)^2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε/2) (by positivity)] with n hn
  intro x
  have H := abs_sq_sub_sq_le_two (hF n x) (hf x)
  have Hn := hn x
  simp only [Real.dist_eq] at Hn ⊢
  rw [abs_sub_comm] at Hn ⊢
  linarith

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

theorem scalarCDFSusceptibilitySquareAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilitySquareAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilitySquareAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := fun x => (scalarCDFHessian β α r s x)^2
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n x => (scalarCDFHessian β (αn n) r s x)^2
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    unitBoundedSquare_tendstoUniformly
      (fun n => scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
      (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
      (scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs)
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_square_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_square_bound β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_square_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_square_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_square_bound β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_square_bound β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

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

theorem scalarIncrementAverage_mono (l : List (ℝ × ℝ)) {f g h : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hh : BoundedScalar h)
    (hle : ∀ x,g x≤h x) (x : ℝ) :
    scalarIncrementAverage l f g x≤ scalarIncrementAverage l f h x := by
  simp only [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_mono hf hg hh hle _ _ _ _

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

theorem scalarCDFAverage_tendstoUniformly_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t f g)
      (scalarCDFAverage β α s t f g) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound x
  rw [Real.dist_eq,abs_sub_comm]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

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

theorem scalarCDFAverage_tendstoUniformly_varying (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} {fn gn : ℕ → ℝ → ℝ}
    (hf : BoundedDerivs f) (hfn : ∀ n,BoundedDerivs (fn n)) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hfnK : ∀ n,LipschitzWith K (fn n))
    (hgL : LipschitzWith L g) (hgnL : ∀ n,LipschitzWith L (gn n))
    (hgB : ∀ z,|g z|≤B) (hgnB : ∀ n z,|gn n z|≤B)
    (hfU : TendstoUniformly fn f atTop) (hgU : TendstoUniformly gn g atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t (fn n) (gn n))
      (scalarCDFAverage β α s t f g) atTop := by
  have hfix := scalarCDFAverage_tendstoUniformly_cdf_lipschitz β hα hm hn hnm hD hf hfK hgL hgB s t ht hs hst
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let φ : ℝ → ℝ := fun e => 2*e+2*(B:ℝ)*(Real.exp (2*e)-1)
  have hφ : ContinuousAt φ 0 := by dsimp [φ]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hφ ε hε
  let e := δ/2
  have he : 0<e := half_pos hδ
  have hsmall : φ e<ε := by
    have H := hbound (show dist e 0<δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; dsimp [e]; linarith)
    have hz : φ 0=0 := by simp [φ]
    rw [hz,Real.dist_eq,sub_zero] at H
    exact (le_abs_self _).trans_lt H
  filter_upwards [Metric.tendstoUniformly_iff.mp hfU e he,
    Metric.tendstoUniformly_iff.mp hgU e he,Metric.tendstoUniformly_iff.mp hfix e he] with n hfn' hgn' hfix' x
  have H := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n) (hfn n) hf
    (hfnK n) hfK (hgnL n) hgL (hgnB n) hgB he.le
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn' z).le)
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hgn' z).le) s t ht x
  have hf' := hfix' x
  rw [Real.dist_eq,abs_sub_comm] at hf' ⊢
  have HT := abs_sub_le (scalarCDFAverage β (αn n) s t (fn n) (gn n) x)
    (scalarCDFAverage β (αn n) s t f g x) (scalarCDFAverage β α s t f g x)
  have HA : |scalarCDFAverage β (αn n) s t (fn n) (gn n) x-scalarCDFAverage β α s t f g x|<φ e := by
    dsimp [φ]
    linarith
  exact HA.trans hsmall

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

theorem scalarCDFConditionalSusceptibility_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFConditionalSusceptibility β (αn n) r q)
      (scalarCDFConditionalSusceptibility β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-q):ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal (q-r):ℝ)=q-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-q)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-r)≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  exact scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm q _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_lipschitz β ha hm q _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) q _ hs)
    (scalarCDFHessian_lipschitz β ha hm q _ hs) (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) q _ hs)
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ hs) (fun n => scalarCDFHessian_abs_le_one β (hn n) (hnm n) q _ hs)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD q _ hs (hr.trans hrq) (by rw [hs0]; linarith))
    r _ ht hr (by rw [ht0]; linarith)

theorem scalarCDFJointSusceptibilityTest_regular (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    LipschitzWith (susceptibilityLipschitzConstant+conditionalSusceptibilityLipschitz)
      (scalarCDFJointSusceptibilityTest β α r q) ∧
    ∀ x,|scalarCDFJointSusceptibilityTest β α r q x|≤1 := by
  have hs : Real.toNNReal (1-r)≤1 := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (by linarith),NNReal.coe_one]; linarith
  have H := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  refine ⟨unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r _ hs) H.1
    (scalarCDFHessian_abs_le_one β ha hm r _ hs) H.2,?_⟩
  intro x
  exact unitBoundedProduct_abs_le (scalarCDFHessian_abs_le_one β ha hm r _ hs x) (H.2 x)

theorem scalarCDFJointSusceptibilityTest_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    TendstoUniformly (fun n => scalarCDFJointSusceptibilityTest β (αn n) r q)
      (scalarCDFJointSusceptibilityTest β α r q) atTop := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  exact unitBoundedProduct_tendstoUniformly
    (fun n => (scalarCDFConditionalSusceptibility_regular β (hn n) (hnm n) hr hrq hq).2)
    (scalarCDFHessian_abs_le_one β ha hm r _ hs)
    (scalarCDFHessian_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith))
    (scalarCDFConditionalSusceptibility_tendstoUniformly β ha hm hn hnm hD hr hrq hq)

theorem scalarCDFJointSusceptibility_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    Tendsto (fun n => scalarCDFJointSusceptibility β (αn n) r q) atTop
      (𝓝 (scalarCDFJointSusceptibility β α r q)) := by
  have hs0 : (Real.toNNReal (1-r):ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have ht0 : (Real.toNNReal r:ℝ)=r := Real.coe_toNNReal _ hr
  have hs : Real.toNNReal (1-r)≤1 := by rw [← NNReal.coe_le_coe,hs0,NNReal.coe_one]; linarith
  have ht : Real.toNNReal r≤1 := by rw [← NNReal.coe_le_coe,ht0,NNReal.coe_one]; linarith
  have hg := scalarCDFJointSusceptibilityTest_regular β ha hm hr hrq hq
  have hgn (n) := scalarCDFJointSusceptibilityTest_regular β (hn n) (hnm n) hr hrq hq
  have HP := scalarCDFJointSusceptibilityTest_tendstoUniformly β ha hm hn hnm hD hr hrq hq
  exact (scalarCDFAverage_tendstoUniformly_varying β ha hm hn hnm hD
    (scalarCDFValue_regular β ha hm r _ hs) (fun n => scalarCDFValue_regular β (hn n) (hnm n) r _ hs)
    (scalarCDFValue_lipschitz β ha hm r _ hs) (fun n => scalarCDFValue_lipschitz β (hn n) (hnm n) r _ hs)
    hg.1 (fun n => (hgn n).1)
    (B:=1) hg.2 (fun n => (hgn n).2)
    (scalarCDFValue_tendstoUniformly_interval β ha hm hn hnm hD r _ hs hr (by rw [hs0]; linarith)) HP
    0 _ ht le_rfl (by rw [ht0]; linarith)).tendsto_at 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCoefficientBound
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

theorem narrowCDFMean_bounds (β : ℝ) {α : ℝ → ℝ} (hm : Monotone α)
    (r : ℝ) {h θ : ℝ} (hh : 0<h) (hθ : 0≤θ) :
    narrowCDFMean β α r h θ∈Icc (β^2*θ*α r) (β^2*θ*α (r+h)) := by
  have hlo : (∫ z in r..r+h,α r)≤∫ z in r..r+h,α z := by
    apply intervalIntegral.integral_mono_on (show r ≤ r+h by linarith) intervalIntegrable_const hm.intervalIntegrable
    intro z hz; exact hm hz.1
  have hhi : (∫ z in r..r+h,α z)≤∫ z in r..r+h,α (r+h) := by
    apply intervalIntegral.integral_mono_on (show r ≤ r+h by linarith) hm.intervalIntegrable intervalIntegrable_const
    intro z hz; exact hm hz.2
  simp only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul] at hlo hhi
  have hn : h≠0 := ne_of_gt hh
  have Hlo := mul_le_mul_of_nonneg_left hlo (show 0≤β^2*(θ/h) by positivity)
  have Hhi := mul_le_mul_of_nonneg_left hhi (show 0≤β^2*(θ/h) by positivity)
  constructor
  · convert Hlo using 1 <;> try simp only [narrowCDFMean]
    all_goals field_simp
  · convert Hhi using 1 <;> try simp only [narrowCDFMean]
    all_goals field_simp

theorem narrowTentError_bound {B μ a θ ω : ℝ} (hB : 0≤B) (hμ : 0≤μ) (hμB : μ≤B)
    (ha : a∈Icc (0:ℝ) 1) (hω : ω∈Icc (0:ℝ) 1) :
    narrowTentError μ (B*a) (B*θ) ω≤6*B^2*θ^2+4*B^2*ω := by
  have hBa0 : 0≤B*a := mul_nonneg hB ha.1
  have hBa : B*a≤B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 hB
  have hmB : μ*(B*a)≤B^2 := by nlinarith [mul_le_mul hBa hμB hμ hB]
  have hBa2 : (B*a)^2≤B^2 := by nlinarith [sq_nonneg (B-B*a)]
  have hω2 : ω^2≤ω := by nlinarith [hω.1,hω.2]
  have hq : (B*a*ω)^2≤B^2*ω := by
    calc
      _ = (B*a)^2*ω^2 := by ring
      _ ≤ B^2*ω^2 := mul_le_mul_of_nonneg_right hBa2 (sq_nonneg ω)
      _ ≤ _ := mul_le_mul_of_nonneg_left hω2 (sq_nonneg B)
  have hm := mul_le_mul_of_nonneg_right hmB hω.1
  have hb := mul_le_mul_of_nonneg_right hBa2 hω.1
  unfold narrowTentError
  nlinarith

theorem narrowCDFTrialCoefficient_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (r q : ℝ)
    {h a θ : ℝ} (hh : 0<h) (ha : 0≤a) (hθ : 0≤θ) (haθ : a+θ=1) :
    narrowCDFTrialCoefficient β α r h q a θ≤
      β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
      2*a*narrowCDFMean β α r h θ*(β^2*scalarCDFJointSusceptibility β α r q-1)+
      narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2) := by
  let M := narrowCDFMean β α r h θ
  let ω := α (r+h)-α (r-h)
  have hM := narrowCDFMean_bounds β hm r hh hθ
  have hai : a∈Icc (0:ℝ) 1 := ⟨ha,by linarith⟩
  have hθ1 : θ≤1 := by linarith
  have hω : ω∈Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (hm (show r-h ≤ r+h by linarith)),by dsimp only [ω]; linarith [(hα (r+h)).2,(hα (r-h)).1]⟩
  have hω0 : 0≤ω := hω.1
  have hM0 : 0≤M := (mul_nonneg (mul_nonneg (sq_nonneg β) hθ) (hα r).1).trans hM.1
  have hθB : β^2*θ≤β^2 := by nlinarith [sq_nonneg β]
  have hMθ : M≤β^2*θ := hM.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hα (r+h)).2 (mul_nonneg (sq_nonneg β) hθ))
  have hMB : M≤β^2 := hMθ.trans hθB
  have HErr' := narrowTentError_bound (B:=β^2) (θ:=θ) (sq_nonneg β) hM0 hMB hai hω
  have hdiff : M-β^2*θ*α r≤β^2*ω := by
    have hmL := hm (show r-h ≤ r by linarith)
    have hd0 : 0≤α (r+h)-α r := sub_nonneg.mpr (hm (by linarith : r ≤ r+h))
    calc
      _ ≤ β^2*θ*(α (r+h)-α r) := by dsimp only [M] at *; nlinarith [hM.2]
      _ ≤ β^2*θ*ω := mul_le_mul_of_nonneg_left (by dsimp only [ω]; linarith) (mul_nonneg (sq_nonneg β) hθ)
      _ ≤ β^2*ω := mul_le_mul_of_nonneg_right hθB hω.1
  have hc : 2*a*(M-β^2*θ*α r)≤2*β^2*ω := by
    have H := mul_le_mul_of_nonneg_left hdiff (show 0≤2*a by positivity)
    have H' := mul_le_mul_of_nonneg_left hai.2 (show 0≤2*β^2*ω by positivity)
    nlinarith
  have ha2 : a^2≤1 := by nlinarith [hai.1,hai.2]
  have hc2 : β^2*a^2*ω≤β^2*ω := by nlinarith [mul_le_mul_of_nonneg_left ha2 (show 0≤β^2*ω by positivity)]
  have hn : 0≤β^2*α r*θ^2 := by have := (hα r).1; positivity
  unfold narrowCDFTrialCoefficient narrowCDFErrorConstant
  change _≤_+2*a*M*(_-1)+(10*β^4+3*β^2)*(ω+θ^2)
  change narrowTentError M (β^2*a) (β^2*θ) ω≤_ at HErr'
  have hωβ := mul_nonneg (sq_nonneg (β^2)) hω0
  dsimp only [M,ω] at *
  nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg θ),mul_nonneg (sq_nonneg (β^2)) (sq_nonneg θ)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarConditionalStability
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

theorem scalarHierarchy_hessian_square_cramer {f : ℝ → ℝ}
    (hf : BoundedDerivs f) (hc : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (x : ℝ) :
    (∑ i,(v i)^2)*(rootHessian 0 (scalarHierarchy n m v f) x)^2 ≤
      (1+2*(∑ i,(v i)^2))*(scalarHierarchyAverage n m v f
        (fun y => (rootGradient 0 f y)^2) x-(rootGradient 0 (scalarHierarchy n m v f) x)^2) := by
  let S := ∑ i,(v i)^2
  let K := scalarHierarchyAverage n m v f (rootHessian 0 f) x
  let H := rootHessian 0 (scalarHierarchy n m v f) x
  let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
    (rootGradient 0 (scalarHierarchy n m v f) x)^2
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd := scalarHierarchy_cramer_data hf hc n m v hm x
  change 0≤K ∧ K≤H ∧ H≤K+V ∧ S*K^2≤V at hd

  have hH1 : H≤1 := (le_abs_self H).trans ((hc.scalarHierarchy hf n m v hm).bounds x).2
  have hV : 0≤V := (mul_nonneg hS (sq_nonneg _)).trans hd.2.2.2
  have he : H^2≤K^2+2*V := by
    have hdiff : 0≤H-K := sub_nonneg.mpr hd.2.1
    have hsum : H+K≤2 := by linarith [hd.2.1]
    have hh := mul_le_mul_of_nonneg_left hsum hdiff
    nlinarith [hd.2.2.1]
  have heS := mul_le_mul_of_nonneg_left he hS
  change S*H^2≤(1+2*S)*V
  nlinarith [hd.2.2.2]

theorem scalarIncrementAverage_hessian_square_cramer (l j : List (ℝ × ℝ))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) :
    let H := scalarIncrementChain j f
    rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤
      (1+2*rawVariance j)*(scalarIncrementAverage (l++j) f (fun x => (rootGradient 0 f x)^2) 0-
        scalarIncrementAverage l H (fun x => (rootGradient 0 H x)^2) 0) := by
  dsimp only
  let H := scalarIncrementChain j f
  have hH := scalarIncrementChain_regular j hf
  have hHc : ScalarSpinConvex H := by
    change ScalarSpinConvex (scalarIncrementChain j f)
    rw [scalarIncrementChain_get]
    exact hc.scalarHierarchy hf _ _ _ (fun i => hj _ (List.get_mem _ _))
  have hχ := hHc.hessian_bounded hH
  have hU := hHc.gradient_bounded hH
  have hV := (scalarIncrementAverage_bounded j hf (hc.gradient_bounded hf).sq).sub hU.sq
  have hpoint (x : ℝ) : rawVariance j*(rootHessian 0 H x)^2 ≤
      (1+2*rawVariance j)*(scalarIncrementAverage j f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 H x)^2) := by
    have G := scalarHierarchy_hessian_square_cramer hf hc j.length
      (fun i => (j.get i).1) (fun i => (j.get i).2) (fun i => hj _ (List.get_mem _ _)) x
    rw [sum_get_map j (fun p => p.2^2)] at G
    simpa only [H,scalarIncrementChain_get,scalarIncrementAverage_get,rawVariance] using G
  have G := scalarIncrementAverage_mono l hH (hχ.sq.const_mul (rawVariance j))
    (hV.const_mul (1+2*rawVariance j)) hpoint 0
  change rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤ _
  have hleft := scalarHierarchyAverage_const_mul hH hχ.sq
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2)
    (c:=rawVariance j) (x:=0)
  have hright := scalarHierarchyAverage_const_mul hH hV
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2)
    (c:=1+2*rawVariance j) (x:=0)
  have hsub := scalarHierarchyAverage_sub hH
    (scalarIncrementAverage_bounded j hf (hc.gradient_bounded hf).sq) hU.sq
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2) (x:=0)
  simp only [← scalarIncrementAverage_get] at hleft hright hsub
  rw [hleft,hright] at G
  change rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤
    (1+2*rawVariance j)*scalarIncrementAverage l H (fun x => scalarIncrementAverage j f
      (fun y => (rootGradient 0 f y)^2) x-(rootGradient 0 H x)^2) 0 at G
  rw [hsub] at G
  rw [scalarIncrementAverage_append]
  exact G

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFConditionalStability
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

theorem scalarTimeChainAverage_hessian_square_cramer (β : ℝ) (l j : List (ℝ × ℝ≥0))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) :
    let H := scalarTimeChain β j f
    β^2*(chainDuration j:ℝ)*scalarTimeChainAverage β l H (fun x => (rootHessian 0 H x)^2) 0 ≤
      (1+2*(β^2*(chainDuration j:ℝ)))*(scalarTimeChainAverage β (l++j) f (fun x => (rootGradient 0 f x)^2) 0-
        scalarTimeChainAverage β l H (fun x => (rootGradient 0 H x)^2) 0) := by
  have G := scalarIncrementAverage_hessian_square_cramer
    (scaleIncrementChain β (rawTimeChain l)) (scaleIncrementChain β (rawTimeChain j)) hf hc
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hj))
  dsimp only at G ⊢
  rw [← scaleIncrementChain_append,← rawTimeChain_append] at G
  simpa only [rawVariance_scale,rawVariance_rawTimeChain,scalarIncrementChain_rawTimeChain,
    scalarIncrementAverage_rawTimeChain] using G

theorem scalarCDF_conditional_stability_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    β^2*(q-r)*scalarCDFSusceptibilitySquareAverage β (quantileCDF k Q) r ≤
      (1+2*(β^2*(q-r)))*(scalarCDFOverlap β (quantileCDF k Q) q-
        scalarCDFOverlap β (quantileCDF k Q) r) := by
  let α := quantileCDF k Q
  have ha := quantileCDF_bounds k Q
  have hm := quantileCDF_monotone k Q
  let sr := Real.toNNReal (1-r)
  let sq := Real.toNNReal (1-q)
  let tq := Real.toNNReal q
  let tr := Real.toNNReal r
  let tj := Real.toNNReal (q-r)
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hsq : (sq:ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have htq : (tq:ℝ)=q := Real.coe_toNNReal _ (by linarith)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have htj : (tj:ℝ)=q-r := Real.coe_toNNReal _ (sub_nonneg.mpr hrq)
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have hsq1 : sq≤1 := by rw [← NNReal.coe_le_coe,hsq,NNReal.coe_one]; linarith
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have htq1 : tq≤1 := by rw [← NNReal.coe_le_coe,htq,NNReal.coe_one]; exact hq
  have htj1 : tj≤1 := by rw [← NNReal.coe_le_coe,htj,NNReal.coe_one]; linarith
  obtain ⟨l,hdl,hml,_,hmodelL⟩ := quantile_interval_chain β Q hQ (s:=0) (t:=r) le_rfl hr (hrq.trans hq)
  obtain ⟨j,hdj,hmj,_,hmodelJ⟩ := quantile_interval_chain β Q hQ hr hrq hq
  have hdl' : chainDuration l=tr := NNReal.coe_injective (by rw [htr,hdl,sub_zero])
  have hdj' : chainDuration j=tj := NNReal.coe_injective (by rw [htj,hdj])
  have hdlj : chainDuration (l++j)=tq := by
    apply NNReal.coe_injective
    rw [chainDuration_append,NNReal.coe_add,hdl,hdj,htq]; ring
  have hmlj : ∀ p∈l++j,p.1∈Icc (0:ℝ) 1 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hml p) (hmj p)
  have hmodelLJ : TimeChainModels α 0 (l++j) := hmodelL.append (by simpa only [hdl,zero_add,sub_zero] using hmodelJ)
  let F := scalarCDFValue β α q sq
  let H := scalarCDFValue β α r sr
  have hF : BoundedDerivs F := scalarCDFValue_regular β ha hm q sq hsq1
  have hH : BoundedDerivs H := scalarCDFValue_regular β ha hm r sr hsr1
  have hFc : ScalarSpinConvex F := scalarCDFValue_spinConvex β ha hm q sq hsq1
  have he : scalarTimeChain β j F=H := by
    funext x
    rw [← scalarCDFOperator_eq_chain hF (scalarCDFValue_lipschitz β ha hm q sq hsq1)
      β ha hm j hmj r tj htj1 hdj' hmodelJ x]
    exact (congrFun (scalarCDFValue_suffix_semigroup_quantile β Q hQ hr hrq hq) x).symm
  have havr : scalarTimeChainAverage β l H (fun x => (rootGradient 0 H x)^2) 0=scalarCDFOverlap β α r := by
    have ht := scalarCDFGradient_sq_regular β ha hm r sr hsr1
    change scalarTimeChainAverage β l (scalarCDFValue β α r sr) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm r sr hsr1]
    exact (scalarCDFAverage_eq_chainAverage hH ht.1 ht.2.1
      (scalarCDFValue_lipschitz β ha hm r sr hsr1) (B:=1) ht.2.2.1 (C:=2) ht.2.2.2
      β ha hm l hml 0 tr htr1 hdl' hmodelL 0).symm
  have havq : scalarTimeChainAverage β (l++j) F (fun x => (rootGradient 0 F x)^2) 0=scalarCDFOverlap β α q := by
    have ht := scalarCDFGradient_sq_regular β ha hm q sq hsq1
    change scalarTimeChainAverage β (l++j) (scalarCDFValue β α q sq) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm q sq hsq1]
    exact (scalarCDFAverage_eq_chainAverage hF ht.1 ht.2.1
      (scalarCDFValue_lipschitz β ha hm q sq hsq1) (B:=1) ht.2.2.1 (C:=2) ht.2.2.2
      β ha hm (l++j) hmlj 0 tq htq1 hdlj hmodelLJ 0).symm
  have havχ : scalarTimeChainAverage β l H (fun x => (rootHessian 0 H x)^2) 0=
      scalarCDFSusceptibilitySquareAverage β α r := by
    change scalarTimeChainAverage β l (scalarCDFValue β α r sr) _ 0=_
    rw [scalarCDFValue_rootHessian β ha hm r sr hsr1]
    exact (scalarCDFAverage_eq_chainAverage_lipschitz hH
      (scalarCDFValue_lipschitz β ha hm r sr hsr1)
      (scalarCDFHessian_square_lipschitz β ha hm r sr hsr1)
      (B:=1) (scalarCDFHessian_square_bound β ha hm r sr hsr1)
      β ha hm l hml 0 tr htr1 hdl' hmodelL 0).symm
  have G := scalarTimeChainAverage_hessian_square_cramer β l j hF hFc hmj
  dsimp only at G
  rw [he,hdj,havr,havq,havχ] at G
  exact G

theorem scalarCDF_conditional_stability (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r q : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    β^2*(q-r)*scalarCDFSusceptibilitySquareAverage β α r ≤
      (1+2*(β^2*(q-r)))*(scalarCDFOverlap β α q-scalarCDFOverlap β α r) := by
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hn (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hnm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have Hχ := scalarCDFSusceptibilitySquareAverage_tendsto β ha α.mono hn hnm hD ⟨hr,hrq.trans hq⟩
  have HΓ := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono hn hnm hD
  have HL := Hχ.const_mul (β^2*(q-r))
  have HR := ((HΓ.tendsto_at ⟨hr.trans hrq,hq⟩).sub (HΓ.tendsto_at ⟨hr,hrq.trans hq⟩)).const_mul (1+2*(β^2*(q-r)))
  exact le_of_tendsto_of_tendsto HL HR (Eventually.of_forall (fun n =>
    scalarCDF_conditional_stability_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hr hrq hq))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFIdentityStability
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

theorem scalarCDF_susceptibility_square_le_one (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r u : ℝ}
    (hr : 0 ≤ r) (hru : r<u) (hu : u≤1)
    (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s) :
    β^2*scalarCDFSusceptibilitySquareAverage β α r≤1 := by
  let d (n : ℕ) : ℝ := (u-r)/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := div_pos (sub_pos.mpr hru) (by positivity)
  have hdle (n : ℕ) : d n≤u-r := by
    dsimp [d]
    apply div_le_self (sub_nonneg.mpr hru.le)
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have H (n : ℕ) : β^2*scalarCDFSusceptibilitySquareAverage β α r≤1+2*(β^2*d n) := by
    have hqin : r+d n∈Icc r u := ⟨by linarith [hd n],by linarith [hdle n]⟩
    have G := scalarCDF_conditional_stability β α ha h1 hr hqin.1 (hqin.2.trans hu)
    rw [hΓ (r+d n) hqin,hΓ r ⟨le_rfl,hru.le⟩] at G
    have G' : d n*(β^2*scalarCDFSusceptibilitySquareAverage β α r)≤d n*(1+2*(β^2*d n)) := by
      nlinarith [G]
    exact (mul_le_mul_iff_right₀ (hd n)).mp (by simpa only [mul_comm] using G')
  have ht : Tendsto d atTop (𝓝 0) := by
    simpa only [d,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (u-r)
  have Hlim : Tendsto (fun n => 1+2*(β^2*d n)) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using ((ht.const_mul (β^2)).const_mul 2).const_add 1
  exact ge_of_tendsto Hlim (Eventually.of_forall H)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleContinuumTrial
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

theorem uniformCDFQuantiles_pointwise_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => quantileCDF n (uniformCDFQuantiles n α) s) atTop (𝓝 (α s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => quantileCDF_uniformCDFQuantiles_error n α hα hα1 hs)
    (show Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) by
      simpa only [Nat.cast_add,Nat.cast_one,one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
  simpa only [Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointLoss
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

theorem scalarCDFJointSusceptibility_loss (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1)
    {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    scalarCDFJointSusceptibility β α r q ≤ scalarCDFSusceptibilitySquareAverage β α r-
      α r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have hJ := scalarCDFJointSusceptibility_tendsto β ha α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) hD hr hrq hq
  have hS := scalarCDFSusceptibilitySquareAverage_tendsto β ha α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) hD ⟨hr,hrq.trans hq⟩
  have hα := uniformCDFQuantiles_pointwise_tendsto α ha h1 ⟨hr,hrq.trans hq⟩
  exact le_of_tendsto_of_tendsto hJ (hS.sub (((hα.mul_const (β^2*(q-r))).mul_const
    ((scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3)).div_const 2))
    (Eventually.of_forall (fun n => scalarCDFJointSusceptibility_quantile_loss β
      (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α h1) hr hrq hq))

theorem scalarJointLossConstant_pos {β a : ℝ} (hβ : β≠0) (ha : 0<a) :
    0 < scalarJointLossConstant β a := by
  unfold scalarJointLossConstant
  have hb4 : 0<β^4 := by
    have H := sq_pos_of_ne_zero hβ
    nlinarith [sq_pos_of_pos H]
  have hf := scalarSusceptibilityFloor_pos (β^2) (1+2*β^2+4*(β^2)^2)
  positivity

theorem scalarCDFJointSusceptibility_strict_loss (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r q u a : ℝ}
    (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) (hru : r<u) (hu : u≤1)
    (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s) (har : a≤α r) (ha0 : 0≤a) :
    β^2*scalarCDFJointSusceptibility β α r q≤1-scalarJointLossConstant β a*(q-r) := by
  have H := mul_le_mul_of_nonneg_left (scalarCDFJointSusceptibility_loss β α ha h1 hr hrq hq) (sq_nonneg β)
  have H₀ := scalarCDF_susceptibility_square_le_one β α ha h1 hr hru hu hΓ
  have Hp := mul_le_mul le_rfl har ha0 (show 0≤β^4*((scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3)*(q-r)/2 by
    have := scalarSusceptibilityFloor_pos (β^2) (1+2*β^2+4*(β^2)^2)
    have := sub_nonneg.mpr hrq
    positivity)
  dsimp [scalarJointLossConstant]
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowNegativeCoefficient
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

theorem narrowCDFTrialCoefficient_quantitative_oai {β : ℝ} (hβ : β≠0)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q u a θ m η : ℝ} (hh : 0< h) (hr : 0≤ r) (hrq : r≤ q) (hq : q≤1)
    (hru : r< u) (hu : u≤1) (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s)
    (hm : 0 < m) (hmr : m≤α r) (ha : 1/2≤ a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hS : scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q))
    (hdev : |q-scalarCDFOverlap β α q|≤η) :
    narrowCDFTrialCoefficient β α r h q a θ≤
      3*β^2*η/h+narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2)-
        (β^2*m*scalarJointLossConstant β m)*θ*(q-r) := by
  have ha0 : 0≤ a := by linarith
  have ha1 : a≤1 := by linarith
  have hθ1 : θ≤1 := by linarith
  have hη : 0≤η := (abs_nonneg _).trans hdev
  have hK0 : 0≤(2*a^2+θ^2)/h := by positivity
  have hK : (2*a^2+θ^2)/h≤3/h := by
    apply div_le_div_of_nonneg_right _ hh.le
    nlinarith [sq_nonneg (1-a),sq_nonneg (1-θ)]
  have hSq : scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x)≤η := by
    rw [hS]
    have H := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdev) (hα q).1
    have H' := mul_le_mul_of_nonneg_right (hα q).2 hη
    nlinarith
  have Hq : β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))≤3*β^2*η/h := by
    calc
      _ ≤ β^2*((2*a^2+θ^2)/h)*η := mul_le_mul_of_nonneg_left hSq (mul_nonneg (sq_nonneg β) hK0)
      _ ≤ β^2*(3/h)*η := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg β)) hη
      _ = _ := by ring
  have hJ := scalarCDFJointSusceptibility_strict_loss β α hα hα1 hr hrq hq hru hu hΓ hmr hm.le
  have hL : 0≤ scalarJointLossConstant β m := (scalarJointLossConstant_pos hβ hm).le
  have hD : 0≤ q-r := sub_nonneg.mpr hrq
  have hmean := narrowCDFMean_bounds β α.mono r hh hθ
  have hmeanm : β^2*θ*m≤ narrowCDFMean β α r h θ :=
    (mul_le_mul_of_nonneg_left hmr (mul_nonneg (sq_nonneg β) hθ)).trans hmean.1
  have hmean0 : 0≤ narrowCDFMean β α r h θ := (by positivity : 0≤β^2*θ*m).trans hmeanm
  have hmixed : β^2*θ*m≤2*a*narrowCDFMean β α r h θ := by
    have H := mul_le_mul_of_nonneg_right ha hmean0
    linarith
  have Hmix : 2*a*narrowCDFMean β α r h θ*(β^2*scalarCDFJointSusceptibility β α r q-1)≤
      -(β^2*m*scalarJointLossConstant β m)*θ*(q-r) := by
    have H := mul_le_mul_of_nonneg_left (show β^2*scalarCDFJointSusceptibility β α r q-1≤-scalarJointLossConstant β m*(q-r) by linarith)
      (show 0≤2*a*narrowCDFMean β α r h θ by positivity)
    have H' := mul_le_mul_of_nonneg_right hmixed (mul_nonneg hL hD)
    nlinarith only [H,H']
  have H := narrowCDFTrialCoefficient_le β hα α.mono r q hh ha0 hθ haθ
  linarith

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative_oai := @OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative_oai
