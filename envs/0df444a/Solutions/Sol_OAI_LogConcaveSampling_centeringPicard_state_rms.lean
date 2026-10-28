-- Prove2me | solution 1 for OAI.LogConcaveSampling.centeringPicard_state_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:54:29.331897+00:00
-- url     : https://prove2.me/submissions/0704e96d-5995-40fb-8bdf-d708aa1f97c9

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_centeringTrueVelocity_continuous
import Theorems.Thm_OAI_LogConcaveSampling_centering_velocity_taylor_uniform
import Theorems.Thm_OAI_LogConcaveSampling_stationary_lie_taylor_rms

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_NormalizedLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma dir_zero (f : E → ℝ) : dir 0 f=fun _ => 0 := by funext x; simp [dir]

end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Directional
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace
open MeasureTheory

lemma directional_mul {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x*g x)=fun x => directional v f x*g x+f x*directional v g x := by
  funext x
  unfold directional
  change (fderiv ℝ (f*g) x) v=_
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma directional_add {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x+g x)=fun x => directional v f x+directional v g x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv

lemma directional_sum {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀ i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => ∑ i∈s,f i x)=fun x => ∑ i∈s,directional v (f i) x := by
  funext x
  have hh := HasFDerivAt.fun_sum (u:=s) (fun i hi => (hf i hi x).hasFDerivAt)
  simpa only [directional,sum_apply] using
    congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh.fderiv

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolyC1
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integrable_polynomial_gibbs {d : ℕ} {H f : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : Continuous f)
    (hg : HasPolynomialGrowth f) : Integrable f (gibbs H) := by
  apply integrable_gibbs_of_weighted hH (ht.integrable_exp hH)
  simpa using integrable_tilted H hH hf ht hg 0

namespace PolyC1
variable {d : ℕ} {f g : Point d → ℝ}
lemma differentiable (hf : PolyC1 f) : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
end PolyC1

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ParametricFDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CompactIntegral
open Set Function Filter MeasureTheory Metric
open scoped Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma parametric_hasFDerivAt {f : E × ℝ → F} (hf : ContDiff ℝ 1 f)
    {s : Set ℝ} (hs : IsCompact s) (x : E) :
    HasFDerivAt (fun x => ∫t in s,f (x,t))
      (∫t in s,(fderiv ℝ f (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D := fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hs).exists_bound_of_continuousOn hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F':=fun y t => D (y,t)) (bound:=fun _ => C) (ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun y => (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs.measurableSet] with t ht y hy
    exact hC (y,t) ⟨ball_subset_closedBall hy,ht⟩
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards [] with t y _hy
    exact ((hf.differentiable (by norm_num) (y,t)).hasFDerivAt).comp y
      ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const (𝕜:=ℝ) t y))

theorem contDiff_parametric {f : E × ℝ → F} (n : ℕ)
    (hf : ContDiff ℝ (n:WithTop ℕ∞) f) {s : Set ℝ} (hs : IsCompact s) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => ∫t in s,f (x,t)) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (continuous_parametric_integral_of_continuous (f:=fun x t => f (x,t)) hf.continuous hs)
  | succ n ih =>
    let D := fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ (n:WithTop ℕ∞) D := (hf.fderiv_right (by simp)).clm_comp contDiff_const
    have hd (x : E) := parametric_hasFDerivAt (hf.of_le (by exact_mod_cast Nat.succ_pos n)) hs x
    rw [show ((n+1:ℕ):WithTop ℕ∞)=(n:WithTop ℕ∞)+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt,?_⟩
    refine ⟨by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫t in s,f (x,t))=fun x => ∫t in s,D (x,t) := funext fun x => (hd x).fderiv
    rw [he]
    exact ih hD

theorem smooth_parametric {f : E × ℝ → F} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    {s : Set ℝ} (hs : IsCompact s) :
    ContDiff ℝ (⊤:ℕ∞) (fun x => ∫t in s,f (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_parametric n (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hs
end LogConcaveSampling.CompactIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

lemma interpolation_exponent {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 1-ρ^2≠0) :
    -primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2))=
      -‖y‖^2/(2*(1-ρ^2))+
        (inner ℝ (conditionalParameter (ρ,y)).1 z-
          (conditionalParameter (ρ,y)).2*‖z‖^2-primitivePotential F x r z) := by
  simp only [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_right,inner_smul_left,conditionalParameter,conj_trivial]
  rw [real_inner_comm z y]
  field_simp
  ring

lemma interpolation_density_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) (y : Point d) :
    (∫⁻ z,ENNReal.ofReal (Real.exp (-primitivePotential F x r z-
      ‖y-ρ • z‖^2/(2*(1-ρ^2)))))=gibbsDensity (interpolationPotential F x r ρ) y := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  let p := conditionalParameter (ρ,y)
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  have hi := integrable_quadraticTilt (hF.continuous_potential x r) continuous_const ht
    (growth_const (1:ℝ)) p hp
  have hz := quadratic_partition_pos (hF.continuous_potential x r) ht p hp
  have he : ∀ z,Real.exp (-primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2)))=
      Real.exp (-‖y‖^2/(2*(1-ρ^2)))*
        Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-primitivePotential F x r z) := by
    intro z
    rw [interpolation_exponent F x r ρ y z (by linarith),Real.exp_add]
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hH := (hF.continuous_potential x r).measurable
  rw [lintegral_const_mul _ (by fun_prop)]
  have ht' : (∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-
      primitivePotential F x r z)))=ENNReal.ofReal (quadraticTilt (primitivePotential F x r) (fun _ => (1:ℝ)) p) := by
    dsimp [quadraticTilt]
    simp only [smul_eq_mul,mul_one] at hi ⊢
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      hi.aestronglyMeasurable,ENNReal.ofReal_toReal
        ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).2 hi)]
  rw [ht',←ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold gibbsDensity interpolationPotential
  congr 1
  rw [neg_sub,Real.exp_sub,Real.exp_log hz]
  dsimp [p]
  rw [neg_div,Real.exp_neg]
  ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianMarginalLowerTail
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma gaussian_marginal_lowerTail {d : ℕ} {P H : Point d → ℝ}
    (hP : Continuous P) (ht : HasGaussianLowerTail P) {a ρ : ℝ}
    (ha : 0<a) (hρ : ρ^2≤1)
    (hD : ∀y,(∫⁻z,ENNReal.ofReal (Real.exp (-P z-‖y-ρ • z‖^2/(2*a))))=
      ENNReal.ofReal (Real.exp (-H y))) : HasGaussianLowerTail H := by
  obtain ⟨m,hm,C,hC⟩ := ht
  let b := min m a⁻¹/4
  have hb : 0<b := div_pos (lt_min hm (inv_pos.mpr ha)) (by norm_num)
  have hb1 : 2*b≤ m/2 := by dsimp [b]; linarith [min_le_left m a⁻¹]
  have hb2 : 2*b≤1/(2*a) := by
    have he : a⁻¹/2=1/(2*a) := by field_simp
    rw [←he]
    dsimp [b]; linarith [min_le_right m a⁻¹]
  let J := ∫z : Point d,Real.exp (-(m/2)*‖z‖^2)
  have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨b,hb,C+Real.log (J+1),fun y => ?_⟩
  have hpoint : ∀z : Point d,Real.exp (-P z-‖y-ρ • z‖^2/(2*a))≤
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2) := by
    intro z
    have hsum := norm_add_le (y-ρ • z) (ρ • z)
    rw [sub_add_cancel] at hsum
    have hy : ‖y‖^2≤2*‖y-ρ • z‖^2+2*‖z‖^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg y) hsum 2
      have hz : ‖ρ • z‖^2≤‖z‖^2 := by
        rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
        exact mul_le_of_le_one_left (sq_nonneg _) hρ
      nlinarith [sq_nonneg (‖y-ρ • z‖-‖ρ • z‖)]
    have hby := mul_le_mul_of_nonneg_left hy hb.le
    have h1 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖y-ρ • z‖)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : ‖y-ρ • z‖^2/(2*a)=(1/(2*a))*‖y-ρ • z‖^2 := by ring
    rw [he]
    nlinarith [hC z]
  have hbound : Integrable (fun z : Point d =>
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2)) :=
    (integrable_gaussian_envelope d (by positivity : 0 < m/2)).const_mul _
  have hk : Integrable (fun z : Point d => Real.exp (-P z-‖y-ρ • z‖^2/(2*a))) := by
    apply hbound.mono' (by fun_prop)
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint z
  have he : (∫z,Real.exp (-P z-‖y-ρ • z‖^2/(2*a)))=Real.exp (-H y) := by
    have hh := hD y
    rw [←ofReal_integral_eq_lintegral_ofReal hk
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at hh
    have h := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => (Real.exp_pos _).le)),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hi := integral_mono hk hbound hpoint
  rw [he,integral_const_mul] at hi
  change Real.exp (-H y)≤Real.exp (C-b*‖y‖^2)*J at hi
  have hh : Real.exp (-H y)≤Real.exp (C-b*‖y‖^2+Real.log (J+1)) := by
    rw [Real.exp_add,Real.exp_log (by linarith : 0<J+1)]
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
  have := Real.exp_le_exp.mp hh
  linarith

lemma interpolationPotential_lowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    HasGaussianLowerTail (interpolationPotential F x r ρ) := by
  have ha := (probability_time hρ0 hρ1).1
  apply gaussian_marginal_lowerTail (hF.continuous_potential x r)
    (hF.hasGaussianLowerTail x hr hl) ha (by linarith)
  intro y
  exact interpolation_density_integral hF x hr hl (by linarith) y

lemma interpolationPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (1+‖r*ρ‖₊*⟨(Real.pi^2/2)*ρ*((lam:ℝ)*r),by positivity⟩)
      (gradient (interpolationPotential F x r ρ)) := by
  have he := funext (interpolationPotential_gradient hF x hr hl hρ0 hρ1)
  rw [he]
  exact LipschitzWith.id.add ((lipschitzWith_smul (r*ρ)).comp (conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AdjointCoordinateContinuous
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma jet_neg {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l (fun x => -f x)=fun x => -JetCalculus.jet v l f x := by
  simpa only [neg_one_mul] using JetCalculus.jet_const_mul hf v l (-1)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolySmooth
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace PolySmooth
variable {d : ℕ} {f g H : Point d → ℝ}

lemma jet_growth (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    HasPolynomialGrowth (JetCalculus.jet b l f) := by
  have hh := hf.growth (l.map b)
  simpa only [JetCalculus.jet_map,Function.id_comp] using hh

lemma directional (hf : PolySmooth f) (v : Point d) : PolySmooth (LogConcaveSampling.directional v f) := by
  refine ⟨directional_smooth hf.smooth v,fun l => ?_⟩
  have he : JetCalculus.jet id [v] f=LogConcaveSampling.directional v f := rfl
  have hh := hf.growth (l++[v])
  rw [JetCalculus.jet_append,he] at hh
  exact hh

lemma jet (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    PolySmooth (JetCalculus.jet b l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact ih.directional (b i)

lemma polyC1 (hf : PolySmooth f) : PolyC1 f :=
  ⟨hf.smooth.of_le (by simp),hf.growth [],fun v => (hf.directional v).growth []⟩

lemma add (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,fun l => ?_⟩
  rw [JetCalculus.jet_add hf.smooth hg.smooth]
  exact Appell.HasGrowth.add (hf.growth l) (hg.growth l)

lemma neg (hf : PolySmooth f) : PolySmooth (fun x => -f x) := by
  refine ⟨hf.smooth.neg,fun l => ?_⟩
  rw [jet_neg hf.smooth]
  simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
    Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.growth l)

lemma mul (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,fun l => ?_⟩
  induction l generalizing f g with
  | nil => exact Appell.HasGrowth.mul (hf.growth []) (hg.growth [])
  | cons v l ih =>
    change HasPolynomialGrowth (LogConcaveSampling.directional v
      (JetCalculus.jet id l (fun x => f x*g x)))
    rw [←jet_directional (hf.smooth.mul hg.smooth),
      directional_mul hf.polyC1.differentiable hg.polyC1.differentiable,
      JetCalculus.jet_add ((hf.directional v).smooth.mul hg.smooth)
        (hf.smooth.mul (hg.directional v).smooth)]
    exact Appell.HasGrowth.add (ih (hf.directional v) hg) (ih hf (hg.directional v))

lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),fun l => ?_⟩
  rw [JetCalculus.jet_sum s (fun i hi => (hf i hi).smooth)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth l)

lemma adjoint (hH : PolySmooth H) (hf : PolySmooth f) (v : Point d) :
    PolySmooth (adjointCoordinate H v f) :=
  (hf.directional v).neg.add ((hH.directional v).mul hf)

lemma const (c : ℝ) : PolySmooth (fun _ : Point d => c) := by
  refine ⟨contDiff_const,fun l => ?_⟩
  rw [JetCalculus.jet_const]
  split_ifs <;> exact growth_const _

lemma integrable (hf : PolySmooth f) (hH : Continuous H) (ht : HasGaussianLowerTail H) :
    Integrable f (gibbs H) :=
  integrable_polynomial_gibbs hH ht hf.smooth.continuous (hf.growth [])

lemma tensorAdjoint {ι : Type*} [Fintype ι] {V : ι → Point d → ℝ}
    (hH : PolySmooth H) (hV : ∀i,PolySmooth (V i)) (b : ι → Point d) :
    PolySmooth (LogConcaveSampling.tensorAdjoint H b V) :=
  sum Finset.univ (fun i _ => hH.adjoint (hV i) (b i))
end PolySmooth
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SpaceBasis
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma PolySmooth.linear {d : ℕ} (L : Point d →L[ℝ] ℝ) : PolySmooth L := by
  apply PolySmooth.of_basis_growth L.contDiff
  intro l
  cases l with
  | nil => exact growth_of_lipschitz L.lipschitz
  | cons i l =>
    change HasPolynomialGrowth (LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l L))
    rw [←jet_directional L.contDiff]
    have he : LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i) L=
        fun _ => L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
      funext y
      simp [LogConcaveSampling.directional]
    rw [he,JetCalculus.jet_const]
    split_ifs <;> exact growth_const _

lemma growth_potential_of_gradient_lipschitz {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (hK : LipschitzWith K (gradient H)) : HasPolynomialGrowth H := by
  let C := |H 0|+‖gradient H 0‖+(K:ℝ)+1
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,2,fun y => ?_⟩
  have ht := quadratic_remainder_of_gradient_lipschitz hH hK 0 y
  rw [zero_add] at ht
  have hi := abs_real_inner_le_norm y (gradient H 0)
  have hb : |H y|≤|H 0|+‖y‖*‖gradient H 0‖+(K:ℝ)*‖y‖^2/2 := by
    have he : H y=(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0) := by ring
    calc
      |H y| = |(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0)| := congrArg abs he
      _ ≤ |H y-H 0-inner ℝ y (gradient H 0)|+|H 0|+|inner ℝ y (gradient H 0)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hy : ‖y‖≤1+‖y‖^2 := by nlinarith [sq_nonneg (‖y‖-1)]
  have hh := mul_le_mul_of_nonneg_right hy (norm_nonneg (gradient H 0))
  change ‖H y‖≤C*(1+‖y‖^2)
  rw [Real.norm_eq_abs]
  dsimp [C]
  nlinarith [mul_nonneg (abs_nonneg (H 0)) (sq_nonneg ‖y‖),
    mul_nonneg (show (0:ℝ)≤K from K.coe_nonneg) (sq_nonneg ‖y‖)]

lemma interpolationPotential_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    PolySmooth (interpolationPotential F x r ρ) := by
  have hs := interpolationPotential_smooth hF x hr.le hl hρ0 hρ1
  apply PolySmooth.of_basis_growth hs
  intro l
  cases l with
  | nil =>
    exact growth_potential_of_gradient_lipschitz (hs.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top)))
      (interpolationPotential_gradient_lipschitz hF x hr.le hl hρ0 hρ1)
  | cons i l =>
    let v := EuclideanSpace.basisFun (Fin d) ℝ i
    change HasPolynomialGrowth (directional v
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l (interpolationPotential F x r ρ)))
    rw [←jet_directional hs]
    have he : directional v (interpolationPotential F x r ρ)=fun y =>
        inner ℝ v y+(r*ρ)*inner ℝ v (conditionalFieldMean F x r ρ y) := by
      funext y
      rw [directional_gradient,interpolationPotential_gradient hF x hr.le hl hρ0 hρ1,
        real_inner_comm,inner_add_right,inner_smul_right]
    rw [he]
    exact ((PolySmooth.linear (innerSL ℝ v)).add ((PolySmooth.const (r*ρ)).mul
      (conditionalFieldMean_component_polySmooth hF x hr hlam hl hρ0 hρ1 i))).jet_growth _ l

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateRank
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped Topology NNReal RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hF hr hlam hl in
lemma conditionalFirstJet_smooth (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalFirstJet F x r ((lam:ℝ)*r)) p := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (conditionalU_joint_smooth hF x hr hlam hl
    (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ j) [()] (by simp)
    (EuclideanSpace.basisFun (Fin d) ℝ i) p hp).smul contDiffAt_const

lemma terminalJacobian_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalJacobian hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (((terminalForward_smooth hF x hr.le hl hT0 hT1).fderiv_right (by simp)).comp
    ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1))).clm_comp contDiff_const

include hlam in
lemma steinIntegrand_smooth : ContDiff ℝ (⊤:ℕ∞) (steinIntegrand hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  have hU : ContDiff ℝ (⊤:ℕ∞) (fun p => conditionalFirstJet F x r ((lam:ℝ)*r)
      (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (conditionalFirstJet_smooth hF x hr hlam hl _ (smoothTimeClip_sq_lt hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1)).contDiffAt
  exact (terminalJacobian_smooth hF x hr hl hT0 hT1).clm_comp hU

include hlam in
lemma centeringKernel_smooth : ContDiff ℝ (⊤:ℕ∞) (centeringKernel hF x hr hl hT0 hT1) := by
  let : CompleteSpace (Point d →L[ℝ] Point d) := ContinuousLinearMap.instCompleteSpace
  have hs := CompactIntegral.smooth_parametric
    ((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).comp (contDiff_snd.prodMk contDiff_fst))
    (s:=Icc (0:ℝ) T) isCompact_Icc
  exact ContinuousLinearMap.adjoint.contDiff.comp hs
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set Function
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalJacobian_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalJacobian hF x hr hl hT0 hT1 (t,y)=
      fderiv ℝ (probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩)
        (terminalBackward hF x hr.le hl hT0 hT1 (t,y)) := by
  have hh := ((terminalForward_smooth hF x hr.le hl hT0 hT1).differentiable (by simp)
    ((t:ℝ),terminalBackward hF x hr.le hl hT0 hT1 (t,y))).hasFDerivAt.comp
    (terminalBackward hF x hr.le hl hT0 hT1 (t,y))
    ((hasFDerivAt_const (t:ℝ) _).prodMk (hasFDerivAt_id _))
  have he : (fun z => terminalForward hF x hr.le hl hT0 hT1 (t,z))=
      probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩ :=
    funext (terminalForward_eq hF x hr.le hl hT0 hT1 t)
  change HasFDerivAt (fun z => terminalForward hF x hr.le hl hT0 hT1 (t,z)) _ _ at hh
  rw [he] at hh
  change HasFDerivAt _ ((fderiv ℝ (terminalForward hF x hr.le hl hT0 hT1)
    ((t:ℝ),terminalBackward hF x hr.le hl hT0 hT1 (t,y))).comp
      (ContinuousLinearMap.inr ℝ ℝ (Point d))) _ at hh
  simpa only [terminalJacobian,smoothTimeClip_eq hT0 hT1 t.2] using hh.fderiv.symm

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensor
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma fullList_perm {K : Type u} [Fintype K] {l m : List K}
    (hl : l.Nodup) (hm : m.Nodup) (hal : ∀k,k∈l) (ham : ∀k,k∈m) : l.Perm m := by
  apply (List.perm_ext_iff_of_nodup hl hm).mpr
  intro k
  simp only [hal k,ham k]

lemma spatialTensor_relabel {d : ℕ} {S T K J : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (c : J ⊕ T → Fin d) :
    spatialTensor F l y (c ∘ (f.sumCongr e))=
      spatialTensor (fun a => F (a ∘ e)) m y c := by
  unfold spatialTensor
  simp only [Function.comp_def,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  have hh := congrFun (JetCalculus.jet_perm (hF (fun s => c (Sum.inr (e s))))
    (fun j => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl j))) hlm) y
  rw [JetCalculus.jet_map] at hh
  exact hh

lemma spatialTensor_polySmooth {d : ℕ} {S K : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) : PolySmooth (fun y => spatialTensor F l y c) :=
  (hF _).jet _ l

lemma spatialTensor_allSplit_relabel {d : ℕ} {S T K J : Type u}
    [Fintype S] [Fintype T] [Fintype K] [Fintype J]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (B : ℝ)
    (hB : TensorEnergy.AllSplitBound (spatialTensor F l y) B) :
    TensorEnergy.AllSplitBound (spatialTensor (fun a => F (a ∘ e)) m y) B := by
  have hh := hB.reindex (f.sumCongr e)
  simpa only [spatialTensor_relabel F hF e f l m hlm y] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical

universe u

lemma jet_selectList {d : ℕ} {K : Type u} (p : K → Prop) [DecidablePred p]
    (v : K → Point d) (l : List K) (f : Point d → ℝ) :
    JetCalculus.jet (fun k : {k // p k} => v k.val) (selectList p l) f=
      JetCalculus.jet v (l.filter (fun k => decide (p k))) f := by
  rw [←map_selectList p l,JetCalculus.jet_map]
  rfl

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreSlots
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

universe u

lemma extendedSpatial_allSplit {d : ℕ} {S K : Type u} [Fintype S] [Fintype K]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M : ℝ}
    (h : TensorEnergy.AllSplitBound (spatialTensor F l y) M) :
    TensorEnergy.AllSplitBound (extendedSpatial F l y) M :=
  h.reindex (Equiv.sumAssoc K S Unit).symm

lemma spatialContractTerm_eq {d : ℕ} {S T K : Type u} (p : K → Prop) [DecidablePred p]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : K ⊕ (S ⊕ T) → Fin d) :
    spatialContractTerm p F G l y c = ∑z : Fin d,
      JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
        (l.filter (fun k => decide (p k))) (F (Sum.elim (fun s => c (Sum.inr (Sum.inl s))) (fun _ => z))) y *
      JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
        (l.filter (fun k => decide (¬p k))) (G (Sum.elim (fun t => c (Sum.inr (Sum.inr t))) (fun _ => z))) y := by
  unfold spatialContractTerm TensorEnergy.singleContract extendedSpatial spatialTensor
  apply Finset.sum_congr rfl
  intro z _
  simp only [Function.comp_def,Equiv.sumAssoc_symm_apply_inl,Sum.elim_inl,
    contractSpatialSlots_ll,contractSpatialSlots_rl]
  rw [jet_selectList p (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l,
    jet_selectList (fun k => ¬p k) (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l]
  congr 2 <;> congr 1 <;> funext s <;> cases s <;> rfl

lemma spatialContractTerm_allSplit {d : ℕ} {S T K : Type u}
    [Fintype S] [Fintype T] [Fintype K] [Nonempty S] [Nonempty T]
    (p : K → Prop) [DecidablePred p]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ}
    {G : (T ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M N : ℝ}
    (hF : TensorEnergy.AllSplitBound (spatialTensor F (selectList p l) y) M)
    (hG : TensorEnergy.AllSplitBound (spatialTensor G (selectList (fun k => ¬p k) l) y) N) :
    TensorEnergy.AllSplitBound (spatialContractTerm p F G l y) (M*N) :=
  ((extendedSpatial_allSplit hF).singleContract (extendedSpatial_allSplit hG)).reindex
    (contractSpatialSlots p)

lemma spatialTensor_singleContract {d : ℕ} {S T K : Type u}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (l : List K) (hl : l.Nodup) (y : Point d) (c : K ⊕ (S ⊕ T) → Fin d) :
    spatialTensor (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a) l y c=
      ∑s ∈ l.toFinset.powerset,spatialContractTerm (fun k => k∈s) F G l y c := by
  unfold spatialTensor TensorEnergy.singleContract
  rw [JetCalculus.jet_sum _ (fun z _ => (hF _).mul (hG _))]
  simp_rw [JetCalculus.jet_mul (hF _) (hG _) _ l hl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact (spatialContractTerm_eq (fun k => k∈s) F G l y c).symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

lemma scoreField_polySmooth {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (c : Empty ⊕ Unit → Fin d) : PolySmooth (scoreField H c) := hH.directional _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ReindexedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace TensorEnergy
lemma Bound.sum_norm {I O J : Type*} [Fintype I] [Fintype O]
    (s : Finset J) {A : J → Matrix O I ℝ} {M : J → ℝ}
    (hM : ∀j∈s,0≤M j) (h : ∀j∈s,Bound (A j) ((M j)^2)) :
    Bound (fun o i => ∑j∈s,A j o i) ((∑j∈s,M j)^2) := by
  have he : (fun o i => ∑j∈s,A j o i)=∑j∈s,A j := by
    ext o i
    exact (Matrix.sum_apply o i s A).symm
  rw [he]
  apply (bound_iff_norm_le (Finset.sum_nonneg hM)).mpr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => (h j hj).norm_le (hM j hj)))

lemma AllSplitBound.sum {S J : Type} [Fintype S] {d : ℕ}
    (s : Finset J) {T : J → (S → Fin d) → ℝ} {M : J → ℝ}
    (hM : ∀j∈s,0≤M j) (h : ∀j∈s,AllSplitBound (T j) (M j)) :
    AllSplitBound (fun a => ∑j∈s,T j a) (∑j∈s,M j) := by
  intro I O _ _ _ _ _ _ e
  exact Bound.sum_norm s hM (fun j hj => h j hj I O e)

end TensorEnergy

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Slice
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory TensorExpression
open scoped Classical BigOperators ENNReal NNReal

lemma spatialTensor_const_mul {S : Type} {d j : ℕ}
    (V : (S → Fin d) → Point d → ℝ) (hV : ∀c,ContDiff ℝ (⊤:ℕ∞) (V c))
    (a : ℝ) (y : Point d) :
    spatialTensor (fun c z => a*V c z) (List.finRange j) y=
      fun c => a*spatialTensor V (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_const_mul (hV _) _ _ a) y

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorEnergy
variable {I J S : Type} [Fintype I] [Fintype J] [Fintype S]

lemma Bound.frobeniusSquared_row {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (hC : 0≤C) :
    ∑i,∑j,(A i j)^2≤Fintype.card I*C := by
  have hb (i : I) : ∑j,(A i j)^2≤C := by
    have hh := h.transpose hC (fun k => if k=i then 1 else 0)
    simpa using hh
  exact (Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp)

lemma AllSplitBound.frobeniusSquared {d : ℕ} {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) [Nonempty I] (e : S ≃ I ⊕ Unit) :
    ∑c,(T c)^2≤d*M^2 := by
  let A : (Unit → Fin d) → (I → Fin d) → ℝ :=
    fun o i => T (fun s => Sum.elim i o (e s))
  have hb : Bound A (M^2) := h I Unit e
  have he : (∑c,(T c)^2)=∑o : Unit → Fin d,∑i : I → Fin d,(A o i)^2 := by
    let ec : ((Unit → Fin d) × (I → Fin d)) ≃ (S → Fin d) :=
      ((Equiv.prodComm _ _).trans (Equiv.sumArrowEquivProdArrow I Unit (Fin d)).symm).trans
        (Equiv.arrowCongr e.symm (Equiv.refl (Fin d)))
    have hh := Equiv.sum_comp ec (fun c => (T c)^2)
    rw [Fintype.sum_prod_type] at hh
    exact hh.symm
  rw [he]
  simpa using hb.frobeniusSquared_row (sq_nonneg M)
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

lemma zeroExtend_out {I J : Type*} (e : I ↪ J) (f : I → ℝ) {j : J} (hj : j∉Set.range e) :
    zeroExtend e f j=0 := Function.extend_apply' _ _ _ hj

lemma zeroExtend_sum {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : I → ℝ) :
    (∑j,zeroExtend e f j)=∑i,f i :=
  (Fintype.sum_of_injective e e.injective f (zeroExtend e f)
    (fun _ hj => zeroExtend_out e f hj) (fun i => (zeroExtend_apply e f i).symm)).symm

lemma zeroExtend_sq {I J : Type*} (e : I ↪ J) (f : I → ℝ) :
    (fun j => (zeroExtend e f j)^2)=zeroExtend e (fun i => (f i)^2) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; norm_num

lemma zeroExtend_mul {I J : Type*} (e : I ↪ J) (f : I → ℝ) (g : J → ℝ) :
    (fun j => zeroExtend e f j*g j)=zeroExtend e (fun i => f i*g (e i)) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; simp

lemma sum_restrict_le {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : J → ℝ)
    (hf : ∀j,0≤f j) : (∑i,f (e i))≤∑j,f j := by
  rw [←Finset.sum_image (f:=f) (g:=(e : I → J)) (by intro i _ j _ h; exact e.injective h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

lemma Bound.zeroExtend {I O I' O' : Type*} [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    {A : O → I → ℝ} {C : ℝ} (hA : Bound A C) (hC : 0≤C)
    (eI : I ↪ I') (eO : O ↪ O') :
    Bound (fun o i => TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o) C := by
  intro v
  have he : (fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i)=
      TensorEnergy.zeroExtend eO (fun o => ∑i,A o i*v (eI i)) := by
    funext o
    by_cases ho : o∈Set.range eO
    · obtain ⟨o,rfl⟩ := ho
      simp only [zeroExtend_apply]
      rw [zeroExtend_mul,zeroExtend_sum]
    · simp only [zeroExtend_out eO _ ho,zero_mul,Finset.sum_const_zero]
  change (∑o,((fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i) o)^2)≤_
  rw [he,zeroExtend_sq,zeroExtend_sum]
  exact (hA (fun i => v (eI i))).trans
    (mul_le_mul_of_nonneg_left (sum_restrict_le eI (fun i => (v i)^2) (fun _ => sq_nonneg _)) hC)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

lemma AllSplitBound.zeroExtend {S : Type} [Fintype S] {d D : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (hT : AllSplitBound T M) (ι : S → Fin d ↪ Fin D) :
    AllSplitBound (TensorEnergy.zeroExtend (slotEmbedding ι) T) M := by
  intro I O _ _ _ _ _ _ e
  let ei := slotEmbedding (fun i => ι (e.symm (.inl i)))
  let eo := slotEmbedding (fun o => ι (e.symm (.inr o)))
  have he (i : I → Fin d) (o : O → Fin d) :
      (fun s => Sum.elim (ei i) (eo o) (e s))=
      slotEmbedding ι (fun s => Sum.elim i o (e s)) := by
    funext s
    rcases h : e s with a|b <;>
      simp only [h,Sum.elim_inl,Sum.elim_inr,ei,eo,slotEmbedding_apply,e.symm_apply_eq.mpr h.symm]
  have hrow (o : O → Fin D) (i : I → Fin D) :
      TensorEnergy.zeroExtend (slotEmbedding ι) T (fun s => Sum.elim i o (e s))=
      TensorEnergy.zeroExtend eo (fun o => TensorEnergy.zeroExtend ei (fun i => T (fun s => Sum.elim i o (e s))) i) o := by
    by_cases hi : i∈Set.range ei
    · obtain ⟨a,rfl⟩ := hi
      by_cases ho : o∈Set.range eo
      · obtain ⟨b,rfl⟩ := ho
        rw [he,zeroExtend_apply,zeroExtend_apply,zeroExtend_apply]
      · rw [zeroExtend_out eo _ ho,zeroExtend_out]
        rintro ⟨c,hc⟩
        apply ho
        refine ⟨fun b => c (e.symm (.inr b)),?_⟩
        funext b
        have hh := congrFun hc (e.symm (.inr b))
        change ι (e.symm (.inr b)) (c (e.symm (.inr b)))=o b
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inr] using hh
    · rw [zeroExtend_out]
      · by_cases ho : o∈Set.range eo
        · obtain ⟨b,rfl⟩ := ho
          rw [zeroExtend_apply,zeroExtend_out ei _ hi]
        · rw [zeroExtend_out eo _ ho]
      · rintro ⟨c,hc⟩
        apply hi
        refine ⟨fun a => c (e.symm (.inl a)),?_⟩
        funext a
        have hh := congrFun hc (e.symm (.inl a))
        change ι (e.symm (.inl a)) (c (e.symm (.inl a)))=i a
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inl] using hh
  have hb := (hT I O e).zeroExtend (sq_nonneg M) ei eo
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ext o i
  exact hrow o i
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ForestTensor
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

lemma arrayTensor_coordinate_expansion {d : ℕ} {S I : Type} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) ((S → Fin d) → ℝ))
    (v : I → Point d) (o : S → Fin d) :
    A v o=∑a : I → Fin d,A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (a i)) o*
      ∏i,inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (a i)) (v i) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : v=fun i => ∑j : Fin d,inner ℝ (b j) (v i) • b j := by
    funext i
    exact (b.sum_repr' (v i)).symm
  conv_lhs => rw [hv]
  rw [A.map_sum]
  simp only [A.map_smul_univ,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma arrayTensor_compAlong {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) ((S → Fin d) → ℝ))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    (a : S ⊕ Fin n → Fin d) :
    arrayTensor (c.compAlongOrderedFinpartition A B) a=
      forestTensor (fun i => Fin (c.partSize i)) (arrayTensor A)
        (fun i q => multilinearTensor (B i) (q ∘ Equiv.sumComm Unit (Fin (c.partSize i))))
        (a ∘ (Equiv.refl S).sumCongr c.equivSigma) := by
  unfold arrayTensor forestTensor
  rw [OrderedFinpartition.compAlongOrderFinpartition_apply,arrayTensor_coordinate_expansion]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

lemma AllSplitBound.array_compAlong {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) ((S → Fin d) → ℝ))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    {M : ℝ} {N : Fin c.length → ℝ}
    (hA : AllSplitBound (arrayTensor A) M)
    (hB : ∀i,AllSplitBound (multilinearTensor (B i)) (N i)) :
    AllSplitBound (arrayTensor (c.compAlongOrderedFinpartition A B)) (M*∏i,N i) := by
  let (i : Fin c.length) : Nonempty (Fin (c.partSize i)) := Fin.pos_iff_nonempty.mp (c.partSize_pos i)
  have hf := hA.forest (fun i => Fin (c.partSize i))
    (fun i => (hB i).reindex (Equiv.sumComm Unit (Fin (c.partSize i))))
  have hh := hf.reindex ((Equiv.refl S).sumCongr c.equivSigma)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  exact arrayTensor_compAlong c A B a

lemma iteratedFDeriv_array_comp_allSplit {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    {f : Point d → Point d} {g : Point d → (S → Fin d) → ℝ} (x : Point d)
    (hf : ContDiffAt ℝ (n:WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (n:WithTop ℕ∞) g (f x))
    (M N : ℕ → ℝ) (hM : ∀k,0≤M k) (hN : ∀k,0≤N k)
    (hG : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g (f x))) (M k))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (N k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i)) := by
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast le_rfl)]
  have hh := AllSplitBound.finite_sum
    (fun c : OrderedFinpartition n => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))
    (fun c : OrderedFinpartition n => (hG c.length c.length_le).array_compAlong c _ _
      (fun i => hF (c.partSize i) (c.partSize_le i)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  simp only [FormalMultilinearSeries.taylorComp,arrayTensor,
    sum_apply,Finset.sum_apply,FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]

lemma spatialTensor_eq_arrayTensor {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) :
    spatialTensor (fun c z => g z c) (List.finRange n) y=
      fun c => arrayTensor (iteratedFDeriv ℝ n g y) (c ∘ Equiv.sumComm S (Fin n)) := by
  funext c
  let L : ((S → Fin d) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (fun s => c (Sum.inr s))
  dsimp [spatialTensor]
  change JetCalculus.jet _ _ (L ∘ g) y=_
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hg),
    L.iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl
lemma AllSplitBound.of_spatialTensor {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) {C : ℝ}
    (h : AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) C) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) C := by
  rw [spatialTensor_eq_arrayTensor hg y] at h
  have hh := h.reindex (Equiv.sumComm (Fin n) S)
  simpa only [Function.comp_def,Equiv.sumComm_apply,Sum.swap_swap] using hh

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma PolySmooth.sq {d : ℕ} {f : Point d → ℝ} (hf : PolySmooth f) : PolySmooth (fun y => (f y)^2) := by
  simpa only [pow_two] using hf.mul hf

lemma spatialSquared_polySmooth {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    PolySmooth (spatialSquared F j) :=
  PolySmooth.sum _ (fun c _ => (spatialTensor_polySmooth F hF _ c).sq)

lemma singleContract_polySmooth {d : ℕ} {S T : Type}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    (a : S ⊕ T → Fin d) :
    PolySmooth (fun y => singleContract (fun c => F c y) (fun c => G c y) a) :=
  PolySmooth.sum _ (fun _z _ => (hF _).mul (hG _))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateProjection
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators
open TensorEnergy

lemma coordinateProjection_basis_in {d D : ℕ} (e : Fin d ↪ Fin D) (i : Fin d) :
    coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ (e i))=
      EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp only [e.injective.eq_iff]

lemma coordinateProjection_basis_out {d D : ℕ} (e : Fin d ↪ Fin D) {i : Fin D}
    (hi : i∉Set.range e) : coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ i)=0 := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,PiLp.zero_apply]
  exact ite_eq_right (fun h => hi ⟨j,h⟩)

lemma slotEmbedding_mem_range {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D) (c : S → Fin D) :
    c∈Set.range (slotEmbedding e) ↔ ∀s,c s∈Set.range (e s) := by
  constructor
  · rintro ⟨a,rfl⟩ s
    exact ⟨a s,rfl⟩
  · intro h
    choose a ha using h
    exact ⟨a,funext ha⟩

namespace JetCalculus
lemma jet_eq_zero_of_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Type*} (v : S → E) (l : List S) (f : E → ℝ) {s : S} (hs : s∈l) (hv : v s=0) :
    jet v l f=fun _ => 0 := by
  induction l with
  | nil => simp at hs
  | cons i l ih =>
    rcases List.mem_cons.mp hs with rfl|hs
    · simp only [jet,hv,dir_zero]
    · rw [jet,ih hs]
      funext x
      simp [dir]
end JetCalculus

lemma arrayCoordinateLift_smooth {S : Type} {d D : ℕ} (e : Fin d ↪ Fin D)
    (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (c : S → Fin D) :
    ContDiff ℝ (⊤:ℕ∞) (arrayCoordinateLift e ι F c) := by
  by_cases hc : c∈Set.range (slotEmbedding ι)
  · obtain ⟨a,rfl⟩ := hc
    change ContDiff ℝ (⊤:ℕ∞) (fun y => TensorEnergy.zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) (slotEmbedding ι a))
    simp only [zeroExtend_apply]
    exact (hF a).comp (coordinateProjection e).contDiff
  · have he : arrayCoordinateLift e ι F c=fun _ => 0 := by
      funext y; exact zeroExtend_out _ _ hc
    rw [he]; exact contDiff_const

lemma spatialTensor_coordinateLift {S J : Type} [Fintype J] {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (l : List J) (hl : ∀j,j∈l) (y : Point D) :
    spatialTensor (arrayCoordinateLift e ι F) l y=
      TensorEnergy.zeroExtend (slotEmbedding (Sum.elim (fun _ : J => e) ι))
        (spatialTensor F l (coordinateProjection e y)) := by
  funext c
  by_cases hc : c∈Set.range (slotEmbedding (Sum.elim (fun _ : J => e) ι))
  · obtain ⟨a,rfl⟩ := hc
    rw [zeroExtend_apply]
    unfold spatialTensor arrayCoordinateLift
    have hc : (fun s => slotEmbedding (Sum.elim (fun _ : J => e) ι) a (.inr s))=
        slotEmbedding ι (fun s => a (.inr s)) := rfl
    rw [hc]
    simp only [zeroExtend_apply,slotEmbedding_apply,Sum.elim_inl]
    have hh := JetCalculus.jet_comp_affine (hF (fun s => a (.inr s))) (coordinateProjection e) 0
      (fun j => EuclideanSpace.basisFun (Fin D) ℝ (e (a (.inl j)))) l
    simp only [add_zero,coordinateProjection_basis_in] at hh
    exact congrFun hh y
  · rw [zeroExtend_out _ _ hc]
    by_cases hs : (fun s => c (.inr s))∈Set.range (slotEmbedding ι)
    · obtain ⟨a,ha⟩ := hs
      have hj : ∃j : J,c (.inl j)∉Set.range e := by
        by_contra! hj
        apply hc
        rw [slotEmbedding_mem_range]
        rintro (j|s)
        · exact hj j
        · exact ⟨a s,congrFun ha s⟩
      obtain ⟨j,hj⟩ := hj
      unfold spatialTensor arrayCoordinateLift
      rw [←ha]
      simp only [zeroExtend_apply]
      have hh := JetCalculus.jet_comp_affine (hF a) (coordinateProjection e) 0
        (fun j => EuclideanSpace.basisFun (Fin D) ℝ (c (.inl j))) l
      simp only [add_zero] at hh
      rw [hh,JetCalculus.jet_eq_zero_of_direction _ l _ (hl j) (coordinateProjection_basis_out e hj)]
    · have he : arrayCoordinateLift e ι F (fun s => c (.inr s))=fun _ => 0 := by
        funext z; exact zeroExtend_out _ _ hs
      change JetCalculus.jet _ l (arrayCoordinateLift e ι F _) y=0
      rw [he,JetCalculus.jet_const]
      split_ifs <;> rfl

lemma AllSplitBound.coordinateLift {S : Type} [Fintype S] {d D j : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) {M : ℝ}
    (hb : ∀x,AllSplitBound (spatialTensor F (List.finRange j) x) M) (y : Point D) :
    AllSplitBound (spatialTensor (arrayCoordinateLift e ι F) (List.finRange j) y) M := by
  rw [spatialTensor_coordinateLift e ι F hF _ (fun k => List.mem_finRange k) y]
  exact (hb _).zeroExtend _
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma productPointEquiv_norm_sq {d e : ℕ} (y : Point (d+e)) :
    ‖y‖^2=‖(productPointEquiv d e y).1‖^2+‖(productPointEquiv d e y).2‖^2 := by
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d ⊕ Fin e => ℝ) (T y)
  simp only [Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type] at hh
  rw [T.norm_map] at hh
  simpa [productPointEquiv,T,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,EuclideanSpace.real_norm_sq_eq] using hh

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SplitBundle
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma partition_array_scale {n : ℕ} (c : OrderedFinpartition n)
    (A B : ℕ → ℝ) (R : ℝ) (w : ℕ) :
    (A c.length/R^(c.length+w))*(∏i,B (c.partSize i)/R^(c.partSize i-1))=
      (A c.length*(∏i,B (c.partSize i)))/R^(n+w) := by
  rw [Finset.prod_div_distrib,←mul_div_mul_comm,Finset.prod_pow_eq_pow_sum,←pow_add]
  have he : c.length+w+(∑i,(c.partSize i-1))=n+w := by
    have := _root_.OAI.OrderedFinpartition.sum_pred_partSize c
    omega
  rw [he]

lemma array_composition_scale {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    {f : Point d → Point d} {g : Point d → (S → Fin d) → ℝ} (x : Point d)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k)
    (R : ℝ) (hR : 0<R) (w : ℕ)
    (hG : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g (f x))) (A k/R^(k+w)))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (B k/R^(k-1))) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      ((∑c : OrderedFinpartition n,A c.length*∏i,B (c.partSize i))/R^(n+w)) := by
  have hh := iteratedFDeriv_array_comp_allSplit x
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (fun k => A k/R^(k+w)) (fun k => B k/R^(k-1))
    (fun k => div_nonneg (hA _) (pow_nonneg hR.le _))
    (fun k => div_nonneg (hB _) (pow_nonneg hR.le _)) hG hF
  simpa only [partition_array_scale,Finset.sum_div] using hh
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetCompactIntegral
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace JetCalculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma jet_compact_integral {f : E × ℝ → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    {s : Set ℝ} (hs : IsCompact s) {ι : Type} (v : ι → E) (l : List ι) (y : E) :
    jet v l (fun y => ∫t in s,f (y,t)) y=
      ∫t in s,jet (fun i => (v i,0)) l f (y,t) := by
  induction l generalizing y with
  | nil => rfl
  | cons k l ih =>
    let J := jet (fun i => (v i,0)) l f
    have hJ : ContDiff ℝ (⊤:ℕ∞) J := smooth_jet hf _ _
    have he : jet v l (fun y => ∫t in s,f (y,t))=fun y => ∫t in s,J (y,t) := funext ih
    change dir (v k) (jet v l (fun y => ∫t in s,f (y,t))) y=_
    rw [he]
    have hd := CompactIntegral.parametric_hasFDerivAt (hJ.of_le (by simp)) hs y
    unfold dir
    rw [hd.fderiv]
    have hI : IntegrableOn (fun t => (fderiv ℝ J (y,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) s :=
      (((hJ.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_comp
        continuous_const).continuousOn.integrableOn_compact hs
    rw [ContinuousLinearMap.integral_apply hI]
    rfl
end JetCalculus

namespace TensorEnergy
lemma AllSplitBound.compact_integral {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    {A : ℝ → (S → Fin d) → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hA : ∀c,Continuous (fun t => A t c)) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈s,AllSplitBound (A t) B) :
    AllSplitBound (fun c => ∫t in s,A t c) (volume.real s*B) := by
  have hc : Continuous A := continuous_pi hA
  have hi : IntegrableOn A s := hc.continuousOn.integrableOn_compact hs
  have he : (fun c => ∫t in s,A t c)=∫t in s,A t := by
    funext c
    exact ((ContinuousLinearMap.proj c : ((S → Fin d) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi)
  rw [he]
  have hbi := (splitBundle (S:=S) (d:=d)).integral_comp_comm hi
  have hbound := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=s)
    (f:=fun t => splitBundle (A t)) hs.measure_lt_top
    (fun t ht => bundle_norm_le hB (hb t ht))
  rw [hbi] at hbound
  exact (allSplitBound_bundle _).mono (norm_nonneg _) (by simpa only [mul_comm] using hbound)

lemma array_iterated_eq_jet {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n g y) c=
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => g z (fun s => c (Sum.inl s))) y := by
  let L : ((S → Fin d) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (fun s => c (Sum.inl s))
  change _=JetCalculus.jet _ _ (L ∘ g) y
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hg),
    L.iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma array_iterated_joint_jet {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) (t : ℝ) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c=
      JetCalculus.jet (fun i => (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)),(0:ℝ)))
        (List.finRange n) (fun z => g z (fun s => c (Sum.inl s))) (y,t) := by
  have hz : ContDiff ℝ (⊤:ℕ∞) (fun z => g (z,t)) := hg.comp (contDiff_id.prodMk contDiff_const)
  rw [array_iterated_eq_jet hz]
  exact JetCalculus.jet_left_slice
    ((ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) _ _ _ _

lemma arrayTensor_compact_integral {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    {s : Set ℝ} (hs : IsCompact s) (y : Point d) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y) c=
      ∫t in s,arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c := by
  rw [array_iterated_eq_jet (CompactIntegral.smooth_parametric hg hs)]
  have he : (fun z => (∫t in s,g (z,t)) (fun s => c (Sum.inl s)))=
      fun z => ∫t in s,g (z,t) (fun s => c (Sum.inl s)) := by
    funext z
    exact ((ContinuousLinearMap.proj (fun s => c (Sum.inl s)) : ((S → Fin d) → ℝ) →L[ℝ] ℝ).integral_comp_comm
      ((hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs)).symm
  have hc : ContDiff ℝ (⊤:ℕ∞) (fun z => g z (fun s => c (Sum.inl s))) :=
    (ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg
  rw [he,JetCalculus.jet_compact_integral hc hs]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (array_iterated_joint_jet hg y t c).symm

lemma compactIntegral_iterated_split {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    {s : Set ℝ} (hs : IsCompact s) (y : Point d) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈s,AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y)) B) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y)) (volume.real s*B) := by
  have hc (c : S ⊕ Fin n → Fin d) : Continuous
      (fun t => arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c) := by
    simp_rw [array_iterated_joint_jet hg]
    exact (JetCalculus.smooth_jet
      ((ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) _ _).continuous.comp
      (continuous_const.prodMk continuous_id)
  have he : arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y)=
      fun c => ∫t in s,arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c :=
    funext (arrayTensor_compact_integral hg hs y)
  rw [he]
  exact AllSplitBound.compact_integral hs hc hB hb
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MatrixArray
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

lemma matrixArray_apply {d : ℕ} (A : Point d →L[ℝ] Point d) (c : Unit ⊕ Unit → Fin d) :
    matrixArray d A c=inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
      (A (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))) := rfl

lemma arrayTensor_jacobian {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) (c : (Unit ⊕ Unit) ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d (fderiv ℝ f z)) y) c=
      multilinearTensor (iteratedFDeriv ℝ (n+1) f y) (c ∘ (jacobianSlots n).symm) := by
  have hd : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  change arrayTensor (iteratedFDeriv ℝ n ((matrixArray d) ∘ fderiv ℝ f) y) c = _
  rw [(matrixArray d).iteratedFDeriv_comp_left hd.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  simp only [arrayTensor,ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply,matrixArray_apply,multilinearTensor,
    jacobianSlots_symm_out,iteratedFDeriv_succ_apply_right,jacobianSlots_symm_last]
  have hv : (Fin.init fun i => EuclideanSpace.basisFun (Fin d) ℝ (c ((jacobianSlots n).symm (Sum.inr i))))=
      (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))) := by
    funext i
    change EuclideanSpace.basisFun (Fin d) ℝ (c ((jacobianSlots n).symm (Sum.inr i.castSucc)))=_
    rw [jacobianSlots_symm_init]
  rw [hv]

lemma AllSplitBound.jacobian {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) {C : ℝ}
    (h : AllSplitBound (multilinearTensor (iteratedFDeriv ℝ (n+1) f y)) C) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d (fderiv ℝ f z)) y)) C := by
  have hh := h.reindex (jacobianSlots n).symm
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext c
  exact arrayTensor_jacobian hf y c
lemma allSplit_jacobian_comp {d n : ℕ} {f g : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k)
    (R : ℝ) (hR : 0<R) (y : Point d)
    (ha : ∀k≤n+1,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k g (f y))) (A k/R^(k-1)))
    (hb : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f y)) (B k/R^(k-1))) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      ((fun z => matrixArray d (fderiv ℝ g z)) ∘ f) y))
      ((∑c : OrderedFinpartition n,A (c.length+1)*∏i,B (c.partSize i))/R^n) := by
  have hj : ContDiff ℝ (⊤:ℕ∞) (fun z => matrixArray d (fderiv ℝ g z)) :=
    (matrixArray d).contDiff.comp (hg.fderiv_right (by simp))
  have hh := array_composition_scale (n:=n) y hf hj (fun k => A (k+1)) B
    (fun _ => hA _) hB R hR 0
    (fun k hk => by
      have h := AllSplitBound.jacobian (n:=k) hg (f y) (ha (k+1) (by omega))
      simpa only [Nat.add_sub_cancel,Nat.add_zero] using h) hb
  simpa only [Nat.add_zero] using hh
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensorArrayBound
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators
open TensorEnergy

lemma spatialTensor_of_arrayBound {d : ℕ} {S K : Type} [Fintype S] [DecidableEq S] [Fintype K]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) {B : ℝ}
    (hb : AllSplitBound (arrayTensor (iteratedFDeriv ℝ (Fintype.card K) g y)) B) :
    AllSplitBound (spatialTensor (fun c z => g z c) l y) B := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hb' : AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange (Fintype.card K)) y) B := by
    rw [spatialTensor_eq_arrayTensor hg y]
    exact hb.reindex (Equiv.sumComm S (Fin (Fintype.card K)))
  have hh := spatialTensor_allSplit_relabel (fun c z => g z c)
    (fun c => (ContinuousLinearMap.proj c : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) (Equiv.refl S) e
    (List.finRange (Fintype.card K)) l hp y B hb'
  simpa only [Function.comp_def,Equiv.refl_apply] using hh

lemma arrayBound_spatialContract {d j : ℕ} {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Nonempty S] [Nonempty T]
    {f : Point d → (S ⊕ Unit → Fin d) → ℝ} {g : Point d → (T ⊕ Unit → Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k) (y : Point d)
    (ha : ∀k≤j,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k f y)) (A k))
    (hb : ∀k≤j,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g y)) (B k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ j
      (fun z => singleContract (f z) (g z)) y))
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)) := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have hfc (c) : ContDiff ℝ (⊤:ℕ∞) (fun z => f z c) :=
    (ContinuousLinearMap.proj c : ((S ⊕ Unit → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hf
  have hgc (c) : ContDiff ℝ (⊤:ℕ∞) (fun z => g z c) :=
    (ContinuousLinearMap.proj c : ((T ⊕ Unit → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg
  have hc : ContDiff ℝ (⊤:ℕ∞) (fun z => singleContract (f z) (g z)) := by
    apply contDiff_pi.mpr
    intro c
    exact ContDiff.sum (fun z _ => (hfc _).mul (hgc _))
  have he := spatialTensor_singleContract (fun c z => f z c) (fun c z => g z c)
    hfc hgc (List.finRange j) (List.nodup_finRange j) y
  have hs : AllSplitBound (spatialTensor (fun c z => singleContract (f z) (g z) c) (List.finRange j) y)
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)) := by
    have he' : spatialTensor (fun c z => singleContract (f z) (g z) c) (List.finRange j) y=
        fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
          spatialContractTerm (fun k => k∈s) (fun c z => f z c) (fun c z => g z c) (List.finRange j) y c := by
      funext c
      have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by
        ext k
        simp
      simpa only [heq] using he c
    rw [he']
    apply AllSplitBound.sum
    · intro s _; exact mul_nonneg (hA _) (hB _)
    · intro s _
      have hn : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
      have hfs := spatialTensor_of_arrayBound (K:=s) (B:=A s.card) hf (selectList (fun k => k∈s) (List.finRange j))
        (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
        (by rw [Fintype.card_coe]; exact ha s.card hn)
      have hgs := spatialTensor_of_arrayBound (K:={k : Fin j // k∉s}) (B:=B (j-s.card)) hg (selectList (fun k => k∉s) (List.finRange j))
        (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
        (by rw [Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin]; exact hb (j-s.card) (Nat.sub_le j s.card))
      exact spatialContractTerm_allSplit (fun k => k∈s) hfs hgs
  rw [spatialTensor_eq_arrayTensor hc y] at hs
  have hh := hs.reindex (Equiv.sumComm (Fin j) (S ⊕ T))
  simpa only [Function.comp_def,Equiv.sumComm_apply,Sum.swap_swap] using hh
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayRelabel
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

lemma arrayTensor_relabel {d n : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T)
    {f : Point d → (S → Fin d) → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d)
    (c : T ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n ((arrayRelabel e) ∘ f) y) c=
      arrayTensor (iteratedFDeriv ℝ n f y) (c ∘ Equiv.sumCongr e (Equiv.refl (Fin n))) := by
  rw [(arrayRelabel e).iteratedFDeriv_comp_left hf.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma AllSplitBound.array_relabel {d n : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T)
    {f : Point d → (S → Fin d) → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) {B : ℝ}
    (h : AllSplitBound (arrayTensor (iteratedFDeriv ℝ n f y)) B) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n ((arrayRelabel e) ∘ f) y)) B := by
  have hh := h.reindex (Equiv.sumCongr e (Equiv.refl (Fin n)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext c
  exact arrayTensor_relabel e hf y c

lemma matrixArray_comp {d : ℕ} (A B : Point d →L[ℝ] Point d) :
    matrixArray d (A.comp B)=singleContract (matrixArray d A)
      (arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d B)) := by
  funext c
  let v := B (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
  have he := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hh := congrArg (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) (A z)) he
  simpa only [map_sum,map_smul,inner_sum,real_inner_smul_right,
    OrthonormalBasis.repr_apply_apply,real_inner_comm,singleContract,
    matrixArray_apply,arrayRelabel,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,Function.comp_apply,Equiv.sumComm_apply,
    Sum.swap_inl,Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,mul_comm,v,ContinuousLinearMap.comp_apply] using hh.symm

lemma matrixComposition_split {d n : ℕ} {f g : Point d → Point d →L[ℝ] Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k) (y : Point d)
    (ha : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k ((matrixArray d) ∘ f) y)) (A k))
    (hb : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k ((matrixArray d) ∘ g) y)) (B k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d ((f z).comp (g z))) y))
      (∑s∈(Finset.univ : Finset (Fin n)).powerset,A s.card*B (n-s.card)) := by
  have hfg := (matrixArray d).contDiff.comp hf
  have hgg := (matrixArray d).contDiff.comp hg
  have hh := LogConcaveSampling.arrayBound_spatialContract hfg
    ((arrayRelabel (Equiv.sumComm Unit Unit)).contDiff.comp hgg) A B hA hB y ha
    (fun k hk => AllSplitBound.array_relabel (Equiv.sumComm Unit Unit) hgg y (hb k hk))
  have he : (fun z => matrixArray d ((f z).comp (g z)))=
      fun z => singleContract (matrixArray d (f z))
        (arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d (g z))) :=
    funext (fun z => matrixArray_comp (f z) (g z))
  rw [he]
  exact hh
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators
open TensorEnergy

lemma transportMajorant_nonneg (n : ℕ) : 0≤transportMajorant n :=
  (probabilityTransport_iterated_split n).choose_spec.1

lemma probabilityTransport_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      fun z => spatialTransport hF x hr hl hT0 hT1 s (t,z) :=
    funext (fun z => (spatialTransport_eq hF x hr hl hT0 hT1 s t z).symm)
  rw [he]
  exact (spatialTransport_smooth hF x hr hl hT0 hT1 s).comp (contDiff_const.prodMk contDiff_id)

lemma transportMajorant_bound {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n
      (probabilityTransport hF x hr.le hl hT0 hT1 s t) y)) (transportMajorant n/R^(n-1)) :=
  (probabilityTransport_iterated_split n).choose_spec.2 d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 s t y

lemma jacobianMajorant_nonneg (n : ℕ) : 0≤jacobianMajorant n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (transportMajorant_nonneg _)
    (Finset.prod_nonneg (fun _ _ => transportMajorant_nonneg _)))

lemma terminalJacobian_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (terminalJacobian hF x hr hl hT0 hT1 (t,z))) y))
      (jacobianMajorant n/R^n) := by
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩
  have hf : ContDiff ℝ (⊤:ℕ∞) f := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have hg : ContDiff ℝ (⊤:ℕ∞) g := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have hh := allSplit_jacobian_comp (n:=n) hf hg transportMajorant transportMajorant
    transportMajorant_nonneg transportMajorant_nonneg R hR y
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ (f y))
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ y)
  have he : (fun z => matrixArray d (terminalJacobian hF x hr hl hT0 hT1 (t,z)))=
      (fun z => matrixArray d (fderiv ℝ g z)) ∘ f := by
    funext z
    rw [terminalJacobian_eq,terminalBackward_eq]
    rfl
  rw [he]
  simpa only [Nat.add_zero,jacobianMajorant] using hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma matrixArray_firstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L ρ : ℝ)
    (y : Point d) (c : Unit ⊕ Unit → Fin d) :
    matrixArray d (conditionalFirstJet F x r L (ρ,y)) c=
      conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) L
        (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) [()] := by
  simp only [matrixArray_apply,conditionalFirstJet,sum_apply,
    smul_apply,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,inner_sum,innerSL_apply_apply]
  simp only [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma normalizedMatrix_eq_firstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L ρ : ℝ)
    (y : Point d) (c : Unit ⊕ Unit → Fin d) :
    L*normalizedTensor F x r ρ L y (Sum.elim (fun _ => true) (fun _ => false))
      [Sum.inr (),Sum.inl ()] c=matrixArray d (conditionalFirstJet F x r L (ρ,y)) c := by
  rw [matrixArray_firstJet]
  have hi : conditionalSlotEmbedding d (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) c
      (Sum.inr ())=Sum.inl (c (Sum.inr ())) := rfl
  have ho : conditionalSlotEmbedding d (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) c
      (Sum.inl ())=Sum.inr (c (Sum.inl ())) := rfl
  simp only [normalizedTensor,conditionalU,Fintype.card_sum,Fintype.card_unit,
    Nat.add_sub_cancel,pow_one,List.length_singleton,JetCalculus.jet,hi,ho]
  rw [←jointPosition_basis,←jointField_basis]
  ring

lemma normalizedMatrix_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z c => normalizedTensor F x r ρ ((lam:ℝ)*r) z
        (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) [Sum.inr (),Sum.inl ()] c) y))
      (normalizedTensorMajorant (n+2) (1-ρ^2)) := by
  let mask : Unit ⊕ Unit → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let l : List (Unit ⊕ Unit) := [Sum.inr (),Sum.inl ()]
  let g : Point d → (Unit ⊕ Unit → Fin d) → ℝ :=
    fun z c => normalizedTensor F x r ρ ((lam:ℝ)*r) z mask l c
  have hg : ContDiff ℝ (⊤:ℕ∞) g := contDiff_pi.mpr (fun c =>
    normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 mask l (by simp [l]) c)
  have hN : l.Nodup := by simp [l]
  have hall : ∀s,s∈l := by rintro (u|u) <;> cases u <;> simp [l]
  have hb := normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y mask l
    (by simp [l]) hN hall (List.finRange n) (List.nodup_finRange _) (by simp)
  change AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) _ at hb
  have hh := AllSplitBound.of_spatialTensor hg y hb
  simpa only [Fintype.card_fin,Fintype.card_sum,Fintype.card_unit] using hh

lemma conditionalFirstJet_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,z))) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+2) 1/R^n) := by
  let g : Point d → (Unit ⊕ Unit → Fin d) → ℝ := fun z c =>
    normalizedTensor F x r ρ ((lam:ℝ)*r) z (Sum.elim (fun _ => true) (fun _ => false))
      [Sum.inr (),Sum.inl ()] c
  have hg : ContDiff ℝ (⊤:ℕ∞) g := contDiff_pi.mpr (fun c =>
    normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 _ _ (by simp) c)
  have hbase := normalizedMatrix_iterated_split (n:=n) hF x hr hlam hl hρ0 hρ1 y
  have hscale := (hbase.mono (normalizedTensorMajorant_nonneg _ _)
    (by simpa only [Nat.add_sub_cancel] using normalizedTensorMajorant_scale (n:=n+2) hR ha)).const_mul
    ((lam:ℝ)*r)
  have he : (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,z)))=
      fun z => ((lam:ℝ)*r) • g z := by
    funext z c
    exact (normalizedMatrix_eq_firstJet F x r ((lam:ℝ)*r) ρ z c).symm
  rw [he,iteratedFDeriv_const_smul_apply' (hg.contDiffAt.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  change AllSplitBound (fun a => ((lam:ℝ)*r) * arrayTensor (iteratedFDeriv ℝ n g y) a) _
  simpa only [mul_div_assoc,g] using hscale
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ComposedJetMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical NNReal BigOperators
open TensorEnergy

lemma composedJetMajorant_nonneg (n : ℕ) : 0 ≤ composedJetMajorant n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (normalizedTensorMajorant_nonneg _ _)
    (Finset.prod_nonneg (fun _ _ => transportMajorant_nonneg _)))

lemma backwardFirstJet_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r)
        (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z)))) y))
      (((lam:ℝ)*r)*composedJetMajorant n/R^n) := by
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z))
  have hf : ContDiff ℝ (⊤:ℕ∞) f := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have ht2 : (t:ℝ)^2<1 := by nlinarith [t.2.1,t.2.2]
  have hg0 : ContDiff ℝ (⊤:ℕ∞) (fun z => conditionalFirstJet F x r ((lam:ℝ)*r) (t,z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (conditionalFirstJet_smooth hF x hr hlam hl ((t:ℝ),z) ht2).comp z
      (contDiffAt_const.prodMk contDiffAt_id)
  have hg : ContDiff ℝ (⊤:ℕ∞) g := (matrixArray d).contDiff.comp hg0
  have htR : R^2≤1-(t:ℝ)^2 := by nlinarith [t.2.1,t.2.2]
  have hh := array_composition_scale (n:=n) y hf hg
    (fun k => ((lam:ℝ)*r)*normalizedTensorMajorant (k+2) 1) transportMajorant
    (fun k => mul_nonneg (mul_nonneg lam.2 hr.le) (normalizedTensorMajorant_nonneg _ _))
    transportMajorant_nonneg R hR 0
    (fun order _ => by simpa only [Nat.add_zero] using
      conditionalFirstJet_iterated_split (n:=order) hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) hR htR (f y))
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ y)
  have he : (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r)
        (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z))))=g ∘ f := by
    funext z
    rw [terminalBackward_eq]
    rfl
  rw [he]
  simpa only [Nat.add_zero,composedJetMajorant,Finset.mul_sum,mul_assoc] using hh

lemma kernelMajorant_nonneg (n : ℕ) : 0≤kernelMajorant n :=
  Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (jacobianMajorant_nonneg _) (composedJetMajorant_nonneg _))

lemma steinIntegrand_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (steinIntegrand hF x hr hl hT0 hT1 (t,z))) y))
      (((lam:ℝ)*r)*kernelMajorant n/R^n) := by
  have hf : ContDiff ℝ (⊤:ℕ∞) (fun z => terminalJacobian hF x hr hl hT0 hT1 (t,z)) :=
    (terminalJacobian_smooth hF x hr hl hT0 hT1).comp
    (contDiff_const.prodMk (contDiff_id (E:=Point d)))
  have hg : ContDiff ℝ (⊤:ℕ∞) (fun z => conditionalFirstJet F x r ((lam:ℝ)*r)
      (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    apply (conditionalFirstJet_smooth hF x hr hlam hl _ (by nlinarith [t.2.1,t.2.2])).comp z
    exact contDiffAt_const.prodMk
      (((terminalBackward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
  have hh := matrixComposition_split (n:=n) hf hg
    (fun k => jacobianMajorant k/R^k) (fun k => ((lam:ℝ)*r)*composedJetMajorant k/R^k)
    (fun k => div_nonneg (jacobianMajorant_nonneg _) (pow_nonneg hR.le _))
    (fun k => div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (composedJetMajorant_nonneg _)) (pow_nonneg hR.le _)) y
    (fun _ _ => terminalJacobian_iterated_split hF x hr hlam hl hR hRT hT0 hT1 t y)
    (fun _ _ => backwardFirstJet_iterated_split hF x hr hlam hl hR hRT hT0 hT1 t y)
  have he (s : Finset (Fin n)) :
      (jacobianMajorant s.card/R^s.card)*(((lam:ℝ)*r)*composedJetMajorant (n-s.card)/R^(n-s.card))=
        ((lam:ℝ)*r)*(jacobianMajorant s.card*composedJetMajorant (n-s.card))/R^n := by
    rw [div_mul_div_comm,←pow_add,Nat.add_sub_of_le ((Finset.card_le_univ s).trans_eq (Fintype.card_fin n))]
    ring
  simp_rw [he] at hh
  simpa only [steinIntegrand,smoothTimeClip_eq hT0 hT1 t.2,kernelMajorant,
    ←Finset.sum_div,←Finset.mul_sum] using hh
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MatrixArrayAdjoint
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Classical NNReal BigOperators RealInnerProductSpace
open TensorEnergy

lemma matrixArray_adjoint {d : ℕ} (A : Point d →L[ℝ] Point d) :
    matrixArray d A.adjoint=arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d A) := by
  funext c
  change inner ℝ _ (A.adjoint _)=inner ℝ _ (A _)
  rw [ContinuousLinearMap.adjoint_inner_right,real_inner_comm]
  rfl

theorem centeringKernel_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (centeringKernel hF x hr hl hT0 hT1 z)) y))
      (((lam:ℝ)*r)*kernelMajorant n/R^n) := by
  let : CompleteSpace (Point d →L[ℝ] Point d) := ContinuousLinearMap.instCompleteSpace
  let g : Point d × ℝ → (Unit ⊕ Unit → Fin d) → ℝ :=
    fun p => matrixArray d (steinIntegrand hF x hr hl hT0 hT1 (p.2,p.1))
  have hg : ContDiff ℝ (⊤:ℕ∞) g := (matrixArray d).contDiff.comp
    ((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).comp (contDiff_snd.prodMk contDiff_fst))
  have hB : 0≤((lam:ℝ)*r)*kernelMajorant n/R^n := by
    exact div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _)
  have hh := compactIntegral_iterated_split (n:=n) hg (s:=Icc (0:ℝ) T) isCompact_Icc y hB
    (fun t ht => steinIntegrand_iterated_split hF x hr hlam hl hR hRT hT0 hT1 ⟨t,ht⟩ y)
  have hvol : volume.real (Icc (0:ℝ) T)=T := by
    simp only [Measure.real,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT0]
  rw [hvol] at hh
  have hb := hh.mono (mul_nonneg hT0 hB) (mul_le_of_le_one_left hB hT1.le)
  have hh' := AllSplitBound.array_relabel (Equiv.sumComm Unit Unit)
    (CompactIntegral.smooth_parametric hg isCompact_Icc) y hb
  have he : (fun z => matrixArray d (centeringKernel hF x hr hl hT0 hT1 z))=
      (arrayRelabel (Equiv.sumComm Unit Unit)) ∘ (fun z => ∫t in Icc (0:ℝ) T,g (z,t)) := by
    funext z
    rw [centeringKernel,matrixArray_adjoint]
    congr 1
    exact ((matrixArray d).integral_comp_comm
      (((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc)).symm
  rw [he]
  exact hh'
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayComponentPolySmooth
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma arrayComponent_polySmooth {d : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (hS : 2≤Fintype.card S) {g : Point d → (S → Fin d) → ℝ}
    (hg : ContDiff ℝ (⊤:ℕ∞) g) (M : ℕ → ℝ) (hM : ∀n,0≤M n)
    (hB : ∀n y,AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) (M n))
    (c : S → Fin d) : PolySmooth (fun y => g y c) := by
  apply PolySmooth.of_basis_growth ((ContinuousLinearMap.proj c).contDiff.comp hg)
  intro l
  apply growth_of_bounded (hM l.length)
  intro y
  have hh := (hB l.length y).reindex (Equiv.sumComm S (Fin l.length))
  rw [←spatialTensor_eq_arrayTensor hg y] at hh
  have hb := hh.entry_le (hM _) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (Sum.elim l.get c)
  change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ l.get)
    (List.finRange l.length) (fun y => g y c) y|≤_ at hb
  rw [←JetCalculus.jet_map,List.map_get_finRange] at hb
  exact hb

lemma centeringKernel_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hT0 : 0≤T) (hT1 : T<1) (c : Unit ⊕ Unit → Fin d) :
    PolySmooth (fun y => matrixArray d (centeringKernel hF x hr hl hT0 hT1 y) c) := by
  let R := Real.sqrt (1-T^2)
  have hR : 0<R := Real.sqrt_pos.mpr (by nlinarith)
  have hRT : R^2≤1-T^2 := (Real.sq_sqrt (by nlinarith)).le
  exact arrayComponent_polySmooth (by simp)
    ((matrixArray d).contDiff.comp (centeringKernel_smooth hF x hr hlam hl hT0 hT1))
    (fun n => ((lam:ℝ)*r)*kernelMajorant n/R^n)
    (fun n => div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _))
    (fun _ y => centeringKernel_iterated_split hF x hr hlam hl hR hRT hT0 hT1 y) c

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_CompLinear
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma Appell.HasGrowth.comp_linear {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z]
    {f : F → Z} (hf : Appell.HasGrowth f) (L : E →L[ℝ] F) :
    Appell.HasGrowth (fun x => f (L x)) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  refine ⟨C*(1+‖L‖^n),by positivity,n,fun x => (hf (L x)).trans ?_⟩
  have hp : ‖L x‖^n≤‖L‖^n*‖x‖^n := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) n
  have hLn := pow_nonneg (norm_nonneg L) n
  have hxn := pow_nonneg (norm_nonneg x) n
  nlinarith [mul_le_mul_of_nonneg_left hp hC,mul_nonneg hC hLn,mul_nonneg hC hxn]

lemma PolySmooth.comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : PolySmooth f) (L : Point d →L[ℝ] Point e) : PolySmooth (fun x => f (L x)) := by
  refine ⟨hf.smooth.comp L.contDiff,fun l => ?_⟩
  have he := JetCalculus.jet_comp_affine hf.smooth L 0 id l
  simp only [add_zero,id_eq] at he
  rw [he]
  have hh := hf.growth (l.map L)
  rw [JetCalculus.jet_map] at hh
  exact Appell.HasGrowth.comp_linear hh L

lemma productPotential_polySmooth {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) : PolySmooth (productPotential H G) :=
  (hH.comp_linear ((ContinuousLinearMap.fst ℝ (Point d) (Point e)).comp
    (productPointEquiv d e).toContinuousLinearMap)).add
    (hG.comp_linear ((ContinuousLinearMap.snd ℝ (Point d) (Point e)).comp
      (productPointEquiv d e).toContinuousLinearMap))

lemma gaussianPotential_polySmooth (d : ℕ) : PolySmooth (fun y : Point d => ‖y‖^2/2) := by
  have h (i : Fin d) : PolySmooth (fun y : Point d => y i) := PolySmooth.linear (PiLp.proj 2 _ i)
  have hs := PolySmooth.sum Finset.univ (fun i _ => (h i).mul (h i))
  have hh := (PolySmooth.const (1/2)).mul hs
  have he : (fun y : Point d => ‖y‖^2/2)=(fun y : Point d => (1/2 : ℝ)*(∑i,y i*y i)) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
    ring
  rw [he]
  exact hh

lemma productPotential_lowerTail {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : HasGaussianLowerTail H) (hG : HasGaussianLowerTail G) :
    HasGaussianLowerTail (productPotential H G) := by
  obtain ⟨a,ha,A,hA⟩ := hH
  obtain ⟨b,hb,B,hB⟩ := hG
  refine ⟨min a b,lt_min ha hb,A+B,fun y => ?_⟩
  rw [productPointEquiv_norm_sq]
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖(productPointEquiv d e y).1‖)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖(productPointEquiv d e y).2‖)
  have h₃ := hA (productPointEquiv d e y).1
  have h₄ := hB (productPointEquiv d e y).2
  dsimp [productPotential]
  nlinarith

lemma gaussianPotential_lowerTail (d : ℕ) : HasGaussianLowerTail (fun y : Point d => ‖y‖^2/2) := by
  exact ⟨1/2,by norm_num,0,fun _ => by linarith⟩
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_FinsetSumSum
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma tensorAdjoint_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (a : S → Fin d) : PolySmooth
      (tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => F (Sum.elim a (fun _ => z)))) :=
  hH.tensorAdjoint (fun _ => hF _) _

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open TensorEnergy
open scoped Classical

lemma spatialTensor_finRange_of_arrayBound {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) {B : ℝ}
    (hb : AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) B) :
    AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) B := by
  rw [spatialTensor_eq_arrayTensor hg y]
  exact hb.reindex (Equiv.sumComm S (Fin n))
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorGrad
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma tensorGrad_polySmooth {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S ⊕ Unit → Fin d) : PolySmooth (tensorGrad F c) :=
  (hF _).directional _

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma lieInside_polySmooth {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (c : S ⊕ Unit → Fin d) : PolySmooth (lieInside A F c) :=
  singleContract_polySmooth A (tensorGrad F) hA (tensorGrad_polySmooth F hF) _

lemma tensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (c : S → Fin d) : PolySmooth (tensorLie H A F c) :=
  tensorAdjoint_polySmooth hH (lieInside A F) (lieInside_polySmooth A F hA hF) c

lemma productEnergyBudget_nonneg {C E : ℕ → ℝ} (hE : ∀j,0 ≤ E j) (j : ℕ) :
    0 ≤ productEnergyBudget C E j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hE _)))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_ProductEnergyBudgetScaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma adjointEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀j,0 ≤ B j) (j : ℕ) : 0 ≤ adjointEnergyBudget K C B j := by
  unfold adjointEnergyBudget
  apply mul_nonneg (by norm_num)
  apply add_nonneg (add_nonneg (hB _) (mul_nonneg hK (hB _)))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hB _)))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IterTensorLie
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal BigOperators
open TensorEnergy

lemma iterEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C D : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀k,0 ≤ B k) (n j : ℕ) : 0 ≤ iterEnergyBudget K C D B n j := by
  induction n generalizing j with
  | zero => exact hB j
  | succ n ih => exact adjointEnergyBudget_nonneg hK D (fun k => productEnergyBudget_nonneg ih k) j

lemma iterTensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (n : ℕ) (c : S → Fin d) :
    PolySmooth (iterTensorLie H A F n c) := by
  induction n generalizing c with
  | zero => exact hF c
  | succ n ih => exact tensorLie_polySmooth hH A _ hA ih c

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma adjointCoordinate_sum {d : ℕ} {ι : Type*} [Fintype ι] (H : Point d → ℝ)
    (v : Point d) (f : ι → Point d → ℝ) (hf : ∀i,Differentiable ℝ (f i)) :
    adjointCoordinate H v (fun y => ∑i,f i y)=fun y => ∑i,adjointCoordinate H v (f i) y := by
  unfold adjointCoordinate
  rw [directional_sum _ (fun i _ => hf i)]
  funext y
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.mul_sum]

lemma adjointCoordinate_mul {d : ℕ} (H : Point d → ℝ) (v : Point d)
    {f g : Point d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    adjointCoordinate H v (fun y => f y*g y)=fun y =>
      adjointCoordinate H v f y*g y-f y*directional v g y := by
  unfold adjointCoordinate
  rw [directional_mul hf hg]
  funext y
  ring

lemma tensorLie_eq_directional {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,ContDiff ℝ (⊤:ℕ∞) (A c)) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y) (c : S → Fin d) (y : Point d) :
    tensorLie H A F c y=directional (skewLieField H A y) (F c) y := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hess : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
      directional (b i) (directional (b z) (F c)) y)=0 := by
    have he : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y)=
        -(∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hsk i z y,directional_commute (hF c) (b i) (b z)]
      ring
    linarith
  have hin (i : Fin d) : lieInside A F (Sum.elim c (fun _ => i))=
      fun y => ∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y := rfl
  have hadj (i : Fin d) : adjointCoordinate H (b i)
      (lieInside A F (Sum.elim c (fun _ => i))) y=
      ∑z : Fin d,(adjointCoordinate H (b i) (A (Sum.elim (fun _ => i) (fun _ => z))) y*
        directional (b z) (F c) y-A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
    rw [hin i,adjointCoordinate_sum H (b i) (fun z y => A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y) (fun z =>
      ((hA (Sum.elim (fun _ => i) (fun _ => z))).differentiable (by simp)).mul ((directional_smooth (hF c) (b z)).differentiable (by simp)))]
    apply Finset.sum_congr rfl
    intro z _
    exact congrFun (adjointCoordinate_mul H (b i) ((hA _).differentiable (by simp))
      ((directional_smooth (hF c) (b z)).differentiable (by simp))) y
  unfold tensorLie tensorAdjoint
  change (∑i : Fin d,adjointCoordinate H (b i) (lieInside A F (Sum.elim c (fun _ => i))) y)=_
  simp_rw [hadj]
  simp only [Finset.sum_sub_distrib]
  rw [hess,sub_zero,Finset.sum_comm]
  simp only [directional,skewLieField,map_sum,map_smul,smul_eq_mul,Finset.sum_mul]
  rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma spatialEnergy_from_split {d j : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) [IsProbabilityMeasure (gibbs H)]
    (F : (Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    {M : ℝ} (hj : 0<j) (hb : ∀y,AllSplitBound (spatialTensor F (List.finRange j) y) M) :
    spatialEnergy F j (gibbs H) ≤ d*M^2 := by
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  have hh (y : Point d) : spatialSquared F j y≤d*M^2 :=
    (hb y).frobeniusSquared (Equiv.refl (Fin j ⊕ Unit))
  have hi := (spatialSquared_polySmooth F hF j).integrable hH ht
  exact (integral_mono hi (integrable_const _) hh).trans_eq (by simp)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorVector
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma tensorVector_contDiff {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) :
    ContDiff ℝ (⊤:ℕ∞) (tensorVector F) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hF)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma coordinateProjection_left {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (leftCoordinates d e) y=(productPointEquiv d e y).1 := by
  ext i
  rfl
lemma coordinateProjection_right {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (rightCoordinates d e) y=(productPointEquiv d e y).2 := by
  ext i
  rfl

lemma productPointEquiv_basis_left {d e : ℕ} (i : Fin d) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))=
      (EuclideanSpace.basisFun (Fin d) ℝ i,0) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    exact coordinateProjection_basis_in (leftCoordinates d e) i
  · rw [←coordinateProjection_right]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [rightCoordinates] at hh
    omega
lemma productPointEquiv_basis_right {d e : ℕ} (i : Fin e) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))=
      (0,EuclideanSpace.basisFun (Fin e) ℝ i) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [leftCoordinates] at hh
    omega
  · rw [←coordinateProjection_right]
    exact coordinateProjection_basis_in (rightCoordinates d e) i

lemma directional_comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : Differentiable ℝ f) (L : Point d →L[ℝ] Point e) (v y : Point d) :
    directional v (fun z => f (L z)) y=directional (L v) f (L y) := by
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v)
    ((hf (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv

lemma productPotential_directional_left {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin d) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin d) ℝ i) H (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_left (e:=e) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,L,coordinateProjection_left]

lemma productPotential_directional_right {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin e) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_right (d:=d) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,R,coordinateProjection_right]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma jointSkew_skew {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (i z : Fin (d+d)) (y : Point (d+d)) :
    jointSkew K s (Sum.elim (fun _ => i) (fun _ => z)) y=
      -jointSkew K s (Sum.elim (fun _ => z) (fun _ => i)) y := by
  induction i using Fin.addCases <;> induction z using Fin.addCases <;>
    simp only [jointSkew,jointSkewEntry,Sum.elim_inl,Sum.elim_inr,Fin.addCases_left,Fin.addCases_right,mul_zero,mul_neg,neg_neg,neg_zero]

lemma jointSkew_polySmooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀i j,PolySmooth (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j)))) (s : ℝ) (c : Unit ⊕ Unit → Fin (d+d)) :
    PolySmooth (jointSkew K s c) := by
  suffices h : ∀i z : Fin (d+d),PolySmooth (jointSkewEntry K s i z) from h _ _
  intro i z
  let L := (ContinuousLinearMap.fst ℝ (Point d) (Point d)).comp
    (productPointEquiv d d).toContinuousLinearMap
  have hL (y : Point (d+d)) : L y=(productPointEquiv d d y).1 := rfl
  change PolySmooth (fun y => jointSkewEntry K s i z y)
  induction i using Fin.addCases <;> induction z using Fin.addCases
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul ((hK _ _).comp_linear L)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul (((hK _ _).comp_linear L).neg)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))

lemma directional_gaussianPotential {d : ℕ} (v y : Point d) :
    directional v (fun z : Point d => ‖z‖^2/2) y=inner ℝ y v := by
  have hd := ((hasFDerivAt_id y).norm_sq.const_mul (1/2 : ℝ)).fderiv
  change (fderiv ℝ (fun z : Point d => ‖z‖^2/2) y) v=_
  have he : (fun z : Point d => ‖z‖^2/2)=(fun z : Point d => (1/2:ℝ)*‖z‖^2) := by funext z; ring
  dsimp only [id_eq] at hd
  rw [he,hd]
  simp

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma eq_pairLabels {D : ℕ} (c : Unit ⊕ Unit → Fin D) : c=pairLabels (c (.inl ())) (c (.inr ())) := by
  funext a
  rcases a with ⟨⟩|⟨⟩ <;> rfl

lemma pair_lift_in {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin d) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F
      (pairLabels (e₁ i) (e₂ j)) y=F (pairLabels i j) (coordinateProjection e y) := by
  have he : pairLabels (e₁ i) (e₂ j)=slotEmbedding (Sum.elim (fun _ => e₁) (fun _ => e₂)) (pairLabels i j) := by
    funext a; rcases a with ⟨⟩|⟨⟩ <;> rfl
  rw [he]
  exact zeroExtend_apply _ _ _

lemma pair_lift_out_left {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hi ⟨c (.inl ()),congrFun hc (.inl ())⟩
lemma pair_lift_out_right {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hj : j∉Set.range e₂) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hj ⟨c (.inr ()),congrFun hc (.inr ())⟩

lemma left_not_right {d e : ℕ} (i : Fin d) : i.castAdd e∉Set.range (rightCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [rightCoordinates] at hh
  omega
lemma right_not_left {d e : ℕ} (i : Fin e) : i.natAdd d∉Set.range (leftCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [leftCoordinates] at hh
  omega

lemma jointSkew_eq_lifts {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) :
    jointSkew K s=fun c y =>
      s⁻¹*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d))
        (fun c y => matrixArray d (K y) (c ∘ Equiv.sumComm Unit Unit)) c y+
      (-s⁻¹)*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d))
        (fun c y => matrixArray d (K y) c) c y := by
  funext c y
  rw [eq_pairLabels c]
  generalize c (.inl ())=i,c (.inr ())=j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rw [pair_lift_out_right _ _ _ _ _ _ (left_not_right _),
      pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,mul_zero,add_zero]
  · change _=s⁻¹*arrayCoordinateLift _ _ _
      (pairLabels (leftCoordinates d d _) (rightCoordinates d d _)) y+_
    rw [pair_lift_in,pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,add_zero,coordinateProjection_left]
    rfl
  · change _=_+(-s⁻¹)*arrayCoordinateLift _ _ _
      (pairLabels (rightCoordinates d d _) (leftCoordinates d d _)) y
    rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),pair_lift_in]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,zero_add,coordinateProjection_left,mul_neg,neg_mul]
    rfl
  · rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),
      pair_lift_out_right _ _ _ _ _ _ (right_not_left _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_right,mul_zero,add_zero]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma spatialTensor_add {S J : Type} {d : ℕ}
    (F G : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c)) (l : List J) (y : Point d) :
    spatialTensor (fun c z => F c z+G c z) l y=
      fun c => spatialTensor F l y c+spatialTensor G l y c := by
  funext c
  exact congrFun (JetCalculus.jet_add (hF _) (hG _) _ l) y

theorem jointSkew_spatial_bound {d n : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀c,ContDiff ℝ (⊤:ℕ∞) (fun y => matrixArray d (K y) c))
    {M : ℝ} (hM : 0≤M)
    (hb : ∀y,AllSplitBound (spatialTensor (fun c z => matrixArray d (K z) c) (List.finRange n) y) M)
    (s : ℝ) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (jointSkew K s) (List.finRange n) y) (2*|s⁻¹| *M) := by
  let F := fun c z => matrixArray d (K z) c
  let G := fun c => F (c ∘ Equiv.sumComm Unit Unit)
  have hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c) := fun _ => hK _
  have hbg (z : Point d) : AllSplitBound (spatialTensor G (List.finRange n) z) M := by
    apply spatialTensor_allSplit_relabel F hK (Equiv.sumComm Unit Unit) (Equiv.refl (Fin n))
      (List.finRange n) (List.finRange n) _ z M (hb z)
    simp
  let L := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d)) G
  let R := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d)) F
  have hL : ∀c,ContDiff ℝ (⊤:ℕ∞) (L c) := arrayCoordinateLift_smooth _ _ _ hG
  have hR : ∀c,ContDiff ℝ (⊤:ℕ∞) (R c) := arrayCoordinateLift_smooth _ _ _ hK
  have hbL : AllSplitBound (spatialTensor L (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hG hbg y
  have hbR : AllSplitBound (spatialTensor R (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hK hb y
  have he : jointSkew K s=fun c z => s⁻¹*L c z+(-s⁻¹)*R c z := jointSkew_eq_lifts K s
  rw [he,spatialTensor_add _ _ (fun c => contDiff_const.mul (hL c))
    (fun c => contDiff_const.mul (hR c)),spatialTensor_const_mul L hL,
    spatialTensor_const_mul R hR]
  have hh := (hbL.abs_const_mul s⁻¹).add (hbR.abs_const_mul (-s⁻¹))
    (mul_nonneg (abs_nonneg _) hM) (mul_nonneg (abs_nonneg _) hM)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_neg]
  ring

theorem centering_jointSkew_spatial_bound {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s : ℝ) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
      (List.finRange n) y) (2*|s⁻¹| *(((lam:ℝ)*r)*kernelMajorant n/R^n)) := by
  apply jointSkew_spatial_bound
    (fun c => (centeringKernel_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)
    (div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _))
  intro z
  exact spatialTensor_finRange_of_arrayBound
    ((matrixArray d).contDiff.comp (centeringKernel_smooth hF x hr hlam hl hT0 hT1)) z
    (centeringKernel_iterated_split (n:=n) hF x hr hlam hl hR hRT hT0 hT1 z)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators
open TensorEnergy

lemma scoreLabels_eq {d : ℕ} (c : Empty ⊕ Unit → Fin d) :
    c=fun _ => c (.inr ()) := by
  funext a
  rcases a with e|⟨⟩
  · exact e.elim
  · rfl

lemma scalarSlot_lift_in {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin d) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => e₁ i) y=
      F (fun _ => i) (coordinateProjection e y) := by
  exact zeroExtend_apply (slotEmbedding (fun _ : Empty ⊕ Unit => e₁))
    (fun a => F a (coordinateProjection e y)) (fun _ => i)

lemma scalarSlot_lift_out {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => i) y=0 := by
  apply zeroExtend_out
  rintro ⟨a,ha⟩
  exact hi ⟨a (.inr ()),congrFun ha (.inr ())⟩

lemma scoreField_product {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) :
    scoreField (productPotential H G)=fun c y =>
      arrayCoordinateLift (leftCoordinates d e) (fun _ => leftCoordinates d e) (scoreField H) c y+
      arrayCoordinateLift (rightCoordinates d e) (fun _ => rightCoordinates d e) (scoreField G) c y := by
  funext c y
  rw [scoreLabels_eq c]
  generalize c (.inr ())=i
  induction i using Fin.addCases with
  | left i =>
    change _=arrayCoordinateLift _ _ _ (fun _ => leftCoordinates d e i) y+_
    rw [scalarSlot_lift_in,scalarSlot_lift_out _ _ _ _ (left_not_right i),add_zero,coordinateProjection_left]
    exact productPotential_directional_left hH hG i y
  | right i =>
    change _=_+arrayCoordinateLift _ _ _ (fun _ => rightCoordinates d e i) y
    rw [scalarSlot_lift_out _ _ _ _ (right_not_left i),scalarSlot_lift_in,zero_add,coordinateProjection_right]
    exact productPotential_directional_right hH hG i y

lemma scoreField_product_allSplit {d e n : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hbH : ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange n) y) M)
    (hbG : ∀y,AllSplitBound (spatialTensor (scoreField G) (List.finRange n) y) N)
    (y : Point (d+e)) :
    AllSplitBound (spatialTensor (scoreField (productPotential H G)) (List.finRange n) y) (M+N) := by
  have hsH (c) := (scoreField_polySmooth hH c).smooth
  have hsG (c) := (scoreField_polySmooth hG c).smooth
  rw [scoreField_product (hH.smooth.differentiable (by simp)) (hG.smooth.differentiable (by simp)),
    spatialTensor_add _ _ (arrayCoordinateLift_smooth _ _ _ hsH) (arrayCoordinateLift_smooth _ _ _ hsG)]
  exact (AllSplitBound.coordinateLift _ _ _ hsH hbH y).add
    (AllSplitBound.coordinateLift _ _ _ hsG hbG y) hM hN
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalMeanArray
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma scoreAugmented_gaussian {d : ℕ} {K : Type} (l : List K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) :
    scoreAugmented (fun z : Point d => ‖z‖^2/2) l y c=
      if l=[] then (if c (.inl (.inr ()))=c (.inr ()) then 1 else 0) else 0 := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ
  have hg : directional (v (c (.inr ()))) (fun z : Point d => ‖z‖^2/2)=
      fun z => inner ℝ (v (c (.inr ()))) z := by
    funext z
    rw [directional_gaussianPotential,real_inner_comm]
  have hd : directional (v (c (.inl (.inr ()))))
      (fun z => inner ℝ (v (c (.inr ()))) z)=fun _ =>
      inner ℝ (v (c (.inr ()))) (v (c (.inl (.inr ())))) := by
    funext z
    exact congrArg (fun A : Point d →L[ℝ] ℝ => A (v (c (.inl (.inr ())))))
      (innerSL ℝ (v (c (.inr ())))).hasFDerivAt.fderiv
  unfold scoreAugmented
  change JetCalculus.jet _ l (directional _ (directional (v (c (.inr ()))) _)) y=_
  rw [hg,hd,JetCalculus.jet_const]
  by_cases hl : l=[]
  · simp only [hl,↓reduceIte]
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply,v,eq_comm]
  · simp only [hl,↓reduceIte]

lemma scoreField_gaussian_allSplit {d n : ℕ} (hn : 0<n) (y : Point d) :
    AllSplitBound (spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2))
      (List.finRange n) y) 1 := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hh := (allSplitBound_spatial_delta (d:=d) (List.finRange h) (by simp)).reindex (scoreSpatialSlots h)
  have he : (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0))=
      spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2)) (List.finRange (h+1)) y := by
    funext c
    rw [←scoreAugmented_gaussian,scoreSpatial_eq]
  change AllSplitBound (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0)) _ at hh
  rw [he] at hh
  apply hh.mono
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

lemma centeringScore_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (scoreField (productPotential
      (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)))
      (List.finRange n) y) (2+normalizedTensorMajorant (n+1) (1-T^2)) := by
  convert scoreField_product_allSplit
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
    (add_nonneg (by norm_num : (0:ℝ)≤1) (normalizedTensorMajorant_nonneg _ _))
    (by norm_num : (0:ℝ)≤1) (scoreField_spatial_allSplit hF x hr hlam hl hT0 hT1 n hn)
    (scoreField_gaussian_allSplit hn) y using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma probability_gibbs_of_gaussianTail {d : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) : IsProbabilityMeasure (gibbs H) := by
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
      integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) 0
  exact probability_gibbs_of_partition (partition_pos_of_continuous hH).ne'
    (partition_ne_top_of_integrable hi)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma directional_basis_gradient {d : ℕ} (H : Point d → ℝ) (y : Point d) (i : Fin d) :
    directional (EuclideanSpace.basisFun (Fin d) ℝ i) H y=gradient H y i := by
  rw [directional_gradient]
  have hh (v : Point d) : inner ℝ v (EuclideanSpace.basisFun (Fin d) ℝ i)=v i := by
    simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]
  exact hh (gradient H y)

lemma gradient_productPotential {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (y : Point (d+e)) :
    productPointEquiv d e (gradient (productPotential H G) y)=
      (gradient H (productPointEquiv d e y).1,gradient G (productPointEquiv d e y).2) := by
  apply Prod.ext
  · ext i
    change gradient (productPotential H G) y (Fin.castAdd e i)=_
    rw [←directional_basis_gradient,productPotential_directional_left hH hG,directional_basis_gradient]
  · ext i
    change gradient (productPotential H G) y (Fin.natAdd d i)=_
    rw [←directional_basis_gradient,productPotential_directional_right hH hG,directional_basis_gradient]

lemma productPointEquiv_fst_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).1‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).2‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).1]
lemma productPointEquiv_snd_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).2‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).1‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).2]

lemma productPotential_gradient_lipschitz {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) {K L : ℝ≥0}
    (hK : LipschitzWith K (gradient H)) (hL : LipschitzWith L (gradient G)) :
    LipschitzWith (K+L) (gradient (productPotential H G)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [dist_eq_norm,NNReal.coe_add]
  have h1 := hK.dist_le_mul (productPointEquiv d e y).1 (productPointEquiv d e z).1
  have h2 := hL.dist_le_mul (productPointEquiv d e y).2 (productPointEquiv d e z).2
  simp only [dist_eq_norm] at h1 h2
  have hp := productPointEquiv_norm_sq (gradient (productPotential H G) y-gradient (productPotential H G) z)
  rw [map_sub,gradient_productPotential hH hG,gradient_productPotential hH hG] at hp
  simp only [Prod.fst_sub,Prod.snd_sub] at hp
  have h1' := productPointEquiv_fst_norm_le (y-z)
  have h2' := productPointEquiv_snd_norm_le (y-z)
  simp only [map_sub,Prod.fst_sub,Prod.snd_sub] at h1' h2'
  have h1'' := h1.trans (mul_le_mul_of_nonneg_left h1' K.2)
  have h2'' := h2.trans (mul_le_mul_of_nonneg_left h2' L.2)
  have hn : ‖gradient (productPotential H G) y-gradient (productPotential H G) z‖≤
      ‖gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1‖+
      ‖gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2‖ := by
    nlinarith [norm_nonneg (gradient (productPotential H G) y-gradient (productPotential H G) z),
      norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1),
      norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2),
      mul_nonneg (norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1))
        (norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2))]
  exact hn.trans ((add_le_add h1'' h2'').trans_eq (by ring))
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NormSubSqTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E]

lemma norm_sub_sq_le_two (x y : E) : ‖x-y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (x-y)) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

lemma sub_sq_bound {f g : Ω → E} (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g ν)
    (hfi : Integrable (fun z => ‖f z‖^2) ν) (hgi : Integrable (fun z => ‖g z‖^2) ν)
    {A B : ℝ} (hA : (∫z,‖f z‖^2 ∂ν)≤A) (hB : (∫z,‖g z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖f z-g z‖^2) ν ∧
      (∫z,‖f z-g z‖^2 ∂ν)≤2*A+2*B := by
  have hi : Integrable (fun z => 2*‖f z‖^2+2*‖g z‖^2) ν :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hm : AEStronglyMeasurable (fun z => ‖f z-g z‖^2) ν := (hf.sub hg).norm.pow 2
  have hs : Integrable (fun z => ‖f z-g z‖^2) ν :=
    hi.mono' hm (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_sub_sq_le_two (f z) (g z)))
  refine ⟨hs,(integral_mono hs hi (fun z => norm_sub_sq_le_two (f z) (g z))).trans ?_⟩
  rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul]
  linarith
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma weight_integral (u : I → ℝ) (f : I → E) (a b : ℝ) :
    ∫t in a..b,interpolation u f t=∑i,weight u i a b • f i := by
  simp only [interpolation]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_smul_const (basis u i) (f i)
  · intro i _
    exact ((basis_continuous u i).smul continuous_const).intervalIntegrable a b

lemma reproduces_scalar (u : I → ℝ) (hu : Function.Injective u)
    (p : ℝ[X]) (hp : p.degree<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*p.eval (u i))=p.eval t := by
  have he := congrArg (fun q : ℝ[X] => q.eval t)
    (Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn (by simpa using hp))
  simpa only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,basis,mul_comm] using he.symm

lemma reproduces_power (u : I → ℝ) (hu : Function.Injective u) (k : ℕ)
    (hk : k<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*(u i)^k)=t^k := by
  have hh := reproduces_scalar u hu (X^k) (by simpa using hk) t
  simpa only [eval_pow,eval_X] using hh

omit [CompleteSpace E] in
lemma reproduces_vector (u : I → ℝ) (hu : Function.Injective u) (m : ℕ)
    (hm : m≤Fintype.card I) (v : Fin m → E) (t : ℝ) :
    interpolation u (fun i => ∑k : Fin m,(u i)^(k:ℕ) • v k) t=
      ∑k : Fin m,t^(k:ℕ) • v k := by
  unfold interpolation
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [←Finset.sum_smul,reproduces_power u hu k (lt_of_lt_of_le k.2 hm)]

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
lemma norm_integral_sq (f : α → E) (hf : MemLp f 2 μ) :
    ‖∫x,f x ∂μ‖^2 ≤ μ.real univ * ∫x,‖f x‖^2 ∂μ := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by constructor <;> norm_num)
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ : α => (by norm_num : (0:ℝ)≤1)))
    (by simpa using hf.norm) (by simpa using (memLp_const (μ:=μ) (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ))
  simp only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,mul_one] at hh
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hh
  have hi : 0≤∫x,‖f x‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ha := (norm_integral_le_integral_norm f).trans hh
  have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
  simpa only [mul_pow,Real.sq_sqrt hi,Real.sq_sqrt (show 0≤μ.real univ from measureReal_nonneg),mul_comm] using hs

omit [CompleteSpace E] in
lemma time_seed_sq [SFinite ν] {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hi : Integrable (fun p => ‖f p‖^2) (μ.prod ν)) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤
        μ.real univ * (∫t,∫z,‖f (t,z)‖^2 ∂ν ∂μ) := by
  have hsq := hi.integral_prod_right
  have hm : AEStronglyMeasurable (fun z => ∫t,f (t,z) ∂μ) ν :=
    hf.prod_swap.integral_prod_right'
  have hbound : ∀ᵐ z ∂ν,‖∫t,f (t,z) ∂μ‖^2≤μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) := by
    filter_upwards [hi.prod_left_ae,hf.prodMk_right] with z hz hzm
    exact norm_integral_sq _ ((memLp_two_iff_integrable_sq_norm hzm).mpr hz)
  have hiout : Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν := by
    apply (hsq.const_mul (μ.real univ)).mono' (hm.norm.pow 2)
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq] using hz
  refine ⟨hiout,?_⟩
  calc
    _ ≤ ∫z,μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) ∂ν := integral_mono_ae hiout (hsq.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap (f:=fun t z => ‖f (t,z)‖^2) hi).symm
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_sq_of_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun p => ‖f p‖^2) (μ.prod ν) := by
  apply (integrable_prod_iff (hf.norm.pow 2)).mpr
  refine ⟨hslice,?_⟩
  simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
  apply (integrable_const B).mono' ((hf.norm.pow 2).integral_prod_right')
  filter_upwards [hB] with t ht
  have hn : 0≤∫z,‖f (t,z)‖^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,Pi.pow_apply] using ht

omit [CompleteSpace E] in
theorem time_seed_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*B := by
  have hi := integrable_sq_of_uniform hf hslice hB
  obtain ⟨ho,hv⟩ := time_seed_sq hf hi
  refine ⟨ho,hv.trans ?_⟩
  have hh := integral_mono_ae hi.integral_prod_left (integrable_const B) hB
  simp only [integral_const,smul_eq_mul] at hh
  convert mul_le_mul_of_nonneg_left hh (measureReal_nonneg (μ:=μ) (s:=univ)) using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} [SFinite ν]

omit [CompleteSpace E] in
lemma interpolation_continuous (u : I → ℝ) (v : I → E) : Continuous (interpolation u v) :=
  continuous_finsetSum _ (fun i _ => (basis_continuous u i).smul continuous_const)

lemma cellQuadrature_eq_integral (u : I → ℝ) (v : I → E) (ℓ θ : ℝ) :
    cellQuadrature u v ℓ θ=ℓ • ∫t in 0..θ,interpolation u v t := by
  rw [weight_integral,Finset.smul_sum]
  simp only [cellQuadrature,smul_smul]

theorem cellQuadrature_error_rms (u : I → ℝ) (f : ℝ → Ω → E) (ℓ : ℝ) {θ B : ℝ}
    (hθ : 0≤θ)
    (hf : ∀z,IntervalIntegrable (fun t => f t z) volume 0 θ)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × Ω => f p.1 p.2-interpolation u (fun i => f (u i) p.2) p.1)
      ((volume.restrict (Ioc 0 θ)).prod ν))
    (hi : ∀t∈Ioc 0 θ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν)
    (hB : ∀t∈Ioc 0 θ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2) ν ∧
      (∫z,‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2 ∂ν)≤ℓ^2*θ^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 θ)
  have hs : ∀ᵐ t ∂μ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.time_seed_uniform hm hs hb
  have he (z : Ω) : ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ=
      ℓ • (∫t,(f t z-interpolation u (fun i => f (u i) z) t) ∂μ) := by
    rw [cellQuadrature_eq_integral,←smul_sub,←intervalIntegral.integral_sub (hf z)
      ((interpolation_continuous u (fun i => f (u i) z)).intervalIntegrable 0 θ),
      intervalIntegral.integral_of_le hθ]
  have hnorm (v : E) : ‖ℓ • v‖^2=ℓ^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp_rw [he,hnorm]
  refine ⟨hv.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=θ := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 θ)=θ
    rw [Real.volume_real_Ioc_of_le hθ,sub_zero]
  rw [hμ] at hv
  exact (mul_le_mul_of_nonneg_left hv.2 (sq_nonneg ℓ)).trans_eq (by ring)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set
open scoped BigOperators

variable {I β E : Type*} [Fintype I] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β}

omit [CompleteSpace E] in
lemma norm_weighted_sum_sq (w : I → ℝ) (v : I → E) :
    ‖∑i,w i • v i‖^2≤(∑i,|w i|)*(∑i,|w i| *‖v i‖^2) := by
  have h := norm_sum_le Finset.univ (fun i => w i • v i)
  simp only [norm_smul,Real.norm_eq_abs] at h
  apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun i => |w i| * ‖v i‖) (f:=fun i => |w i|) (g:=fun i => |w i| *‖v i‖^2)
  · exact fun i _ => abs_nonneg _
  · exact fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro index _; exact le_of_eq (by ring)

omit [CompleteSpace E] in
theorem weighted_sum_sq (w : I → ℝ) (f : I → β → E) {B : ℝ}
    (hm : ∀i,AEStronglyMeasurable (f i) ν)
    (hi : ∀i,Integrable (fun z => ‖f i z‖^2) ν)
    (hB : ∀i,(∫z,‖f i z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∑i,w i • f i z‖^2) ν ∧
      (∫z,‖∑i,w i • f i z‖^2 ∂ν)≤(∑i,|w i|)^2*B := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun z => (∑i,|w i|)*(∑i,|w i| *‖f i z‖^2)) ν := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun z => ‖∑i,w i • f i z‖^2) ν := by
    have hh := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun z => ‖∑i,w i • f i z‖^2) ν :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i z)))
  refine ⟨ho,(integral_mono ho hs (fun z => norm_weighted_sum_sq w (fun i => f i z))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    have hh := Finset.sum_le_sum (fun (i : I) (_ : i∈Finset.univ) =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg (w i)))
    have h := mul_le_mul_of_nonneg_left hh hw0
    simpa only [←Finset.sum_mul,pow_two,mul_assoc] using h
  · intro i _
    exact (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChainTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma chainTaylor_scaled_eval (J : ℕ → ℝ → E) (n : ℕ) (a ℓ t : ℝ) :
    chainTaylor J n a (a+ℓ*t)=
      ∑k : Fin (n+1),t^(k:ℕ) •
        (((k.val.factorial:ℝ)⁻¹*ℓ^(k:ℕ)) • J k a) := by
  unfold chainTaylor
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [show a+ℓ*t-a=ℓ*t by ring,mul_pow,smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
lemma reproduces_cell_chainTaylor (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    interpolation u (fun i => chainTaylor J n a (a+ℓ*u i)) t=
      chainTaylor J n a (a+ℓ*t) := by
  simp_rw [chainTaylor_scaled_eval]
  exact reproduces_vector u hu (n+1) hn _ t

omit [CompleteSpace E] in
lemma interpolation_sub_unused (u : I → ℝ) (f g : I → E) (t : ℝ) :
    interpolation u (fun i => f i-g i) t=interpolation u f t-interpolation u g t := by
  simp [interpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma cell_chain_error_eq (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    J 0 (a+ℓ*t)-interpolation u (fun i => J 0 (a+ℓ*u i)) t=
      (J 0 (a+ℓ*t)-chainTaylor J n a (a+ℓ*t))-
        interpolation u (fun i => J 0 (a+ℓ*u i)-chainTaylor J n a (a+ℓ*u i)) t := by
  rw [interpolation_sub_unused,reproduces_cell_chainTaylor u hu n hn]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

omit [CompleteSpace E] in
theorem cell_chain_error_rms (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → Ω → E) (a ℓ t : ℝ) {B C : ℝ}
    (hB : 0≤B) (hC : 1≤C) (hc : ∑i,|basis u i t|≤C)
    (hm : ∀s∈insert t (Set.range u),AEStronglyMeasurable
      (fun z => J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)) ν)
    (hi : ∀s∈insert t (Set.range u),Integrable
      (fun z => ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2) ν)
    (hR : ∀s∈insert t (Set.range u),(∫z,
      ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2) ν ∧
      (∫z,‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2 ∂ν)≤4*C^2*B := by
  let R (s : ℝ) (z : Ω) := J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)
  have hmt := hm t (mem_insert t _)
  have hmn (i : I) := hm (u i) (mem_insert_of_mem t (mem_range_self i))
  have hit := hi t (mem_insert t _)
  have hin (i : I) := hi (u i) (mem_insert_of_mem t (mem_range_self i))
  have hRn (i : I) := hR (u i) (mem_insert_of_mem t (mem_range_self i))
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basis u i t) (fun i => R (u i)) hmn hin hRn
  have hms : AEStronglyMeasurable (fun z => interpolation u (fun i => R (u i) z) t) ν := by
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hmn i).const_smul (basis u i t))
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [interpolation,Finset.sum_apply,Pi.smul_apply,R]
  have hsb : (∫z,‖interpolation u (fun i => R (u i) z) t‖^2 ∂ν)≤C^2*B := by
    apply hsum.2.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hc 2) hB
  have hs := RMSIntegral.sub_sq_bound hmt hms hit hsum.1 (hR t (mem_insert t _)) hsb
  have he (z : Ω) := cell_chain_error_eq u hu n hn (fun k v => J k v z) a ℓ t
  simp_rw [he]
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hc2 : 1≤C^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc2 hB]
end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CenteringPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

lemma gradient_gaussianPotential {d : ℕ} (y : Point d) :
    gradient (fun z : Point d => ‖z‖^2/2) y=y := by
  ext i
  rw [←directional_basis_gradient,directional_gaussianPotential]
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

lemma gaussianPotential_gradient_lipschitz (d : ℕ) :
    LipschitzWith 1 (gradient (fun z : Point d => ‖z‖^2/2)) := by
  have he : gradient (fun z : Point d => ‖z‖^2/2)=id := funext gradient_gaussianPotential
  rw [he]
  exact LipschitzWith.id

lemma centeringPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith (centeringGradientBound lam r T (by positivity))
      (gradient (centeringPotential F x r T)) :=
  productPotential_gradient_lipschitz
    ((interpolationPotential_smooth hF x hr.le hl hT0 hT1).differentiable (by simp))
    ((gaussianPotential_polySmooth d).smooth.differentiable (by simp))
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hT0 hT1)
    (gaussianPotential_gradient_lipschitz d)

lemma centeringSkew_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s : ℝ) :
    ∀c,PolySmooth (jointSkew (centeringKernel hF x hr hl hT0 hT1) s c) := by
  apply jointSkew_polySmooth
  intro i j
  simpa only [matrixArray_apply,Sum.elim_inl,Sum.elim_inr] using
    centeringKernel_polySmooth hF x hr hlam hl hT0 hT1 (Sum.elim (fun _ => i) (fun _ => j))

lemma centeringScore_scaled_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound
      (spatialTensor (scoreField (centeringPotential F x r T)) (List.finRange k) y)
      ((2+normalizedTensorMajorant (k+1) (1-T^2))*1^k) := by
  intro k hk y
  simpa only [centeringPotential,one_pow,mul_one] using
    centeringScore_allSplit hF x hr hlam hl hT0 hT1 hk y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportCorrectionMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma vectorArray_spatial {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) :
    spatialTensor (vectorArray f) (List.finRange n) y=
      fun c => multilinearTensor (iteratedFDeriv ℝ n f y) (c ∘ Equiv.sumComm Unit (Fin n)) := by
  funext c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (.inr ())))
  change JetCalculus.jet _ _ (L ∘ f) y=_
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hf),
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma vectorArray_polySmooth {d : ℕ} {f : Point d → Point d} {L : ℝ≥0}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hL : LipschitzWith L f)
    (M : ℕ → ℝ) (hM : ∀n,0≤M n)
    (hB : ∀n,0<n → ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) (M n))
    (c : Unit → Fin d) : PolySmooth (vectorArray f c) := by
  apply PolySmooth.of_basis_growth ((innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ()))).contDiff.comp hf)
  intro l
  by_cases hl : l=[]
  · subst l
    exact growth_of_lipschitz ((innerSL ℝ _).lipschitz.comp hL)
  · have hn : 0<l.length := List.length_pos_iff.mpr hl
    apply growth_of_bounded (hM l.length)
    intro y
    have hh := (hB l.length hn y).reindex (Equiv.sumComm Unit (Fin l.length))
    rw [←vectorArray_spatial hf y] at hh
    have hb := hh.entry_le (hM _) (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique]; omega)
      (Sum.elim l.get c)
    change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ l.get)
      (List.finRange l.length) (vectorArray f c) y|≤_ at hb
    rw [←JetCalculus.jet_map,List.map_get_finRange] at hb
    exact hb

lemma vectorArray_energy {d n : ℕ} {H : Point d → ℝ} {f : Point d → Point d}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (hp : ∀c,PolySmooth (vectorArray f c)) (hn : 0<n) {M : ℝ}
    (hB : ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) M) :
    spatialEnergy (vectorArray f) n (gibbs H)≤d*M^2 := by
  let := probability_gibbs_of_gaussianTail hH ht
  apply spatialEnergy_from_split hH ht _ hp hn
  intro y
  rw [vectorArray_spatial hf y]
  exact (hB y).reindex (Equiv.sumComm Unit (Fin n))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma normalizedTensorMajorant_inv_scale {k : ℕ} {R a : ℝ}
    (hR : 0<R) (hR1 : R≤1) (ha : R^2≤a) :
    normalizedTensorMajorant (k+1) a≤normalizedTensorMajorant (k+1) 1*(R⁻¹)^k := by
  have hh := normalizedTensorMajorant_scale (n:=k+1) hR ha
  have hp : R^k≤R^(k+1-2) := pow_le_pow_of_le_one hR.le hR1 (by omega)
  apply hh.trans
  rw [inv_pow,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (normalizedTensorMajorant_nonneg _ _) (pow_pos hR _) hp

lemma centeringPotential_gradient_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ}
    (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith harmonicGradientBound (gradient (centeringPotential F x r T)) := by
  apply (centeringPotential_gradient_lipschitz hF x hr hl hT0 hT1).weaken
  change (1+‖r*T‖*((Real.pi^2/2)*T*((lam:ℝ)*r)))+1≤2+Real.pi^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hT0)]
  have hl0 : 0≤(lam:ℝ)*r^2 := mul_nonneg lam.2 (sq_nonneg r)
  have hT : T^2≤1 := by nlinarith
  have hb : (lam:ℝ)*r^2*T^2≤1/2 := by
    calc
      _ ≤ (lam:ℝ)*r^2*1 := mul_le_mul_of_nonneg_left hT hl0
      _ ≤ _ := by simpa only [mul_one] using hl
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi)
  nlinarith [sq_nonneg Real.pi]

lemma centeringScore_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField (centeringPotential F x r T))
      (List.finRange k) y) ((2+normalizedTensorMajorant (k+1) 1)*(R⁻¹)^k) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hi : 1≤R⁻¹ := (one_le_inv₀ hR).mpr hR1
  intro k hk y
  have hh := centeringScore_scaled_bound hF x hr hlam hl hT0 hT1 k hk y
  simp only [one_pow,mul_one] at hh
  apply hh.mono (add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _))
  have he := normalizedTensorMajorant_inv_scale (k:=k) hR hR1 hRT
  have hp : (2:ℝ)≤2*(R⁻¹)^k := by nlinarith [one_le_pow₀ hi (n:=k)]
  nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma centeringSkew_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (hs : 0 < s) :
    ∀k y,AllSplitBound
      (spatialTensor (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (List.finRange k) y)
      ((2*kernelMajorant k)*((lam:ℝ)*r/s)*(R⁻¹)^k) := by
  intro k y
  convert centering_jointSkew_spatial_bound hF x hr hlam hl hR hRT hT0 hT1 s y using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos (inv_pos.mpr hs)]
  simp only [inv_pow,div_eq_mul_inv]
  ring

lemma identityArray_polySmooth (d : ℕ) (c : Unit → Fin d) :
    PolySmooth (vectorArray (id : Point d → Point d) c) :=
  vectorArray_polySmooth contDiff_id LipschitzWith.id (fun _ => 1)
    (fun _ => by norm_num) (fun _ _ y => multilinearTensor_id_bound y) c

lemma identityArray_inv_energy {d k : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) {R : ℝ}
    (hR : 0<R) (hR1 : R≤1) (hk : 0<k) :
    spatialEnergy (vectorArray (id : Point d → Point d)) k (gibbs H)≤
      d*(R⁻¹)^(2*k)*1 := by
  have he := vectorArray_energy hH ht contDiff_id (identityArray_polySmooth d) hk
    (fun y => multilinearTensor_id_bound (n:=k) y)
  simp only [one_pow,mul_one] at he ⊢
  apply he.trans
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ ((one_le_inv₀ hR).mpr hR1))

attribute [local instance] OAI.LogConcaveSampling.centeringStateBudgetDecidableEqUnit
theorem centering_state_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0 < s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    let A := vectorArray (id : Point (d+d) → Point (d+d))
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector A (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector A (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d+d)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringStateBudget (n+1)) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have q := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1)
    (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (identityArray_polySmooth (d+d))
    (jointSkew_skew _ s) (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1) (fun _ => 1)
    (α:=(lam:ℝ)*r/s) (κ:=d+d) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => by norm_num) (centeringSkew_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 hs)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (fun k hk => by simpa only [Nat.cast_add] using identityArray_inv_energy hH.smooth.continuous ht hR hR1 hk)
    Ξ hder hm hlaw hab hsub n
  simpa only [centeringStateBudget,Nat.cast_add] using q

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudgetNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma centeringStateBudget_nonneg (n : ℕ) : 0 ≤ centeringStateBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => by norm_num) n 0

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open scoped NNReal BigOperators

variable {I E X : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace X]

lemma correction_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (correction w φ) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro z v
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  simp only [correction,dist_eq_norm,←Finset.sum_sub_distrib,←smul_sub]
  calc
    _ ≤ ∑j,‖w i j • (φ j (z j)-φ j (v j))‖ := norm_sum_le _ _
    _ ≤ ∑j,|w i j| *((K:ℝ)*dist z v) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [dist_eq_norm] using ((hφ j).dist_le_mul (z j) (v j)).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist z v j) (by positivity))
    _ = (∑j,|w i j|)*((K:ℝ)*dist z v) := by rw [Finset.sum_mul]
    _ ≤ (A:ℝ)*((K:ℝ)*dist z v) := mul_le_mul_of_nonneg_right (hw i) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul,dist_eq_norm]; ring

lemma step_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : I → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (step w φ a) := by
  apply LipschitzWith.of_dist_le_mul
  intro z v
  simpa only [step,dist_add_left] using (correction_lipschitz w φ hw hφ).dist_le_mul z v

theorem iterate_defect {Y : Type*} [PseudoMetricSpace Y] {q : ℝ≥0}
    {G : Y → Y} (hG : LipschitzWith q G) (hq : (q:ℝ)≤1/2)
    (a e : Y) {D : ℝ} (hD : 0≤D) (he : dist (G e) e≤D) (n : ℕ) :
    dist (G^[n] a) e≤2*D+(q:ℝ)^n*dist a e := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply,pow_zero,one_mul]; linarith
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ dist (G (G^[n] a)) (G e)+dist (G e) e := dist_triangle _ _ _
      _ ≤ (q:ℝ)*dist (G^[n] a) e+D := add_le_add (hG.dist_le_mul _ _) he
      _ ≤ (q:ℝ)*(2*D+(q:ℝ)^n*dist a e)+D := add_le_add (mul_le_mul_of_nonneg_left ih q.coe_nonneg) le_rfl
      _ ≤ 2*D+(q:ℝ)^(n+1)*dist a e := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hq hD]

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AngleNodes
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

lemma liePathJet_measurable {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (Ξ : Point d → ℝ → Point d) (hm : Measurable (fun p : ℝ × Point d => Ξ p.2 p.1))
    (k : ℕ) (v : ℝ) :
    Measurable (fun y => tensorVector (iterTensorLie H A F k) (Ξ y v)) :=
  (tensorVector_contDiff _ (fun c => (iterTensorLie_polySmooth hH A F hA hF k c).smooth)).continuous.measurable.comp
    (hm.comp (measurable_const.prodMk measurable_id))

lemma chainTaylor_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (J : ℕ → ℝ → Ω → E)
    (hm : ∀k t,Measurable (J k t)) (n : ℕ) (a b : ℝ) :
    Measurable (fun y => chainTaylor (fun k t => J k t y) n a b) := by
  unfold chainTaylor
  exact Finset.measurable_sum _ (fun k _ => (hm k a).const_smul _)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma probabilityNodes_injective {n : ℕ} (hn : 0<n) : Function.Injective (probabilityNodes n) := by
  intro i j hij
  apply Fin.ext
  have hne : (n:ℝ)≠0 := by exact_mod_cast ne_of_gt hn
  have he : (i:ℝ)=(j:ℝ) := (div_left_inj' hne).mp hij
  exact_mod_cast he

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma finiteCoordinateProjection_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (v : EuclideanSpace ℝ J) : ‖finiteCoordinateProjection e v‖≤‖v‖ := by
  have he : ‖finiteCoordinateProjection e v‖^2≤‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑i : I,(v (e i))^2)≤∑j : J,(v j)^2
    calc
      _ = ∑j∈Finset.univ.map e,(v j)^2 := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (finiteCoordinateProjection e v),norm_nonneg v]

lemma projection_interpolation {I E G : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (u : I → ℝ) (v : I → E) (t : ℝ) :
    L (interpolation u v t)=interpolation u (fun i => L (v i)) t := by
  simp only [interpolation,map_sum,map_smul]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_SingleCellBasisBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure Ω}

omit [CompleteSpace E] in
theorem singleCell_interpolation_rms (n : ℕ) (hn : 0<n) (C : ℝ) (hC : 1 ≤ C)
    (hC' : ∀v∈Icc (0:ℝ) 1,∑i,|basis (probabilityNodes n) i v| ≤ C) :
    ∀J : ℕ → ℝ → Ω → E, (∀k t,Measurable (J k t)) →
      ∀B : ℝ,0 ≤ B →
      (∀t∈Icc (0:ℝ) 1,
        Integrable (fun y => ‖J 0 t y-chainTaylor (fun k v => J k v y) n 0 t‖^2) μ ∧
        (∫y,‖J 0 t y-chainTaylor (fun k v => J k v y) n 0 t‖^2 ∂μ) ≤
          (t^(n+1)/(n.factorial:ℝ))^2*B) →
      ∀v∈Icc (0:ℝ) 1,
        Integrable (fun y => ‖J 0 v y-interpolation (probabilityNodes n)
          (fun i => J 0 (probabilityNodes n i) y) v‖^2) μ ∧
        (∫y,‖J 0 v y-interpolation (probabilityNodes n)
          (fun i => J 0 (probabilityNodes n i) y) v‖^2 ∂μ) ≤ 4*C^2*B := by
  intro J hJ B hB htay v hv
  have hs (t : ℝ) (ht : t∈insert v (range (probabilityNodes n))) : t∈Icc (0:ℝ) 1 := by
    rcases ht with rfl|⟨i,rfl⟩
    · exact hv
    · exact probabilityNodes_mem hn i
  have h := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) J 0 1 v hB hC (hC' v hv)
    (fun t _ => by
      simp only [zero_add,one_mul]
      apply Measurable.aestronglyMeasurable
      exact (hJ 0 t).sub (chainTaylor_measurable J hJ n 0 t))
    (fun t ht => by simpa only [zero_add,one_mul] using (htay t (hs t ht)).1)
    (fun t ht => by
      simp only [zero_add,one_mul]
      apply (htay t (hs t ht)).2.trans
      apply mul_le_of_le_one_left hB
      apply pow_le_one₀ (by positivity [(hs t ht).1])
      apply (div_le_iff₀ (by positivity : 0<(n.factorial:ℝ))).mpr
      simp only [one_mul]
      exact (pow_le_one₀ (hs t ht).1 (hs t ht).2).trans (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)))
  simpa only [zero_add,one_mul] using h

theorem singleCell_quadrature_rms [SFinite μ] (n : ℕ) (f : ℝ → Ω → E)
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hc : ∀y,ContinuousOn (fun t => f t y) (Icc (0:ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀t∈Icc (0:ℝ) 1,Integrable (fun y => ‖f t y-interpolation (probabilityNodes n)
      (fun i => f (probabilityNodes n i) y) t‖^2) μ)
    (hb : ∀t∈Icc (0:ℝ) 1,(∫y,‖f t y-interpolation (probabilityNodes n)
      (fun i => f (probabilityNodes n i) y) t‖^2 ∂μ) ≤ B)
    {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    Integrable (fun y => ‖(∫t in 0..θ,f t y)-∑i,weight (probabilityNodes n) i 0 θ •
      f (probabilityNodes n i) y‖^2) μ ∧
    (∫y,‖(∫t in 0..θ,f t y)-∑i,weight (probabilityNodes n) i 0 θ •
      f (probabilityNodes n i) y‖^2 ∂μ) ≤ B := by
  have hh := cellQuadrature_error_rms (probabilityNodes n) f 1 hθ.1
    (fun y => ((hc y).mono (by
      intro t ht; exact ⟨ht.1,ht.2.trans hθ.2⟩)).intervalIntegrable_of_Icc hθ.1)
    (by
      apply Measurable.aestronglyMeasurable
      apply hm.sub
      unfold interpolation
      exact Finset.measurable_sum _ (fun i _ =>
        ((basis_continuous (probabilityNodes n) i).measurable.comp measurable_fst).smul
          (hm.comp (measurable_const.prodMk measurable_snd))))
    (fun t ht => hi t ⟨ht.1.le,ht.2.trans hθ.2⟩)
    (fun t ht => hb t ⟨ht.1.le,ht.2.trans hθ.2⟩)
  simp only [one_smul,cellQuadrature,one_mul,one_pow] at hh
  exact ⟨hh.1,hh.2.trans (mul_le_of_le_one_left hB (pow_le_one₀ hθ.1 hθ.2))⟩
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E]

lemma nodeLp_ae {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) (f : Lp E 2 ν) :
    (nodeLp hφ f : Ω → E)=ᵐ[ν] fun z => φ (f z) := by
  filter_upwards [Lp.coeFn_add ((lipschitz_zero_shift hφ).compLp (by simp) f)
      (Lp.const 2 ν (φ 0)),
    (lipschitz_zero_shift hφ).coeFn_compLp (by simp) f,
    Lp.coeFn_const 2 ν (φ 0)] with z hz hφz hc
  simp only [nodeLp,hz,Pi.add_apply,hφz,Function.comp_apply,hc,Function.const_apply,sub_add_cancel]

lemma nodeLp_lipschitz {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) :
    LipschitzWith K (nodeLp (ν:=ν) hφ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [nodeLp,dist_add_right] using
    ((lipschitz_zero_shift hφ).lipschitzWith_compLp (by simp)).dist_le_mul f g

variable [NormedSpace ℝ E] [Fintype I]

lemma stepLp_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) : LipschitzWith (A*K) (stepLp w φ hφ a) :=
  step_lipschitz w _ a hw (fun j => nodeLp_lipschitz (hφ j))

lemma stepLp_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a z : I → Lp E 2 ν) (i : I) :
    (stepLp w φ hφ a z i : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun j => a j ω) (fun j => z j ω) i := by
  classical
  have ha := Lp.coeFn_add (a i) (∑j,w i j • nodeLp (hφ j) (z j))
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => w i j • nodeLp (hφ j) (z j))
  have hm : ∀ᵐω ∂ν,∀j,(w i j • nodeLp (hφ j) (z j) : Lp E 2 ν) ω=
      w i j • φ j (z j ω) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (w i j) (nodeLp (hφ j) (z j)),nodeLp_ae (hφ j) (z j)] with ω h1 h2
    simp only [h1,Pi.smul_apply,h2]
  filter_upwards [ha,hs,hm] with ω h1 h2 h3
  simp only [stepLp,step,correction,Pi.add_apply,h1,h2,h3]

theorem rms_picard_defect (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D : ℝ} (hD : 0≤D) (he : ∀i,dist (stepLp w φ hφ a e i) (e i)≤D) (n : ℕ) :
    dist ((stepLp w φ hφ a)^[n] a) e≤2*D+(A*K:ℝ≥0)^n*dist a e := by
  apply iterate_defect (stepLp_lipschitz w φ hφ a hw) (by exact_mod_cast hq) a e hD
    ((dist_pi_le_iff hD).mpr he) n

section Inner
omit [NormedSpace ℝ E] [IsFiniteMeasure ν]
variable [InnerProductSpace ℝ E]

lemma lp_norm_sq_integral (f : Lp E 2 ν) : ‖f‖^2=∫ω,‖f ω‖^2 ∂ν := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end Inner
end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

omit [IsFiniteMeasure ν] in
lemma lp_rms_eq (f g : Lp E 2 ν) {u v : Ω → E}
    (hf : (f : Ω → E)=ᵐ[ν] u) (hg : (g : Ω → E)=ᵐ[ν] v) :
    Integrable (fun ω => ‖u ω-v ω‖^2) ν ∧
      (∫ω,‖u ω-v ω‖^2 ∂ν)=dist f g^2 := by
  have he : (fun ω => (f-g : Lp E 2 ν) ω)=ᵐ[ν] fun ω => u ω-v ω := by
    filter_upwards [Lp.coeFn_sub f g,hf,hg] with ω h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
  have hi := (Lp.memLp (f-g)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hn : (fun ω => ‖(f-g : Lp E 2 ν) ω‖^2)=ᵐ[ν] fun ω => ‖u ω-v ω‖^2 :=
    he.fun_comp (fun z => ‖z‖^2)
  refine ⟨hi.congr hn,?_⟩
  rw [dist_eq_norm,lp_norm_sq_integral]
  exact integral_congr_ae hn.symm

lemma iterateLp_nodes_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Ω → E) (aLp : I → Lp E 2 ν)
    (ha : ∀i,(aLp i : Ω → E)=ᵐ[ν] a i) (N : ℕ) (i : I) :
    ((stepLp w φ hφ aLp)^[N] aLp i : Ω → E)=ᵐ[ν]
      fun ω => nodes w φ (fun ω j => a j ω) N ω i := by
  induction N generalizing i with
  | zero => simpa only [Function.iterate_zero_apply,nodes] using ha i
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have hia : ∀ᵐω ∂ν,∀j,aLp j ω=a j ω := ae_all_iff.mpr ha
    have hii : ∀ᵐω ∂ν,∀j,((stepLp w φ hφ aLp)^[N] aLp j : Ω → E) ω=
        nodes w φ (fun ω j => a j ω) N ω j := ae_all_iff.mpr ih
    filter_upwards [stepLp_ae w φ hφ aLp ((stepLp w φ hφ aLp)^[N] aLp) i,hia,hii] with ω h1 h2 h3
    simp only [h1,nodes,step,correction,Pi.add_apply,h2,h3]

theorem nodes_rms (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Ω → E)
    (ha : ∀i,MemLp (a i) 2 ν) (he : ∀i,MemLp (e i) 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D H : ℝ} (hD : 0≤D) (hH : 0≤H)
    (hdef : ∀i,(∫ω,‖step w φ (fun j => a j ω) (fun j => e j ω) i-e i ω‖^2 ∂ν)≤D^2)
    (hinit : ∀i,(∫ω,‖a i ω-e i ω‖^2 ∂ν)≤H^2) (N : ℕ) (i : I) :
    Integrable (fun ω => ‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2) ν ∧
      (∫ω,‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2 ∂ν)≤
        (2*D+(A*K:ℝ≥0)^N*H)^2 := by
  let aLp : I → Lp E 2 ν := fun j => (ha j).toLp (a j)
  let eLp : I → Lp E 2 ν := fun j => (he j).toLp (e j)
  have ha' (j : I) : (aLp j : Ω → E)=ᵐ[ν] a j := (ha j).coeFn_toLp
  have he' (j : I) : (eLp j : Ω → E)=ᵐ[ν] e j := (he j).coeFn_toLp
  have hstep (j : I) : (stepLp w φ hφ aLp eLp j : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun i => a i ω) (fun i => e i ω) j := by
    filter_upwards [stepLp_ae w φ hφ aLp eLp j,ae_all_iff.mpr ha',ae_all_iff.mpr he'] with ω h1 h2 h3
    simpa only [h2,h3] using h1
  have hdef' (j : I) : dist (stepLp w φ hφ aLp eLp j) (eLp j)≤D := by
    have hh := (lp_rms_eq _ _ (hstep j) (he' j)).2
    have hb := hdef j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=stepLp w φ hφ aLp eLp j) (y:=eLp j)]
  have hinit' : dist aLp eLp≤H := by
    apply (dist_pi_le_iff hH).mpr
    intro j
    have hh := (lp_rms_eq _ _ (ha' j) (he' j)).2
    have hb := hinit j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=aLp j) (y:=eLp j)]
  have hb := rms_picard_defect w φ hφ aLp eLp hw hq hD hdef' N
  have hrms := lp_rms_eq _ _ (iterateLp_nodes_ae w φ hφ a aLp ha' N i) (he' i)
  refine ⟨hrms.1,?_⟩
  rw [hrms.2]
  apply pow_le_pow_left₀ dist_nonneg _ 2
  exact (dist_le_pi_dist _ _ i).trans (hb.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinit' (show 0≤((A*K:ℝ≥0):ℝ)^N from by positivity))))
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicStationaryMoment
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal RealInnerProductSpace

lemma growth_vector_memLp {d e : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {f : Point d → Point e} (hg : Appell.HasGrowth f) (hm : AEStronglyMeasurable f μ)
    (hμ : Appell.HasMoments μ) : MemLp f 2 μ := by
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ((hg.norm.pow 2).integrable (hm.norm.pow 2) hμ)

lemma centering_lipschitz_memLp {d e : ℕ} {F : Point d → ℝ} {lam K : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {f : Point (d+d) → Point e} (hf : LipschitzWith K f) :
    MemLp f 2 (gibbs (centeringPotential F x r T)) := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact growth_vector_memLp (Appell.HasGrowth.lipschitz hf) hf.continuous.aestronglyMeasurable
    (ht.hasExpMoments hH.smooth.continuous).hasMoments

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringJointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

lemma rms_bound_pullback {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : Measurable f) (hlaw : μ.map f=ν)
    {e : Y → E} (he : Measurable e) (hi : Integrable (fun y => ‖e y‖^2) ν)
    {B : ℝ} (hB : (∫y,‖e y‖^2 ∂ν)≤B) :
    Integrable (fun x => ‖e (f x)‖^2) μ ∧ (∫x,‖e (f x)‖^2 ∂μ)≤B := by
  rw [←hlaw] at hi
  refine ⟨hi.comp_measurable hf,?_⟩
  rw [←integral_map hf.aemeasurable (he.norm.pow_const 2).aestronglyMeasurable,hlaw]
  exact hB

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_StationaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

namespace StationaryPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  {μ : Measure E} {V : E → E} (X : StationaryPath μ V)

lemma measurable_slice (t : ℝ) : Measurable (fun y => X.path y t) :=
  X.measurable.comp (measurable_const.prodMk measurable_id)

lemma measurePreserving {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    MeasurePreserving (fun y => X.path y t) μ μ := ⟨X.measurable_slice t,X.law t ht⟩

lemma memLp_slice {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (hi : MemLp (id : E → E) 2 μ) :
    MemLp (fun y => X.path y t) 2 μ := hi.comp_measurePreserving (X.measurePreserving ht)

lemma integral_eq [CompleteSpace E] (hV : Continuous V) (y : E) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) : (∫u in 0..t,V (X.path y u))=X.path y t-y := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (X.continuous y).continuousOn
    (fun u hu => (X.derivative y u ⟨hu.1.le,hu.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2)))
    ((hV.comp (X.continuous y)).intervalIntegrable 0 t)
  simpa only [X.initial] using he
end StationaryPath

lemma centeringWeight_bound (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    ∑j,|centeringWeight n i j| ≤ centeringRowBudget n := by
  change ∑j,|centeringWeight n i j| ≤ ((n:ℝ)+1)*singleCellBasisBudget n
  have hi := probabilityNodes_mem hn i
  have hb := weights_abs_bound (probabilityNodes n) hi.1 hi.2 (singleCellBasisBudget_spec n).2
  simpa only [centeringWeight,centeringRowBudget,NNReal.coe_mk,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    hb.trans (mul_le_of_le_one_right (by positivity [(singleCellBasisBudget_spec n).1]) hi.2)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IdentityOutputEmbedding
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma identityOutputProjection_vector {d : ℕ} (f : Point d → Point d) (y : Point d) :
    identityOutputProjection d (tensorVector (vectorArray f) y)=f y := by
  ext i
  change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (f y)=_
  simp only [EuclideanSpace.basisFun_inner]

lemma identityOutputProjection_lie {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y) (y : Point d) :
    identityOutputProjection d (tensorVector
      (iterTensorLie H A (vectorArray (id : Point d → Point d)) 1) y)=skewLieField H A y := by
  ext i
  change tensorLie H A (vectorArray (id : Point d → Point d)) (fun _ => i) y=_
  rw [tensorLie_eq_directional H A _ (fun c => (hA c).smooth)
    (fun c => (identityArray_polySmooth d c).smooth) hsk]
  change fderiv ℝ ((innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) : Point d → ℝ) y
    (skewLieField H A y)=_
  rw [ContinuousLinearMap.fderiv]
  simp only [innerSL_apply_apply, EuclideanSpace.basisFun_inner]

lemma projection_rms {Ω I J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype I] [Fintype J] (e : I ↪ J)
    {f : Ω → EuclideanSpace ℝ J} (hm : Measurable f)
    {B : ℝ} (hi : Integrable (fun y => ‖f y‖^2) μ) (hb : (∫y,‖f y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖finiteCoordinateProjection e (f y)‖^2) μ ∧
      (∫y,‖finiteCoordinateProjection e (f y)‖^2 ∂μ)≤B := by
  have ha (y : Ω) : ‖finiteCoordinateProjection e (f y)‖^2≤‖f y‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  have h := hi.mono' (((finiteCoordinateProjection e).continuous.measurable.comp hm).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def] using ha y))
  exact ⟨h,(integral_mono h hi ha).trans hb⟩
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringVelocityInterpolationRms
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal RealInnerProductSpace

attribute [local instance] OAI.LogConcaveSampling.centeringVelocityInterpolationRmsDecidableEqUnit
theorem centering_velocity_interpolation_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
    (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) (n : ℕ) (hn : 0<n) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    let V := fun t y => skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)
    Integrable (fun y => ‖V v y-interpolation (probabilityNodes n)
      (fun i => V (probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖V v y-interpolation (probabilityNodes n)
      (fun i => V (probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      4*(singleCellBasisBudget n)^2*
        (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)) := by
  intro V
  let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
  let I := vectorArray (id : Point (d+d) → Point (d+d))
  let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I (k+1)) (Ξ y t)
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have hA := centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s
  have hI := identityArray_polySmooth (d+d)
  have hJ (k : ℕ) (t : ℝ) : Measurable (J k t) :=
    liePathJet_measurable hH A I hA hI Ξ hm (k+1) t
  have hb := singleCell_interpolation_rms n hn (singleCellBasisBudget n)
    (singleCellBasisBudget_spec n).1 (singleCellBasisBudget_spec n).2 J hJ
    (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2))
    (by positivity [centeringStateBudget_nonneg (n+2)])
    (fun t ht => by
      simpa only [sub_zero,zero_add,Nat.zero_add] using
        centering_velocity_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 hs Ξ hder hm hlaw n 0 t
          le_rfl ht.1 ht.2) v hv
  let E := fun y => J 0 v y-interpolation (probabilityNodes n) (fun i => J 0 (probabilityNodes n i) y) v
  have hE : Measurable E := (hJ 0 v).sub
    (Finset.measurable_sum _ (fun i _ => (hJ 0 _).const_smul (basis (probabilityNodes n) i v)))
  have he (y : Point (d+d)) :
      V v y-interpolation (probabilityNodes n) (fun i => V (probabilityNodes n i) y) v=
        identityOutputProjection (d+d) (E y) := by
    simp only [E,map_sub,projection_interpolation,J,Nat.zero_add]
    simp only [identityOutputProjection_lie _ A hA (jointSkew_skew _ s),V,A,I]
  simp_rw [he]
  exact projection_rms (identityOutputEmbedding (d+d)) hE hb.1 hb.2

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringStateQuadratureBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

lemma centeringStateQuadratureBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    0 ≤ centeringStateQuadratureBudget n d lam r R s := by
  unfold centeringStateQuadratureBudget
  positivity [centeringStateBudget_nonneg (n+2)]

include hlam hR hRT hs

theorem centering_state_quadrature_rms (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    let V := skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
    let e := fun y => X.path y (probabilityNodes n i)-y-
      ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))
    Integrable (fun y => ‖e y‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖e y‖^2 ∂gibbs (centeringPotential F x r T)) ≤ centeringStateQuadratureBudget n d lam r R s := by
  intro V e
  have hV := centeringTrueVelocity_continuous hF x hr hlam hl hT0 hT1 s
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  have hh (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := centering_velocity_interpolation_rms
    hF x hr hlam hl hR hRT hT0 hT1 hs X.path X.derivative X.measurable X.law n hn ht
  have hb := singleCell_quadrature_rms n (fun t y => V (X.path y t))
    (hV.measurable.comp X.measurable) (fun y => (hV.comp (X.continuous y)).continuousOn)
    (centeringStateQuadratureBudget_nonneg n d lam r R s)
    (fun t ht => (hh t ht).1) (fun t ht => (hh t ht).2) (probabilityNodes_mem hn i)
  dsimp only [V] at hb
  simp_rw [X.integral_eq hV _ (probabilityNodes_mem hn i)] at hb
  exact hb

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_10
theorem centering_initial_rms {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Integrable (fun y => ‖X.path y t-y‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖X.path y t-y‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1) := by
  have hh := centering_state_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 hs
    X.path X.derivative X.measurable X.law 0 0 t le_rfl ht.1 ht.2
  simp only [chainTaylor,Nat.zero_add,Finset.range_one,Finset.sum_singleton,Nat.factorial_zero,
    Nat.cast_one,inv_one,pow_zero,one_mul,one_smul,iterTensorLie,X.initial,
    sub_zero,pow_one,div_one] at hh
  let E := fun y => tensorVector (vectorArray (id : Point (d+d) → Point (d+d))) (X.path y t)-
    tensorVector (vectorArray (id : Point (d+d) → Point (d+d))) y
  have hc := (tensorVector_contDiff _ (fun c => (identityArray_polySmooth (d+d) c).smooth)).continuous.measurable
  have hE : Measurable E := (hc.comp (X.measurable_slice t)).sub hc
  have he (y : Point (d+d)) : X.path y t-y=identityOutputProjection (d+d) (E y) := by
    simp only [E,map_sub,identityOutputProjection_vector,id_eq]
  simp_rw [he]
  apply projection_rms (identityOutputEmbedding (d+d)) hE hh.1
  apply hh.2.trans
  simp only [Nat.cast_add]
  exact mul_le_of_le_one_left (by positivity [centeringStateBudget_nonneg 1])
    (pow_le_one₀ ht.1 ht.2)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ] {V Vhat : E → E}

theorem stationaryPicard_rms (X : StationaryPath μ V) (hV : Continuous V)
    {K : ℝ≥0} (hhat : LipschitzWith K Vhat) (hbase : MemLp (id : E → E) 2 μ)
    (n : ℕ) (hn : 0<n) (hq : centeringRowBudget n*K ≤ 1/2)
    {Bq Bv Bi : ℝ} (hBq : 0 ≤ Bq) (hBv : 0 ≤ Bv) (hBi : 0 ≤ Bi)
    (hquad : ∀i : Fin (n+1),
      Integrable (fun y => ‖X.path y (probabilityNodes n i)-y-
        ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))‖^2) μ ∧
      (∫y,‖X.path y (probabilityNodes n i)-y-
        ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))‖^2 ∂μ) ≤ Bq)
    (hvint : Integrable (fun y => ‖Vhat y-V y‖^2) μ)
    (hvel : (∫y,‖Vhat y-V y‖^2 ∂μ) ≤ Bv)
    (hinit : ∀i : Fin (n+1),(∫y,‖X.path y (probabilityNodes n i)-y‖^2 ∂μ) ≤ Bi)
    (N : ℕ) (i : Fin (n+1)) :
    Integrable (fun y => ‖stationaryPicard n N Vhat y i-X.path y (probabilityNodes n i)‖^2) μ ∧
    (∫y,‖stationaryPicard n N Vhat y i-X.path y (probabilityNodes n i)‖^2 ∂μ) ≤
      (2*Real.sqrt (2*(centeringRowBudget n:ℝ)^2*Bv+2*Bq)+
        ((centeringRowBudget n*K:ℝ≥0):ℝ)^N*Real.sqrt Bi)^2 := by
  have he (j : Fin (n+1)) : MemLp (fun y => X.path y (probabilityNodes n j)) 2 μ :=
    X.memLp_slice (probabilityNodes_mem hn j) hbase
  apply FinitePicard.nodes_rms (centeringWeight n) (fun _ => Vhat) (fun _ => hhat)
    (fun _ y => y) (fun j y => X.path y (probabilityNodes n j)) (fun _ => hbase) he
    (centeringWeight_bound n hn) hq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ _ N i
  · intro k
    let e := fun j y => Vhat (X.path y (probabilityNodes n j))-V (X.path y (probabilityNodes n j))
    have hem (j : Fin (n+1)) : Measurable (e j) :=
      (hhat.continuous.measurable.sub hV.measurable).comp (X.measurable_slice _)
    have heb (j : Fin (n+1)) := rms_bound_pullback (X.measurable_slice (probabilityNodes n j))
      (X.law _ (probabilityNodes_mem hn j)) (hhat.continuous.measurable.sub hV.measurable) hvint hvel
    have hsum := weighted_sum_sq (centeringWeight n k) e (fun j => (hem j).aestronglyMeasurable)
      (fun j => (heb j).1) (fun j => (heb j).2)
    let q := fun y => X.path y (probabilityNodes n k)-y-
      ∑j,centeringWeight n k j • V (X.path y (probabilityNodes n j))
    have hqm : Measurable q := ((X.measurable_slice _).sub measurable_id).sub
      (Finset.measurable_sum _ (fun j _ =>
        (hV.measurable.comp (X.measurable_slice _)).const_smul (centeringWeight n k j)))
    have hsm : Measurable (fun y => ∑j,centeringWeight n k j • e j y) :=
      Finset.measurable_sum _ (fun j _ => (hem j).const_smul _)
    have hh := sub_sq_bound hsm.aestronglyMeasurable hqm.aestronglyMeasurable
      hsum.1 (hquad k).1 hsum.2 (hquad k).2
    have hid (y : E) : FinitePicard.step (centeringWeight n) (fun _ => Vhat) (fun _ => y)
        (fun j => X.path y (probabilityNodes n j)) k-X.path y (probabilityNodes n k)=
      (∑j,centeringWeight n k j • e j y)-q y := by
      simp only [FinitePicard.step,Pi.add_apply,FinitePicard.correction,e,q,smul_sub,Finset.sum_sub_distrib]
      abel
    simp_rw [hid]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2*(centeringRowBudget n:ℝ)^2*Bv+2*Bq)]
    apply hh.2.trans
    have hw := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (centeringWeight_bound n hn k) 2
    have hwv := mul_le_mul_of_nonneg_right hw hBv
    nlinarith
  · intro k
    rw [Real.sq_sqrt hBi]
    simpa only [norm_sub_rev] using hinit k
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CenteringMeanCircuit
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T h ψ s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

include hlam hR hRT hs

theorem centeringPicard_state_rms_oai (n m N nc Nc : ℕ) (hnc : 0<nc)
    (e : ProbabilityNode T h (n+1)) {K : ℝ≥0}
    (hhat : LipschitzWith K (centeringVelocityJoint F x r T h ψ s n m N e))
    (hq : centeringRowBudget nc*K ≤ 1/2) {Bv : ℝ} (hBv : 0 ≤ Bv)
    (hvi : Integrable (fun y => ‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2)
      (gibbs (centeringPotential F x r T)))
    (hvb : (∫y,‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2
      ∂gibbs (centeringPotential F x r T)) ≤ Bv) (i : Fin (nc+1)) :
    Integrable (fun y => ‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖stationaryPicard nc Nc (centeringVelocityJoint F x r T h ψ s n m N e) y i-
      X.path y (probabilityNodes nc i)‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      centeringPicardBudget nc Nc d lam K r R s Bv := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact stationaryPicard_rms X (centeringTrueVelocity_continuous hF x hr hlam hl hT0 hT1 s)
    hhat (centering_lipschitz_memLp hF x hr hlam hl hT0 hT1 (LipschitzWith.id)) nc hnc hq
    (centeringStateQuadratureBudget_nonneg nc d lam r R s) hBv
    (by positivity [centeringStateBudget_nonneg 1])
    (centering_state_quadrature_rms hF x hr hlam hl hR hRT hT0 hT1 hs X nc hnc) hvi hvb
    (fun j => (centering_initial_rms hF x hr hlam hl hR hRT hT0 hT1 hs X
      (probabilityNodes_mem hnc j)).2) Nc i

end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.centeringPicard_state_rms_oai := @OAI.LogConcaveSampling.centeringPicard_state_rms_oai
