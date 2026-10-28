-- Prove2me | solution 1 for OAI.LogConcaveSampling.TensorSum.matrix_one_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:54:52.674255+00:00
-- url     : https://prove2.me/submissions/adc31ae4-564b-49d0-9619-d687179d5a43

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_TensorSum_spatialBound_Lp

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

lemma map_snd_withDensity {E G : Type*} [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure G) [SFinite μ] [SFinite ν]
    {w : E × G → ℝ≥0∞} (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.snd=
      ν.withDensity (fun y => ∫⁻ x,w (x,y) ∂μ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd]
  change (∫⁻ a, (f ∘ Prod.snd) a ∂(μ.prod ν).withDensity w)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (hf.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ hw.lintegral_prod_left' hf,
    lintegral_prod_symm _ (hw.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro y
  exact lintegral_mul_const (f y) (hw.comp (measurable_id.prodMk measurable_const))

lemma probability_density_eq_gibbs {d : ℕ} {H : Point d → ℝ}
    {c : ℝ≥0∞} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (he : μ=c • volume.withDensity (gibbsDensity H)) : μ=gibbs H := by
  have hh := congrArg (fun ν : Measure (Point d) => ν Set.univ) he
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hh
  have hc : c=(partition H)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hh.symm
  simpa [gibbs,hc] using he

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

lemma interpolationLaw_probability {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (ρ : ℝ) : IsProbabilityMeasure (interpolationLaw F x r ρ) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  unfold interpolationLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem interpolationLaw_eq_gibbs {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) :
    interpolationLaw F x r ρ=gibbs (interpolationPotential F x r ρ) := by
  let := interpolationLaw_probability hF x hr hl ρ
  apply probability_density_eq_gibbs
  have ha : 0 < 1-ρ^2 := by linarith
  have hσ : Real.sqrt (1-ρ^2)≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hd := EulerDensity.joint_density (hF.continuous_potential x r).measurable
    (fun z => ρ • z) (by fun_prop) hσ
  have he : interpolationLaw F x r ρ=
      (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun p => (p.1,ρ • p.1+Real.sqrt (1-ρ^2) • p.2))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [he,hd,Measure.map_smul,map_snd_withDensity _ _ (by
    have := (hF.continuous_potential x r).measurable
    fun_prop)]
  congr 1
  congr 1
  funext y
  simp only [Real.sq_sqrt ha.le]
  exact interpolation_density_integral hF x hr hl hρ y
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
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_PolynomialBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped BigOperators

lemma polynomialBudget_nonneg (P : Polynomial ℝ) : 0≤polynomialBudget P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma eval_abs_le_polynomialBudget (P : Polynomial ℝ) {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ≤1) :
    |P.eval ρ|≤polynomialBudget P := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum polynomialBudget
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [abs_mul,abs_pow,abs_of_nonneg h0]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ h0 h1)

lemma scaledCoefficient_bound (P : Polynomial ℝ) (n : ℕ) {r L ρ : ℝ}
    (hl0 : 0 ≤ r*L) (hl1 : r*L≤1) (h0 : 0≤ρ) (h1 : ρ≤1) :
    |(r*L)^n*P.eval ρ|≤polynomialBudget P := by
  rw [abs_mul,abs_pow,abs_of_nonneg hl0]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl1) (abs_nonneg _)).trans
    (by simpa using eval_abs_le_polynomialBudget P h0 h1)
end LogConcaveSampling

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ProperSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma splitEnvelope_nonneg (T : (S → Fin d) → ℝ) : 0 ≤ splitEnvelope T :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma splitMatrix_norm_le (T : (S → Fin d) → ℝ) (p : ProperSplit S) :
    ‖splitMatrix T p‖ ≤ splitEnvelope T :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ p)

lemma allSplitBound_envelope (T : (S → Fin d) → ℝ) :
    AllSplitBound T (splitEnvelope T) := by
  intro I O _ _ _ _ _ _ e
  have h := (bound_norm (splitMatrix T (properOfEquiv e))).mono
    (pow_le_pow_left₀ (norm_nonneg _) (splitMatrix_norm_le T (properOfEquiv e)) 2)
  have h' := h.reindex (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma measurable_splitEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c)) :
    Measurable (fun x => splitEnvelope (T x)) := by
  apply Finset.measurable_sum
  intro p _
  let : MeasurableSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  have : BorelSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  apply Measurable.norm
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => hT _))

end LogConcaveSampling.TensorEnergy

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorExpression
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

namespace TensorExpression

lemma eval_polySmooth {d : ℕ} {base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ}
    {H : Point d → ℝ} (hbase : ∀q c,PolySmooth (base q c)) (hH : PolySmooth H)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) : PolySmooth (A.eval base H c) := by
  induction A with
  | jet q => exact hbase q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    exact PolySmooth.sum Finset.univ (fun z _ => (ihA _).mul (ihB _))
  | adjoint hn A ih => exact hH.tensorAdjoint (fun z => ih _) _

lemma physicalBase_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q : ℕ) (c : Fin (q+2) → Fin d) : PolySmooth (physicalBase F x r ρ ((lam:ℝ)*r) q c) := by
  exact normalizedTensor_polySmooth hF x hr hlam hl hρ0 hρ1 _ _
    (List.nodup_finRange _) (by simp) (by simp) c

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

lemma physicalBase_eq_U {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) (y : Point d) :
    physicalBase F x r ρ L q c y=
      L⁻¹*conditionalU F x r ρ y (JetCalculus.spaceBasis d (c (Fin.last (q+1)))) L
        (fun j : Fin (q+1) => JetCalculus.spaceBasis d (c j.castSucc)) (List.finRange (q+1)) := by
  unfold physicalBase normalizedTensor conditionalU
  rw [List.finRange_succ_last,JetCalculus.jet_append,JetCalculus.jet_map]
  simp only [Fintype.card_fin,Nat.add_sub_cancel,List.length_finRange,Function.comp_def]
  have hv : (fun j : Fin (q+1) => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc))=
      fun j : Fin (q+1) => jointPosition d (JetCalculus.spaceBasis d (c j.castSucc)) := by
    funext j
    have he : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc=
        Sum.inl (c j.castSucc) := by simp [conditionalSlotEmbedding]
    rw [he]
    exact (jointPosition_basis _).symm
  rw [hv]
  have hf : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c (Fin.last (q+1))=
      Sum.inr (c (Fin.last (q+1))) := by simp [conditionalSlotEmbedding]
  simp only [JetCalculus.jet,hf]
  rw [←jointField_basis]
  field_simp

lemma jointBase_slice {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) :
    (fun y => jointBase F x r L q c (ρ,y))=physicalBase F x r ρ L q c := by
  funext y
  exact (physicalBase_eq_U F x r ρ L hL q c y).symm

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

lemma jointEval_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) :
    (fun y => A.jointEval F x r ((lam:ℝ)*r) c (ρ,y))=
      A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) c := by
  induction A with
  | jet q => exact jointBase_slice F x r ρ _ (by positivity) q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    funext y
    simp only [jointEval,eval]
    apply Finset.sum_congr rfl
    intro z _
    rw [congrFun (ihA _) y,congrFun (ihB _) y]
  | adjoint hn A ih =>
    funext y
    dsimp only [jointEval,eval]
    rw [joint_gadj_slice hF x hr.le hl hρ0 hρ1 (fun z =>
      (A.jointEval_timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp))]
    have he : (fun z y => A.jointEval F x r ((lam:ℝ)*r) (Fin.snoc c z) (ρ,y))=
        fun z => A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) (Fin.snoc c z) := by
      funext z
      exact ih _
    rw [he]

end TensorExpression
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

lemma spatialEnvelope_nonneg {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : 0≤ spatialEnvelope F j y :=
  TensorEnergy.splitEnvelope_nonneg _

lemma spatialEnvelope_measurable {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    Measurable (spatialEnvelope F j) :=
  TensorEnergy.measurable_splitEnvelope _ (fun c =>
    (spatialTensor_polySmooth F hF (List.finRange j) c).smooth.continuous.measurable)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NaturalMomentNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LogConcaveSampling
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma natural_moment_norm {f : Ω → ℝ} (hf : ∀x,0 ≤ f x) {n : ℕ} (hn : 0<n) :
    eLpNorm' f (n:ℝ) μ ^ n = ∫⁻x,ENNReal.ofReal (f x)^n ∂μ := by
  rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne'),
    ENNReal.rpow_one]
  simp only [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf _)]

lemma norm_le_iff_natural_moment {f : Ω → ℝ} (hf : ∀x,0 ≤ f x) {n : ℕ} (hn : 0<n)
    (B : ℝ≥0∞) :
    eLpNorm' f (n:ℝ) μ  ≤  B ↔ (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)  ≤  B^n := by
  rw [←natural_moment_norm hf hn]
  simpa only [ENNReal.rpow_natCast] using
    (ENNReal.rpow_le_rpow_iff (show (0:ℝ)<n by exact_mod_cast hn)).symm

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

namespace TensorAtom
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) := by
  change PolySmooth (fun y => A.expression.jointEval F x r ((lam:ℝ)*r) (c ∘ A.labels) (ρ,y))
  rw [TensorExpression.jointEval_slice hF x hr hlam hl h0 h1]
  exact TensorExpression.eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression _

omit [Fintype S] in
lemma spatialBound_nonneg {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) (y : Point d) : 0≤A.spatialBound F x r ρ L j y :=
  spatialEnvelope_nonneg _ _ _

omit [Fintype S] in
lemma spatialBound_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (j : ℕ) : Measurable (A.spatialBound F x r ρ ((lam:ℝ)*r) j) :=
  spatialEnvelope_measurable _ (TensorExpression.eval_polySmooth
    (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression) j

lemma spatialBound_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y)
      (A.spatialBound F x r ρ ((lam:ℝ)*r) j y) := by
  let V := A.expression.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ)
  have hs := TensorExpression.eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression
  have he : A.slice F x r ρ ((lam:ℝ)*r)=fun c => V (c ∘ A.labels) := by
    funext c
    exact A.expression.jointEval_slice hF x hr hlam hl h0 h1 _
  rw [he]
  exact spatialTensor_allSplit_relabel V (fun c => (hs c).smooth) A.labels
    (Equiv.refl (Fin j)) _ _ (by simp) y _ (TensorEnergy.allSplitBound_envelope _)

end TensorAtom

lemma spatialTensor_const_mul {S : Type} {d j : ℕ}
    (V : (S → Fin d) → Point d → ℝ) (hV : ∀c,ContDiff ℝ (⊤:ℕ∞) (V c))
    (a : ℝ) (y : Point d) :
    spatialTensor (fun c z => a*V c z) (List.finRange j) y=
      fun c => a*spatialTensor V (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_const_mul (hV _) _ _ a) y

lemma spatialTensor_sum {S I : Type} [Fintype I] {d j : ℕ}
    (V : I → (S → Fin d) → Point d → ℝ) (hV : ∀i c,ContDiff ℝ (⊤:ℕ∞) (V i c))
    (y : Point d) :
    spatialTensor (fun c z => ∑i,V i c z) (List.finRange j) y=
      fun c => ∑i,spatialTensor (V i) (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_sum Finset.univ (fun i _ => hV i _) _ _) y

namespace TensorSum
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma spatialBound_nonneg {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) (y : Point d) : 0≤A.spatialBound F x r ρ L j y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (polynomialBudget_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _))

omit [Fintype S] in
lemma spatialBound_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (j : ℕ) : Measurable (A.spatialBound F x r ρ ((lam:ℝ)*r) j) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((A.term i).atom.spatialBound_measurable hF x hr hlam hl h0 h1 j))

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) :=
by
  change PolySmooth (fun z => ∑i, ((r*((lam:ℝ)*r))^(A.term i).power*
    (A.term i).coefficient.eval ρ)*(A.term i).atom.slice F x r ρ ((lam:ℝ)*r) c z)
  exact PolySmooth.sum Finset.univ (fun i _ =>
    (PolySmooth.const _).mul ((A.term i).atom.slice_polySmooth hF x hr hlam hl h0 h1 c))

lemma spatialBound_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y)
      (A.spatialBound F x r ρ ((lam:ℝ)*r) j y) := by
  let L := (lam:ℝ)*r
  let a := fun i => (r*L)^(A.term i).power*(A.term i).coefficient.eval ρ
  have hs (i : A.index) (c : S → Fin d) := (A.term i).atom.slice_polySmooth hF x hr hlam hl h0 h1 c
  have he : A.slice F x r ρ L=fun c z => ∑i,a i*(A.term i).atom.slice F x r ρ L c z := rfl
  rw [he,spatialTensor_sum _ (fun i c => contDiff_const.mul (hs i c).smooth)]
  simp_rw [spatialTensor_const_mul _ (fun c => (hs _ c).smooth)]
  apply TensorEnergy.AllSplitBound.finite_sum
  · intro i; exact mul_nonneg (polynomialBudget_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _)
  · intro i
    have ht := (A.term i).atom.spatialBound_allSplit hF x hr hlam hl h0 h1 j y
    apply (TensorEnergy.AllSplitBound.abs_const_mul ht (a i)).mono (mul_nonneg (abs_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _))
    apply mul_le_mul_of_nonneg_right _ (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _)
    exact scaledCoefficient_bound _ _ (by dsimp [L]; positivity)
      (by change r*((lam:ℝ)*r)≤1; nlinarith [hl]) h0 h1.le
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

namespace TensorSum
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma momentBudget_ne_top (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) :
    A.momentBudget d j p≠⊤ := by
  apply ne_of_lt
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
  exact ENNReal.pow_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)) ENNReal.ofReal_lt_top)

end TensorSum
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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MatrixColor
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
open scoped ENNReal

lemma integral_sq_le_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀x,0≤f x)
    {B : ℝ≥0∞} (hB : B≠⊤) (hN : eLpNorm f 2 μ≤B) :
    Integrable (fun x => (f x)^2) μ ∧ (∫x,(f x)^2 ∂μ)≤B.toReal^2 := by
  have hm : MemLp f 2 μ := ⟨hf, lt_of_le_of_lt hN (lt_top_iff_ne_top.mpr hB)⟩
  have hi := hm.integrable_sq
  refine ⟨hi,?_⟩
  have hnorm : eLpNorm f (2 : ℝ≥0∞) μ = eLpNorm' f (2 : ℝ) μ := by
    simpa using (eLpNorm_nnreal_eq_eLpNorm' (p := 2) (by norm_num) (f := f))
  rw [hnorm] at hN
  have hh := (norm_le_iff_natural_moment hf0 (by norm_num : 0<2) B).mp hN
  have he : (∫x,(f x)^2 ∂μ)=(∫⁻x,ENNReal.ofReal (f x)^2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hi.1]
    simp_rw [ENNReal.ofReal_pow (hf0 _)]
  rw [he,←ENNReal.toReal_pow]
  exact ENNReal.toReal_le_toReal (ne_of_lt ((lt_of_le_of_lt hh (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hB)))))
    (ENNReal.pow_ne_top hB) |>.mpr hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma allSplit_integral_frobenius {Ω S I : Type} [MeasurableSpace Ω] [Fintype S]
    [Fintype I] [Nonempty I] {μ : Measure Ω} {d : ℕ}
    {T : (S → Fin d) → Ω → ℝ} {b : Ω → ℝ} {B : ℝ≥0∞}
    (hT : ∀c,Integrable (fun y => (T c y)^2) μ)
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀y,0≤b y) (hB : B≠⊤)
    (hN : eLpNorm b 2 μ≤B) (hs : ∀y,TensorEnergy.AllSplitBound (fun c => T c y) (b y))
    (e : S ≃ I ⊕ Unit) :
    (∑c,∫y,(T c y)^2 ∂μ)≤d*B.toReal^2 := by
  obtain ⟨hi,hv⟩ := integral_sq_le_of_eLpNorm hb hb0 hB hN
  calc
    _ = ∫y,∑c,(T c y)^2 ∂μ := (integral_finsetSum Finset.univ (fun c _ => hT c)).symm
    _ ≤ ∫y,(d:ℝ)*(b y)^2 ∂μ := integral_mono
      (integrable_finsetSum Finset.univ (fun c _ => hT c)) (hi.const_mul _) (fun y => (hs y).frobeniusSquared e)
    _ = (d:ℝ)*(∫y,(b y)^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)

namespace TensorSum

lemma spatialTensor_integrable_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {S : Type} [Fintype S] (A : TensorSum S) (j : ℕ) (c : Fin j ⊕ S → Fin d) :
    Integrable (fun y => (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y c)^2)
      (interpolationLaw F x r ρ) := by
  have hp := spatialTensor_polySmooth (A.slice F x r ρ ((lam:ℝ)*r))
    (A.slice_polySmooth hF x hr hlam hl h0 h1) (List.finRange j) c
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith) (by nlinarith)]
  exact integrable_polynomial_gibbs
    (interpolationPotential_smooth hF x hr.le hl h0 h1).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)
    (hp.smooth.continuous.pow 2) (Appell.HasGrowth.pow (hp.growth []) 2)

lemma spatialTensor_l2 {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) (j : ℕ) :
    (∑c,∫y,(spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y c)^2 ∂interpolationLaw F x r ρ)≤
      d*(A.momentBudget d j 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+j)) := by
  have hR : 0≤(Real.sqrt (1-ρ^2))⁻¹ := by positivity
  have hB : A.momentBudget d j 2*ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(w+j)≠⊤ :=
    ENNReal.mul_ne_top (A.momentBudget_ne_top _ _ _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hh := allSplit_integral_frobenius (A.spatialTensor_integrable_sq hF x hr hlam hl h0 h1 j)
    (A.spatialBound_measurable hF x hr hlam hl h0 h1 j).aestronglyMeasurable
    (A.spatialBound_nonneg _ _ _ _ _ j) hB (A.spatialBound_Lp hF x hr hlam hl h0 h1 hd hw j (by norm_num) (by norm_num))
    (A.spatialBound_allSplit hF x hr hlam hl h0 h1 j) (Equiv.sumAssoc (Fin j) Unit Unit).symm
  convert hh using 1
  · congr 2; exact Subsingleton.elim _ _
  · rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,mul_pow]
    rw [←pow_mul]
    ring
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

lemma matrix_one_energy_eq {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (μ : Measure (Point d)) :
    (∑c,∫y,(spatialTensor A (List.finRange 1) y c)^2 ∂μ)=
      ∑a : Fin d,∑i : Fin d,∑j : Fin d,∫y,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
        (A (Sum.elim (fun _ => a) (fun _ => j))) y)^2 ∂μ := by
  have he := Equiv.sum_comp (matrixOneColor d) (fun c => ∫y,(spatialTensor A (List.finRange 1) y c)^2 ∂μ)
  simp only [Fintype.sum_prod_type] at he
  exact he.symm

namespace TensorSum

lemma slice_directional_integrable_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (a i j : Fin d) :
    Integrable (fun y => (directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2)
      (interpolationLaw F x r ρ) := A.spatialTensor_integrable_sq hF x hr hlam hl h0 h1 1 (matrixOneColor d (a,i,j))

lemma matrix_one_energy_oai {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    (∑a : Fin d,∫y,∑i : Fin d,∑j : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2
       ∂interpolationLaw F x r ρ)≤d*(A.momentBudget d 1 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+1)) := by
  simp_rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => A.slice_directional_integrable_sq hF x hr hlam hl h0 h1 _ i j)),
    integral_finsetSum Finset.univ (fun j _ => A.slice_directional_integrable_sq hF x hr hlam hl h0 h1 _ _ j)]
  rw [←matrix_one_energy_eq]
  exact A.spatialTensor_l2 hF x hr hlam hl h0 h1 hd hw 1
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.TensorSum.matrix_one_energy_oai := @OAI.LogConcaveSampling.TensorSum.matrix_one_energy_oai
