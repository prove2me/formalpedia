-- Prove2me | solution 1 for OAI.LogConcaveSampling.TensorSum.spatialBound_Lp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:51:51.266018+00:00
-- url     : https://prove2.me/submissions/15e799b6-c7d7-4f8d-8bb1-0ac94e226004

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

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
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GrowthInnerGradient
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

lemma growth_inner_gradient {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (v : Point d) :
    HasPolynomialGrowth (fun z => inner ℝ (gradient H z) v) := by
  have hh := growth_of_lipschitz (((innerSL ℝ v).lipschitz).comp hL)
  simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using hh

theorem polynomial_gibbs_ibp {d : ℕ} {H g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hg : ContDiff ℝ 1 g)
    (hgg : HasPolynomialGrowth g) (v : Point d)
    (hgd : HasPolynomialGrowth (fun z => fderiv ℝ g z v)) :
    (∫ z,fderiv ℝ g z v ∂gibbs H)=
      ∫ z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have hgc : Continuous (fun z => fderiv ℝ g z v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hSc : Continuous (fun z => inner ℝ (gradient H z) v) :=
    hL.continuous.inner continuous_const
  have hSg : HasPolynomialGrowth (fun z => (inner ℝ (gradient H z) v)*g z) :=
    Appell.HasGrowth.mul (growth_inner_gradient hL v) hgg
  have hf'g : Integrable (fun z => Real.exp (-H z)*((inner ℝ (gradient H z) v)*g z)) := by
    simpa using integrable_tilted H hH.continuous (hSc.mul hg.continuous) ht hSg 0
  have hfg' : Integrable (fun z => Real.exp (-H z)*fderiv ℝ g z v) := by
    simpa using integrable_tilted H hH.continuous hgc ht hgd 0
  have hfg : Integrable (fun z => Real.exp (-H z)*g z) := by
    simpa using integrable_tilted H hH.continuous hg.continuous ht hgg 0
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (by
      convert! hf'g.neg using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [hD]
      change -(Real.exp (-H z)*inner ℝ (gradient H z) v)*g z=
        -(Real.exp (-H z)*(inner ℝ (gradient H z) v*g z))
      ring) hfg' hfg
    (fun z _ => ((hH.differentiable (by norm_num) z).neg).exp)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa using integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simp only [smul_eq_mul,hh]
end LogConcaveSampling

end UpperProof
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

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetCongrList
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

namespace LogConcaveSampling.JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

lemma jet_congr_on_list (v w : ι → E) (l : List ι) (f : E → ℝ)
    (h : ∀i∈l,v i=w i) : jet v l f=jet w l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change dir (v i) (jet v l f) = dir (w i) (jet w l f)
    rw [h i (by simp)]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
end LogConcaveSampling.JetCalculus

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetMapPositions
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

namespace LogConcaveSampling.JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*}

lemma jet_map_positions (v : ι → E) (e : κ → ι) (l : List κ) (f : E → ℝ) :
    jet v (l.map e) f=jet (v ∘ e) l f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,jet,ih,Function.comp_apply]

lemma jet_finRange (v : ι → E) (l : List ι) (f : E → ℝ) :
    jet v l f=jet (fun k : Fin l.length => v (l.get k)) (List.finRange l.length) f := by
  change jet v l f=jet (v ∘ l.get) (List.finRange l.length) f
  rw [← jet_map_positions]
  congr 1
  exact (List.map_get_finRange l).symm
end LogConcaveSampling.JetCalculus

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

lemma directional_neg {d : ℕ} {f : Point d → ℝ} (hf : Differentiable ℝ f) (v : Point d) :
    directional v (fun x => -f x)=fun x => -directional v f x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.neg).fderiv

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
lemma continuous (hf : PolyC1 f) : Continuous f := hf.smooth.continuous
lemma differentiable (hf : PolyC1 f) : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
lemma directional_continuous (hf : PolyC1 f) (v : Point d) : Continuous (directional v f) :=
  (hf.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
lemma add (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,Appell.HasGrowth.add hf.growth hg.growth,fun v => ?_⟩
  rw [directional_add hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (hf.derivative_growth v) (hg.derivative_growth v)
lemma neg (hf : PolyC1 f) : PolyC1 (fun x => -f x) := by
  refine ⟨hf.smooth.neg,?_,fun v => ?_⟩
  · simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) hf.growth
  · rw [directional_neg hf.differentiable]
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v)
lemma mul (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,Appell.HasGrowth.mul hf.growth hg.growth,fun v => ?_⟩
  rw [directional_mul hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
end PolyC1

lemma adjointCoordinate_pairing {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    (∫x,adjointCoordinate H v f x*g x ∂gibbs H)=∫x,f x*directional v g x ∂gibbs H := by
  have hs : Continuous (directional v H) := (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsg : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  have hi₁ : Integrable (fun z => directional v f z*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hf.directional_continuous v).mul hg.continuous)
    (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
  have hi₂ : Integrable (fun z => f z*directional v g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    (hf.continuous.mul (hg.directional_continuous v))
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
  have hi₃ : Integrable (fun z => (directional v H z*f z)*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hs.mul hf.continuous).mul hg.continuous)
    (Appell.HasGrowth.mul (Appell.HasGrowth.mul hsg hf.growth) hg.growth)
  have hh := polynomial_gibbs_ibp hH ht hL (hf.mul hg).smooth (hf.mul hg).growth v
    ((hf.mul hg).derivative_growth v)
  change (∫x,directional v (fun x => f x*g x) x ∂gibbs H)=_ at hh
  rw [directional_mul hf.differentiable hg.differentiable,integral_add hi₁ hi₂] at hh
  simp only [←directional_gradient,mul_assoc] at hi₃ ⊢ hh
  change (∫x,(-directional v f x+directional v H x*f x)*g x ∂gibbs H)=_
  simp_rw [add_mul,neg_mul,mul_assoc]
  rw [integral_add (f:=fun z => -(directional v f z*g z)) hi₁.neg hi₃,integral_neg]
  linarith

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Lipschitz
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

lemma PolyC1.of_lipschitz {d : ℕ} {f : Point d → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hL : LipschitzWith K f) : PolyC1 f := by
  refine ⟨hf,growth_of_lipschitz hL,fun v => ⟨(K:ℝ)*‖v‖,by positivity,0,fun x => ?_⟩⟩
  have hn := (fderiv ℝ f x).le_opNorm v
  have hb := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  change ‖(fderiv ℝ f x) v‖ ≤ _
  simp only [pow_zero]
  exact hn.trans ((mul_le_mul_of_nonneg_right hb (norm_nonneg v)).trans (by nlinarith [mul_nonneg K.coe_nonneg (norm_nonneg v)]))

lemma polyC1_directional_potential {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H)) (v : Point d) :
    PolyC1 (directional v H) := by
  apply PolyC1.of_lipschitz ((directional_smooth hH v).of_le (by simp))
  have he : (fun x => (innerSL ℝ v) (gradient H x))=directional v H := by
    funext x
    rw [innerSL_apply_apply,real_inner_comm,directional_gradient]
  simpa only [Function.comp_def,he] using (innerSL ℝ v).lipschitz.comp hL

lemma polyC1_adjointCoordinate {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (hf : PolyC1 f) (v : Point d) (hd : PolyC1 (directional v f)) :
    PolyC1 (adjointCoordinate H v f) :=
  hd.neg.add ((polyC1_directional_potential hH hL v).mul hf)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_DirectionalAdjointCoordinate
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

lemma directional_adjointCoordinate {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Point d) :
    directional u (adjointCoordinate H v f)=fun x =>
      adjointCoordinate H v (directional u f) x+directional u (directional v H) x*f x := by
  have hD : Differentiable ℝ (directional v f) := (directional_smooth hf v).differentiable (by simp)
  have hS : Differentiable ℝ (directional v H) := (directional_smooth hH v).differentiable (by simp)
  change directional u (fun x => -directional v f x+directional v H x*f x)=_
  rw [directional_add (f:=fun x => -directional v f x)
    (g:=fun x => directional v H x*f x) hD.neg (hS.mul (hf.differentiable (by simp))),directional_neg hD,
    directional_mul hS (hf.differentiable (by simp)),directional_commute hf u v]
  funext x
  simp only [adjointCoordinate]
  ring

lemma adjointCoordinate_smooth {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Point d) :
    ContDiff ℝ (⊤ : ℕ∞) (adjointCoordinate H v f) :=
  (directional_smooth hf v).neg.add ((directional_smooth hH v).mul hf)

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

lemma directional_prod {d : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => ∏i∈s,f i x)=fun x =>
      ∑i∈s,(∏j∈s.erase i,f j x)*directional v (f i) x := by
  funext x
  have hh := (HasFDerivAt.finsetProd (fun i hi => (hf i hi x).hasFDerivAt)).fderiv
  simpa only [directional,sum_apply,smul_apply,smul_eq_mul] using
    congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh

namespace PolyC1
lemma const {d : ℕ} (c : ℝ) : PolyC1 (fun _ : Point d => c) := by
  refine ⟨contDiff_const,growth_const c,fun v => ?_⟩
  have he : directional v (fun _ : Point d => c)=fun _ => 0 := by
    funext x
    simp [directional]
  rw [he]
  exact growth_const 0

lemma prod {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolyC1 (f i)) : PolyC1 (fun x => ∏i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (d:=d) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self i s)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
end PolyC1

end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma jet_neg {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l (fun x => -f x)=fun x => -JetCalculus.jet v l f x := by
  simpa only [neg_one_mul] using JetCalculus.jet_const_mul hf v l (-1)

theorem jet_adjointCoordinate {d : ℕ} {ι : Type*} [DecidableEq ι]
    {H f : Point d → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) (hl : l.Nodup)
    (u : Point d) :
    JetCalculus.jet v l (adjointCoordinate H u f)=fun x =>
      adjointCoordinate H u (JetCalculus.jet v l f) x+
      ∑s∈l.toFinset.powerset.erase ∅,
        JetCalculus.jet v (l.filter (fun i => i∈s)) (directional u H) x*
        JetCalculus.jet v (l.filter (fun i => i∉s)) f x := by
  have hd := directional_smooth hf u
  have hs := directional_smooth hH u
  change JetCalculus.jet v l (fun x => -directional u f x+directional u H x*f x)=_
  rw [JetCalculus.jet_add hd.neg (hs.mul hf),jet_neg hd,jet_directional hf,
    JetCalculus.jet_mul hs hf v l hl]
  funext x
  dsimp only
  rw [←Finset.add_sum_erase _ _ (by simp : (∅:Finset ι)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty, decide_false, decide_not, Bool.not_false,
    List.filter_false, List.filter_true, JetCalculus.jet]
  simp only [adjointCoordinate]
  ring

theorem jet_tensorAdjoint {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i))
    (b : ι → Point d) (v : κ → Point d) (l : List κ) (hl : l.Nodup) :
    JetCalculus.jet v l (tensorAdjoint H b V)=fun x =>
      tensorAdjoint H b (fun i => JetCalculus.jet v l (V i)) x+
      ∑s∈l.toFinset.powerset.erase ∅,∑i,
        JetCalculus.jet v (l.filter (fun j => j∈s)) (directional (b i) H) x*
        JetCalculus.jet v (l.filter (fun j => j∉s)) (V i) x := by
  unfold tensorAdjoint
  rw [JetCalculus.jet_sum Finset.univ
    (fun i _ => adjointCoordinate_smooth hH (hV i) (b i))]
  simp_rw [jet_adjointCoordinate hH (hV _) v l hl]
  funext x
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MultisetProd
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

lemma PolyC1.multisetProd {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,PolyC1 (f i)) :
    PolyC1 (fun x => (s.map (fun i => f i x)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simpa using PolyC1.const (d:=d) 1
  | @cons a s ih =>
    simpa only [Multiset.map_cons,Multiset.prod_cons] using
      (hf a (Multiset.mem_cons_self _ _)).mul
        (ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi)))

lemma integrable_multiset_sum {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} {μ : Measure (Point d)} (hf : ∀i∈s,Integrable (f i) μ) :
    Integrable (fun x => (s.map (fun i => f i x)).sum) μ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons]
    exact (hf a (Multiset.mem_cons_self _ _)).add
      (ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi)))

lemma integral_multiset_sum {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} {μ : Measure (Point d)} (hf : ∀i∈s,Integrable (f i) μ) :
    (∫x,(s.map (fun i => f i x)).sum ∂μ)=(s.map (fun i => ∫x,f i x ∂μ)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have hs := integrable_multiset_sum s (fun i hi => hf i (Multiset.mem_cons_of_mem hi))
    simp only [Multiset.map_cons,Multiset.sum_cons]
    rw [integral_add (hf a (Multiset.mem_cons_self _ _)) hs,
      ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi))]

lemma directional_multisetProd {d : ℕ} {ι : Type*} [DecidableEq ι] (s : Multiset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => (s.map (fun i => f i x)).prod)=fun x =>
      (s.map (fun i => ((s.erase i).map (fun j => f j x)).prod *
        directional v (f i) x)).sum := by
  funext x
  unfold directional
  rw [fderiv_multiset_prod (fun i hi => hf i hi x)]
  have he : ∀t : Multiset (Point d →L[ℝ] ℝ), t.sum v=(t.map (fun A => A v)).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp [ih]
  rw [he,Multiset.map_map]
  rfl

theorem adjointCoordinate_mixed_product_pairing {d : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] {H f : Point d → ℝ}
    {g : ι → Point d → ℝ} {r : κ → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f)
    (s : Finset ι) (hg : ∀j∈s,PolyC1 (g j))
    (t : Multiset κ) (hr : ∀j∈t,PolyC1 (r j)) (v : Point d) :
    (∫x,adjointCoordinate H v f x*(∏j∈s,g j x)*(t.map (fun k => r k x)).prod ∂gibbs H)=
      (∑j∈s,∫x,f x*directional v (g j) x*(∏k∈s.erase j,g k x)*
        (t.map (fun k => r k x)).prod ∂gibbs H)+
      (t.map (fun j => ∫x,f x*(∏k∈s,g k x)*directional v (r j) x*
        ((t.erase j).map (fun k => r k x)).prod ∂gibbs H)).sum := by
  let G := fun x => ∏j∈s,g j x
  let R := fun x => (t.map (fun j => r j x)).prod
  have hG : PolyC1 G := PolyC1.prod s hg
  have hR : PolyC1 R := PolyC1.multisetProd t hr
  have hiG : Integrable (fun x => f x*directional v G x*R x) (gibbs H) :=
    integrable_polynomial_gibbs hH.continuous ht
      ((hf.continuous.mul (hG.directional_continuous v)).mul hR.continuous)
      ((Appell.HasGrowth.mul hf.growth (hG.derivative_growth v)).mul hR.growth)
  have hiR : Integrable (fun x => f x*G x*directional v R x) (gibbs H) :=
    integrable_polynomial_gibbs hH.continuous ht
      ((hf.continuous.mul hG.continuous).mul (hR.directional_continuous v))
      ((Appell.HasGrowth.mul hf.growth hG.growth).mul (hR.derivative_growth v))
  change (∫x,adjointCoordinate H v f x*G x*R x ∂gibbs H)=_
  simp_rw [mul_assoc (adjointCoordinate H v f _) (G _) (R _)]
  rw [adjointCoordinate_pairing hH ht hL hf (hG.mul hR) v,
    directional_mul hG.differentiable hR.differentiable]
  simp_rw [mul_add,mul_assoc]
  rw [integral_add (by simpa only [mul_assoc] using hiG)
    (by simpa only [mul_assoc] using hiR)]
  congr 1
  · change (∫x,f x*(directional v (fun x => ∏j∈s,g j x) x*R x) ∂gibbs H)=_
    rw [directional_prod s (fun j hj => (hg j hj).differentiable)]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    have hi (j : ι) (hj : j∈s) : Integrable (fun x =>
        f x*((∏k∈s.erase j,g k x)*directional v (g j) x*R x)) (gibbs H) := by
      have hp := PolyC1.prod (s.erase j) (fun k hk => hg k (Finset.mem_of_mem_erase hk))
      exact integrable_polynomial_gibbs hH.continuous ht
        (hf.continuous.mul ((hp.continuous.mul ((hg j hj).directional_continuous v)).mul hR.continuous))
        (Appell.HasGrowth.mul hf.growth (Appell.HasGrowth.mul (Appell.HasGrowth.mul hp.growth ((hg j hj).derivative_growth v)) hR.growth))
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [R]
    ring
  · change (∫x,f x*(G x*directional v (fun x => (t.map (fun k => r k x)).prod) x) ∂gibbs H)=_
    rw [directional_multisetProd t (fun j hj => (hr j hj).differentiable)]
    have he : (fun x => f x*(G x*(t.map (fun j => ((t.erase j).map (fun k => r k x)).prod*
        directional v (r j) x)).sum))=fun x =>
        (t.map (fun j => f x*G x*directional v (r j) x*
          ((t.erase j).map (fun k => r k x)).prod)).sum := by
      funext x
      rw [←Multiset.sum_map_mul_left,←Multiset.sum_map_mul_left]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro j hj
      ring
    rw [he]
    have hhi : ∀j∈t,Integrable (fun x => f x*G x*directional v (r j) x*
        ((t.erase j).map (fun k => r k x)).prod) (gibbs H) := by
      intro j hj
      have hp := PolyC1.multisetProd (t.erase j) (fun k hk => hr k (Multiset.mem_of_mem_erase hk))
      exact integrable_polynomial_gibbs hH.continuous ht
        (((hf.continuous.mul hG.continuous).mul ((hr j hj).directional_continuous v)).mul hp.continuous)
        (Appell.HasGrowth.mul (Appell.HasGrowth.mul (Appell.HasGrowth.mul hf.growth hG.growth) ((hr j hj).derivative_growth v)) hp.growth)
    simpa only [G,mul_assoc] using integral_multiset_sum t hhi
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

lemma prod {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∏i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (d:=d) 1
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MultisetProd2
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

namespace LogConcaveSampling.PolySmooth
variable {d : ℕ} {ι : Type*}

lemma multiset_prod (m : Multiset ι) (f : ι → Point d → ℝ)
    (hf : ∀i∈m,PolySmooth (f i)) :
    PolySmooth (fun x => (m.map (fun i => f i x)).prod) := by
  induction m using Multiset.induction_on with
  | empty => simpa using PolySmooth.const (d:=d) 1
  | @cons i m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons]
    exact (hf i (Multiset.mem_cons_self _ _)).mul
      (ih (fun j hj => hf j (Multiset.mem_cons_of_mem hj)))
end LogConcaveSampling.PolySmooth

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

lemma splitEnvelope_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (hM : 0≤M) (h : AllSplitBound T M) :
    splitEnvelope T ≤ Fintype.card (ProperSplit S)*M := by
  calc
    _ ≤ ∑p : ProperSplit S,M := Finset.sum_le_sum (fun p _ =>
      Bound.norm_le hM (h _ _ (splitEquiv p)))
    _ = _ := by simp

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

lemma natural_moment_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ)
    (hf : ∀i,AEStronglyMeasurable (f i) μ) (hf0 : ∀i x,0 ≤ f i x)
    {n : ℕ} (hn : 0<n) (B : ι → ℝ≥0∞)
    (hB : ∀i,(∫⁻x,ENNReal.ofReal (f i x)^n ∂μ)  ≤  B i^n) :
    (∫⁻x,ENNReal.ofReal (∑i,f i x)^n ∂μ)  ≤  (∑i,B i)^n := by
  apply (norm_le_iff_natural_moment (fun x => Finset.sum_nonneg (fun i _ => hf0 i x)) hn _).mp
  have hnorm {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ) :
      eLpNorm g (n : ℝ≥0∞) μ = eLpNorm' g (n : ℝ) μ := by
    simpa only [ENNReal.coe_natCast, NNReal.coe_natCast] using
      (eLpNorm_nnreal_eq_eLpNorm' (p := (n : ℝ≥0)) (by exact_mod_cast hn.ne'))
  rw [← hnorm (Finset.univ.aestronglyMeasurable_fun_sum (fun i _ => hf i))]
  have hsum := eLpNorm_sum_le (μ:=μ) (s:=Finset.univ) (f:=f)
    (fun i _ => hf i) (show 1 ≤ (n:ℝ≥0∞) by exact_mod_cast hn)
  have he : (fun x => ∑i,f i x)=∑i,f i := by ext x; simp
  rw [he]
  apply hsum.trans
  apply Finset.sum_le_sum
  intro i _
  rw [hnorm (hf i)]
  exact (norm_le_iff_natural_moment (hf0 i) hn _).mpr (hB i)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ProperSplitCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma properSplit_card_le : Fintype.card (ProperSplit S) ≤ 2^Fintype.card S := by
  calc
    _ ≤ Fintype.card (S → Bool) := Fintype.card_subtype_le _
    _ = _ := by simp

lemma measurable_splitMatrix_norm {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c))
    (p : ProperSplit S) : Measurable (fun x => ‖splitMatrix (T x) p‖) := by
  let : MeasurableSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  have : BorelSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  apply Measurable.norm
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => hT _))

lemma moment_splitEnvelope {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c))
    {n : ℕ} (hn : 0<n) (B : ℝ≥0∞)
    (hB : ∀p : ProperSplit S,
      (∫⁻x,ENNReal.ofReal ‖splitMatrix (T x) p‖^n ∂μ) ≤ B^n) :
    (∫⁻x,ENNReal.ofReal (splitEnvelope (T x))^n ∂μ) ≤
      ((2:ℝ≥0∞)^Fintype.card S*B)^n := by
  have hh := natural_moment_sum (μ:=μ) (fun p : ProperSplit S => fun x => ‖splitMatrix (T x) p‖)
    (fun p => (measurable_splitMatrix_norm T hT p).aestronglyMeasurable)
    (fun _ _ => norm_nonneg _) hn (fun _ => B) hB
  apply hh.trans
  apply pow_le_pow_left'
  simpa using mul_le_mul'
    (show (Fintype.card (ProperSplit S):ℝ≥0∞) ≤ 2^Fintype.card S by
      exact_mod_cast properSplit_card_le (S:=S)) (le_refl B)

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_WireStep
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

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma Bound.trace_sq {A : I → I → ℝ} {C : ℝ} (hA : Bound A C) :
    (∑ i,A i i)^2 ≤ (Fintype.card I:ℝ)^2*C := by
  have hh := dot_sq (fun _ : I => (1:ℝ)) (fun i => A i i)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  have hg := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset I)) => hA.entry_sq i i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hg
  exact hh.trans ((mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)).trans_eq (by ring))
end LogConcaveSampling.TensorEnergy
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

lemma Bound.wireStep {I O S X Y : Type*} [Fintype I] [Fintype O] [Fintype S]
    [Fintype X] [Fintype Y] [DecidableEq S] {A : O → I → ℝ} {C : ℝ}
    (hA : Bound A C) (hC : 0≤C) (ei : X ≃ I×S) (eo : Y ≃ O×S) :
    Bound (wireStep A ei eo) C := by
  have hh := (hA.kronecker (bound_identity (I:=S)) hC).reindex eo ei
  change Bound (fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0) C
  simpa only [mul_one] using hh

lemma Bound.trace_abs {I : Type*} [Fintype I] {A : I → I → ℝ} {C : ℝ}
    (hA : Bound A (C^2)) (hC : 0≤C) : |∑i,A i i|≤(Fintype.card I:ℝ)*C := by
  have hh := hA.trace_sq
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)).mp
  simpa only [sq_abs,mul_pow] using hh

end LogConcaveSampling.TensorEnergy
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical

variable {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]

omit [∀k,Fintype (D k)] [DecidableEq (D 0)] in
lemma pathWeight_snoc (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (h : Path (D:=D) n) (y : D (n+1)) :
    pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)=pathWeight A n h*A n y (h (Fin.last n)) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    change A k.val (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.succ.castSucc)
      (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.castSucc.castSucc) = _
    simp only [Fin.snoc_castSucc]
  · simp only [Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc,Fin.val_last]

theorem circuit_path_expansion (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (B : D 0 → D n → ℝ) :
    (∑h : Path (D:=D) n,pathWeight A n h*B (h 0) (h (Fin.last n)))=
      ∑i,∑j,circuit A n j i*B i j := by
  induction n with
  | zero =>
    rw [←(Fin.consEquiv (fun k : Fin 1 => D k.val)).sum_comp]
    simp [pathWeight,circuit,Fintype.sum_prod_type]
  | succ n ih =>
    rw [←(Fin.snocEquiv (fun k : Fin (n+2) => D k.val)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply]
    change (∑y : D (n+1),∑h : Path (D:=D) n,
      pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)*
        B (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (0 : Fin (n+1)).castSucc)
          (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (Fin.last (n+1))))=_
    simp_rw [pathWeight_snoc,Fin.snoc_castSucc,Fin.snoc_last]
    have hh (y : D (n+1)) :
        (∑h : Path (D:=D) n,pathWeight A n h*A n y (h (Fin.last n))*B (h 0) y)=
        ∑i,∑j,circuit A n j i*(A n y j*B i y) := by
      simpa only [mul_assoc] using ih (fun i j => A n y j*B i y)
    simp_rw [hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro y hy
    simp only [circuit,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
end LogConcaveSampling.TensorEnergy

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

lemma spatialEnvelope_nonneg {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : 0≤ spatialEnvelope F j y :=
  TensorEnergy.splitEnvelope_nonneg _

lemma spatialEnvelope_measurable {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    Measurable (spatialEnvelope F j) :=
  TensorEnergy.measurable_splitEnvelope _ (fun c =>
    (spatialTensor_polySmooth F hF (List.finRange j) c).smooth.continuous.measurable)

lemma spatialTensor_allSplit_envelope {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor F l y) (spatialEnvelope F (Fintype.card K) y) := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := spatialTensor_allSplit_relabel F hF (Equiv.refl S) e
    (List.finRange (Fintype.card K)) l hp y _ (TensorEnergy.allSplitBound_envelope _)
  simpa only [Function.comp_def,Equiv.refl_apply,spatialEnvelope] using hh

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
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Vertex
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

section
namespace LogConcaveSampling.TraceOpening

lemma auxiliary_between {n : ℕ} {H : Type*} (left right : H → Fin (n+1))
    (hpair : ∀h,left h < right h) (h : H) :
    level left (Sum.inl (left h))<level left (Sum.inr h) ∧
    level left (Sum.inr h)<level left (Sum.inl (right h)) := by
  have hp := hpair h
  simp only [Fin.lt_def] at hp
  simp only [level]
  omega

theorem all_vertex_splits_nontrivial {n : ℕ} {H : Type*}
    (left right : H → Fin (n+1)) (hpair : ∀h,left h < right h)
    (R : Vertex n H → Vertex n H → Prop)
    (hchain : ∀i : Fin n,R (Sum.inl i.castSucc) (Sum.inl i.succ))
    (hleft : ∀h,R (Sum.inl (left h)) (Sum.inr h))
    (hright : ∀h,R (Sum.inr h) (Sum.inl (right h))) :
    ∀v : Vertex n H,
      (v=Sum.inl 0 ∨ ∃u,R u v ∧ level left u<level left v) ∧
      (v=Sum.inl (Fin.last n) ∨ ∃w,R v w ∧ level left v<level left w) := by
  intro v
  cases v with
  | inr h =>
    exact ⟨Or.inr ⟨_,hleft h,(auxiliary_between left right hpair h).1⟩,
      Or.inr ⟨_,hright h,(auxiliary_between left right hpair h).2⟩⟩
  | inl i =>
    constructor
    · by_cases hi : i=0
      · exact Or.inl (congrArg Sum.inl hi)
      · right
        have hi0 : 0 < (i : Fin (n+1)).val := by
          have : i.val ≠ 0 := fun he => hi (Fin.ext (by simpa only [Fin.val_zero] using he))
          omega
        let j : Fin n := ⟨i.val-1,by omega⟩
        have he : j.succ=i := Fin.ext (by dsimp [j]; omega)
        refine ⟨Sum.inl j.castSucc,?_,?_⟩
        · simpa only [he] using hchain j
        · simp only [level,Fin.val_castSucc]
          dsimp [j]
          omega
    · by_cases hi : i=Fin.last n
      · exact Or.inl (congrArg Sum.inl hi)
      · right
        have hin : i.val<n := by
          have : i.val≠n := fun he => hi (Fin.ext he)
          omega
        let j : Fin n := ⟨i.val,hin⟩
        have he : j.castSucc=i := Fin.ext rfl
        refine ⟨Sum.inl j.succ,?_,?_⟩
        · simpa only [he] using hchain j
        · simp only [level,Fin.val_succ]
          dsimp [j]
          omega

lemma orderKey_strict {V : Type*} [Fintype V] (r : V → ℕ) {u v : V}
    (h : r u < r v) : orderKey r u<orderKey r v := by
  have hu := (Fintype.equivFin V u).isLt
  have hv := (Fintype.equivFin V v).isLt
  dsimp only [orderKey]
  nlinarith

lemma orderKey_div {V : Type*} [Fintype V] (r : V → ℕ) (v : V) :
    orderKey r v/(Fintype.card V+1)=r v := by
  unfold orderKey
  have hv : (Fintype.equivFin V v).val<Fintype.card V+1 :=
    lt_trans (Fintype.equivFin V v).isLt (Nat.lt_succ_self _)
  rw [Nat.mul_comm (r v), Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt hv, Nat.add_zero]

lemma orderKey_injective {V : Type*} [Fintype V] (r : V → ℕ) :
    Function.Injective (orderKey r) := by
  intro u v he
  have hr : r u=r v := by
    simpa only [orderKey_div] using congrArg (fun k => k/(Fintype.card V+1)) he
  have hc : (Fintype.equivFin V u).val=(Fintype.equivFin V v).val := by
    simp only [orderKey,hr] at he
    omega
  exact (Fintype.equivFin V).injective (Fin.ext hc)

theorem ordered_nontrivial_splits {n : ℕ} {H : Type*} [Fintype H]
    (left right : H → Fin (n+1)) (hpair : ∀h,left h < right h)
    (R : Vertex n H → Vertex n H → Prop)
    (hchain : ∀i : Fin n,R (Sum.inl i.castSucc) (Sum.inl i.succ))
    (hleft : ∀h,R (Sum.inl (left h)) (Sum.inr h))
    (hright : ∀h,R (Sum.inr h) (Sum.inl (right h))) :
    ∃ key : Vertex n H → ℕ, Function.Injective key ∧
      ∀v : Vertex n H,
        (v=Sum.inl 0 ∨ ∃u,R u v ∧ key u<key v) ∧
        (v=Sum.inl (Fin.last n) ∨ ∃w,R v w ∧ key v<key w) := by
  refine ⟨orderKey (level left),orderKey_injective _,fun v => ?_⟩
  obtain ⟨hv₁,hv₂⟩ := all_vertex_splits_nontrivial left right hpair R hchain hleft hright v
  constructor
  · rcases hv₁ with h | ⟨u,hu,huv⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,hu,orderKey_strict _ huv⟩
  · rcases hv₂ with h | ⟨w,hw,hvw⟩
    · exact Or.inl h
    · exact Or.inr ⟨w,hw,orderKey_strict _ hvw⟩
end LogConcaveSampling.TraceOpening

end
section
namespace LogConcaveSampling

lemma traceMomentOrder_bounds {d j : ℕ} {c p : ℝ} (hc : 1 ≤ c) (hp : 2≤p) :
    0<traceMomentOrder d j c p ∧ p≤2*(traceMomentOrder d j c p:ℝ) ∧
    ((j:ℝ)+c)*Real.log ((d:ℝ)+1)≤(traceMomentOrder d j c p:ℝ) ∧
    (traceMomentOrder d j c p:ℝ) ≤ c*(p+((j:ℝ)+1)*Real.log ((d:ℝ)+1)) := by
  have ht : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hj : (0:ℝ)≤j := Nat.cast_nonneg j
  have ha : 0≤p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1) := by positivity
  have hlo := Nat.le_ceil (p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))
  have hhi := (Nat.ceil_lt_add_one ha).le
  change (p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))≤(traceMomentOrder d j c p:ℝ) at hlo
  change (traceMomentOrder d j c p:ℝ)≤(p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))+1 at hhi
  have hn : 0<traceMomentOrder d j c p := by
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨hn,?_,?_,?_⟩
  · have := mul_nonneg (by linarith : 0≤(j:ℝ)+c) ht
    linarith
  · linarith
  · have h₁ : (j:ℝ)+c ≤ c*((j:ℝ)+1) := by nlinarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht
    have h₃ := mul_le_mul_of_nonneg_right hc (by linarith : 0≤p)
    nlinarith

lemma traceMomentOrder_polynomial {d j : ℕ} {c p : ℝ} (hc : 1 ≤ c) (hp : 2≤p) :
    (traceMomentOrder d j c p:ℝ) ≤ c*(p+(j:ℝ)+Real.log ((d:ℝ)+1))^2 := by
  have hh := (traceMomentOrder_bounds (d:=d) (j:=j) hc hp).2.2.2
  have ht : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hj : (0:ℝ)≤j := Nat.cast_nonneg j
  have hcross : 0≤(p-1)*Real.log ((d:ℝ)+1) := mul_nonneg (by linarith) ht
  have h1 : p+((j:ℝ)+1)*Real.log ((d:ℝ)+1)≤
      (p+(j:ℝ)+Real.log ((d:ℝ)+1))^2 := by nlinarith [sq_nonneg (p-1),sq_nonneg (j:ℝ)]
  exact hh.trans (mul_le_mul_of_nonneg_left h1 (by linarith))

lemma traceMomentOrder_dimension_root {d j : ℕ} {c p : ℝ}
    (hd : 1≤d) (hc : 1 ≤ c) (hp : 2≤p) :
    (d:ℝ)^(((j:ℝ)+c)/(2*(traceMomentOrder d j c p:ℝ)))≤Real.exp (1/2) := by
  have hs := traceMomentOrder_bounds (d:=d) (j:=j) hc hp
  have hsp : 0<(traceMomentOrder d j c p:ℝ) := by exact_mod_cast hs.1
  have hd0 : 0<(d:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hd)
  have hlog : Real.log (d:ℝ)≤Real.log ((d:ℝ)+1) := Real.log_le_log hd0 (by linarith)
  have hnum : ((j:ℝ)+c)*Real.log (d:ℝ)≤(traceMomentOrder d j c p:ℝ) :=
    (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hs.2.2.1
  rw [Real.rpow_def_of_pos hd0]
  apply Real.exp_le_exp.mpr
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<2*(traceMomentOrder d j c p:ℝ))).mpr
  nlinarith
end LogConcaveSampling

end
section
open scoped Matrix.Norms.L2Operator

namespace LogConcaveSampling.TraceMoment
open Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma hermitian_norm_eigenvalues {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    ‖A‖=‖hA.eigenvalues‖ := by
  calc
    ‖A‖=‖Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))‖ := congrArg norm hA.spectral_theorem
    _=‖hA.eigenvalues‖ := by
      simp only [Unitary.conjStarAlgAut_apply, ←Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal,
        RCLike.ofReal_real_eq_id,Function.id_comp]

lemma hermitian_trace_pow {A : Matrix I I ℝ} (hA : A.IsHermitian) (s : ℕ) :
    (A^s).trace=∑i,(hA.eigenvalues i)^s := by
  have he : A^s=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (hA.eigenvalues^s)) := by
    calc
      A^s=(Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)))^s := congrArg (fun B => B^s) hA.spectral_theorem
      _=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))^s) := (map_pow _ _ _).symm
      _=_ := by simp only [RCLike.ofReal_real_eq_id,Function.id_comp,diagonal_pow]
  rw [he]
  simp only [Unitary.conjStarAlgAut_apply,trace_mul_cycle,Unitary.coe_star_mul_self,
    one_mul,trace_diagonal,Pi.pow_apply]

lemma psd_norm_pow_le_trace_pow {A : Matrix I I ℝ} (hA : A.PosSemidef)
    {s : ℕ} (hs : 0 < s) : ‖A‖^s≤(A^s).trace := by
  cases isEmpty_or_nonempty I with
  | inl hi =>
    have he : A=0 := Subsingleton.elim _ _
    simp [he,hs.ne']
  | inr hi =>
    rw [hermitian_norm_eigenvalues hA.1,hermitian_trace_pow hA.1]
    obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
    have hb : ‖hA.1.eigenvalues‖≤hA.1.eigenvalues i := by
      apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr
      intro j
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg j)] using hmax j (Finset.mem_univ j)
    exact (pow_le_pow_left₀ (norm_nonneg _) hb s).trans
      (Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) s) (Finset.mem_univ i))

theorem rectangular_trace_moment (A : Matrix I J ℝ) {s : ℕ} (hs : 0 < s) :
    ‖A‖^(2*s)≤((A*A.transpose)^s).trace := by
  have hN := l2_opNorm_conjTranspose_mul_self A.conjTranspose
  simp only [conjTranspose_conjTranspose,l2_opNorm_conjTranspose] at hN
  have hh := psd_norm_pow_le_trace_pow (posSemidef_self_mul_conjTranspose A) hs
  rw [hN,←pow_two,←pow_mul] at hh
  simpa only [conjTranspose_eq_transpose_of_trivial] using hh
end LogConcaveSampling.TraceMoment

end
section
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

lemma initial_degree : (initial (P:=P)).degree=Fintype.card P := by
  simp [State.degree,initial]

lemma hitPrimary_degree (S : State P) {i j : P} (hi : i∈S.pending) :
    (hitPrimary S i j).degree=S.degree := by
  have he : (∑k,(Function.update S.derivatives j (i::S.derivatives j) k).length)=
      (∑k,(S.derivatives k).length)+1 := by
    have hl : (fun k => (Function.update S.derivatives j (i::S.derivatives j) k).length)=
        Function.update (fun k => (S.derivatives k).length) j ((S.derivatives j).length+1) := by
      funext k
      by_cases hk : k=j
      · subst k; simp
      · simp [Function.update_of_ne hk]
    rw [hl,Finset.sum_update_of_mem (Finset.mem_univ j),Finset.sdiff_singleton_eq_erase]
    have hs := Finset.add_sum_erase Finset.univ (fun k => (S.derivatives k).length) (Finset.mem_univ j)
    omega
  simp only [State.degree,hitPrimary,he,Finset.card_erase_of_mem hi]
  have hp := Finset.card_pos.mpr ⟨i,hi⟩
  omega

lemma pair_degree (S : State P) {i j : P} (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) :
    (pair S i j).degree=S.degree := by
  have hj' : j∈S.pending.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hp := Finset.card_pos.mpr ⟨j,hj'⟩
  simp only [Finset.card_erase_of_mem hi] at hp
  simp only [State.degree,pair,Multiset.map_cons,Multiset.sum_cons,Hessian.degree,List.length_nil,
    zero_add,Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
  omega

lemma hitHessian_degree (S : State P) {i : P} (hi : i∈S.pending)
    {h : Hessian P} (hh : h∈S.hessians) : (hitHessian S i h).degree=S.degree := by
  have hm := congrArg (fun t : Multiset (Hessian P) => (t.map Hessian.degree).sum)
    (Multiset.cons_erase hh)
  simp only [Multiset.map_cons,Multiset.sum_cons] at hm
  have hp := Finset.card_pos.mpr ⟨i,hi⟩
  simp only [State.degree,hitHessian,Finset.card_erase_of_mem hi,Multiset.map_cons,
    Multiset.sum_cons,Hessian.degree,Hessian.hit,List.length_cons]
  simp only [Hessian.degree] at *
  omega

lemma Step.degree_eq {S T : State P} (h : Step S T) : T.degree=S.degree := by
  cases h with
  | primary i j hi hij => exact hitPrimary_degree S hi
  | pair i j hi hj hij => exact pair_degree S hi hj hij
  | hessian i h hi hh => exact hitHessian_degree S hi hh

theorem reachable_degree {S : State P} (h : Relation.ReflTransGen Step initial S) :
    S.degree=Fintype.card P := by
  induction h with
  | refl => exact initial_degree
  | tail hstep h ih => exact h.degree_eq.trans ih

lemma degree_identity (S : State P) (hp : S.pending=∅) :
    S.degree=(∑j,(S.derivatives j).length)+
      (S.hessians.map (fun h => h.extra.length)).sum+2*S.hessians.card := by
  have hm : (S.hessians.map Hessian.degree).sum=
      (S.hessians.map (fun h => h.extra.length)).sum+2*S.hessians.card := by
    induction S.hessians using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Hessian.degree]
      omega
  simp only [State.degree,hp,Finset.card_empty,zero_add,hm]
  omega

theorem terminal_degree_count {S : State P}
    (h : Relation.ReflTransGen Step initial S) (hp : S.pending=∅) :
    (∑j,(S.derivatives j).length)+(S.hessians.map (fun h => h.extra.length)).sum+
      2*S.hessians.card=Fintype.card P := by
  rw [←degree_identity S hp]
  exact reachable_degree h

omit [Fintype P] in
lemma hessian_degree_lower (S : State P) :
    2*S.hessians.card≤(S.hessians.map Hessian.degree).sum := by
  induction S.hessians using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Hessian.degree]
    omega

lemma branches_length (S : State P) (i : P) (hdeg : S.degree=Fintype.card P) :
    (branches S i).length≤3*Fintype.card P := by
  simp only [branches,List.length_append,List.length_map,Finset.length_toList,Multiset.length_toList]
  have hp : (Finset.univ.erase i).card≤Fintype.card P := by simp
  have hd : S.pending.card≤Fintype.card P := Finset.card_le_univ _
  have hp' : (S.pending.erase i).card≤S.pending.card := Finset.card_erase_le
  have hh := hessian_degree_lower S
  unfold State.degree at hdeg
  omega

omit [Fintype P] [DecidableEq P] in
lemma list_sum_constant {α : Type*} (L : List α) (b : ℕ) :
    (L.map (fun _ => b)).sum=L.length*b := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

lemma expand_length (n : ℕ) (S : State P) (hdeg : S.degree=Fintype.card P) :
    (expand n S).length≤(3*Fintype.card P+1)^n := by
  induction n generalizing S with
  | zero => simp [expand]
  | succ n ih =>
    simp only [expand]
    split_ifs with hp
    · rw [List.length_flatMap]
      have h₁ : ((branches S (Classical.choose hp)).map (fun U => (expand n U).length)).sum≤
          ((branches S (Classical.choose hp)).map (fun _ => (3*Fintype.card P+1)^n)).sum := by
        apply List.sum_le_sum
        intro U hU
        exact ih U ((branches_step S (Classical.choose_spec hp) hU).degree_eq.trans hdeg)
      have h₂ := branches_length S (Classical.choose hp) hdeg
      have hpow := Nat.mul_le_mul_right ((3*Fintype.card P+1)^n) h₂
      change ((branches S (Classical.choose hp)).map (fun U => (expand n U).length)).sum≤
        ((branches S (Classical.choose hp)).map (fun _ => (3*Fintype.card P+1)^n)).sum at h₁
      rw [list_sum_constant] at h₁
      rw [pow_succ]
      exact h₁.trans (hpow.trans (by
        rw [Nat.mul_comm ((3*Fintype.card P+1)^n)]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)))
    · simp only [List.length_singleton]
      exact Nat.one_le_pow _ _ (by omega)

theorem full_expansion_bookkeeping :
    (expand (Fintype.card P) (initial (P:=P))).length≤
      (3*Fintype.card P+1)^(Fintype.card P) ∧
    ∀S∈expand (Fintype.card P) (initial (P:=P)),S.pending=∅ ∧ S.good ∧
      (∑j,(S.derivatives j).length)+(S.hessians.map (fun h => h.extra.length)).sum+
      2*S.hessians.card=Fintype.card P := by
  refine ⟨expand_length _ _ initial_degree,fun S hS => ?_⟩
  have hr := mem_expand_reachable hS
  have ht := mem_expand_terminal (by simp [initial]) hS
  exact ⟨ht,reachable_good hr,terminal_degree_count hr ht⟩
end LogConcaveSampling.AdjointRemoval

end
section
open MeasureTheory
open scoped ENNReal NNReal

namespace LogConcaveSampling.NetworkMoments

theorem lintegral_prod_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → Ω → ℝ≥0∞} {M : ι → ℝ≥0∞}
    (hf : ∀i∈s,AEMeasurable (f i) μ)
    (hm : ∀i∈s,(∫⁻x,(f i x)^s.card ∂μ)≤(M i)^s.card) :
    (∫⁻x,∏i∈s,f i x ∂μ)≤∏i∈s,M i := by
  have hc : 0<(s.card:ℝ) := by exact_mod_cast hs.card_pos
  have hp : (∑_i∈s,1/(s.card:ℝ))=1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hc.ne'
  have hr (z : ℝ≥0∞) : (z^s.card)^(1/(s.card:ℝ))=z := by
    rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul]
    simp only [mul_one_div_cancel hc.ne',ENNReal.rpow_one]
  have hh := ENNReal.lintegral_prod_norm_pow_le s
    (fun i hi => (hf i hi).pow_const s.card) hp
    (fun _ _ => (div_nonneg (by norm_num) hc.le))
  simp only [hr] at hh
  calc
    (∫⁻x,∏i∈s,f i x ∂μ)≤∏i∈s,(∫⁻x,(f i x)^s.card ∂μ)^(1/(s.card:ℝ)) := hh
    _ ≤ ∏i∈s,((M i)^s.card)^(1/(s.card:ℝ)) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact ENNReal.rpow_le_rpow (hm i hi) (by positivity)
    _ = ∏i∈s,M i := by simp only [hr]

end LogConcaveSampling.NetworkMoments

end
end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Inside
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

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
lemma hessian_hit (H : Point d → ℝ) (b : P → Point d) (h : Hessian P) (i : P) :
    hessian H b (h.hit i)=directional (b i) (hessian H b h) := rfl

lemma term_split (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (i : P) (x : Point d) :
    term H b f S x=primary H b f S i x*(∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  unfold term
  congr 1
  exact (Finset.mul_prod_erase Finset.univ (fun j => primary H b f S j x) (Finset.mem_univ i)).symm

omit [Fintype P] in
lemma primary_congr (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S T : State P) (j : P) (hp : j∈S.pending ↔ j∈T.pending)
    (hd : S.derivatives j=T.derivatives j) : primary H b f S j=primary H b f T j := by
  unfold primary
  by_cases hs : j∈S.pending
  · rw [ite_eq_left hs,ite_eq_left (hp.mp hs)]
    congr 1
    unfold inside
    rw [hd]
  · rw [ite_eq_right hs,ite_eq_right (fun ht => hs (hp.mpr ht))]
    unfold inside
    rw [hd]

lemma hitPrimary_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    term H b f (hitPrimary S i j) x=
      inside b f S i x*
      (if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x)*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  have hj : j∈Finset.univ.erase i := by simp [hij.symm]
  rw [term_split H b f _ i x,←Finset.mul_prod_erase (Finset.univ.erase i)
    (fun k => primary H b f (hitPrimary S i j) k x) hj]
  have hi' : primary H b f (hitPrimary S i j) i=inside b f S i := by
    simp [primary,inside,hitPrimary,Function.update_of_ne hij]
  have hj' : primary H b f (hitPrimary S i j) j=
      fun x => if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x := by
    simp only [primary,inside,hitPrimary,Function.update_self,JetCalculus.jet,
      Finset.mem_erase,hij.symm,ne_eq,not_false_eq_true,true_and]
    split_ifs <;> rfl
  have hr : (∏k∈(Finset.univ.erase i).erase j,primary H b f (hitPrimary S i j) k x)=
      ∏k∈(Finset.univ.erase i).erase j,primary H b f S k x := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    apply congrFun (primary_congr H b f (hitPrimary S i j) S k ?_ ?_) x
    · exact ⟨fun ht => (Finset.mem_erase.mp ht).2,fun ht => Finset.mem_erase.mpr ⟨hki,ht⟩⟩
    · exact Function.update_of_ne hkj _ _
  rw [hi',hj',hr]
  dsimp only [hitPrimary]
  ring

lemma pair_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    term H b f (pair S i j) x=
      inside b f S i x*directional (b i) (directional (b j) H) x*inside b f S j x*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  have hj : j∈Finset.univ.erase i := by simp [hij.symm]
  rw [term_split H b f _ i x,←Finset.mul_prod_erase (Finset.univ.erase i)
    (fun k => primary H b f (pair S i j) k x) hj]
  have hi' : primary H b f (pair S i j) i=inside b f S i := by simp [primary,inside,pair]
  have hj' : primary H b f (pair S i j) j=inside b f S j := by simp [primary,inside,pair]
  have hr : (∏k∈(Finset.univ.erase i).erase j,primary H b f (pair S i j) k x)=
      ∏k∈(Finset.univ.erase i).erase j,primary H b f S k x := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    apply congrFun (primary_congr H b f (pair S i j) S k ?_ rfl) x
    exact ⟨fun ht => (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).2,
      fun ht => Finset.mem_erase.mpr ⟨hkj,Finset.mem_erase.mpr ⟨hki,ht⟩⟩⟩
  rw [hi',hj',hr]
  simp only [pair,Multiset.map_cons,Multiset.prod_cons,hessian,JetCalculus.jet]
  ring

lemma hitHessian_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (i : P) (h : Hessian P) (x : Point d) :
    term H b f (hitHessian S i h) x=
      inside b f S i x*(∏j∈Finset.univ.erase i,primary H b f S j x)*
      directional (b i) (hessian H b h) x*
      ((S.hessians.erase h).map (fun g => hessian H b g x)).prod := by
  rw [term_split H b f _ i x]
  have hi' : primary H b f (hitHessian S i h) i=inside b f S i := by
    simp [primary,inside,hitHessian]
  have hr : (∏j∈Finset.univ.erase i,primary H b f (hitHessian S i h) j x)=
      ∏j∈Finset.univ.erase i,primary H b f S j x := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    apply congrFun (primary_congr H b f (hitHessian S i h) S j ?_ rfl) x
    exact ⟨fun ht => (Finset.mem_erase.mp ht).2,fun ht => Finset.mem_erase.mpr ⟨hji,ht⟩⟩
  rw [hi',hr]
  simp only [hitHessian,Multiset.map_cons,Multiset.prod_cons,hessian_hit]
  ring

omit [Fintype P] in
lemma Regular.primary_polyC1 {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) (j : P) : PolyC1 (primary H b f S j) := by
  unfold primary
  split_ifs
  · exact polyC1_adjointCoordinate h.smooth_H h.lipschitz (h.primary_jets j _) (b j)
      (h.primary_jets j (j::S.derivatives j))
  · exact h.primary_jets j _

lemma Regular.term_polyC1 {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) : PolyC1 (term H b f S) :=
  (PolyC1.prod Finset.univ (fun j _ => h.primary_polyC1 S j)).mul
    (PolyC1.multisetProd _ (fun h' _ => h.hessian_jets h'))

lemma Regular.integrable_term {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) : Integrable (term H b f S) (gibbs H) :=
  integrable_polynomial_gibbs h.smooth_H.continuous h.tail (h.term_polyC1 S).continuous (h.term_polyC1 S).growth

omit [Fintype P] in
lemma primary_directional {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) (i j : P) :
    directional (b i) (primary H b f S j)=fun x =>
      (if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x)+
      (if j∈S.pending then directional (b i) (directional (b j) H) x*inside b f S j x else 0) := by
  unfold primary
  split_ifs with hj
  · exact directional_adjointCoordinate h.smooth_H (JetCalculus.smooth_jet (h.smooth_f j) b _) _ _
  · funext x; simp
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

lemma primary_branch_integrand {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    inside b f S i x*directional (b i) (primary H b f S j) x*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun g => hessian H b g x)).prod=
      term H b f (hitPrimary S i j) x+(if j∈S.pending then term H b f (pair S i j) x else 0) := by
  rw [primary_directional h,hitPrimary_term _ _ _ _ hij]
  by_cases hj : j∈S.pending
  · simp only [hj,ite_true,pair_term _ _ _ _ hij]
    ring
  · simp only [hj,ite_false,add_zero]

lemma pending_sum {S : State P} (i : P) (F : P → ℝ) :
    (∑j∈Finset.univ.erase i,if j∈S.pending then F j else 0)=∑j∈S.pending.erase i,F j := by
  rw [←Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]

theorem integral_one_step {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) {i : P} (hi : i∈S.pending) :
    (∫x,term H b f S x ∂gibbs H)=
      ((branches S i).map (fun T => ∫x,term H b f T x ∂gibbs H)).sum := by
  have he := adjointCoordinate_mixed_product_pairing
    (h.smooth_H.of_le (by simp)) h.tail h.lipschitz (h.primary_jets i (S.derivatives i))
    (Finset.univ.erase i) (fun j _ => h.primary_polyC1 S j)
    S.hessians (fun g _ => h.hessian_jets g) (b i)
  have hleft : (fun x => adjointCoordinate H (b i) (inside b f S i) x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun g => hessian H b g x)).prod)=term H b f S := by
    funext x
    rw [term_split H b f S i x]
    simp only [primary,hi,ite_true]
  change (∫x,adjointCoordinate H (b i) (inside b f S i) x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=_ at he
  rw [hleft] at he
  rw [he]
  have hp (j : P) (hj : j∈Finset.univ.erase i) :
      (∫x,inside b f S i x*directional (b i) (primary H b f S j) x*
        (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
        (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=
      (∫x,term H b f (hitPrimary S i j) x ∂gibbs H)+
        (if j∈S.pending then ∫x,term H b f (pair S i j) x ∂gibbs H else 0) := by
    have hij := (Finset.mem_erase.mp hj).1.symm
    simp_rw [primary_branch_integrand h S hij]
    by_cases hj' : j∈S.pending
    · simp only [hj',ite_true]
      exact integral_add (h.integrable_term _) (h.integrable_term _)
    · simp only [hj',ite_false,add_zero]
  have hs : (∑j∈Finset.univ.erase i,∫x,inside b f S i x*directional (b i) (primary H b f S j) x*
        (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
        (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=
      (∑j∈Finset.univ.erase i,∫x,term H b f (hitPrimary S i j) x ∂gibbs H)+
      (∑j∈S.pending.erase i,∫x,term H b f (pair S i j) x ∂gibbs H) := by
    rw [Finset.sum_congr rfl hp,Finset.sum_add_distrib,pending_sum]
  simp only [inside] at hs
  rw [hs]
  have hh : (S.hessians.map (fun g => ∫x,inside b f S i x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*directional (b i) (hessian H b g) x*
      ((S.hessians.erase g).map (fun g' => hessian H b g' x)).prod ∂gibbs H)).sum=
      (S.hessians.map (fun g => ∫x,term H b f (hitHessian S i g) x ∂gibbs H)).sum := by
    simp_rw [hitHessian_term]
  simp only [inside] at hh
  rw [hh]
  simp only [branches,List.map_append,List.map_map,List.sum_append,Function.comp_def]
  have hfins (s : Finset P) (F : P → ℝ) : (s.toList.map F).sum=∑j∈s,F j := by
    simp
  rw [hfins,hfins]
  congr 1
  have hh := congrArg (fun ms : Multiset (Hessian P) =>
    (ms.map (fun g => ∫x,term H b f (hitHessian S i g) x ∂gibbs H)).sum) S.hessians.coe_toList
  simp

omit [Fintype P] [DecidableEq P] in
lemma list_sum_map_flatMap {α β : Type*} (L : List α) (B : α → List β) (F : β → ℝ) :
    ((L.flatMap B).map F).sum=(L.map (fun a => ((B a).map F).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

theorem integral_expand {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (n : ℕ) (S : State P) :
    (∫x,term H b f S x ∂gibbs H)=
      ((expand n S).map (fun T => ∫x,term H b f T x ∂gibbs H)).sum := by
  induction n generalizing S with
  | zero => simp [expand]
  | succ n ih =>
    simp only [expand]
    split_ifs with hp
    · rw [list_sum_map_flatMap,integral_one_step h S (Classical.choose_spec hp)]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact ih T
    · simp

lemma term_terminal (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (hS : S.pending=∅) :
    term H b f S=fun x => (∏j,JetCalculus.jet b (S.derivatives j) (f j) x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  funext x
  simp [term,primary,inside,hS]

theorem actual_adjoint_expansion {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) :
    (∫x,(∏j,adjointCoordinate H (b j) (f j) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∫x,(∏j,JetCalculus.jet b (S.derivatives j) (f j) x)*
          (S.hessians.map (fun h => hessian H b h x)).prod ∂gibbs H)).sum := by
  have he := integral_expand h (Fintype.card P) initial
  have hi : term H b f initial=fun x => ∏j,adjointCoordinate H (b j) (f j) x := by
    funext x
    simp [term,primary,inside,initial,JetCalculus.jet]
  rw [hi] at he
  rw [he]
  apply congrArg List.sum
  apply List.map_congr_left
  intro S hS
  rw [term_terminal H b f S (mem_expand_terminal (by simp [initial]) hS)]
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P]

lemma product_tensorAdjoint (H : Point d → ℝ) (b : I → Point d)
    (f : P → I → Point d → ℝ) (x : Point d) :
    (∏p,tensorAdjoint H b (f p) x)=
      ∑a : P → I,∏p,adjointCoordinate H (b (a p)) (f p (a p)) x := by
  classical
  simp only [tensorAdjoint]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]

theorem tensor_actual_adjoint_expansion
    {H : Point d → ℝ} {b : I → Point d} {f : P → I → Point d → ℝ}
    {K : ℝ≥0}
    (h : ∀a : P → I,Regular H (fun p => b (a p)) (fun p => f p (a p)) K) :
    (∫x,(∏p,tensorAdjoint H b (f p) x) ∂gibbs H)=
      ∑a : P → I,((expand (Fintype.card P) initial).map (fun S =>
        ∫x,(∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (f p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  classical
  simp_rw [product_tensorAdjoint]
  have hi (a : P → I) : Integrable
      (fun x => ∏p,adjointCoordinate H (b (a p)) (f p (a p)) x) (gibbs H) := by
    have hh := (h a).integrable_term initial
    have he : term H (fun p => b (a p)) (fun p => f p (a p)) initial=
        fun x => ∏p,adjointCoordinate H (b (a p)) (f p (a p)) x := by
      funext x
      simp [term,primary,inside,initial,JetCalculus.jet]
    rwa [he] at hh
  rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
  exact Finset.sum_congr rfl (fun a _ => actual_adjoint_expansion (h a))

theorem tensor_actual_adjoint_expansion_branch_first
    {H : Point d → ℝ} {b : I → Point d} {f : P → I → Point d → ℝ}
    {K : ℝ≥0}
    (h : ∀a : P → I,Regular H (fun p => b (a p)) (fun p => f p (a p)) K) :
    (∫x,(∏p,tensorAdjoint H b (f p) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∑a : P → I,∫x,(∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (f p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  classical
  rw [tensor_actual_adjoint_expansion h]
  generalize expand (Fintype.card P) (initial (P:=P)) = L
  induction L with
  | nil => simp
  | cons S L ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_AdjointMatrix
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

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma regular_of_polySmooth {d : ℕ} {P : Type*}
    {H : Point d → ℝ} {f : P → Point d → ℝ} (b : P → Point d) {K : ℝ≥0}
    (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : ∀p,PolySmooth (f p)) :
    Regular H b f K := by
  refine ⟨hH.smooth,ht,hL,fun p => (hf p).smooth,
    fun p l => ((hf p).jet b l).polyC1,?_⟩
  intro h
  exact (((hH.directional (b h.second)).directional (b h.first)).jet b h.extra).polyC1

end LogConcaveSampling.AdjointRemoval

namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem hessian_distinguished_neighbors {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    destination hS (h : Hessian P).first=Sum.inr h ∧
    destination hS (h : Hessian P).second=Sum.inr h ∧
    (h : Hessian P).first≠(h : Hessian P).second := by
  have hf : (h : Hessian P).first∈ports S (Sum.inr h) := by
    simp [ports,Hessian.tokens]
  have hs : (h : Hessian P).second∈ports S (Sum.inr h) := by
    simp [ports,Hessian.tokens]
  have lift (i : P) (hi : i∈ports S (Sum.inr h)) : destination hS i=Sum.inr h := by
    let p : Port S := ⟨Sum.inr h,(ports S (Sum.inr h)).mkToType i ⟨0,Multiset.count_pos.mpr hi⟩⟩
    exact destination_label hS p
  exact ⟨lift _ hf,lift _ hs,(reachable_good (mem_expand_reachable hS)).2 h Multiset.coe_mem⟩
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

lemma adjacent_ne (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    {u v : TargetVertex S} (h : Adjacent hS u v) : u≠v := by
  intro he
  rcases h with ⟨k,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ | ⟨i,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · have hh : k.castSucc=k.succ := Sum.inl.inj he
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega
  · have hh : k.succ=k.castSucc := Sum.inl.inj he
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega
  · exact destination_primary_ne hS he.symm rfl
  · exact destination_primary_ne hS he rfl

theorem actual_removal_graph_order
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial) :
    ∃ key : TargetVertex S → ℕ, Function.Injective key ∧
      (∀u v,Adjacent hS u v → key u≠key v) ∧
      ∀v : TargetVertex S,
        (v=Sum.inl 0 ∨ ∃u,Adjacent hS u v ∧ key u<key v) ∧
        (v=Sum.inl (Fin.last n) ∨ ∃w,Adjacent hS v w ∧ key v<key w) := by
  let left (h : S.hessians) : Fin (n+1) := min (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second
  let right (h : S.hessians) : Fin (n+1) := max (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second
  have hp (h : S.hessians) : left h < right h := by
    have hh := (hessian_distinguished_neighbors hS h).2.2
    exact min_lt_max.mpr hh
  have hchain (k : Fin n) : Adjacent hS (Sum.inl k.castSucc) (Sum.inl k.succ) :=
    Or.inl ⟨k,Or.inl ⟨rfl,rfl⟩⟩
  have hleft (h : S.hessians) : Adjacent hS (Sum.inl (left h)) (Sum.inr h) := by
    obtain ⟨hf,hs,_⟩ := hessian_distinguished_neighbors hS h
    refine Or.inr ⟨left h,Or.inl ⟨rfl,?_⟩⟩
    cases min_choice (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second with
    | inl he => exact (he ▸ hf).symm
    | inr he => exact (he ▸ hs).symm
  have hright (h : S.hessians) : Adjacent hS (Sum.inr h) (Sum.inl (right h)) := by
    obtain ⟨hf,hs,_⟩ := hessian_distinguished_neighbors hS h
    refine Or.inr ⟨right h,Or.inr ⟨rfl,?_⟩⟩
    cases max_choice (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second with
    | inl he => exact (he ▸ hf).symm
    | inr he => exact (he ▸ hs).symm
  obtain ⟨key,hkey,horder⟩ := TraceOpening.ordered_nontrivial_splits left right hp
    (Adjacent hS) hchain hleft hright
  exact ⟨key,hkey,fun u v huv hEq => adjacent_ne hS huv (hkey hEq),horder⟩
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_ColoringSplit
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

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped BigOperators

variable {d : ℕ} {P C : Type*} [Fintype P] [DecidableEq P] [Fintype C]

omit [Fintype C] in

theorem branch_factor_polySmooth (S : State P) {H : Point d → ℝ}
    (hH : PolySmooth H) (b : P → Point d) (f : P → Point d → ℝ)
    (hf : ∀p,PolySmooth (f p)) :
    PolySmooth (fun x =>
      (∏p,JetCalculus.jet b (S.derivatives p) (f p) x)*
      (S.hessians.map (fun h => hessian H b h x)).prod) := by
  apply (PolySmooth.prod Finset.univ (fun p _ => (hf p).jet b (S.derivatives p))).mul
  apply PolySmooth.multiset_prod
  intro h _
  exact (((hH.directional (b h.second)).directional (b h.first)).jet b h.extra)

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped BigOperators NNReal

variable {d : ℕ} {P I T : Type*} [Fintype P] [DecidableEq P] [Fintype I] [Fintype T]

theorem parametrized_adjoint_expansion
    {H : Point d → ℝ} (b : I → Point d) (F : T → P → I → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀t p i,PolySmooth (F t p i)) :
    (∫x,(∑t,∏p,tensorAdjoint H b (F t p) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∑t,∑a : P → I,∫x,
          (∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (F t p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  have hi (t : T) : Integrable (fun x => ∏p,tensorAdjoint H b (F t p) x) (gibbs H) :=
    (PolySmooth.prod Finset.univ (fun p _ => hH.tensorAdjoint (hF t p) b)).integrable
      hH.smooth.continuous ht
  rw [integral_finsetSum Finset.univ (fun t _ => hi t)]
  have he (t : T) := tensor_actual_adjoint_expansion_branch_first
    (fun a : P → I => regular_of_polySmooth (fun p => b (a p)) hH ht hK (fun p => hF t p (a p)))
  simp_rw [he]
  generalize expand (Fintype.card P) (initial (P:=P))=L
  induction L with
  | nil => simp
  | cons S L ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitBoundUpto
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

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

lemma circuit_bound_upto {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) (C : ℕ → ℝ) (n : ℕ)
    (hC : ∀k<n,0≤C k) (hA : ∀k<n,Bound (A k) (C k)) :
    Bound (circuit A n) (∏k∈Finset.range n,C k) := by
  induction n with
  | zero => simpa only [circuit,Finset.range_zero,Finset.prod_empty] using (bound_identity (I:=D 0))
  | succ n ih =>
    have hi := ih (fun k hk => hC k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      (fun k hk => hA k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    simpa only [circuit,Finset.prod_range_succ,mul_comm] using
      (hA n (Nat.lt_succ_self n)).comp hi (hC n (Nat.lt_succ_self n))

theorem closed_wire_circuit_bound_upto
    {D I O S : ℕ → Type*} [∀k,Fintype (D k)] [∀k,Fintype (I k)]
    [∀k,Fintype (O k)] [∀k,Fintype (S k)] [∀k,DecidableEq (S k)]
    [DecidableEq (D 0)]
    (A : ∀k,O k → I k → ℝ) (C : ℕ → ℝ)
    (ei : ∀k,D k ≃ I k×S k) (eo : ∀k,D (k+1) ≃ O k×S k)
    (n : ℕ) (hC : ∀k<n,0≤C k) (hA : ∀k<n,Bound (A k) ((C k)^2))
    (close : D 0 ≃ D n) :
    |∑i,circuit (fun k => wireStep (A k) (ei k) (eo k)) n (close i) i|≤
      (Fintype.card (D 0):ℝ)*(∏k∈Finset.range n,C k) := by
  have hlocal (k : ℕ) (hk : k<n) : Bound (wireStep (A k) (ei k) (eo k)) ((C k)^2) :=
    (hA k hk).wireStep (sq_nonneg _) (ei k) (eo k)
  have hh := (circuit_bound_upto _ (fun k => (C k)^2) n (fun k _ => sq_nonneg _) hlocal).reindex
    close (Equiv.refl (D 0))
  rw [Finset.prod_pow] at hh
  exact hh.trace_abs (Finset.prod_nonneg (fun k hk => hC k (Finset.mem_range.mp hk)))
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_History
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

namespace LogConcaveSampling.Frontier
open scoped Classical

variable {E C : Type*} (a b : E → ℕ)

theorem sum_consistent_histories [Fintype E] [Fintype C] {n : ℕ}
    (hab : ∀e,a e<b e) (han : ∀e,a e≤n)
    (F : History (C:=C) a b n → ℝ) :
    (∑h : History (C:=C) a b n,if Consistent a b h then F h else 0)=
      ∑c : E → C,F (historyOf a b c) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (Consistent a b)]
  have hz : (∑i : {h : History (C:=C) a b n // ¬Consistent a b h},
      if Consistent a b i.val then F i.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [i.property,ite_false]
  rw [hz,add_zero]
  simp only [Subtype.property,ite_true]
  exact ((historyEquiv (C:=C) a b hab han).sum_comp (fun h => F h.val)).symm
end LogConcaveSampling.Frontier
namespace LogConcaveSampling.Frontier
open scoped BigOperators Classical
open TensorEnergy

variable {E C : Type*} [Fintype E] [Fintype C]
    (a b : E → ℕ) (hab : ∀e,a e<b e)

omit [Fintype E] [Fintype C] in
lemma consistent_iff_spectators {n : ℕ} (h : History (C:=C) a b n) :
    Consistent a b h ↔ ∀k : Fin n,
      (outputCoordinates a b hab k.val (h k.succ)).2 =
      (inputCoordinates a b hab k.val (h k.castSucc)).2 := by
  constructor
  · intro hh k
    funext e
    exact hh k.val k.isLt e
  · intro hh k hk e
    exact congrFun (hh ⟨k,hk⟩) e

omit [Fintype C] in

lemma pathWeight_graphStep
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ)
    (n : ℕ) (h : History (C:=C) a b n) :
    pathWeight (D:=fun k => Live a b k → C) (graphStep a b hab A) n h =
      if Consistent a b h then
        ∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
          (inputCoordinates a b hab k.val (h k.castSucc)).1
      else 0 := by
  classical
  by_cases hc : Consistent a b h
  · rw [ite_eq_left hc]
    unfold pathWeight graphStep wireStep
    exact Finset.prod_congr rfl (fun k _ => by
      rw [ite_eq_left ((consistent_iff_spectators a b hab h).mp hc k),mul_one])
  · rw [ite_eq_right hc]
    have he : ∃k : Fin n,
      (outputCoordinates a b hab k.val (h k.succ)).2 ≠
      (inputCoordinates a b hab k.val (h k.castSucc)).2 := by
      simpa only [not_forall] using
        (mt (consistent_iff_spectators a b hab h).mpr hc)
    obtain ⟨k,hk⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [graphStep,wireStep,ite_eq_right hk,mul_zero]

theorem coordinate_sum_eq_circuit
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (n : ℕ)
    (han : ∀e,a e≤n) (B : (Live a b 0 → C) → (Live a b n → C) → ℝ) :
    (∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
      B (fun e => c e.val) (fun e => c e.val)) =
    ∑i,∑j,circuit (D:=fun k => Live a b k → C) (graphStep a b hab A) n j i*B i j := by
  have hs := sum_consistent_histories (C:=C) a b hab han
    (fun h => (∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
      (inputCoordinates a b hab k.val (h k.castSucc)).1)*B (h 0) (h (Fin.last n)))
  have hp := circuit_path_expansion (D:=fun k => Live a b k → C) (graphStep a b hab A) n B
  have hs' : (∑h : History (C:=C) a b n,if Consistent a b h then
      (∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
        (inputCoordinates a b hab k.val (h k.castSucc)).1)*B (h 0) (h (Fin.last n)) else 0)=
      (∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
        B (fun e => c e.val) (fun e => c e.val)) := hs
  rw [←hs',←hp]
  apply Finset.sum_congr rfl
  intro h hh
  rw [pathWeight_graphStep]
  split_ifs <;> simp only [zero_mul]

end LogConcaveSampling.Frontier
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

lemma emit_le_length (first last : V) (q : ℕ) (e : Edge (U:=U) q) :
    emit key src dst first last q e≤length key := by
  rcases e with e | (i|i)
  · exact (min_le_left _ _).trans (key_lt_length key (src e))
  · exact Nat.zero_le _
  · exact key_lt_length key last

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

lemma incident_sides (first last : V) (q : ℕ) {u v : V}
    (h : Adjacent src dst u v) (huv : key u<key v) :
    Nonempty (Frontier.Outgoing (emit key src dst first last q) (key u)) ∧
    Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v)) := by
  obtain ⟨e,he⟩ := h
  rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · constructor
    · exact ⟨⟨Sum.inl e,by simp only [emit,hs,ht,min_eq_left (Nat.add_le_add_right huv.le 1)]⟩⟩
    · exact ⟨⟨Sum.inl e,by simp only [absorb,hs,ht,max_eq_right (Nat.add_le_add_right huv.le 1)]⟩⟩
  · constructor
    · exact ⟨⟨Sum.inl e,by simp only [emit,hs,ht,min_eq_right (Nat.add_le_add_right huv.le 1)]⟩⟩
    · exact ⟨⟨Sum.inl e,by simp only [absorb,hs,ht,max_eq_left (Nat.add_le_add_right huv.le 1)]⟩⟩

theorem factor_splits_nonempty (first last : V) (q : ℕ) (hq : 0<q)
    (horder : ∀v,(v=first ∨ ∃u,Adjacent src dst u v ∧ key u<key v) ∧
      (v=last ∨ ∃w,Adjacent src dst v w ∧ key v<key w)) (v : V) :
    Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v)) ∧
    Nonempty (Frontier.Outgoing (emit key src dst first last q) (key v)) := by
  obtain ⟨hi,ho⟩ := horder v
  constructor
  · rcases hi with rfl | ⟨u,hu,hk⟩
    · exact ⟨⟨Sum.inr (Sum.inl ⟨0,hq⟩),rfl⟩⟩
    · exact (incident_sides key src dst first last q hu hk).2
  · rcases ho with rfl | ⟨w,hw,hk⟩
    · exact ⟨⟨Sum.inr (Sum.inr ⟨0,hq⟩),rfl⟩⟩
    · exact (incident_sides key src dst first last q hw hk).1
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

lemma internal_adjacent (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (e : InternalEdge β) :
    Adjacent hS (edgeSource (S:=S) β e) (edgeTarget hS β e) := by
  rcases e with ⟨k,i⟩ | i
  · exact Or.inl ⟨k,Or.inl ⟨rfl,rfl⟩⟩
  · exact Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩

lemma internal_source_ne (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (e : InternalEdge β) :
    edgeSource (S:=S) β e ≠ edgeTarget hS β e :=
  adjacent_ne hS (internal_adjacent hS β e)

lemma adjacent_has_edge (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) {u v : TargetVertex S} (h : Adjacent hS u v) :
    GraphSchedule.Adjacent (edgeSource (S:=S) β) (edgeTarget hS β) u v := by
  rcases h with ⟨k,h⟩ | ⟨i,h⟩
  · refine ⟨Sum.inl ⟨k,⟨0,hβ k⟩⟩,?_⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · refine ⟨Sum.inr i,?_⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U C : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

lemma closing_iff (first last : V) (q : ℕ) (c : Edge (U:=U) q → C) :
    (fun e : Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) (length key) => c e.val)=
        close key src dst first last q
          (fun e : Frontier.Live (emit key src dst first last q)
            (absorb key src dst first last q) 0 => c e.val) ↔
    ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i)) := by
  constructor
  · intro h i
    exact congrFun h ⟨Sum.inr (Sum.inr i),key_lt_length key last,Nat.lt_succ_self _⟩
  · intro h
    funext e
    obtain ⟨i,rfl⟩ := (outputEdges key src dst first last q).symm.surjective e
    exact h i

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqC
attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqC
theorem sum_closed_coordinates [Fintype U] [Fintype C]
    (first last : V) (q : ℕ) (F : (Edge (U:=U) q → C) → ℝ) :
    (∑c : Edge (U:=U) q → C,F c*
      (if (fun e : Frontier.Live (emit key src dst first last q)
        (absorb key src dst first last q) (length key) => c e.val)=
          close key src dst first last q
            (fun e : Frontier.Live (emit key src dst first last q)
              (absorb key src dst first last q) 0 => c e.val) then 1 else 0))=
      ∑c : U ⊕ Fin q → C,F (duplicate c) := by
  simp_rw [closing_iff,mul_ite,mul_one,mul_zero]
  let P (c : Edge (U:=U) q → C) := ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i))
  rw [←Fintype.sum_subtype_add_sum_subtype P]
  have hz : (∑i : {c : Edge (U:=U) q → C // ¬P c},if P i.val then F i.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [i.property,ite_false]
  change (∑i : {c : Edge (U:=U) q → C // P c},if P i.val then F i.val else 0)+
    (∑i : {c : Edge (U:=U) q → C // ¬P c},if P i.val then F i.val else 0)=_
  rw [hz,add_zero]
  simp only [Subtype.property,ite_true]
  exact ((cutColorEquiv (U:=U) (C:=C) q).sum_comp (fun c => F c.val)).symm
end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_RankEquiv
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

namespace LogConcaveSampling.Frontier
open scoped BigOperators Classical
open TensorEnergy

variable {E C : Type*} [Fintype E] [Fintype C]
    (a b : E → ℕ) (hab : ∀e,a e<b e)
include hab in

theorem coordinate_contraction_bound_upto
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (M : ℕ → ℝ)
    (n : ℕ) (hM : ∀k<n,0≤M k) (hA : ∀k<n,Bound (A k) ((M k)^2))
    (han : ∀e,a e≤n) (close : (Live a b 0 → C) ≃ (Live a b n → C)) :
    |∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Live a b n => c e.val)=close (fun e : Live a b 0 => c e.val)
        then 1 else 0)| ≤
      (Fintype.card (Live a b 0 → C):ℝ)*(∏k∈Finset.range n,M k) := by
  rw [coordinate_sum_eq_circuit a b hab A n han
    (fun i j => if j=close i then 1 else 0)]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact closed_wire_circuit_bound_upto (D:=fun k => Live a b k → C)
    (I:=fun k => Incoming b k → C) (O:=fun k => Outgoing a k → C)
    (S:=fun k => Spectator a b k → C) A M
    (inputCoordinates a b hab) (outputCoordinates a b hab) n hM hA close
end LogConcaveSampling.Frontier
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqUp
attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqUp
theorem scheduled_coordinate_bound_upto (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k<length key,0≤M k) (hA : ∀k<length key,Bound (A k) ((M k)^2)) :
    |∑c : Edge (U:=U) q → Fin d,
      (∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Frontier.Live (emit key src dst first last q)
          (absorb key src dst first last q) (length key) => c e.val)=
        close key src dst first last q
          (fun e : Frontier.Live (emit key src dst first last q)
            (absorb key src dst first last q) 0 => c e.val) then 1 else 0)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  calc
    _ ≤ (Fintype.card (Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) 0 → Fin d):ℝ)*
        (∏k∈Finset.range (length key),M k) := by
      exact Frontier.coordinate_contraction_bound_upto (E:=Edge (U:=U) q) (C:=Fin d)
        (emit key src dst first last q) (absorb key src dst first last q)
        (emit_lt_absorb key src dst hkey hne first last q) A M (length key) hM hA
        (emit_le_length key src dst first last q) (close key src dst first last q)
    _ = _ := by
      rw [Fintype.card_fun,Fintype.card_fin,
        Fintype.card_congr (inputEdges key src dst first last q),Fintype.card_fin,Nat.cast_pow]
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqRUp
attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqRUp
theorem reduced_coordinate_bound_upto (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k<length key,0≤M k) (hA : ∀k<length key,Bound (A k) ((M k)^2)) :
    |∑c : U ⊕ Fin q → Fin d,
      ∏k : Fin (length key),A k.val (fun e => duplicate c e.val) (fun e => duplicate c e.val)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  rw [←sum_closed_coordinates key src dst first last q
    (fun c => ∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))]
  exact scheduled_coordinate_bound_upto key src dst hkey hne first last q d A M hM hA
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.TraceOpening
open scoped Classical

variable {V : Type*} [Fintype V]

lemma rankEquiv_lt (key : V → ℕ) (hkey : Function.Injective key) (u v : V) :
    rankEquiv key hkey u < rankEquiv key hkey v ↔ key u < key v := by
  let : LinearOrder V := LinearOrder.lift' key hkey
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.lt_iff_lt

theorem compress_order (key : V → ℕ) (hkey : Function.Injective key) :
    ∃e : V ≃ Fin (Fintype.card V), ∀u v,(e u).val < (e v).val ↔ key u<key v :=
  ⟨rankEquiv key hkey,rankEquiv_lt key hkey⟩
end LogConcaveSampling.TraceOpening
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [Nonempty V]

lemma product_stages (e : V ≃ Fin (Fintype.card V)) {R : Type*} [CommMonoid R] (f : ℕ → R) :
    (∏k : Fin (length (fun v => (e v).val)),f k.val)=∏v,f (e v).val :=
  Eq.symm ((stageEquiv e).prod_comp (fun k => f k.val))

lemma product_stage_range (e : V ≃ Fin (Fintype.card V)) {R : Type*} [CommMonoid R] (f : ℕ → R) :
    (∏k∈Finset.range (length (fun v => (e v).val)),f k)=∏v,f (e v).val := by
  rw [←Fin.prod_univ_eq_prod_range]
  exact product_stages e f
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqRank
attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqRank
theorem ranked_coordinate_bound (e : V ≃ Fin (Fintype.card V)) (src dst : U → V)
    (hne : ∀u,src u≠dst u) (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) k → Fin d) → ℝ)
    (M : V → ℝ) (hM : ∀v,0≤M v)
    (hA : ∀v,Bound (A (e v).val) ((M v)^2)) :
    |∑c : U ⊕ Fin q → Fin d,
      ∏v,A (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)|≤
      (d:ℝ)^q*(∏v,M v) := by
  let N : ℕ → ℝ := fun k => if hk : k<Fintype.card V then M (e.symm ⟨k,hk⟩) else 0
  have hN (v : V) : N (e v).val=M v := by
    simp only [N,dite_eq_left (e v).isLt,Fin.eta,Equiv.symm_apply_apply]
  have hkey : Function.Injective (fun v => (e v).val) := Fin.val_injective.comp e.injective
  have hm (k : ℕ) (hk : k<length (fun v => (e v).val)) : 0≤N k := by
    have hk' : k<Fintype.card V := by rwa [length_equiv_val e] at hk
    change 0 ≤ (if hk : k < Fintype.card V then M (e.symm ⟨k,hk⟩) else 0)
    rw [dite_eq_left hk']
    exact hM _
  have ha (k : ℕ) (hk : k<length (fun v => (e v).val)) : Bound (A k) ((N k)^2) := by
    have hk' : k<Fintype.card V := by rwa [length_equiv_val e] at hk
    have hh := hA (e.symm ⟨k,hk'⟩)
    have hkv : (e (e.symm ⟨k,hk'⟩)).val=k :=
      congrArg Fin.val (e.apply_symm_apply ⟨k,hk'⟩)
    rw [hkv] at hh
    simpa only [N,dite_eq_left hk'] using hh
  have hh := reduced_coordinate_bound_upto (fun v => (e v).val) src dst hkey hne
    first last q d A N hm ha
  have hs (c : U ⊕ Fin q → Fin d) := product_stages e (fun k => A k
    (fun t => duplicate c t.val) (fun t => duplicate c t.val))
  simp_rw [hs] at hh
  rw [product_stage_range e] at hh
  simp only [hN] at hh
  exact hh
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.NetworkMoments
open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem lintegral_primary_auxiliary_le
    {Ω P H : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Nonempty P]
    {μ : Measure Ω} {f : P → Ω → ℝ≥0∞} {g : H → Ω → ℝ≥0∞}
    {M : P → ℝ≥0∞} {B : H → ℝ≥0∞}
    (hf : ∀i,AEMeasurable (f i) μ)
    (hm : ∀i,(∫⁻x,(f i x)^(Fintype.card P) ∂μ)≤(M i)^(Fintype.card P))
    (hg : ∀h x,g h x≤B h) (hB : ∀h,B h≠⊤) :
    (∫⁻x,(∏i,f i x)*(∏h,g h x) ∂μ)≤(∏i,M i)*(∏h,B h) := by
  have hb : (∏h,B h)≠⊤ := ENNReal.prod_ne_top (fun h _ => hB h)
  calc
    _ ≤ ∫⁻x,(∏i,f i x)*(∏h,B h) ∂μ :=
      lintegral_mono (fun x => mul_le_mul' le_rfl (Finset.prod_le_prod' (fun h _ => hg h x)))
    _ = (∫⁻x,∏i,f i x ∂μ)*(∏h,B h) := lintegral_mul_const' _ _ hb
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      apply lintegral_prod_le Finset.univ Finset.univ_nonempty
      · exact fun i _ => hf i
      · simpa only [Finset.card_univ] using fun i (_ : i∈(Finset.univ : Finset P)) => hm i
end LogConcaveSampling.NetworkMoments
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem terminal_moment_budgets {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (j k : ℕ) :
    (∀i,(S.derivatives i).length≤Fintype.card P) ∧
    (∀h∈S.hessians,h.extra.length≤Fintype.card P) ∧
    (∑i,(S.derivatives i).length)+(S.hessians.map (fun h => h.extra.length)).sum≤
      Fintype.card P ∧
    (Fintype.card P)*(k+j)+(∑i,(S.derivatives i).length)+
      (S.hessians.map (fun h => h.extra.length)).sum≤(Fintype.card P)*(k+j+1) ∧
    (Fintype.card P)*(j+1)+(∑i,(S.derivatives i).length)+
      (S.hessians.map (fun h => h.extra.length+1)).sum≤
      2*(Fintype.card P)*(j+1) := by
  have hid := (full_expansion_bookkeeping (P:=P)).2 S hS |>.2.2
  have hsum : (S.hessians.map (fun h => h.extra.length+1)).sum=
      (S.hessians.map (fun h => h.extra.length)).sum+S.hessians.card := by
    induction S.hessians using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons]; omega
  refine ⟨?_,?_,by omega,?_,?_⟩
  · intro i
    have hi := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => (S.derivatives i).length)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro h hh
    have hi : h.extra.length≤(S.hessians.map (fun h => h.extra.length)).sum := by
      apply Multiset.le_sum_of_mem
      exact Multiset.mem_map.mpr ⟨h,hh,rfl⟩
    omega
  · nlinarith
  · rw [hsum]
    have hp : Fintype.card P≤Fintype.card P*(j+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    nlinarith
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

theorem actual_ranked_schedule
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) :
    ∃e : TargetVertex S ≃ Fin (Fintype.card (TargetVertex S)),
      ∀(q : ℕ),0<q → ∀v : TargetVertex S,
        Nonempty (Frontier.Incoming
          (GraphSchedule.absorb (fun v => (e v).val) (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (e v).val) ∧
        Nonempty (Frontier.Outgoing
          (GraphSchedule.emit (fun v => (e v).val) (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (e v).val) := by
  obtain ⟨key,hkey,_,hsplit⟩ := actual_removal_graph_order hS
  obtain ⟨e,he⟩ := TraceOpening.compress_order key hkey
  refine ⟨e,fun q hq v => ?_⟩
  apply GraphSchedule.factor_splits_nonempty (fun v => (e v).val)
    (edgeSource (S:=S) β) (edgeTarget hS β)
    (Sum.inl 0) (Sum.inl (Fin.last n)) q hq _ v
  intro w
  obtain ⟨hi,ho⟩ := hsplit w
  constructor
  · rcases hi with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,(he u w).mpr hk⟩
  · rcases ho with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,(he w u).mpr hk⟩
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
variable {V : Type*} [Fintype V]

lemma rankExtend_at (e : V ≃ Fin (Fintype.card V)) {D : ℕ → Type*}
    (z : ∀k,D k) (a : ∀v,D (e v).val) (v : V) :
    rankExtend e z a (e v).val=a v := by
  simp only [rankExtend,dite_eq_left (e v).isLt,Fin.eta]
  apply eq_of_heq
  exact (cast_heq _ _).trans (congr_arg_heq a (e.symm_apply_apply v))
end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_IncidentMatrix
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

namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] [Fintype U]
    (key : V → ℕ) (src dst : U → V)

omit [Fintype U] in
lemma incidentMatrix_global (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (c : Edge (U:=U) q → Fin d) :
    incidentMatrix key src dst hkey hne first last v q d T
      (fun t => c t.val) (fun t => c t.val)=T (fun t => c t.val) := by
  unfold incidentMatrix
  congr 1
  funext t
  dsimp only [incidentSplit,Equiv.coe_fn_mk]
  split_ifs <;> rfl

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqT
local instance finDecEqT_r6b9e60_1 (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _
lemma incidentMatrix_bound (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : ℝ) (hT : TensorEnergy.AllSplitBound T M)
    [Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v))]
    [Nonempty (Frontier.Outgoing (emit key src dst first last q) (key v))] :
    TensorEnergy.Bound (incidentMatrix key src dst hkey hne first last v q d T) (M^2) :=
  hT _ _ (incidentSplit key src dst hkey hne first last v q)
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.edgeDecEqTG
attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqTG
theorem tensor_graph_bound (e : V ≃ Fin (Fintype.card V)) (src dst : U → V)
    (hne : ∀u,src u≠dst u) (first last : V) (q d : ℕ)
    (hsplit : ∀v,
      Nonempty (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) (e v).val) ∧
      Nonempty (Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) (e v).val))
    (T : ∀v,({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : V → ℝ) (hM : ∀v,0≤M v) (hT : ∀v,AllSplitBound (T v) (M v)) :
    |∑c : U ⊕ Fin q → Fin d, ∏v,T v (fun t => duplicate c t.val)|≤
      (d:ℝ)^q*(∏v,M v) := by
  let key : V → ℕ := fun v => (e v).val
  have hkey : Function.Injective key := Fin.val_injective.comp e.injective
  let D : ℕ → Type _ := fun k =>
    (Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ
  let a : ∀v,D (e v).val := fun v =>
    incidentMatrix key src dst hkey hne first last v q d (T v)
  let A : ∀k,D k := rankExtend e (fun _ _ _ => 0) a
  have hAt (v : V) : A (e v).val=a v := rankExtend_at e _ a v
  have hA (v : V) : Bound (A (e v).val) ((M v)^2) := by
    rw [hAt]
    let := (hsplit v).1
    let := (hsplit v).2
    exact incidentMatrix_bound key src dst hkey hne first last v q d (T v) (M v) (hT v)
  have hb := ranked_coordinate_bound e src dst hne first last q d A M hM hA
  have heq (v : V) (c : U ⊕ Fin q → Fin d) :
      A (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)=
        T v (fun t => duplicate c t.val) := by
    rw [hAt]
    exact incidentMatrix_global key src dst hkey hne first last v q d (T v) (duplicate c)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro v _
  exact (heq v c).symm
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open MeasureTheory TensorEnergy
open scoped BigOperators Classical ENNReal

variable {Ω P H U : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Fintype U]
    [Nonempty P]

attribute [local instance] OAI.LogConcaveSampling.GraphSchedule.finDecEqTGI
theorem tensor_graph_integral_bound (μ : Measure Ω)
    (e : P ⊕ H ≃ Fin (Fintype.card (P ⊕ H))) (src dst : U → P ⊕ H)
    (hne : ∀u,src u≠dst u) (first last : P ⊕ H) (q d : ℕ)
    (hsplit : ∀v,
      Nonempty (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) (e v).val) ∧
      Nonempty (Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) (e v).val))
    (T : Ω → ∀v,({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ)
    (M : P ⊕ H → Ω → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (T x v) (M v x))
    (B : P → ℝ≥0∞) (C : H → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(Fintype.card P) ∂μ)≤B i^(Fintype.card P))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
      ∏v,T x v (fun t => duplicate c t.val)| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  have hpw (x : Ω) : ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
        ∏v,T x v (fun t => duplicate c t.val)|≤
      (d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) := by
    have hb := ENNReal.ofReal_le_ofReal (tensor_graph_bound e src dst hne first last q d
      hsplit (T x) (fun v => M v x) (fun v => hM v x) (fun v => hT v x))
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast,ENNReal.ofReal_prod_of_nonneg (fun v _ => hM v x),
      Fintype.prod_sum_type] at hb
    exact hb
  calc
    _ ≤ ∫⁻x,(d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) ∂μ := lintegral_mono hpw
    _ = (d:ℝ≥0∞)^q*(∫⁻x,(∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x)) ∂μ) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ _ := mul_le_mul' le_rfl
      (NetworkMoments.lintegral_primary_auxiliary_le hMp hp hh hC)
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule TensorEnergy
open scoped BigOperators Classical ENNReal

variable {n : ℕ} {S : State (Fin (n+1))}

attribute [local instance] OAI.LogConcaveSampling.AdjointRemoval.cutDecEqAT
theorem actual_tensor_integral_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q d : ℕ) (hq : 0<q)
    (T : Ω → ∀v : TargetVertex S,
      ({t : Edge (U:=InternalEdge β) q //
        IncidentAt (V:=TargetVertex S) (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) v q t} → Fin d) → ℝ)
    (M : TargetVertex S → Ω → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (T x v) (M v x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      ∏v,T x v (fun t => duplicate c t.val)| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  obtain ⟨e,he⟩ := actual_ranked_schedule hS β hβ
  exact tensor_graph_integral_bound μ e (edgeSource (S:=S) β) (edgeTarget (S:=S) hS β)
    (internal_source_ne hS β) (Sum.inl 0) (Sum.inl (Fin.last n)) q d (he q hq) T M hM hT
    B C hMp (by simpa only [Fintype.card_fin] using hp) hh hC
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_HessianIncidenceTensor
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

namespace LogConcaveSampling.AdjointRemoval
variable {d : ℕ} {P : Type*}

lemma hessian_congr_on_tokens (H : Point d → ℝ) (b c : P → Point d) (h : Hessian P)
    (he : ∀i∈h.tokens,b i=c i) : hessian H b h=hessian H c h := by
  have hf : b h.first=c h.first := he _ (by simp [Hessian.tokens])
  have hs : b h.second=c h.second := he _ (by simp [Hessian.tokens])
  unfold hessian
  rw [hf,hs]
  apply JetCalculus.jet_congr_on_list
  intro i hi
  exact he i (by simp [Hessian.tokens,hi])
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

lemma hessianIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    hessianIncidenceTensor hS β q H b h x (fun t => duplicate c t.val)=
      hessian H (fun i => b (c (Sum.inl (Sum.inr i)))) h x := by
  unfold hessianIncidenceTensor
  refine congrFun (hessian_congr_on_tokens (P:=Fin (n+1)) H _ _
    (h : Hessian (Fin (n+1))) ?_) x
  intro i hi
  have hd : destination hS i=Sum.inr h :=
    (destination_iff_mem hS i (Sum.inr h)).mpr hi
  simp only [dite_eq_left hd]
  rfl
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

lemma primaryIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    primaryIncidenceTensor hS β q b i F x (fun t => duplicate c t.val)=
      JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x := by
  unfold primaryIncidenceTensor
  apply congrFun (JetCalculus.jet_congr_on_list _ _ _ _ ?_) x
  intro j hj
  have hd : destination hS j=Sum.inl i :=
    (destination_iff_mem hS j (Sum.inl i)).mpr hj
  simp only [dite_eq_left hd]
  rfl
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}

attribute [local instance] OAI.LogConcaveSampling.AdjointRemoval.cutDecEqBT
lemma branchIncidenceTensor_global
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (c : InternalEdge β ⊕ Fin q → Fin d) :
    (∏v,branchIncidenceTensor hS β q H b F x v (fun t => duplicate c t.val))=
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod := by
  rw [Fintype.prod_sum_type]
  simp only [branchIncidenceTensor,primaryIncidenceTensor_global,hessianIncidenceTensor_global]
  congr 1
  change (Finset.univ.val.map (fun h : S.hessians =>
    hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod=_
  exact congrArg Multiset.prod (Multiset.map_univ S.hessians
    (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x))

theorem literal_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (M : TargetVertex S → Point d → ℝ) (hM : ∀v x,0≤M v x)
    (hT : ∀v x,AllSplitBound (branchIncidenceTensor hS β q H b F x v) (M v x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  have hb := actual_tensor_integral_bound μ hS β hβ q d hq
    (branchIncidenceTensor hS β q H b F) M hM hT B C hMp hp hh hC
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  congr 2
  apply Finset.sum_congr rfl
  intro c _
  exact (branchIncidenceTensor_global hS β q H b F x c).symm
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_PrimaryPositionTensor
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

namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

lemma primaryIncidenceTensor_positions
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} → Fin d) :
    primaryIncidenceTensor hS β q b i F x a=
      primaryPositionTensor hS β q b i F x (a ∘ primarySlotEquiv hS β q i) := by
  unfold primaryIncidenceTensor primaryPositionTensor
  rw [JetCalculus.jet_finRange]
  congr 2
  funext k
  have hk : (S.derivatives i).get k∈S.derivatives i := List.get_mem _ _
  have hd : destination hS ((S.derivatives i).get k)=Sum.inl i :=
    (destination_iff_mem hS _ (Sum.inl i)).mpr hk
  simp only [dite_eq_left hd]
  rfl

lemma primaryIncidenceTensor_allSplit
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (M : ℝ) (hM : AllSplitBound (primaryPositionTensor hS β q b i F x) M) :
    AllSplitBound (primaryIncidenceTensor hS β q b i F x) M := by
  have he : primaryIncidenceTensor hS β q b i F x=
    fun a => primaryPositionTensor hS β q b i F x (a ∘ primarySlotEquiv hS β q i) :=
      funext (primaryIncidenceTensor_positions hS β q b i F x)
  rw [he]
  exact hM.reindex (primarySlotEquiv hS β q i)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

lemma hessianIncidence_direction
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (h : S.hessians)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d)
    (k : Fin (hessianPositionList (h : Hessian (Fin (n+1)))).length) :
    (if ht : destination hS ((hessianPositionList (h : Hessian (Fin (n+1)))).get k)=Sum.inr h then
      b (a ⟨Sum.inl (Sum.inr ((hessianPositionList (h : Hessian (Fin (n+1)))).get k)),Or.inr ht⟩) else 0)=
      b (a (hessianSlotEquiv hS β q h k)) := by
  have hk : (hessianPositionList (h : Hessian (Fin (n+1)))).get k∈ports S (Sum.inr h) := List.get_mem _ _
  have hd := (destination_iff_mem hS _ (Sum.inr h)).mpr hk
  simp only [dite_eq_left hd]
  rfl

lemma hessianIncidenceTensor_positions
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d) :
    hessianIncidenceTensor hS β q H b h x a=
      hessianPositionTensor H b (h : Hessian (Fin (n+1))) x (a ∘ hessianSlotEquiv hS β q h) := by
  have hf := hessianIncidence_direction hS β q b h a ⟨0,by simp [hessianPositionList]⟩
  have hs := hessianIncidence_direction hS β q b h a ⟨1,by simp [hessianPositionList]⟩
  simp only [hessianPositionList,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ] at hf hs
  unfold hessianIncidenceTensor hessianPositionTensor hessian
  rw [JetCalculus.jet_finRange]
  refine congrFun (congrArg₂
    (fun (v : Fin (h : Hessian (Fin (n+1))).extra.length → Point d) (f : Point d → ℝ) =>
      JetCalculus.jet v (List.finRange (h : Hessian (Fin (n+1))).extra.length) f) ?_ ?_) x
  · funext k
    have he := hessianIncidence_direction hS β q b h a ⟨k.val+2,by simp only [hessianPositionList,List.length_cons]; omega⟩
    simp only [hessianPositionList,List.get_eq_getElem,List.getElem_cons_succ] at he
    convert he using 1 <;> rfl
  · convert congrArg₂ directional hf (congrArg (fun v => directional v H) hs) using 1 <;> rfl

lemma hessianIncidenceTensor_allSplit
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d) (M : ℝ)
    (hM : AllSplitBound (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) M) :
    AllSplitBound (hessianIncidenceTensor hS β q H b h x) M := by
  have he : hessianIncidenceTensor hS β q H b h x=
    fun a => hessianPositionTensor H b (h : Hessian (Fin (n+1))) x (a ∘ hessianSlotEquiv hS β q h) :=
      funext (hessianIncidenceTensor_positions hS β q H b h x)
  rw [he]
  exact hM.reindex (hessianSlotEquiv hS β q h)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}

attribute [local instance] OAI.LogConcaveSampling.AdjointRemoval.cutDecEqPB
theorem positional_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (F i) x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (B : Fin (n+1) → ℝ≥0∞) (C : S.hessians → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤B i^(n+1))
    (hh : ∀h x,ENNReal.ofReal (Mh h x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  apply literal_branch_integral_bound μ hS β hβ q hq H b F (Sum.elim Mp Mh)
    (fun v => Sum.recOn v hMp0 hMh0) _ B C hMp hp hh hC
  intro v x
  cases v with
  | inl i => exact primaryIncidenceTensor_allSplit hS β q b i (F i) x (Mp i x) (hTp i x)
  | inr h => exact hessianIncidenceTensor_allSplit hS β q H b h x (Mh h x) (hTh h x)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators ENNReal

variable {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype P] in
lemma hessian_sum_toType {S : State P} (f : Hessian P → ℕ) :
    (∑h : S.hessians,f h)=(S.hessians.map f).sum := by
  change (Finset.univ.val.map (fun h : S.hessians => f h)).sum=_
  exact congrArg Multiset.sum (Multiset.map_univ S.hessians f)

theorem terminal_product_budget {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (j k : ℕ)
    (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) :
    (∏i : P,A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))*
      (∏h : S.hessians,A^((h : Hessian P).extra.length+1)*R^((h : Hessian P).extra.length))≤
      A^(2*(Fintype.card P)*(j+1))*R^((Fintype.card P)*(k+j+1)) := by
  have hb := terminal_moment_budgets hS j k
  have hpa : (∑i : P,(j+(S.derivatives i).length+1))=
      (Fintype.card P)*(j+1)+∑i : P,(S.derivatives i).length := by
    simp only [show ∀i : P,j+(S.derivatives i).length+1=j+1+(S.derivatives i).length from
      fun i => by omega]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    ring
  have hpr : (∑i : P,(k+j+(S.derivatives i).length))=
      (Fintype.card P)*(k+j)+∑i : P,(S.derivatives i).length := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    ring
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp only [Finset.prod_pow_eq_pow_sum,hpa,hpr]
  rw [hessian_sum_toType (S:=S) (fun h => h.extra.length+1),
    hessian_sum_toType (S:=S) (fun h => h.extra.length)]
  calc
    _ = A^((Fintype.card P)*(j+1)+(∑i,(S.derivatives i).length)+
        (S.hessians.map (fun h => h.extra.length+1)).sum)*
      R^((Fintype.card P)*(k+j)+(∑i,(S.derivatives i).length)+
        (S.hessians.map (fun h => h.extra.length)).sum) := by
          simp only [pow_add]
          ring
    _ ≤ _ := mul_le_mul' (pow_le_pow_right₀ hA hb.2.2.2.2)
      (pow_le_pow_right₀ hR hb.2.2.2.1)
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}

attribute [local instance] OAI.LogConcaveSampling.AdjointRemoval.cutDecEqQB
theorem quantitative_branch_integral_bound
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (F i) x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤
      (A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))^(n+1))
    (hh : ∀(h : S.hessians) x,ENNReal.ofReal (Mh h x)≤
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)) :
    (∫⁻x,ENNReal.ofReal |∑c : InternalEdge β ⊕ Fin q → Fin d,
      (∏i,JetCalculus.jet (fun a => b (c (Sum.inl (Sum.inr a)))) (S.derivatives i)
        (F i (fun t => duplicate c (traceEmbed β q t.val)) (c (Sum.inl (Sum.inr i)))) x)*
      (S.hessians.map (fun h => hessian H (fun a => b (c (Sum.inl (Sum.inr a)))) h x)).prod| ∂μ)≤
      (d:ℝ≥0∞)^q*(A^(2*(n+1)*(j+1))*R^((n+1)*(k+j+1))) := by
  have hC (h : S.hessians) :
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)≠⊤ := by
    finiteness
  have hb := positional_branch_integral_bound μ hS β hβ q hq H b F Mp Mh hMp0 hMh0 hTp hTh
    (fun i => A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))
    (fun h => A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length))
    hMp hp hh hC
  apply hb.trans
  apply mul_le_mul' le_rfl
  simpa only [Fintype.card_fin] using terminal_product_budget hS j k A R hA hR
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped ENNReal

variable {Ω α P : Type*} [MeasurableSpace Ω] [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in

lemma lintegral_abs_list_sum_bound (μ : Measure Ω) (L : List α)
    (f : α → Ω → ℝ) (B : ℝ≥0∞)
    (hm : ∀a∈L,AEMeasurable (f a) μ)
    (hb : ∀a∈L,(∫⁻x,ENNReal.ofReal |f a x| ∂μ)≤B) :
    (∫⁻x,ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ)≤(L.length:ℝ≥0∞)*B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hm' : ∀b∈L,AEMeasurable (f b) μ := fun b h => hm b (List.mem_cons_of_mem a h)
    have hb' : ∀b∈L,(∫⁻x,ENNReal.ofReal |f b x| ∂μ)≤B := fun b h => hb b (List.mem_cons_of_mem a h)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      _ ≤ ∫⁻x,ENNReal.ofReal |f a x|+ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [←ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = (∫⁻x,ENNReal.ofReal |f a x| ∂μ)+(∫⁻x,ENNReal.ofReal |(L.map (fun a => f a x)).sum| ∂μ) :=
        lintegral_add_left' ((hm a (List.mem_cons_self)).abs.ennreal_ofReal) _
      _ ≤ B+(L.length:ℝ≥0∞)*B := add_le_add (hb a List.mem_cons_self) (ih hm' hb')
      _ = ((L.length+1:ℕ):ℝ≥0∞)*B := by simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]; rw [add_comm]

theorem removal_sum_bound (μ : Measure Ω) (f : State P → Ω → ℝ) (B : ℝ≥0∞)
    (hm : ∀S∈expand (Fintype.card P) initial,AEMeasurable (f S) μ)
    (hb : ∀S∈expand (Fintype.card P) initial,(∫⁻x,ENNReal.ofReal |f S x| ∂μ)≤B) :
    (∫⁻x,ENNReal.ofReal |((expand (Fintype.card P) initial).map (fun S => f S x)).sum| ∂μ)≤
      ((3*Fintype.card P+1:ℕ):ℝ≥0∞)^(Fintype.card P)*B := by
  apply (lintegral_abs_list_sum_bound μ _ f B hm hb).trans
  apply mul_le_mul' _ le_rfl
  exact_mod_cast (full_expansion_bookkeeping (P:=P)).1
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Chain
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule
open scoped BigOperators Classical NNReal

variable {n d : ℕ}

lemma split_duplicate (β : Fin n → ℕ) (q : ℕ) (t : TraceColors β q d)
    (a : Fin (n+1) → Fin d) (u : TraceEdge β q) :
    duplicate (coloringSplit.symm (t,a)) (traceEmbed β q u) = t (closeTrace β q u) := by
  rcases u with e | (j | j) <;> rfl

lemma split_adjoint (β : Fin n → ℕ) (q : ℕ) (t : TraceColors β q d)
    (a : Fin (n+1) → Fin d) (j : Fin (n+1)) :
    coloringSplit.symm (t,a) (Sum.inl (Sum.inr j)) = a j := rfl

attribute [local instance] OAI.LogConcaveSampling.AdjointRemoval.cutDecEqCB
lemma chainBranch_eq_split (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ)
    (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (S : State (Fin (n+1))) (x : Point d) :
    chainBranch β q H b F S x = ∑t : TraceColors β q d, ∑a : Fin (n+1) → Fin d,
      (∏i,JetCalculus.jet (fun j => b (a j)) (S.derivatives i)
        (chainField β q F t i (a i)) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (a j)) h x)).prod := by
  unfold chainBranch
  rw [←(Equiv.sum_comp (coloringSplit.symm :
    (TraceColors β q d × (Fin (n+1) → Fin d)) ≃ FullColors β q d))]
  rw [Fintype.sum_prod_type]
  congr 1
  funext t
  congr 1
  funext a
  simp only [split_duplicate, split_adjoint, chainField]

lemma chainBranch_polySmooth (β : Fin n → ℕ) (q : ℕ) {H : Point d → ℝ}
    (hH : PolySmooth H) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (hF : ∀i c z,PolySmooth (F i c z)) (S : State (Fin (n+1))) :
    PolySmooth (chainBranch β q H b F S) := by
  exact PolySmooth.sum Finset.univ (fun c _ =>
    branch_factor_polySmooth S hH (fun j => b (c (Sum.inl (Sum.inr j))))
      (fun i => F i (fun u => duplicate c (traceEmbed β q u.val))
        (c (Sum.inl (Sum.inr i)))) (fun i => hF i _ _))

theorem integral_chain_expansion (β : Fin n → ℕ) (q : ℕ)
    {H : Point d → ℝ} (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀i c z,PolySmooth (F i c z)) :
    (∫x,(∑t : TraceColors β q d,∏i,tensorAdjoint H b (chainField β q F t i) x) ∂gibbs H) =
      ((expand (Fintype.card (Fin (n+1))) initial).map
        (fun S => ∫x,chainBranch β q H b F S x ∂gibbs H)).sum := by
  rw [parametrized_adjoint_expansion b (chainField β q F) hH ht hK
    (fun t i z => hF i _ z)]
  congr 1
  apply List.map_congr_left
  intro S _
  simp_rw [chainBranch_eq_split]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum]
    intro a _
    exact (branch_factor_polySmooth S hH (fun j => b (a j))
      (fun i => chainField β q F t i (a i)) (fun i => hF i _ _)).integrable
      hH.smooth.continuous ht
  · intro t _
    exact (PolySmooth.sum Finset.univ (fun a _ => branch_factor_polySmooth S hH
      (fun j => b (a j)) (fun i => chainField β q F t i (a i))
      (fun i => hF i _ _))).integrable hH.smooth.continuous ht

open TensorEnergy
open scoped ENNReal

lemma primaryPositionTensor_of_chain {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (M : ℝ)
    (hM : AllSplitBound (chainPositionTensor β q b i F (S.derivatives i).length x) M) :
    AllSplitBound (primaryPositionTensor hS β q b i
      (fun a z => F (a ∘ chainSlotEquiv hS β q i) z) x) M := by
  exact hM.reindex ((chainSlotEquiv hS β q i).sumCongr
    (Equiv.refl (Unit ⊕ Fin (S.derivatives i).length)))

theorem chain_branch_bound {S : State (Fin (n+1))}
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound
      (chainPositionTensor β q b i (F i) (S.derivatives i).length x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤
      (A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))^(n+1))
    (hh : ∀(h : S.hessians) x,ENNReal.ofReal (Mh h x)≤
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)) :
    (∫⁻x,ENNReal.ofReal |chainBranch β q H b F S x| ∂μ)≤
      (d:ℝ≥0∞)^q*(A^(2*(n+1)*(j+1))*R^((n+1)*(k+j+1))) := by
  let G : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ :=
    fun i a z => F i (a ∘ chainSlotEquiv hS β q i) z
  have hG : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (G i) x) (Mp i x) :=
    fun i x => primaryPositionTensor_of_chain hS β q b i (F i) x (Mp i x) (hTp i x)
  have hb := quantitative_branch_integral_bound μ hS β hβ q hq H b G Mp Mh hMp0 hMh0
    hG hTh j k A R hA hR hAf hRf hMp hp hh
  simpa only [G,Function.comp_def,chainSlotEquiv,Equiv.coe_fn_mk,chainBranch] using hb

theorem integral_chain_bound (β : Fin n → ℕ) (q : ℕ)
    {H : Point d → ℝ} (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀i c z,PolySmooth (F i c z))
    (B : ℝ≥0∞)
    (hB : ∀S∈expand (Fintype.card (Fin (n+1))) initial,
      (∫⁻x,ENNReal.ofReal |chainBranch β q H b F S x| ∂gibbs H)≤B) :
    ENNReal.ofReal |∫x,(∑t : TraceColors β q d,∏i,tensorAdjoint H b
      (chainField β q F t i) x) ∂gibbs H| ≤ ((3*(n+1)+1:ℕ):ℝ≥0∞)^(n+1)*B := by
  rw [integral_chain_expansion β q b F hH ht hK hF]
  have hi (S : State (Fin (n+1))) :
      Integrable (chainBranch β q H b F S) (gibbs H) :=
    (chainBranch_polySmooth β q hH b F hF S).integrable hH.smooth.continuous ht
  have hiL (L : List (State (Fin (n+1)))) :
      Integrable (fun x => (L.map (fun S => chainBranch β q H b F S x)).sum) (gibbs H) := by
    induction L with
    | nil => simp
    | cons S L ih =>
      change Integrable (fun x => chainBranch β q H b F S x+
        (L.map (fun S => chainBranch β q H b F S x)).sum) (gibbs H)
      exact (hi S).add ih
  have he (L : List (State (Fin (n+1)))) :
      (L.map (fun S => ∫x,chainBranch β q H b F S x ∂gibbs H)).sum =
      ∫x,(L.map (fun S => chainBranch β q H b F S x)).sum ∂gibbs H := by
    induction L with
    | nil => simp
    | cons S L ih => simp only [List.map_cons,List.sum_cons,integral_add (hi S) (hiL L),ih]
  rw [he]
  have hb := removal_sum_bound (gibbs H) (chainBranch β q H b F) B
    (fun S _ => (hi S).aestronglyMeasurable.aemeasurable) hB
  apply le_trans _ (by simpa only [Fintype.card_fin] using hb)
  simpa only [Real.enorm_eq_ofReal_abs,Fintype.card_fin] using
    enorm_integral_le_lintegral_enorm (μ:=gibbs H)
      (fun x => ((expand (Fintype.card (Fin (n+1))) initial).map
        (fun S => chainBranch β q H b F S x)).sum)

end LogConcaveSampling.AdjointRemoval

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma weight_cons (A : Matrix I J ℝ) {n : ℕ} (i k l : I) (j : J)
    (r : Fin n → I) (c : Fin (n+1) → J) :
    weight A i k (Fin.cons l r) (Fin.cons j c) =
      (A i j * A l j) * weight A l k r c := by
  unfold weight
  rw [Fin.prod_univ_succ, ←Fin.cons_snoc_eq_snoc_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem power_entry (A : Matrix I J ℝ) (n : ℕ) (i k : I) :
    ((A*A.transpose)^(n+1)) i k =
      ∑ r : Fin n → I, ∑ c : Fin (n+1) → J, weight A i k r c := by
  induction n generalizing i k with
  | zero =>
    conv_lhs => rw [Nat.zero_add, pow_one]
    rw [Matrix.mul_apply]
    conv_rhs => rw [Fintype.sum_unique]
    conv_rhs => rw [←(Fin.consEquiv (fun _ : Fin 1 => J)).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro j _
    have hs : Fin.snoc (α := fun _ => I) (default : Fin 0 → I) k 0 = k :=
      Fin.snoc_last _ _
    simp [weight, Matrix.transpose_apply, hs]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, ih, Finset.sum_mul,
      Finset.mul_sum]
    rw [←(Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    conv_rhs => rw [←(Fin.consEquiv (fun _ : Fin (n+2) => J)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ c, ∑ j, A i j*A l j*weight A l k r c) =
      ∑ j, ∑ c, weight A i k (Fin.cons l r) (Fin.cons j c)
    simp_rw [weight_cons]
    rw [Finset.sum_comm]

theorem trace_power (A : Matrix I J ℝ) (n : ℕ) :
    ((A*A.transpose)^(n+1)).trace =
      ∑ i, ∑ r : Fin n → I, ∑ c : Fin (n+1) → J, weight A i i r c := by
  simp only [Matrix.trace, Matrix.diag, power_entry]

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma snoc_eq_advance {n : ℕ} (i : I) (r : Fin n → I) (t : Fin (n+1)) :
    Fin.snoc (α := fun _ => I) r i t = Fin.cons (α := fun _ => I) i r (advance t) := by
  refine Fin.lastCases ?_ (fun k => ?_) t
  · simp [advance]
  · have hk : k.val+1<n+1 := by omega
    simp only [Fin.snoc_castSucc, advance, Fin.val_castSucc, dite_eq_left hk]
    change r k = Fin.cons (α := fun _ => I) i r k.succ
    simp only [Fin.cons_succ]

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma closedWeight_cons (A : Matrix I J ℝ) {n : ℕ}
    (i : I) (r : Fin n → I) (c : Fin (n+1) → J) :
    closedWeight A (Fin.cons i r) c = weight A i i r c := by
  simp only [closedWeight, weight, snoc_eq_advance]

theorem trace_power_colors (A : Matrix I J ℝ) (n : ℕ) :
    ((A*A.transpose)^(n+1)).trace =
      ∑r : Fin (n+1) → I,∑c : Fin (n+1) → J,closedWeight A r c := by
  rw [trace_power, ←(Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, closedWeight_cons]

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval
open scoped Classical BigOperators

variable {s a b : ℕ}

lemma close_encodeSlot_col (t : Fin (s+1)) (z : Fin 2) (j : Fin b) :
    closeTrace (bundle a b) a (encodeSlot t z (Sum.inr j)).val =
      encodeWire (Sum.inr (t,j)) := rfl

lemma close_encodeSlot_row (t : Fin (s+1)) (z : Fin 2) (j : Fin a) :
    closeTrace (bundle a b) a (encodeSlot t z (Sum.inl j)).val =
      encodeWire (Sum.inl (rowAt t z,j)) := by
  by_cases hz : z.val=0
  · rw [show rowAt t z=t from ite_eq_left hz]
    by_cases ht : t.val=0
    · simp only [encodeSlot,dite_eq_left hz,dite_eq_left ht,closeTrace,encodeWire]
    · simp only [encodeSlot,dite_eq_left hz,dite_eq_right ht,closeTrace,encodeWire]
  · rw [show rowAt t z=advance t from ite_eq_right hz]
    by_cases ht : t.val=s
    · have ha : advance t=0 := by simp [advance,ht]
      rw [ha]
      change closeTrace (bundle a b) a (encodeSlot t z (Sum.inl j)).val=Sum.inr j
      simp only [encodeSlot,dite_eq_right hz,dite_eq_left ht,closeTrace]
    · have hp : t.val+1 < s+1 := by omega
      have hn : (advance t).val≠0 := by
        simp only [advance,dite_eq_left hp]
        omega
      simp only [encodeSlot,dite_eq_right hz,dite_eq_right ht,closeTrace,encodeWire,dite_eq_right hn]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        simp only [advance,dite_eq_left hp]
        omega
      · exact (Fin.heq_ext_iff (by
          congr 1
          apply Fin.ext
          simp only [advance,dite_eq_left hp]
          omega)).mpr rfl

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {s a b d : ℕ}

lemma chainField_lift_pair (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (c : TraceColors (bundle (s:=s) a b) a d) (t : Fin (s+1)) (z : Fin 2) :
    chainField (bundle a b) a (liftField F) c (primaryPair s (t,z)) =
      F (Sum.elim ((colorEquiv s a b d c).1 (rowAt t z))
        ((colorEquiv s a b d c).2 t)) := by
  unfold chainField liftField
  apply congrArg F
  funext j
  rcases j with j | j
  · simp only [Function.comp_apply,slotEquivAt_pair,close_encodeSlot_row,colorEquiv,
      Equiv.coe_fn_mk,Sum.elim_inl]
  · simp only [Function.comp_apply,slotEquivAt_pair,close_encodeSlot_col,colorEquiv,
      Equiv.coe_fn_mk,Sum.elim_inr]

lemma product_chain_lift (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (c : TraceColors (bundle (s:=s) a b) a d) (x : Point d) :
    (∏i : Primary s,tensorAdjoint H v (chainField (bundle a b) a (liftField F) c i) x) =
      closedWeight (adjointMatrix H v F x)
        (colorEquiv s a b d c).1 (colorEquiv s a b d c).2 := by
  rw [←(primaryPair s).prod_comp]
  simp only [Fintype.prod_prod_type,chainField_lift_pair,Fin.prod_univ_two,
    rowAt,Fin.val_zero,Fin.val_one,ite_true,ite_false,one_ne_zero,
    closedWeight,adjointMatrix]

theorem trace_eq_chain (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ) (x : Point d) :
    ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace =
      ∑c : TraceColors (bundle (s:=s) a b) a d,
        ∏i : Primary s,tensorAdjoint H v (chainField (bundle a b) a (liftField F) c i) x := by
  calc
    _ = ∑rc : RowColors s a d × RowColors s b d,
        closedWeight (adjointMatrix H v F x) rc.1 rc.2 := by
      rw [trace_power_colors,Fintype.sum_prod_type]
    _ = ∑c : TraceColors (bundle (s:=s) a b) a d,
        closedWeight (adjointMatrix H v F x)
          (colorEquiv s a b d c).1 (colorEquiv s a b d c).2 :=
      ((colorEquiv s a b d).sum_comp _).symm
    _ = _ := by simp only [product_chain_lift]

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_FieldPosition
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory TensorEnergy
open scoped Classical BigOperators NNReal ENNReal Matrix.Norms.L2Operator

variable {s a b d : ℕ}

local instance cutDecEqDT_r6b9e60_1 (β : Fin (2*s+1) → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)
lemma lift_position_bound (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (i : Primary s) (e : ℕ) (x : Point d) (M : ℝ)
    (hM : AllSplitBound (fieldPosition v F e x) M) :
    AllSplitBound (chainPositionTensor (bundle a b) a v i (liftField F i) e x) M := by
  exact hM.reindex ((slotEquivAt i).sumCongr (Equiv.refl (Unit ⊕ Fin e)))

lemma trace_polySmooth {H : Point d → ℝ} (hH : PolySmooth H)
    (v : Fin d → Point d) (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (hF : ∀c z,PolySmooth (F c z)) :
    PolySmooth (fun x => ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace) := by
  simp_rw [trace_eq_chain]
  exact PolySmooth.sum Finset.univ (fun c _ => PolySmooth.prod Finset.univ
    (fun i _ => hH.tensorAdjoint (fun z => hF _ z) v))

theorem adjoint_moment_of_branches {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀c z,PolySmooth (F c z))
    (B : ℝ≥0∞)
    (hB : ∀S∈expand (Fintype.card (Primary s)) initial,
      (∫⁻x,ENNReal.ofReal |chainBranch (bundle (s:=s) a b) a H v (liftField F) S x|
        ∂gibbs H)≤B) :
    (∫⁻x,ENNReal.ofReal ‖adjointMatrix H v F x‖^(2*(s+1)) ∂gibbs H) ≤
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞)^(2*s+2)*B := by
  let T := fun x => ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace
  have hi : Integrable T (gibbs H) := (trace_polySmooth hH v F hF).integrable hH.smooth.continuous ht
  have hp (x) : ‖adjointMatrix H v F x‖^(2*(s+1))≤T x :=
    TraceMoment.rectangular_trace_moment _ (Nat.succ_pos s)
  have h0 (x) : 0≤T x := (pow_nonneg (norm_nonneg _) _).trans (hp x)
  have hb := integral_chain_bound (bundle (s:=s) a b) a v (liftField F) hH ht hK
    (fun i c z => hF _ z) B hB
  calc
    _ ≤ ∫⁻x,ENNReal.ofReal (T x) ∂gibbs H := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal ‖adjointMatrix H v F x‖ ^ (2*(s+1)) ≤ _
      rw [←ENNReal.ofReal_pow (norm_nonneg _) (2*(s+1))]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal (∫x,T x ∂gibbs H) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0)).symm
    _ = ENNReal.ofReal |∫x,T x ∂gibbs H| := by
      rw [abs_of_nonneg (integral_nonneg h0)]
    _ ≤ _ := by
      simpa only [T,trace_eq_chain,show 2*s+1+1=2*s+2 from by omega] using hb

theorem adjoint_trace_moment {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (ha : 0<a) (hb : 0<b) {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (hF : ∀c z,PolySmooth (F c z))
    (M N : ℕ → Point d → ℝ)
    (hM0 : ∀e x,0≤M e x) (hN0 : ∀e x,0≤N e x)
    (hM : ∀e x,AllSplitBound (fieldPosition v F e x) (M e x))
    (hN : ∀e x,AllSplitBound (scorePosition H v e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMm : ∀e,AEMeasurable (fun x => ENNReal.ofReal (M e x)) (gibbs H))
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (M e x)^(2*(s+1)) ∂gibbs H) ≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    (∫⁻x,ENNReal.ofReal ‖adjointMatrix H v F x‖^(2*(s+1)) ∂gibbs H)≤
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞)^(2*s+2) * (d:ℝ≥0∞)^a *
        (A^(2*(2*s+2)*(j+1))*R^((2*s+2)*(k+j+1))) := by
  have he : 2*s+1+1=2*(s+1) := by omega
  have hβ : ∀t : Fin (2*s+1),0<bundle a b t := by
    intro t
    unfold bundle
    split <;> assumption
  rw [mul_assoc]
  apply adjoint_moment_of_branches v F hH ht hK hF
  intro S hS
  have hpder (i : Primary s) : (S.derivatives i).length≤2*(s+1) := by
    simpa only [Fintype.card_fin,he] using (terminal_moment_budgets hS j k).1 i
  have hhder (h : S.hessians) : (h : Hessian (Primary s)).extra.length≤2*(s+1) := by
    simpa only [Fintype.card_fin,he] using (terminal_moment_budgets hS j k).2.1 h Multiset.coe_mem
  have hbound := chain_branch_bound (gibbs H) hS (bundle a b) hβ a ha H v (liftField F)
    (fun i => M (S.derivatives i).length) (fun h => N (h : Hessian (Primary s)).extra.length)
    (fun i x => hM0 _ x) (fun h x => hN0 _ x)
    (fun i x => lift_position_bound v F i _ x _ (hM _ x))
    (fun h x => hN _ x) j k A R hA hR hAf hRf
    (fun i => hMm _) (fun i => by simpa only [he] using hp _ (hpder i))
    (fun h x => hh _ (hhder h) x)
  simpa only [show 2*s+1+1=2*s+2 from by omega] using hbound

end LogConcaveSampling.CycleTrace

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
open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator

lemma natural_moment_root_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀x,0≤f x) {n a j k : ℕ} (hn : 0<n)
    (C D A R : ℝ≥0∞)
    (h : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ) ≤
      C^n*D^a*(A^(2*n*(j+1))*R^(n*(k+j+1)))) :
    eLpNorm' f (n:ℝ) μ ≤
      C*D^((a:ℝ)/(n:ℝ))*A^(2*(j+1))*R^(k+j+1) := by
  apply (norm_le_iff_natural_moment (μ:=μ) hf hn _).mpr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hD : (D^((a:ℝ)/(n:ℝ)))^n=D^a := by
    rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul,div_mul_cancel₀ _ hn0,
      ENNReal.rpow_natCast]
  rw [mul_pow,mul_pow,mul_pow,hD]
  simp only [←pow_mul,Nat.mul_comm,Nat.mul_left_comm,mul_assoc]

theorem adjoint_eLpNorm {s a b d : ℕ} {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (ha : 0<a) (hb : 0<b) {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (hF : ∀c z,PolySmooth (F c z))
    (M N : ℕ → Point d → ℝ)
    (hM0 : ∀e x,0≤M e x) (hN0 : ∀e x,0≤N e x)
    (hM : ∀e x,TensorEnergy.AllSplitBound (CycleTrace.fieldPosition v F e x) (M e x))
    (hN : ∀e x,TensorEnergy.AllSplitBound (CycleTrace.scorePosition H v e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMm : ∀e,AEMeasurable (fun x => ENNReal.ofReal (M e x)) (gibbs H))
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (M e x)^(2*(s+1)) ∂gibbs H) ≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    eLpNorm (fun x => ‖CycleTrace.adjointMatrix H v F x‖) (2*(s+1):ℝ≥0∞) (gibbs H) ≤
      (3*(2*(s+1))+1)*(d:ℝ≥0∞)^((a:ℝ)/(2*(s+1):ℝ))*
        A^(2*(j+1))*R^(k+j+1) := by
  have hcont : Continuous (CycleTrace.adjointMatrix H v F) :=
    continuous_matrix fun _ _ => (hH.tensorAdjoint (fun z => hF _ z) v).smooth.continuous
  have hnorm := eLpNorm_nnreal_eq_eLpNorm' (μ:=gibbs H)
    (p:=((2*(s+1):ℕ):ℝ≥0)) (by positivity) (f := fun x => ‖CycleTrace.adjointMatrix H v F x‖)
  push_cast at hnorm
  rw [hnorm]
  have h := CycleTrace.adjoint_trace_moment v F ha hb hH ht hK hF M N hM0 hN0 hM hN
    j k A R hA hR hAf hRf hMm hp hh
  have he : 2*s+2=2*(s+1) := by omega
  simpa only [he,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
    natural_moment_root_product (gibbs H) (fun x => ‖CycleTrace.adjointMatrix H v F x‖)
      (fun _ => norm_nonneg _) (by omega : 0<2*(s+1))
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞) (d:ℝ≥0∞) A R (by simpa only [he] using h)

end LogConcaveSampling

end

end

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
open scoped Classical BigOperators

lemma spatialTensor_adjoint {K S : Type} {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (y : Point d) (c : K ⊕ S → Fin d) :
    spatialTensor (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) l y c =
    spatialAdjointLeading H F l y c+
      ∑s∈l.toFinset.powerset.erase ∅,∑z : Fin d,
        JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
          (l.filter (fun k => k∈s)) (directional (EuclideanSpace.basisFun (Fin d) ℝ z) H) y *
        JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
          (l.filter (fun k => k∉s)) (F (Sum.elim (fun t => c (Sum.inr t)) (fun _ => z))) y := by
  exact congrFun (jet_tensorAdjoint hH.smooth (fun _ => (hF _).smooth) _ _ l hl) y

lemma fieldPosition_spatialInside {K S : Type} {a b d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) (y : Point d)
    (c : (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) → Fin d) :
    CycleTrace.fieldPosition (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun a z => spatialInside F l (a ∘ h) z) e y c=
    spatialTensor F ((List.finRange e).map Sum.inl++l.map Sum.inr) y
      (c ∘ spatialFieldSlots h e) := by
  unfold CycleTrace.fieldPosition spatialInside spatialTensor
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  have he : (fun s => (c ∘ spatialFieldSlots h e) (Sum.inr s))=
      Sum.elim (fun s => c (Sum.inl (h (Sum.inr s)))) (fun _ => c (Sum.inr (Sum.inl ()))) := by
    funext s
    rcases s with s | u
    · rfl
    · cases u; rfl
  rw [he]
  rfl

lemma fieldPosition_spatialInside_allSplit {K S : Type} [Fintype K] [Fintype S] {a b d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l)
    (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (CycleTrace.fieldPosition (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun a z => spatialInside F l (a ∘ h) z) e y)
      (spatialEnvelope F (Fintype.card K+e) y) := by
  have hh := spatialTensor_allSplit_envelope F (fun c => (hF c).smooth)
    ((List.finRange e).map Sum.inl++l.map Sum.inr)
    (JetCalculus.nodup_sum_append (List.nodup_finRange e) hl)
    (by intro k; cases k <;> simp [hall]) y
  have hhh := hh.reindex (spatialFieldSlots h e)
  simpa only [←fieldPosition_spatialInside,Fintype.card_sum,Fintype.card_fin,Nat.add_comm e] using hhh

lemma spatialInside_polySmooth {K S : Type} {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) (z : Fin d) : PolySmooth (spatialInside F l c z) :=
  (hF _).jet _ l

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

lemma spatialContractTerm_allSplit_nonempty {d : ℕ} {S T K : Type}
    [Fintype S] [Fintype T] [Fintype K]
    (p : K → Prop) [DecidablePred p]
    [Nonempty ({k // p k} ⊕ S)] [Nonempty ({k // ¬p k} ⊕ T)]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ}
    {G : (T ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M N : ℝ}
    (hF : TensorEnergy.AllSplitBound (spatialTensor F (selectList p l) y) M)
    (hG : TensorEnergy.AllSplitBound (spatialTensor G (selectList (fun k => ¬p k) l) y) N) :
    TensorEnergy.AllSplitBound (spatialContractTerm p F G l y) (M*N) :=
  ((extendedSpatial_allSplit hF).singleContract (extendedSpatial_allSplit hG)).reindex
    (contractSpatialSlots p)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ReindexedMatrix
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

lemma splitEnvelope_le_pow {S : Type} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (hM : 0≤M) (h : AllSplitBound T M) :
    splitEnvelope T ≤ (2:ℝ)^Fintype.card S*M :=
  (splitEnvelope_le hM h).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast properSplit_card_le (S:=S)) hM)
end TensorEnergy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma natural_moment_sum_finset {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀i∈s,AEStronglyMeasurable (f i) μ) (hf0 : ∀i∈s,∀x,0≤f i x)
    {n : ℕ} (hn : 0<n) (B : ι → ℝ≥0∞)
    (hB : ∀i∈s,(∫⁻x,ENNReal.ofReal (f i x)^n ∂μ)≤B i^n) :
    (∫⁻x,ENNReal.ofReal (∑i∈s,f i x)^n ∂μ)≤(∑i∈s,B i)^n := by
  apply (norm_le_iff_natural_moment (μ:=μ)
    (fun x => Finset.sum_nonneg (fun i hi => hf0 i hi x)) hn _).mp
  have hnorm {summand : Ω → ℝ} (hsm : AEStronglyMeasurable summand μ) :
      eLpNorm summand (n:ℝ≥0∞) μ = eLpNorm' summand (n:ℝ) μ := by
    simpa only [ENNReal.coe_natCast,NNReal.coe_natCast] using
      (eLpNorm_nnreal_eq_eLpNorm' (p:=(n:NNReal)) (by exact_mod_cast hn.ne') (f := summand))
  rw [←hnorm (s.aestronglyMeasurable_fun_sum hf)]
  have hh := eLpNorm_sum_le (μ:=μ) (s:=s) (f:=f) hf
    (show 1≤(n:ℝ≥0∞) by exact_mod_cast hn)
  have he : (fun x => ∑i∈s,f i x)=∑i∈s,f i := by ext x; simp
  rw [he]
  apply hh.trans
  apply Finset.sum_le_sum
  intro index hindex
  rw [hnorm (hf index hindex)]
  exact (norm_le_iff_natural_moment (μ:=μ) (hf0 index hindex) hn _).mpr (hB index hindex)

lemma natural_moment_mul {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀x,0≤f x) (_hg0 : ∀x,0≤g x) (n : ℕ) (A B : ℝ≥0∞)
    (hA : (∫⁻x,ENNReal.ofReal (f x)^(2*n) ∂μ)≤A^(2*n))
    (hB : (∫⁻x,ENNReal.ofReal (g x)^(2*n) ∂μ)≤B^(2*n)) :
    (∫⁻x,ENNReal.ofReal (f x*g x)^n ∂μ)≤(A*B)^n := by
  let F : Bool → Ω → ℝ≥0∞ := fun b x => if b then ENNReal.ofReal (f x)^n else ENNReal.ofReal (g x)^n
  let M : Bool → ℝ≥0∞ := fun b => if b then A^n else B^n
  have hmm : ∀b∈(Finset.univ : Finset Bool),(∫⁻x,(F b x)^(Finset.univ : Finset Bool).card ∂μ)≤(M b)^(Finset.univ : Finset Bool).card := by
    intro b _
    cases b <;> simpa only [F,M,Bool.false_eq_true,↓reduceIte,Finset.card_univ,Fintype.card_bool,
      ←pow_mul,Nat.mul_comm n 2] using (show _ from (by first | exact hB | exact hA))
  have hff : ∀b∈(Finset.univ : Finset Bool),AEMeasurable (F b) μ := by
    intro b _
    cases b
    · exact (ENNReal.measurable_ofReal.comp_aemeasurable hg.aemeasurable).pow_const n
    · exact (ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable).pow_const n
  have hh := NetworkMoments.lintegral_prod_le Finset.univ Finset.univ_nonempty hff hmm
  simpa only [F,M,Fintype.prod_bool,Bool.false_eq_true,↓reduceIte,
    ENNReal.ofReal_mul (hf0 _),mul_pow] using hh

lemma natural_moment_const_mul {f : Ω → ℝ} (_hf0 : ∀x,0≤f x)
    (n : ℕ) {C : ℝ} (hC : 0≤C) (B : ℝ≥0∞)
    (hB : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)≤B^n) :
    (∫⁻x,ENNReal.ofReal (C*f x)^n ∂μ)≤(ENNReal.ofReal C*B)^n := by
  simp only [ENNReal.ofReal_mul hC,mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  exact mul_le_mul' le_rfl hB

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace TensorEnergy

lemma matrix_norm_reindex {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix I J ℝ) (e : K ≃ I) (f : L ≃ J) :
    ‖reindexedMatrix A e f‖=‖A‖ := by
  apply le_antisymm
  · exact ((bound_norm A).reindex e f).norm_le (norm_nonneg _)
  · have hh := (bound_norm (reindexedMatrix A e f)).reindex e.symm f.symm
    simpa only [reindexedMatrix,Equiv.apply_symm_apply] using hh.norm_le (norm_nonneg _)

lemma spatialAdjoint_matrix_norm {K S : Type} [Fintype K] [Fintype S] {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (p : ProperSplit (K ⊕ S)) (y : Point d) :
    ‖splitMatrix (spatialAdjointLeading H F l y) p‖=
      ‖CycleTrace.adjointMatrix H (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun a z => spatialInside F l (a ∘ splitFin p) z) y‖ := by
  let e := Equiv.arrowCongr (Fintype.equivFin (OutSlots p)) (Equiv.refl (Fin d))
  let f := Equiv.arrowCongr (Fintype.equivFin (InSlots p)) (Equiv.refl (Fin d))
  let B := CycleTrace.adjointMatrix H (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun a z => spatialInside F l (a ∘ splitFin p) z) y
  have he : splitMatrix (spatialAdjointLeading H F l y) p=reindexedMatrix B e f := by
    ext o i
    unfold splitMatrix spatialAdjointLeading reindexedMatrix B CycleTrace.adjointMatrix
    congr 2
    funext t
    unfold splitFin
    cases h : splitEquiv p t <;> simp [h,e,f]
  rw [he]
  exact matrix_norm_reindex B e f
end TensorEnergy

theorem spatialAdjoint_split_eLpNorm {S : Type} [Fintype S] {d s : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (N : ℕ → Point d → ℝ) (hN0 : ∀e x,0≤N e x)
    (hN : ∀e x,TensorEnergy.AllSplitBound
      (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*(s+1)) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e)
    (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
    eLpNorm (fun x => ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖)
      (2*(s+1):ℝ≥0∞) (gibbs H)≤
      (3*(2*(s+1))+1)*(d:ℝ≥0∞)^((Fintype.card (TensorEnergy.OutSlots p):ℝ)/(2*(s+1):ℝ))*
        A^(2*(j+1))*R^(k+j+1) := by
  simp_rw [TensorEnergy.spatialAdjoint_matrix_norm]
  apply adjoint_eLpNorm _ _ (Fintype.card_pos) (Fintype.card_pos) hH ht hK
    (fun _ _ => spatialInside_polySmooth F hF _ _ _) (fun e => spatialEnvelope F (j+e)) N
    (fun e x => spatialEnvelope_nonneg F _ x) hN0
    (fun e x => ?_) hN j k A R hA hR hAf hRf
    (fun e => (ENNReal.measurable_ofReal.comp (spatialEnvelope_measurable F hF _)).aemeasurable) hp hh
  simpa only [Fintype.card_fin] using fieldPosition_spatialInside_allSplit F hF
    (List.finRange j) (List.nodup_finRange j) (by simp) (TensorEnergy.splitFin p) e x

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

lemma spatialAdjoint_polySmooth {K S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (l : List K) (c : K ⊕ S → Fin d) :
    PolySmooth (fun y => spatialAdjointLeading H F l y c) :=
  hH.tensorAdjoint (fun z => spatialInside_polySmooth F hF l c z) _

lemma traceDimensionRoot {d j a c n : ℕ} (hd : 1≤d) (hc : 1 ≤ c) (hn : 2≤n)
    (ha : a≤j+c) :
    (d:ℝ≥0∞)^((a:ℝ)/(2*(traceMomentOrder d j c n:ℝ)))≤ENNReal.ofReal (Real.exp (1/2)) := by
  have ht := traceMomentOrder_bounds (d:=d) (j:=j) (by exact_mod_cast hc : (1:ℝ) ≤ c)
    (by exact_mod_cast hn : (2:ℝ)≤n)
  have hs : 0<(traceMomentOrder d j c n:ℝ) := by exact_mod_cast ht.1
  have hupper := traceMomentOrder_dimension_root (d:=d) (j:=j) hd
    (by exact_mod_cast hc : (1:ℝ) ≤ c) (by exact_mod_cast hn : (2:ℝ)≤n)
  apply (ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd : (1:ℝ≥0∞)≤d)
    (div_le_div_of_nonneg_right (by exact_mod_cast ha : (a:ℝ)≤j+(c:ℝ)) (by positivity))).trans
  rw [←ENNReal.ofReal_natCast d,
    ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg d) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hupper

theorem spatialAdjoint_envelope_moment {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (N : ℕ → Point d → ℝ) (hN0 : ∀e x,0≤N e x)
    (hN : ∀e x,TensorEnergy.AllSplitBound
      (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e x) (N e x))
    (j k n : ℕ) (hd : 1≤d) (hn : 2≤n)
    (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hp : ∀e≤2*traceMomentOrder d j (Fintype.card S+1) n,
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*traceMomentOrder d j (Fintype.card S+1) n) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*traceMomentOrder d j (Fintype.card S+1) n))
    (hh : ∀e≤2*traceMomentOrder d j (Fintype.card S+1) n,∀x,
      ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    (∫⁻x,ENNReal.ofReal (TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x))^n ∂gibbs H)≤
      ((2:ℝ≥0∞)^(j+Fintype.card S)*
        ((3*(2*traceMomentOrder d j (Fintype.card S+1) n)+1)*ENNReal.ofReal (Real.exp (1/2))*
          A^(2*(j+1))*R^(k+j+1)))^n := by
  let t := traceMomentOrder d j (Fintype.card S+1) n
  have ht0 : 0<t := (traceMomentOrder_bounds (d:=d) (j:=j)
    (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card S); linarith : (1:ℝ)≤(Fintype.card S:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).1
  have hn2 : n≤2*t := by
    change n≤2*traceMomentOrder d j (Fintype.card S+1) n
    exact_mod_cast (traceMomentOrder_bounds (d:=d) (j:=j)
      (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card S); linarith : (1:ℝ)≤(Fintype.card S:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).2.1
  have he : t-1+1=t := Nat.sub_add_cancel ht0
  have heR : ((t-1:ℕ):ℝ≥0∞)+1=(t:ℝ≥0∞) := by exact_mod_cast he
  have heQ : (t-1:ℕ)+1=t := he
  have heQ' : ((t-1:ℕ):ℝ)+1=(t:ℝ) := by exact_mod_cast heQ
  have hmeas (c : Fin j ⊕ S → Fin d) : Measurable (fun x => spatialAdjointLeading H F (List.finRange j) x c) :=
    (spatialAdjoint_polySmooth hH F hF _ c).smooth.continuous.measurable
  have hlarge (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
      eLpNorm (fun x => ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖)
        (2*t:ℝ≥0∞) (gibbs H)≤
      (3*(2*t)+1)*ENNReal.ofReal (Real.exp (1/2))*A^(2*(j+1))*R^(k+j+1) := by
    have h := spatialAdjoint_split_eLpNorm (s:=t-1) hH ht hK F hF N hN0 hN j k A R hA hR hAf hRf
      (by simpa only [he] using hp) (by simpa only [he] using hh) p
    simp only [heR,heQ'] at h
    have hcard : Fintype.card (TensorEnergy.OutSlots p)≤j+(Fintype.card S+1) := by
      have hh := Fintype.card_subtype_le (fun s : Fin j ⊕ S => ¬p.val s=true)
      change Fintype.card (TensorEnergy.OutSlots p)≤_ at hh
      simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_assoc,Nat.succ_eq_add_one] using hh.trans (Nat.le_succ _)
    have hroot := traceDimensionRoot (d:=d) (j:=j) (a:=Fintype.card (TensorEnergy.OutSlots p))
      (c:=Fintype.card S+1) (n:=n) hd (Nat.le_add_left 1 _) hn hcard
    simp only [Nat.cast_add,Nat.cast_one] at hroot
    exact h.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hroot) le_rfl) le_rfl)
  have hsmall (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
      (∫⁻x,ENNReal.ofReal ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖^n ∂gibbs H)≤
      ((3*(2*t)+1)*ENNReal.ofReal (Real.exp (1/2))*A^(2*(j+1))*R^(k+j+1))^n := by
    apply (norm_le_iff_natural_moment (μ:=gibbs H) (fun _ => norm_nonneg _) (by omega) _).mp
    have hnorm := eLpNorm_nnreal_eq_eLpNorm' (μ:=gibbs H) (p:=(n:ℝ≥0))
      (by exact_mod_cast (show n ≠ 0 by omega))
      (f := fun x => ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖)
    simp only [ENNReal.coe_natCast,NNReal.coe_natCast] at hnorm
    rw [←hnorm]
    apply (eLpNorm_le_eLpNorm_of_exponent_le
      (show (n:ℝ≥0∞)≤2*(t:ℝ≥0∞) by exact_mod_cast hn2)
      (TensorEnergy.measurable_splitMatrix_norm _ hmeas p).aestronglyMeasurable).trans
    exact hlarge p
  simpa only [Fintype.card_sum,Fintype.card_fin] using
    TensorEnergy.moment_splitEnvelope (gibbs H) (spatialAdjointLeading H F (List.finRange j))
      hmeas (by omega : 0<n) _ hsmall

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AnalyticBase
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
open scoped Classical BigOperators ENNReal

lemma spatial_contract_allSplit {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound
      (spatialTensor (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a)
        (List.finRange j) y)
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialEnvelope F s.card y*spatialEnvelope G (j-s.card) y) := by
  have ht := spatialTensor_singleContract F G (fun c => (hF c).smooth) (fun c => (hG c).smooth)
    (List.finRange j) (List.nodup_finRange j) y
  have ht' : spatialTensor (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a)
      (List.finRange j) y=(fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialContractTerm (fun k => k∈s) F G (List.finRange j) y c) := by
    funext c
    convert ht c using 1
    · congr 1
      · ext s
        simp only [Finset.mem_powerset,Finset.subset_univ,true_iff]
        intro k _
        simp
      · funext s
        congr 1
  rw [ht']
  apply TensorEnergy.AllSplitBound.sum
  · intro s _; exact mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)
  · intro s _
    have hfs := spatialTensor_allSplit_envelope F (fun c => (hF c).smooth)
      (selectList (fun k => k∈s) (List.finRange j))
      (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
    have hgs := spatialTensor_allSplit_envelope G (fun c => (hG c).smooth)
      (selectList (fun k => k∉s) (List.finRange j))
      (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
    simpa only [Fintype.card_coe,Fintype.card_subtype_compl,Fintype.card_fin] using
      spatialContractTerm_allSplit (fun k => k∈s) hfs hgs

lemma spatialEnvelope_contract {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (j : ℕ) (y : Point d) :
    spatialEnvelope (fun a x => TensorEnergy.singleContract (fun c => F c x) (fun c => G c x) a) j y ≤
      (2:ℝ)^(j+Fintype.card S+Fintype.card T)*
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,
          spatialEnvelope F s.card y*spatialEnvelope G (j-s.card) y := by
  have hh := TensorEnergy.splitEnvelope_le_pow
    (Finset.sum_nonneg (fun s _ => mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)))
    (spatial_contract_allSplit F G hF hG j y)
  simpa only [spatialEnvelope,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using hh

theorem spatialEnvelope_contract_moment {S T : Type} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ} (μ : Measure (Point d))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    (j n : ℕ) (hn : 0<n) (A B : ℕ → ℝ≥0∞)
    (hA : ∀e≤j,(∫⁻x,ENNReal.ofReal (spatialEnvelope F e x)^(2*n) ∂μ)≤(A e)^(2*n))
    (hB : ∀e≤j,(∫⁻x,ENNReal.ofReal (spatialEnvelope G e x)^(2*n) ∂μ)≤(B e)^(2*n)) :
    (∫⁻x,ENNReal.ofReal (spatialEnvelope
      (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a) j x)^n ∂μ)≤
      ((2:ℝ≥0∞)^(j+Fintype.card S+Fintype.card T)*
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card))^n := by
  let U : Finset (Fin j) → Point d → ℝ := fun s x =>
    spatialEnvelope F s.card x*spatialEnvelope G (j-s.card) x
  let P := (Finset.univ : Finset (Fin j)).powerset
  have hu (s : Finset (Fin j)) (x : Point d) : 0≤U s x :=
    mul_nonneg (spatialEnvelope_nonneg _ _ _) (spatialEnvelope_nonneg _ _ _)
  have hm (s : Finset (Fin j)) : AEStronglyMeasurable (U s) μ :=
    ((spatialEnvelope_measurable F hF _).mul (spatialEnvelope_measurable G hG _)).aestronglyMeasurable
  have hp (s : Finset (Fin j)) (_ : s∈P) : (∫⁻x,ENNReal.ofReal (U s x)^n ∂μ)≤
      (A s.card*B (j-s.card))^n := by
    have hs : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    exact natural_moment_mul (spatialEnvelope_measurable F hF _).aestronglyMeasurable
      (spatialEnvelope_measurable G hG _).aestronglyMeasurable
      (spatialEnvelope_nonneg F _) (spatialEnvelope_nonneg G _) n _ _
      (hA s.card hs) (hB (j-s.card) (Nat.sub_le _ _))
  have hh := natural_moment_const_mul
    (fun x => Finset.sum_nonneg (fun s _ => hu s x)) n
    (by positivity : (0:ℝ)≤2^(j+Fintype.card S+Fintype.card T)) _
    (natural_moment_sum_finset P U (fun s _ => hm s) (fun s _ => hu s) hn
      (fun s => A s.card*B (j-s.card)) hp)
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (spatialEnvelope_contract F G hF hG j x)) n)).trans
  simpa only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

lemma analyticBase_one_le (d j n : ℕ) : 1≤analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  dsimp [analyticBase]; linarith [Nat.cast_nonneg (α:=ℝ) j,Nat.cast_nonneg (α:=ℝ) n]

lemma analyticBase_nat_le (d j n : ℕ) : (n:ℝ)≤analyticBase d j n ∧ (j:ℝ)+1≤analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  dsimp [analyticBase]; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) j,Nat.cast_nonneg (α:=ℝ) n]

lemma analyticBase_double {d j n e : ℕ} (he : e≤j) :
    analyticBase d e (2*n)≤2*analyticBase d j n := by
  have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
  have he' : (e:ℝ)≤j := by exact_mod_cast he
  simp only [analyticBase,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) j]

lemma analyticBase_mono {d j n e m : ℕ} (he : e≤j) (hm : m≤n) :
    analyticBase d e m≤analyticBase d j n := by
  have he' : (e:ℝ)≤j := by exact_mod_cast he
  have hm' : (m:ℝ)≤n := by exact_mod_cast hm
  dsimp [analyticBase]; linarith

lemma traceMomentOrder_budget {d j c n : ℕ} (hc : 1 ≤ c) (hn : 2≤n) :
    (traceMomentOrder d j c n:ℝ)≤(c:ℝ)*(analyticBase d j n)^2 := by
  have ht := traceMomentOrder_polynomial (d:=d) (j:=j)
    (by exact_mod_cast hc : (1:ℝ) ≤ c) (by exact_mod_cast hn : (2:ℝ)≤n)
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
  apply pow_le_pow_left₀
  · have := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    positivity
  · dsimp [analyticBase]; linarith

lemma TameAt.with_base {S : Type} [Fintype S] {d : ℕ} {μ : Measure (Point d)}
    {F : (S → Fin d) → Point d → ℝ} {k C : ℕ} {R : ℝ≥0∞}
    (h : TameAt μ F k C R) (j n : ℕ) (hn : 2≤n) (D : ℝ≥0∞)
    (hD : (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)≤D) :
    (∫⁻x,ENNReal.ofReal (spatialEnvelope F j x)^n ∂μ)≤(D^(C*(j+1))*R^(k+j))^n :=
  (h j n hn).trans (pow_le_pow_left' (mul_le_mul' (pow_le_pow_left' hD _) le_rfl) _)

lemma ofReal_base_one_le (d j n : ℕ) : (1:ℝ≥0∞)≤ENNReal.ofReal (analyticBase d j n) := by
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (analyticBase_one_le d j n)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

lemma subset_sum_le_common {j : ℕ} {f : Finset (Fin j) → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀s : Finset (Fin j),f s≤B) :
    (∑s∈(Finset.univ : Finset (Fin j)).powerset,f s)≤(2:ℝ≥0∞)^j*B := by
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin j)).powerset) (fun s _ => h s)
  simpa only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

lemma profile_base_double {d j n e C D : ℕ} (he : e≤j) (hC : 2*C≤D) :
    (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d e (2*n))≤
      (D:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n) := by
  have hh := ENNReal.ofReal_le_ofReal (analyticBase_double (d:=d) (n:=n) he)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat] at hh
  calc
    _ ≤ (C:ℝ≥0∞)*(2*ENNReal.ofReal (analyticBase d j n)) := mul_le_mul' le_rfl hh
    _ = (2*(C:ℝ≥0∞))*ENNReal.ofReal (analyticBase d j n) := by ring
    _ ≤ _ := mul_le_mul' (by exact_mod_cast hC) le_rfl

theorem TameAt.contract {S T : Type} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {d : ℕ} (μ : Measure (Point d))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    {k l C E : ℕ} {R : ℝ≥0∞} (hC : 20≤C) (hE : 20≤E)
    (hf : TameAt μ F k C R) (hg : TameAt μ G l E R) :
    TameAt μ (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a)
      (k+l) (4*(C+E+Fintype.card S+Fintype.card T+1)) R := by
  intro j n hn
  let q := 4*(C+E+Fintype.card S+Fintype.card T+1)
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  have hq : C+E+Fintype.card S+Fintype.card T+2≤q := by dsimp [q]; omega
  have hD2 : 2≤D := by
    have hq2 : 2≤q := by omega
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast hq2) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  let A : ℕ → ℝ≥0∞ := fun e => D^(C*(e+1))*R^(k+e)
  let B : ℕ → ℝ≥0∞ := fun e => D^(E*(e+1))*R^(l+e)
  have ha (e : ℕ) (he : e≤j) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F e x)^(2*n) ∂μ)≤(A e)^(2*n) :=
    hf.with_base e (2*n) (by omega) D (profile_base_double he (by dsimp [q]; omega))
  have hb (e : ℕ) (he : e≤j) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope G e x)^(2*n) ∂μ)≤(B e)^(2*n) :=
    hg.with_base e (2*n) (by omega) D (profile_base_double he (by dsimp [q]; omega))
  have hsum : (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card))≤
      (2:ℝ≥0∞)^j*(D^((C+E)*(j+1))*R^(k+l+j)) := by
    apply subset_sum_le_common
    intro s
    have hs : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    have he : C*(s.card+1)+E*(j-s.card+1)≤(C+E)*(j+1) := by
      simpa only [Nat.add_mul] using Nat.add_le_add
        (Nat.mul_le_mul_left C (by omega : s.card+1≤j+1))
        (Nat.mul_le_mul_left E (by omega : j-s.card+1≤j+1))
    dsimp [A,B]
    rw [mul_mul_mul_comm,←pow_add,←pow_add,show k+s.card+(l+(j-s.card))=k+l+j from by omega]
    exact mul_le_mul' (pow_le_pow_right₀ hD he) le_rfl
  have htotal : (2:ℝ≥0∞)^(j+Fintype.card S+Fintype.card T)*
      ∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)≤
      D^(q*(j+1))*R^(k+l+j) := by
    calc
      _ ≤ D^(j+Fintype.card S+Fintype.card T)*
          (D^j*(D^((C+E)*(j+1))*R^(k+l+j))) :=
        mul_le_mul' (pow_le_pow_left' hD2 _) (hsum.trans (mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl))
      _ = D^(j+Fintype.card S+Fintype.card T+j+(C+E)*(j+1))*R^(k+l+j) := by rw [pow_add,pow_add]; ring
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        have he : j+Fintype.card S+Fintype.card T+j≤(Fintype.card S+Fintype.card T+2)*(j+1) := by nlinarith
        have hh := Nat.mul_le_mul_right (j+1) hq
        nlinarith
  exact (spatialEnvelope_contract_moment μ F G hF hG j n (by omega) A B ha hb).trans
    (pow_le_pow_left' htotal n)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

lemma adjointConstant_bounds {C s : ℕ} (hC : 20≤C) :
    C*(4*(s+1)+1)≤adjointConstant C s ∧
    80*(s+1)+120≤adjointConstant C s ∧
    18*(s+1)+3≤adjointConstant C s ∧
    4*C+2*s+5≤adjointConstant C s ∧ 120≤adjointConstant C s := by
  have hCs := Nat.mul_le_mul_right s hC
  dsimp [adjointConstant]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma adjoint_base_budget {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    (C:ℝ)*analyticBase d (j+e) (2*traceMomentOrder d j (s+1) n)≤
      ((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : b≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have he' : (e:ℝ)≤2*(t:ℝ) := by
    have he0 : e≤2*t := he
    exact_mod_cast he0
  have hj : (j:ℝ)+Real.log ((d:ℝ)+1)+1≤b := by
    dsimp [b,analyticBase]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : analyticBase d (j+e) (2*t)≤(4*((s:ℝ)+1)+1)*b^2 := by
    simp only [analyticBase,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add]
    nlinarith
  have hq1 : (1:ℝ)≤q := by
    have := (adjointConstant_bounds (s:=s) hC).2.2.2.2
    dsimp [q]; exact_mod_cast (by omega : 1≤adjointConstant C s)
  have hcoef : (C:ℝ)*(4*((s:ℝ)+1)+1)≤q := by
    exact_mod_cast (adjointConstant_bounds (s:=s) hC).1
  calc
    _ ≤ (C:ℝ)*((4*((s:ℝ)+1)+1)*b^2) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg C)
    _ = ((C:ℝ)*(4*((s:ℝ)+1)+1))*b^2 := by ring
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma adjoint_score_budget {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    40*((e:ℝ)+3)≤((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : 1≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have he' : (e:ℝ)≤2*(t:ℝ) := by
    have he0 : e≤2*t := he
    exact_mod_cast he0
  have hcoef : 80*((s:ℝ)+1)+120≤q := by exact_mod_cast (adjointConstant_bounds (s:=s) hC).2.1
  have hq1 : (1:ℝ)≤q := by nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  calc
    _ ≤ (80*((s:ℝ)+1)+120)*b^2 := by nlinarith
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma adjoint_trace_prefactor {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n) :
    (6*(traceMomentOrder d j (s+1) n:ℝ)+1)*Real.exp (1/2)≤
      ((adjointConstant C s:ℝ)*analyticBase d j n)^2 := by
  let b := analyticBase d j n
  let t := traceMomentOrder d j (s+1) n
  let q := adjointConstant C s
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb2 : 1≤b^2 := by nlinarith
  have ht : (t:ℝ)≤((s:ℝ)+1)*b^2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using traceMomentOrder_budget (d:=d) (j:=j)
      (c:=s+1) (n:=n) (by omega) hn
  have hcoef : 18*((s:ℝ)+1)+3≤q := by exact_mod_cast (adjointConstant_bounds (s:=s) hC).2.2.1
  have hq1 : (1:ℝ)≤q := by nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  have he : Real.exp (1/2)≤3 := (Real.exp_le_exp.mpr (by norm_num : (1:ℝ)/2≤1)).trans Real.exp_one_lt_three.le
  calc
    _ ≤ (6*(t:ℝ)+1)*3 := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ (18*((s:ℝ)+1)+3)*b^2 := by nlinarith
    _ ≤ (q:ℝ)*b^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
    _ ≤ (q:ℝ)^2*b^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg b)
    _ = _ := by ring

lemma natural_moment_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀x,0≤f x) (hg0 : ∀x,0≤g x) {n : ℕ} (hn : 0<n) (A B : ℝ≥0∞)
    (hA : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)≤A^n)
    (hB : (∫⁻x,ENNReal.ofReal (g x)^n ∂μ)≤B^n) :
    (∫⁻x,ENNReal.ofReal (f x+g x)^n ∂μ)≤(A+B)^n := by
  apply (norm_le_iff_natural_moment (fun x => add_nonneg (hf0 x) (hg0 x)) hn _).mp
  exact (eLpNorm'_add_le hf hg (by exact_mod_cast hn : (1:ℝ)≤n)).trans
    (add_le_add ((norm_le_iff_natural_moment hf0 hn _).mpr hA)
      ((norm_le_iff_natural_moment hg0 hn _).mpr hB))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators

lemma scoreField_arbitrary_allSplit {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ (⊤:ℕ∞) H)
    {K : Type} [Fintype K] (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d)
    (M : ℝ) (hM : TensorEnergy.AllSplitBound
      (spatialTensor (scoreField H) (List.finRange (Fintype.card K)) y) M) :
    TensorEnergy.AllSplitBound (spatialTensor (scoreField H) l y) M := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := spatialTensor_allSplit_relabel (scoreField H) (fun _ => directional_smooth hH _)
    (Equiv.refl _) e (List.finRange (Fintype.card K)) l hp y M hM
  simpa only [Function.comp_def,Equiv.refl_apply] using hh

lemma spatialTensor_adjoint_sum {K S : Type} {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (y : Point d) :
    spatialTensor (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) l y =
      fun c => spatialAdjointLeading H F l y c+adjointCommutator H F l y c := by
  funext c
  rw [spatialTensor_adjoint hH F hF l hl y c]
  congr 1
  unfold adjointCommutator
  apply Finset.sum_congr rfl
  intro s _
  rw [spatialContractTerm_eq]
  apply Finset.sum_congr rfl
  intro z _
  congr 1

lemma adjointCommutator_allSplit {K S : Type} [Fintype K] [Fintype S] [Nonempty S]
    {d : ℕ} {H : Point d → ℝ} (hH : ContDiff ℝ (⊤:ℕ∞) H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d)
    (M : ℕ → ℝ) (hM0 : ∀e,0≤M e)
    (hM : ∀e,0<e → TensorEnergy.AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    TensorEnergy.AllSplitBound (adjointCommutator H F l y)
      (∑s∈l.toFinset.powerset.erase ∅, M s.card*spatialEnvelope F (Fintype.card K-s.card) y) := by
  apply TensorEnergy.AllSplitBound.sum
  · intro s _; exact mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)
  · intro s hs
    have hs0 : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
    let : Nonempty {k // k∈s} := ⟨⟨hs0.choose,hs0.choose_spec⟩⟩
    have hh := scoreField_arbitrary_allSplit hH
      (selectList (fun k => k∈s) l) (selectList_nodup _ hl) (selectList_full _ hall) y _
      (hM (Fintype.card {k // k∈s}) Fintype.card_pos)
    have hf := spatialTensor_allSplit_envelope F hF
      (selectList (fun k => k∉s) l) (selectList_nodup _ hl) (selectList_full _ hall) y
    have hb := (spatialContractTerm_allSplit_nonempty (fun k => k∈s) hh hf).reindex
      (scoreContractSlots K S)
    simpa only [Fintype.card_coe,Fintype.card_subtype_compl] using hb

lemma spatialEnvelope_adjoint {S : Type} [Fintype S] [Nonempty S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) (y : Point d)
    (M : ℕ → ℝ) (hM0 : ∀e,0≤M e)
    (hM : ∀e,0<e → TensorEnergy.AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    spatialEnvelope (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j y≤
      (2:ℝ)^(j+Fintype.card S)*(TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) y)+
        ∑s∈(Finset.univ : Finset (Fin j)).powerset,M s.card*spatialEnvelope F (j-s.card) y) := by
  have hh := (TensorEnergy.allSplitBound_envelope (spatialAdjointLeading H F (List.finRange j) y)).add
    (adjointCommutator_allSplit hH.smooth F (fun c => (hF c).smooth) (List.finRange j)
      (List.nodup_finRange _) (by simp) y M hM0 hM)
    (TensorEnergy.splitEnvelope_nonneg _)
    (Finset.sum_nonneg (fun s _ => mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)))
  rw [←spatialTensor_adjoint_sum hH F hF _ (List.nodup_finRange _) y] at hh
  have hb := TensorEnergy.splitEnvelope_le_pow
    (add_nonneg (TensorEnergy.splitEnvelope_nonneg _) (Finset.sum_nonneg (fun s _ =>
      mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)))) hh
  simp only [Fintype.card_sum,Fintype.card_fin] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  · intro s _ _; exact mul_nonneg (hM0 _) (spatialEnvelope_nonneg _ _ _)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma adjoint_base_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    (C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d (j+e) (2*traceMomentOrder d j (s+1) n))≤
      ((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_base_budget hC hn e he)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _)))] using hh

lemma adjoint_score_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n)
    (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
    40*((e:ℝ≥0∞)+3)≤((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_score_budget hC hn e he)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤40),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _))),
    ENNReal.ofReal_mul (Nat.cast_nonneg _)] using hh

lemma adjoint_trace_enn {d j n C s : ℕ} (hC : 20≤C) (hn : 2≤n) :
    (3*(2*traceMomentOrder d j (s+1) n)+1:ℝ≥0∞)*ENNReal.ofReal (Real.exp (1/2))≤
      ((adjointConstant C s:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^2 := by
  have hh := ENNReal.ofReal_le_ofReal (adjoint_trace_prefactor (d:=d) (j:=j) (s:=s) hC hn)
  simp only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤6*(traceMomentOrder d j (s+1) n:ℝ)+1),
    ENNReal.ofReal_add (by positivity : (0:ℝ)≤6*(traceMomentOrder d j (s+1) n:ℝ)) (by norm_num : (0:ℝ)≤1),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6),ENNReal.ofReal_ofNat,ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (analyticBase_one_le _ _ _))),
    ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hh
  convert hh using 1 <;> first | rfl | ring

theorem TameAt.adjoint {S : Type} [Fintype S] [Nonempty S] {d : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    {k C : ℕ} {R : ℝ≥0∞} (hd : 1≤d) (hC : 20≤C) (hR : 1≤R) (hRf : R≠⊤)
    (hscore : TameScore H R) (hf : TameAt (gibbs H) F k C R) :
    TameAt (gibbs H) (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) (k+1) (adjointConstant C (Fintype.card S)) R := by
  intro j n hn
  let s := Fintype.card S
  let q := adjointConstant C s
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  let A : ℝ≥0∞ := D^(2*C)
  have hq120 : 120≤q := (adjointConstant_bounds (s:=s) hC).2.2.2.2
  have hCq : C≤q := by dsimp [q,adjointConstant]; nlinarith
  have hD2 : 2≤D := by
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast (by omega : 2≤q)) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  have hDf : D≠⊤ := by dsimp [D]; finiteness
  have hA : 1≤A := one_le_pow₀ hD
  have hAf : A≠⊤ := ENNReal.pow_ne_top hDf
  let B : ℝ≥0∞ := D^((4*C+s+3)*(j+1))*R^(k+j+1)
  have hp (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) :
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*traceMomentOrder d j (s+1) n) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*traceMomentOrder d j (s+1) n) := by
    have ht0 := (traceMomentOrder_bounds (d:=d) (j:=j)
      (by have := Nat.cast_nonneg (α:=ℝ) s; linarith : (1:ℝ)≤(s:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).1
    have hh := hf.with_base (j+e) _ (by omega) (D^2) (adjoint_base_enn hC hn e he)
    simpa only [A,←pow_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using hh
  have hh (e : ℕ) (he : e≤2*traceMomentOrder d j (s+1) n) (x : Point d) :
      ENNReal.ofReal (hscore.bound e)≤A^(e+1)*R^e := by
    apply (hscore.budget e).trans
    apply mul_le_mul' _ le_rfl
    apply (pow_le_pow_left' (adjoint_score_enn hC hn e he) _).trans
    simp only [A,←pow_mul]
    apply pow_le_pow_right₀ hD
    have := Nat.mul_le_mul_right (e+1) (by omega : 32≤2*C)
    nlinarith
  have hl : (∫⁻x,ENNReal.ofReal (TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x))^n ∂gibbs H)≤B^n := by
    apply (spatialAdjoint_envelope_moment hH ht hK F hF (fun e _ => hscore.bound e)
      (fun e _ => hscore.nonneg e) hscore.hessian j k n hd hn A R hA hR hAf hRf hp hh).trans
    apply pow_le_pow_left'
    calc
      _ ≤ D^(j+s)*(D^2*A^(2*(j+1))*R^(k+j+1)) :=
        mul_le_mul' (pow_le_pow_left' hD2 _) (mul_le_mul' (mul_le_mul' (adjoint_trace_enn hC hn) le_rfl) le_rfl)
      _ = D^(j+s+2+4*C*(j+1))*R^(k+j+1) := by dsimp [A]; rw [←pow_mul]; ring_nf
      _ ≤ B := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        nlinarith
  let U : Finset (Fin j) → Point d → ℝ := fun a x => hscore.bound a.card*spatialEnvelope F (j-a.card) x
  let P := (Finset.univ : Finset (Fin j)).powerset
  let E : ℝ≥0∞ := D^(2*C*(j+1))*R^(k+j+1)
  have hu0 (a : Finset (Fin j)) (x : Point d) : 0≤U a x :=
    mul_nonneg (hscore.nonneg _) (spatialEnvelope_nonneg _ _ _)
  have hum (a : Finset (Fin j)) : AEStronglyMeasurable (U a) (gibbs H) :=
    ((spatialEnvelope_measurable F hF _).const_mul _).aestronglyMeasurable
  have hsbase (e : ℕ) (he : e≤j) : 40*((e:ℝ≥0∞)+3)≤D := by
    have he' : (e:ℝ)≤j := by exact_mod_cast he
    have hb := (analyticBase_nat_le d j n).2
    have hb0 : 0≤analyticBase d j n := (zero_le_one.trans (analyticBase_one_le _ _ _))
    have hq' : (120:ℝ)≤q := by exact_mod_cast hq120
    have hb' : 40*((e:ℝ)+3)≤(q:ℝ)*analyticBase d j n := by nlinarith
    have hb'' := ENNReal.ofReal_le_ofReal hb'
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤40),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (Nat.cast_nonneg _)] using hb''
  have hup (a : Finset (Fin j)) : (∫⁻x,ENNReal.ofReal (U a x)^n ∂gibbs H)≤E^n := by
    have ha : a.card≤j := (Finset.card_le_univ a).trans_eq (Fintype.card_fin j)
    have hm := hf.with_base (j-a.card) n hn D (mul_le_mul' (by exact_mod_cast hCq)
      (ENNReal.ofReal_le_ofReal (analyticBase_mono (Nat.sub_le _ _) le_rfl)))
    have hh := natural_moment_const_mul (spatialEnvelope_nonneg F _) n (hscore.nonneg a.card) _ hm
    apply hh.trans
    apply pow_le_pow_left'
    calc
      _ ≤ (D^(16*(a.card+1))*R^a.card)*(D^(C*(j-a.card+1))*R^(k+(j-a.card))) :=
        mul_le_mul' ((hscore.budget a.card).trans (mul_le_mul' (pow_le_pow_left' (hsbase a.card ha) _) le_rfl)) le_rfl
      _ = D^(16*(a.card+1)+C*(j-a.card+1))*R^(k+j) := by
        rw [mul_mul_mul_comm,←pow_add,←pow_add,show a.card+(k+(j-a.card))=k+j from by omega]
      _ ≤ E := by
        apply mul_le_mul' _ (pow_le_pow_right₀ hR (by omega))
        apply pow_le_pow_right₀ hD
        have h16 := Nat.mul_le_mul_right (a.card+1) (by omega : 16≤C)
        have he := Nat.sub_add_cancel ha
        nlinarith
  have hsum : (∫⁻x,ENNReal.ofReal (∑a∈P,U a x)^n ∂gibbs H)≤((2:ℝ≥0∞)^j*E)^n := by
    have hm := natural_moment_sum_finset P U (fun a _ => hum a) (fun a _ => hu0 a) (by omega) (fun _ => E) (fun a _ => hup a)
    apply hm.trans
    apply pow_le_pow_left'
    exact subset_sum_le_common (fun _ => le_rfl)
  have hsB : (2:ℝ≥0∞)^j*E≤B := by
    calc
      _ ≤ D^j*E := mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl
      _ = D^(j+2*C*(j+1))*R^(k+j+1) := by dsimp [E]; rw [pow_add]; ring
      _ ≤ B := by
        apply mul_le_mul' _ le_rfl
        apply pow_le_pow_right₀ hD
        nlinarith
  have hlm : AEStronglyMeasurable (fun x => TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x)) (gibbs H) :=
    (TensorEnergy.measurable_splitEnvelope _ (fun c => (spatialAdjoint_polySmooth hH F hF _ c).smooth.continuous.measurable)).aestronglyMeasurable
  have hsm : AEStronglyMeasurable (fun x => ∑a∈P,U a x) (gibbs H) := by
    have he : (fun x => ∑a∈P,U a x)=∑a∈P,U a := by ext x; simp
    rw [he]
    exact Finset.aestronglyMeasurable_sum P (fun a _ => hum a)
  have hsum0 (x : Point d) : 0≤∑a∈P,U a x := Finset.sum_nonneg (fun a _ => hu0 a x)
  have hcomb := natural_moment_add hlm hsm (fun _ => TensorEnergy.splitEnvelope_nonneg _) hsum0
    (by omega : 0<n) B B hl (hsum.trans (pow_le_pow_left' hsB n))
  have hscale := natural_moment_const_mul (fun x => add_nonneg (TensorEnergy.splitEnvelope_nonneg _) (hsum0 x))
    n (by positivity : (0:ℝ)≤2^(j+s)) _ hcomb
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (spatialEnvelope_adjoint hH F hF j x hscore.bound hscore.nonneg (fun e he => hscore.spatial e he x))) n)).trans
  apply hscale.trans
  apply pow_le_pow_left'
  simp only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
  calc
    _ = (2:ℝ≥0∞)^(j+s)*(2*B) := by rw [two_mul]
    _ ≤ D^(j+s)*(D*B) := mul_le_mul' (pow_le_pow_left' hD2 _) (mul_le_mul' hD2 le_rfl)
    _ = D^(j+s+1+(4*C+s+3)*(j+1))*R^(k+j+1) := by dsimp [B]; rw [pow_add,pow_add]; ring
    _ ≤ D^(q*(j+1))*R^((k+1)+j) := by
      rw [show k+1+j=k+j+1 by omega]
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_right₀ hD
      have hq := (adjointConstant_bounds (s:=s) hC).2.2.2.1
      have hh := Nat.mul_le_mul_right (j+1) hq
      dsimp [q] at *
      nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Reindex
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
open scoped Classical BigOperators ENNReal

theorem TameAt.reindex {S T : Type} [Fintype S] [Fintype T] {d : ℕ}
    (μ : Measure (Point d)) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (e : S ≃ T)
    {k C : ℕ} {R : ℝ≥0∞} (hC : 20≤C) (hf : TameAt μ F k C R) :
    TameAt μ (fun a => F (a ∘ e)) k (4*(C+Fintype.card T+1)) R := by
  intro j n hn
  let q := 4*(C+Fintype.card T+1)
  let D : ℝ≥0∞ := (q:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n)
  have hq : C+Fintype.card T+1≤q := by dsimp [q]; omega
  have hD2 : 2≤D := by
    simpa only [mul_one] using mul_le_mul' (show (2:ℝ≥0∞)≤q by exact_mod_cast (by omega : 2≤q)) (ofReal_base_one_le d j n)
  have hD : 1≤D := (by norm_num : (1:ℝ≥0∞)≤2).trans hD2
  have hpoint (x : Point d) : spatialEnvelope (fun a => F (a ∘ e)) j x≤
      (2:ℝ)^(j+Fintype.card T)*spatialEnvelope F j x := by
    have hh := spatialTensor_allSplit_relabel F (fun c => (hF c).smooth) e (Equiv.refl (Fin j))
      (List.finRange j) (List.finRange j) (by simp) x _ (TensorEnergy.allSplitBound_envelope _)
    have hb := TensorEnergy.splitEnvelope_le_pow (spatialEnvelope_nonneg F j x) hh
    simpa only [spatialEnvelope,Fintype.card_sum,Fintype.card_fin] using hb
  have hm := hf.with_base j n hn D (mul_le_mul' (by exact_mod_cast (by omega : C≤q)) le_rfl)
  have hs := natural_moment_const_mul (spatialEnvelope_nonneg F j) n
    (by positivity : (0:ℝ)≤2^(j+Fintype.card T)) _ hm
  apply (lintegral_mono (fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hpoint x)) n)).trans
  apply hs.trans
  apply pow_le_pow_left'
  simp only [ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
  calc
    _ ≤ D^(j+Fintype.card T)*(D^(C*(j+1))*R^(k+j)) := mul_le_mul' (pow_le_pow_left' hD2 _) le_rfl
    _ = D^(j+Fintype.card T+C*(j+1))*R^(k+j) := by rw [pow_add]; ring
    _ ≤ D^(q*(j+1))*R^(k+j) := by
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_right₀ hD
      have hh := Nat.mul_le_mul_right (j+1) hq
      nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_FinSnocSlots
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
open scoped Classical BigOperators ENNReal NNReal

lemma physicalBase_envelope {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q j : ℕ) (y : Point d) :
    spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y≤
      (2:ℝ)^(j+q+2)*normalizedTensorMajorant (j+q+2) (1-ρ^2) := by
  unfold spatialEnvelope spatialTensor TensorExpression.physicalBase
  have hh := normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y
    (fun i : Fin (q+2) => decide (i=Fin.last (q+1))) (List.finRange (q+2)) (by simp)
    (List.nodup_finRange _) (by simp) (List.finRange j) (List.nodup_finRange _) (by simp)
  have hb := TensorEnergy.splitEnvelope_le_pow (normalizedTensorMajorant_nonneg _ _) hh
  simpa only [Fintype.card_sum,
    Fintype.card_fin,Nat.add_assoc] using hb

lemma physicalBase_envelope_budget {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q j n : ℕ) (y : Point d) :
    ENNReal.ofReal (spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y)≤
      (((100*(q+3):ℕ):ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^((100*(q+3))*(j+1))*
        ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(q+j) := by
  let C := 100*(q+3)
  let b := analyticBase d j n
  let D : ℝ := (C:ℝ)*b
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb' : (j:ℝ)+1≤b := (analyticBase_nat_le d j n).2
  have hD2 : 2≤D := by dsimp [D,C]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q]
  have hD : 1≤D := by linarith
  have hR0 : 0≤R := by dsimp [R]; positivity
  have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
  have hMb : 10*(((j+q+2:ℕ):ℝ)+1)≤D := by
    dsimp [D,C]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) j]
  have hp : spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y≤
      D^(C*(j+1))*R^(q+j) := by
    calc
      _ ≤ (2:ℝ)^(j+q+2)*normalizedTensorMajorant (j+q+2) (1-ρ^2) := physicalBase_envelope hF x hr hlam hl hρ0 hρ1 q j y
      _ ≤ (2:ℝ)^(j+q+2)*((10*(((j+q+2:ℕ):ℝ)+1))^(4*(j+q+2+1))*R^(j+q+2-2)) :=
        mul_le_mul_of_nonneg_left (normalizedTensorMajorant_le ha _) (by positivity)
      _ ≤ D^(j+q+2)*(D^(4*(j+q+3))*R^(q+j)) := by
        rw [show j+q+2-2=q+j by omega,show j+q+2+1=j+q+3 by omega]
        exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hD2 _) (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hMb _) (pow_nonneg hR0 _)) (by positivity) (by positivity)
      _ = D^(j+q+2+4*(j+q+3))*R^(q+j) := by rw [pow_add]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR0 _)
        apply pow_le_pow_right₀ hD
        dsimp [C]
        nlinarith only [Nat.zero_le (q*j),Nat.zero_le q,Nat.zero_le j]
  have hh := ENNReal.ofReal_le_ofReal hp
  simpa only [ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one hD) _),
    ENNReal.ofReal_pow (le_trans zero_le_one hD),ENNReal.ofReal_pow hR0,
    D,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] using hh

theorem physicalBase_tame {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (q : ℕ) :
    TameAt μ (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q)
      q (100*(q+3)) (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) := by
  intro j n _
  apply (lintegral_mono (fun y => pow_le_pow_left' (physicalBase_envelope_budget hF x hr hlam hl hρ0 hρ1 q j n y) n)).trans
  simp only [lintegral_const,measure_univ,mul_one,le_refl]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma finSnocSlots_castSucc (m : ℕ) (i : Fin m) : finSnocSlots m i.castSucc=Sum.inl i := by
  simp [finSnocSlots]

lemma finSnocSlots_last (m : ℕ) : finSnocSlots m (Fin.last m)=Sum.inr () := by
  simp [finSnocSlots,finOneEquiv]

lemma snoc_through_slots {m d : ℕ} (c : Fin m → Fin d) (z : Fin d) :
    (Sum.elim c (fun _ : Unit => z)) ∘ finSnocSlots m=Fin.snoc c z := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Function.comp_apply,finSnocSlots_last,Sum.elim_inr,Fin.snoc_last]
  · simp only [Function.comp_apply,finSnocSlots_castSucc,Sum.elim_inl,Fin.snoc_castSucc]

namespace TensorExpression

lemma profileConstant_ge {n : ℕ} (A : TensorExpression n) : 20≤A.profileConstant := by
  induction A with
  | jet q => dsimp [profileConstant]; omega
  | perm e A ih => dsimp [profileConstant]; omega
  | contract hm hn A B ihA ihB => dsimp [profileConstant]; omega
  | adjoint hn A ih =>
    dsimp [profileConstant]
    exact (by norm_num : 20≤120).trans (adjointConstant_bounds (by omega)).2.2.2.2

theorem eval_tame {d : ℕ} {base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) [IsProbabilityMeasure (gibbs H)]
    (hbase : ∀q c,PolySmooth (base q c)) {R : ℝ≥0∞}
    (hR : 1≤R) (hRf : R≠⊤) (hscore : TameScore H R) (hd : 1≤d)
    (hb : ∀q,TameAt (gibbs H) (base q) q (100*(q+3)) R)
    {n : ℕ} (A : TensorExpression n) :
    TameAt (gibbs H) (A.eval base H) A.weight A.profileConstant R := by
  induction A with
  | jet q => exact hb q
  | perm e A ih =>
    simp only [eval,weight,profileConstant]
    simpa only [Fintype.card_fin] using TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) e A.profileConstant_ge ih
  | @contract m n hm hn A B ihA ihB =>
    let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    let FA := fun a : Fin m ⊕ Unit → Fin d => A.eval base H (a ∘ finSnocSlots m)
    let FB := fun a : Fin n ⊕ Unit → Fin d => B.eval base H (a ∘ finSnocSlots n)
    have hFA : ∀c,PolySmooth (FA c) := fun c => eval_polySmooth hbase hH A _
    have hFB : ∀c,PolySmooth (FB c) := fun c => eval_polySmooth hbase hH B _
    have hta : TameAt (gibbs H) FA A.weight (4*(A.profileConstant+m+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) (finSnocSlots m) A.profileConstant_ge ihA
    have htb : TameAt (gibbs H) FB B.weight (4*(B.profileConstant+n+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (B.eval base H) (eval_polySmooth hbase hH B) (finSnocSlots n) B.profileConstant_ge ihB
    have hc := TameAt.contract (gibbs H) FA FB hFA hFB
      (by have := A.profileConstant_ge; omega) (by have := B.profileConstant_ge; omega) hta htb
    have hFc (a : Fin m ⊕ Fin n → Fin d) : PolySmooth
        (fun y => TensorEnergy.singleContract (fun c => FA c y) (fun c => FB c y) a) := by
      exact PolySmooth.sum Finset.univ (fun z _ => (hFA _).mul (hFB _))
    have hh := TameAt.reindex (gibbs H) _ hFc finSumFinEquiv
      (by simp only [Fintype.card_fin]; omega) hc
    have he : (fun a y => TensorEnergy.singleContract (fun c => FA c y) (fun c => FB c y) (a ∘ finSumFinEquiv))=
        (TensorExpression.contract hm hn A B).eval base H := by
      funext a y
      unfold TensorEnergy.singleContract TensorExpression.eval
      apply Finset.sum_congr rfl
      intro z _
      dsimp [FA,FB]
      rw [snoc_through_slots,snoc_through_slots]
    rw [he] at hh
    simpa only [profileConstant,weight,Fintype.card_fin,Nat.add_assoc] using hh
  | @adjoint n hn A ih =>
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    let FA := fun a : Fin n ⊕ Unit → Fin d => A.eval base H (a ∘ finSnocSlots n)
    have hFA : ∀c,PolySmooth (FA c) := fun c => eval_polySmooth hbase hH A _
    have hta : TameAt (gibbs H) FA A.weight (4*(A.profileConstant+n+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) (finSnocSlots n) A.profileConstant_ge ih
    have hh := TameAt.adjoint hH ht hK FA hFA hd (by have := A.profileConstant_ge; omega) hR hRf hscore hta
    have he : (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun z => FA (Sum.elim a (fun _ => z))))=(TensorExpression.adjoint hn A).eval base H := by
      funext a
      dsimp [FA,TensorExpression.eval]
      simp only [snoc_through_slots]
    rw [he] at hh
    simpa only [profileConstant,weight,Fintype.card_fin] using hh

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma physicalScale_one_le {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    1≤ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹) := by
  have ha := (probability_time hρ0 hρ1).1
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr ha
  have hu : Real.sqrt (1-ρ^2)≤1 := (Real.sqrt_le_one).mpr (by nlinarith [sq_nonneg ρ])
  exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_inv₀ hs |>.mpr hu)

theorem TensorExpression.physical_tame {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hd : 1≤d) {n : ℕ} (A : TensorExpression n) :
    TameAt (interpolationLaw F x r ρ)
      (A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ))
      A.weight A.profileConstant (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) := by
  have hlt : (lam:ℝ)*r^2<1 := by linarith
  have hp : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have he := interpolationLaw_eq_gibbs hF x hr.le hlt hp
  let : IsProbabilityMeasure (interpolationLaw F x r ρ) := interpolationLaw_probability hF x hr.le hlt ρ
  let : IsProbabilityMeasure (gibbs (interpolationPotential F x r ρ)) := he ▸ inferInstance
  rw [he]
  exact A.eval_tame (interpolationPotential_polySmooth hF x hr hlam hl hρ0 hρ1)
    (interpolationPotential_lowerTail hF x hr.le hlt hρ0 hρ1)
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hρ0 hρ1)
    (physicalBase_polySmooth hF x hr hlam hl hρ0 hρ1)
    (physicalScale_one_le hρ0 hρ1) ENNReal.ofReal_ne_top
    (physicalTameScore hF x hr hlam hl hρ0 hρ1) hd
    (physicalBase_tame hF x hr hlam hl hρ0 hρ1 _)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

lemma TameAt.eLpNorm {S : Type} [Fintype S] {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {F : (S → Fin d) → Point d → ℝ}
    (hF : ∀c,PolySmooth (F c)) {k C : ℕ} {R : ℝ≥0∞}
    (h : TameAt μ F k C R) (j : ℕ) {p : ℝ≥0∞} (hpf : p≠⊤) :
    eLpNorm (spatialEnvelope F j) p μ≤
      ((4*(C:ℝ≥0∞))*ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^(C*(j+1))*R^(k+j) := by
  let n := Nat.ceil p.toReal+2
  have hp : p≤(n:ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal hpf (ENNReal.natCast_ne_top n)).mp
    simp only [ENNReal.toReal_natCast]
    have hh := Nat.le_ceil p.toReal
    dsimp [n]
    push_cast
    linarith
  have hm : AEStronglyMeasurable (spatialEnvelope F j) μ :=
    (TensorEnergy.measurable_splitEnvelope _ (fun c =>
      ((hF _).jet _ _).smooth.continuous.measurable)).aestronglyMeasurable
  apply (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=spatialEnvelope F j) hp hm).trans
  have hnorm := eLpNorm_nnreal_eq_eLpNorm' (p:=(n:ℝ≥0))
    (by exact_mod_cast (show n ≠ 0 by omega)) (f := spatialEnvelope F j) (μ:=μ)
  simp only [ENNReal.coe_natCast,NNReal.coe_natCast] at hnorm
  rw [hnorm]
  apply ((norm_le_iff_natural_moment (μ:=μ) (spatialEnvelope_nonneg F j) (by omega : 0<n) _).mpr (h j n (by omega))).trans
  apply mul_le_mul' _ le_rfl
  apply pow_le_pow_left'
  have hb : analyticBase d j n≤4*(p.toReal+j+Real.log ((d:ℝ)+1)+1) := by
    have hceil' : (Nat.ceil p.toReal:ℝ)≤p.toReal+1 := (Nat.ceil_lt_add_one (ENNReal.toReal_nonneg)).le
    have hlog := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    dsimp [analyticBase,n]
    push_cast
    linarith [ENNReal.toReal_nonneg (a:=p),Nat.cast_nonneg (α:=ℝ) j]
  have hh := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat] at hh
  convert mul_le_mul' (le_refl (C:ℝ≥0∞)) hh using 1 <;> first | rfl | ring

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
lemma spatialBound_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (j : ℕ) : Measurable (A.spatialBound F x r ρ ((lam:ℝ)*r) j) :=
  spatialEnvelope_measurable _ (TensorExpression.eval_polySmooth
    (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression) j

omit [Fintype S] in
lemma spatialBound_Lp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorAtom S) (j : ℕ) {p : ℝ≥0∞} (hpf : p≠⊤) :
    eLpNorm (A.spatialBound F x r ρ ((lam:ℝ)*r) j) p (interpolationLaw F x r ρ)≤
      ((4*(A.expression.profileConstant:ℝ≥0∞))*ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        (A.expression.profileConstant*(j+1))*
      ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(A.expression.weight+j) := by
  let : IsProbabilityMeasure (interpolationLaw F x r ρ) := interpolationLaw_probability hF x hr.le (by linarith) ρ
  exact TameAt.eLpNorm (TensorExpression.eval_polySmooth
    (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression)
    (A.expression.physical_tame hF x hr hlam hl h0 h1 hd) j hpf
end TensorAtom

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
lemma spatialBound_Lp_oai {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum S) {w : ℕ} (hw : A.weightLE w)
    (j : ℕ) {p : ℝ≥0∞} (hp : 1≤p) (hpf : p≠⊤) :
    eLpNorm (A.spatialBound F x r ρ ((lam:ℝ)*r) j) p (interpolationLaw F x r ρ)≤
      A.momentBudget d j p*ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(w+j) := by
  let μ := interpolationLaw F x r ρ
  let V := fun i => (A.term i).atom.spatialBound F x r ρ ((lam:ℝ)*r) j
  let a := fun i => polynomialBudget (A.term i).coefficient
  have he : A.spatialBound F x r ρ ((lam:ℝ)*r) j=∑i,a i • V i := by
    funext y
    simp only [spatialBound,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,V,a]
  rw [he]
  apply (eLpNorm_sum_le (μ:=μ) (s:=Finset.univ) (f:=fun index => a index • V index)
    (fun i _ => (((A.term i).atom.spatialBound_measurable hF x hr hlam hl h0 h1 j).const_smul (a i)).aestronglyMeasurable) hp).trans
  rw [momentBudget,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_const_smul]
  have ha : ‖a i‖ₑ=ENNReal.ofReal (a i) := by
    rw [Real.enorm_eq_ofReal_abs,abs_of_nonneg (polynomialBudget_nonneg _)]
  rw [ha,mul_assoc]
  apply mul_le_mul' le_rfl
  apply ((A.term i).atom.spatialBound_Lp hF x hr hlam hl h0 h1 hd j hpf).trans
  apply mul_le_mul' le_rfl
  apply pow_le_pow_right'
  · apply ENNReal.one_le_ofReal.mpr
    have hs0 : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.2 (by nlinarith)
    have hs1 : Real.sqrt (1-ρ^2)≤1 := by
      exact (Real.sqrt_le_iff).2 ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
    exact (one_le_inv₀ hs0).mpr hs1
  · exact Nat.add_le_add_right (hw i) j
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.TensorSum.spatialBound_Lp_oai := @OAI.LogConcaveSampling.TensorSum.spatialBound_Lp_oai
