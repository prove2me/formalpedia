-- Prove2me | solution 1 for OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T14:00:12.21365+00:00
-- url     : https://prove2.me/submissions/e1d4b587-ac92-4425-9edc-2d6fabf5d908

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_TensorSum_spatialBound_Lp
import Theorems.Thm_OAI_LogConcaveSampling_kernelActionPicard_rms

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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointInterpolationLaw
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
open MeasureTheory
open scoped RealInnerProductSpace

lemma interpolation_conditional_exponent {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 1-ρ^2≠0) :
    -primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2))=
      -‖y‖^2/2-conditionalPotential F x r ρ y z := by
  simp only [primitivePotential,conditionalPotential,norm_sub_sq_real,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right]
  rw [real_inner_comm z y]
  field_simp
  ring

lemma weighted_integral_zero_of_gibbs {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Point d → ℝ}
    (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    {u : Point d → E} (hu : (∫ z,u z ∂gibbs H)=0) :
    (∫ z,Real.exp (-H z) • u z)=0 := by
  rw [integral_gibbs_vector hc hi] at hu
  exact (smul_eq_zero.mp hu).resolve_left (inv_ne_zero (integral_exp_pos hi).ne')

theorem interpolation_joint_integral_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Point d × Point d → E}
    (hi : Integrable u (jointInterpolationLaw F x r ρ))
    (hu : ∀ y,(∫ z,u (z,y) ∂gibbs (conditionalPotential F x r ρ y))=0) :
    (∫ p,u p ∂jointInterpolationLaw F x r ρ)=0 := by
  unfold jointInterpolationLaw at hi ⊢
  have ha := (probability_time hρ0 hρ1).1
  have hσ := (Real.sqrt_pos.mpr ha).ne'
  have hp0 := (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
  have hpt := partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith))
  let c := (partition (primitivePotential F x r))⁻¹*
    EulerDensity.noiseCoefficient d (Real.sqrt (1-ρ^2))
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hpt)
    (EulerDensity.noiseCoefficient_positive d hσ).ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp0)
    (EulerDensity.noiseCoefficient_finite _ _)
  let w := fun p : Point d × Point d => Real.exp (-primitivePotential F x r p.1-
    ‖p.2-ρ • p.1‖^2/(2*(1-ρ^2)))
  have hw0 : ∀ p,0≤w p := fun _ => (Real.exp_pos _).le
  have hw : Measurable w := by
    have := (hF.continuous_potential x r).measurable
    dsimp [w]; fun_prop
  have hden : Measurable (fun p => ENNReal.ofReal (w p)) := ENNReal.measurable_ofReal.comp hw
  have hd := EulerDensity.joint_density (hF.continuous_potential x r).measurable
    (fun z => ρ • z) (by fun_prop) hσ
  simp only [Real.sq_sqrt ha.le] at hd
  change _=c • ((volume : Measure (Point d)).prod volume).withDensity
    (fun p => ENNReal.ofReal (w p)) at hd
  rw [hd] at hi ⊢
  have hif : Integrable (fun p => w p • u p) ((volume : Measure (Point d)).prod volume) := by
    have hi' := (integrable_smul_measure hc0 hct).mp hi
    rw [integrable_withDensity_iff_integrable_smul' (hden)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi'
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi'
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    hden (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _)]
  rw [integral_prod_symm _ hif]
  have hz : ∀ y,(∫ z,w (z,y) • u (z,y))=0 := by
    intro y
    have hci := (conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y).integrable_exp
      (conditionalPotential_smooth hF x r ρ y).continuous
    have hh := weighted_integral_zero_of_gibbs
      (conditionalPotential_smooth hF x r ρ y).continuous hci (hu y)
    have he : ∀ z,w (z,y)=Real.exp (-‖y‖^2/2)*Real.exp (-conditionalPotential F x r ρ y z) := by
      intro z; dsimp [w]
      rw [interpolation_conditional_exponent F x r ρ y z ha.ne',sub_eq_add_neg,Real.exp_add]
    simp_rw [he,mul_smul]
    rw [integral_smul,hh,smul_zero]
  simp_rw [hz]
  simp
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InterpolationResidual
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
open scoped RealInnerProductSpace

lemma primitive_identity_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2<1) :
    Integrable (fun z => z) (gibbs (primitivePotential F x r)) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  exact (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).integrable
    continuous_id.aestronglyMeasurable (hF.hasExpMoments x hr hl).hasMoments

lemma interpolationResidual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    Integrable (interpolationResidual F x r ρ) (jointInterpolationLaw F x r ρ) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hi := primitive_identity_integrable hF x hr (by linarith : (lam:ℝ)*r^2<1)
  have hz : Integrable (fun p : Point d × Point d => p.1) (μ.prod ν) := hi.comp_fst ν
  have hg : Integrable (fun p : Point d × Point d => p.2) (μ.prod ν) :=
    (IsGaussian.integrable_id (μ:=ν)).comp_snd μ
  have hy := (hz.smul ρ).add (hg.smul (Real.sqrt (1-ρ^2)))
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hm := integrable_lipschitz_comp_of_integrable hy hM
  have hu := ((hz.sub (hy.smul ρ)).smul (1/(1-ρ^2))).add (hm.smul r)
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).2
  exact hu

lemma conditional_residual_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=0 := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hi := conditional_identity_integrable hF x hr hl hρ0 hρ1 y
  have hh := integral_scaled_affine_add hi (integrable_const
    (conditionalFieldMean F x r ρ y)) (1/(1-ρ^2)) r (ρ • y)
  rw [show (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=
      (1/(1-ρ^2)) • ((∫ z,z ∂gibbs (conditionalPotential F x r ρ y))-ρ • y)+
        r • (∫ _,conditionalFieldMean F x r ρ y ∂gibbs (conditionalPotential F x r ρ y)) from hh,
    integral_const,probReal_univ,one_smul,conditional_mean_identity hF x hr hl hρ0 hρ1]
  have ha := (probability_time hρ0 hρ1).1
  rw [sub_sub_cancel_left,smul_neg,smul_smul]
  have he : 1/(1-ρ^2)*((1-ρ^2)*r)=r := by field_simp
  rw [he,neg_add_cancel]

lemma integrable_scaled_affine_const {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    (hi : Integrable (fun z => z) μ) (c : ℝ) (a b : Point d) :
    Integrable (fun z => c • (z-a)+b) μ :=
  ((hi.sub (integrable_const a)).smul c).add (integrable_const b)

lemma conditional_residual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (fun z => interpolationResidual F x r ρ (z,y))
      (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact integrable_scaled_affine_const (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
    (1/(1-ρ^2)) (ρ • y) (r • conditionalFieldMean F x r ρ y)

theorem interpolation_flux_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {T : Point d → Point d →L[ℝ] ℝ} (hT : Measurable T)
    {C : ℝ} (hC : ∀ y,‖T y‖≤C) :
    (∫ p,T p.2 (interpolationResidual F x r ρ p) ∂jointInterpolationLaw F x r ρ)=0 := by
  have hi := interpolationResidual_integrable hF x hr hl hρ0 hρ1
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p => T p.2 (interpolationResidual F x r ρ p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hT.comp measurable_snd).prodMk hc.measurable)
  apply interpolation_joint_integral_zero hF x hr hl hρ0 hρ1
  · refine (hi.norm.const_mul C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    exact ((T p.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC p.2) (norm_nonneg _))
  · intro y
    have hrz := conditional_residual_integrable hF x hr hl hρ0 hρ1 y
    rw [(T y).integral_comp_comm hrz,conditional_residual_zero hF x hr hl hρ0 hρ1,map_zero]
end LogConcaveSampling

open Function MeasureTheory Set Filter
open scoped Topology NNReal

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityVelocity
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
open Set Function MeasureTheory Filter
open scoped Topology

lemma clampedProbabilityDerivative_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (uncurry (clampedProbabilityDerivative F x r T hT0)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcm := (projIcc 0 T hT0 p.1).2
  have hp : (projIcc 0 T hT0 p.1:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,p.2) hp).continuousAt_fderiv
    (by simp)
  exact (hh.comp (f:=fun q : ℝ × Point d => ((projIcc 0 T hT0 q.1:ℝ),q.2)) ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).continuousAt.prodMk
    continuous_snd.continuousAt)).clm_comp continuousAt_const

lemma clampedProbabilityVelocity_hasFDerivAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) (z : Point d) :
    HasFDerivAt (clampedProbabilityVelocity F x r T hT0 t)
      (clampedProbabilityDerivative F x r T hT0 t z) z := by
  have hcm := (projIcc 0 T hT0 t).2
  have hp : (projIcc 0 T hT0 t:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,z) hp).differentiableAt
    (by simp)
  convert! hh.hasFDerivAt.comp z ((hasFDerivAt_const (projIcc 0 T hT0 t:ℝ) z).prodMk
    (hasFDerivAt_id z)) using 1
  all_goals try with_reducible_and_instances rfl

end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Topology

lemma interpolationPath_continuous {d : ℕ} (p : Point d × Point d) :
    Continuous (fun t => interpolationPath t p) := by unfold interpolationPath; fun_prop

lemma interpolationPath_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPath (d:=d) t) := by unfold interpolationPath; fun_prop

lemma interpolationPathDerivative_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPathDerivative (d:=d) t) := by unfold interpolationPathDerivative; fun_prop

lemma interpolationPath_hasDerivAt {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    HasDerivAt (fun t => interpolationPath t p) (interpolationPathDerivative t p) t := by
  have hs₀ : HasDerivAt (fun t : ℝ => 1-t^2) (-2*t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2) using 1; simp
  have hs := hs₀.sqrt (show 1-t^2≠0 by linarith)
  have hh := ((hasDerivAt_id t).smul_const p.1).add (hs.smul_const p.2)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [one_smul,interpolationPathDerivative]
  rw [sub_eq_add_neg,←neg_smul]
  congr 1
  congr 1
  ring

lemma interpolationPath_norm_le {d : ℕ} {t T : ℝ} (hT : T≤1) (ht : t∈Icc 0 T)
    (p : Point d × Point d) : ‖interpolationPath t p‖≤‖p.1‖+‖p.2‖ := by
  have ht1 := ht.2.trans hT
  have hs0 := Real.sqrt_nonneg (1-t^2)
  have hs1 : Real.sqrt (1-t^2)≤1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg t]
  calc
    _ ≤ ‖t • p.1‖+‖Real.sqrt (1-t^2) • p.2‖ := norm_add_le _ _
    _ = t*‖p.1‖+Real.sqrt (1-t^2)*‖p.2‖ := by
      simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg hs0]
    _ ≤ _ := by nlinarith [norm_nonneg p.1,norm_nonneg p.2]

lemma interpolationPathDerivative_norm_le {d : ℕ} {t T : ℝ} (hT0 : 0≤T) (hT1 : T<1)
    (ht : t∈Icc 0 T) (p : Point d × Point d) :
    ‖interpolationPathDerivative t p‖≤‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖ := by
  have hT : 0<1-T^2 := by nlinarith
  have hs : Real.sqrt (1-T^2)≤Real.sqrt (1-t^2) := by apply Real.sqrt_le_sqrt; nlinarith [ht.1,ht.2]
  have hdiv : t/Real.sqrt (1-t^2)≤1/Real.sqrt (1-T^2) := by
    calc
      _ ≤ 1/Real.sqrt (1-t^2) := div_le_div_of_nonneg_right (ht.2.trans hT1.le) (Real.sqrt_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hT) hs
  calc
    _ ≤ ‖p.1‖+‖(t/Real.sqrt (1-t^2)) • p.2‖ := norm_sub_le _ _
    _ = ‖p.1‖+(t/Real.sqrt (1-t^2))*‖p.2‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht.1 (Real.sqrt_nonneg _))]
    _ ≤ _ := by gcongr

lemma interpolationPath_residual {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p=(1/(1-t^2)) • (p.1-t • interpolationPath t p) := by
  have ha : 1-t^2≠0 := by linarith
  have hs : Real.sqrt (1-t^2)≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have he₁ : 1/(1-t^2)-(1/(1-t^2))*t*t=1 := by field_simp
  have he₂ : (1/(1-t^2))*t*Real.sqrt (1-t^2)=t/Real.sqrt (1-t^2) := by
    field_simp
    rw [Real.sq_sqrt (show 0≤1-t^2 by linarith)]
  unfold interpolationPathDerivative interpolationPath
  simp only [smul_add,smul_sub,smul_smul]
  rw [sub_add_eq_sub_sub,←mul_assoc,←mul_assoc,←sub_smul,he₁,one_smul,he₂]
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

lemma interpolationPath_defect {d : ℕ} {F : Point d → ℝ} (x : Point d) (r : ℝ)
    {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p)=
      interpolationResidual F x r t (p.1,interpolationPath t p) := by
  rw [interpolationPath_residual ht]
  simp [probabilityVelocity,interpolationResidual,sub_eq_add_neg]

lemma interpolationPath_flux {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1)
    {S : Point d → Point d →L[ℝ] ℝ} (hS : Measurable S)
    {C : ℝ} (hC : ∀ y,‖S y‖≤C) :
    (∫ p,S (interpolationPath t p)
      (interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p))
      ∂(gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))=0 := by
  have ht : t^2<1 := by have hh := (probability_time ht0 ht1).1; linarith
  simp_rw [interpolationPath_defect x r ht]
  have hM := conditionalFieldMean_lipschitz hF x hr hl ht0 ht1
  have hc : Continuous (interpolationResidual F x r t) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul t)).const_smul (1/(1-t^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p : Point d × Point d => S p.2 (interpolationResidual F x r t p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hS.comp measurable_snd).prodMk hc.measurable)
  have hh := interpolation_flux_zero hF x hr hl ht0 ht1 hS hC
  rw [jointInterpolationLaw,integral_map (by fun_prop) hm.aestronglyMeasurable] at hh
  exact hh

lemma interpolationPath_defect_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃ g : Point d × Point d → ℝ,
      Integrable g ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) ∧
      ∀ t∈Icc 0 T,∀ p,‖interpolationPathDerivative t p-
        clampedProbabilityVelocity F x r T hT0 t (interpolationPath t p)‖≤g p := by
  let f := clampedProbabilityVelocity F x r T hT0
  let K : ℝ≥0 := ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
  have hc := clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1
  have hL : ∀ t,LipschitzWith K (f t) := clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hc.comp (continuous_id.prodMk continuous_const)).continuousOn : ContinuousOn (fun t => f t 0) (Icc 0 T))
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hz : Integrable (fun p : Point d × Point d => ‖p.1‖) (μ.prod ν) :=
    ((primitive_identity_integrable hF x hr (by linarith)).comp_fst ν).norm
  have hg : Integrable (fun p : Point d × Point d => ‖p.2‖) (μ.prod ν) :=
    ((IsGaussian.integrable_id (μ:=ν)).comp_snd μ).norm
  let g : Point d × Point d → ℝ := fun p =>
    ‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖+C+(K:ℝ)*(‖p.1‖+‖p.2‖)
  refine ⟨g,((hz.add (hg.const_mul _)).add (integrable_const C)).add ((hz.add hg).const_mul _),?_⟩
  intro t ht p
  have hfl := (hL t).dist_le_mul (interpolationPath t p) 0
  rw [dist_eq_norm,dist_zero_right] at hfl
  have hfb : ‖f t (interpolationPath t p)‖≤C+(K:ℝ)*(‖p.1‖+‖p.2‖) := by
    exact (norm_le_norm_add_norm_sub' _ _).trans
      (add_le_add (hC t ht) (hfl.trans (mul_le_mul_of_nonneg_left
        (interpolationPath_norm_le hT1.le ht p) K.coe_nonneg)))
  exact (norm_sub_le _ _).trans (add_le_add
    (interpolationPathDerivative_norm_le hT0 hT1 ht p) hfb) |>.trans_eq (by dsimp [g]; ring)

lemma probabilityFlow_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (probabilityFlow hF x hr hl hT0 hT1) :=
  (GlobalODE.flow_lipschitz _ _ ⟨0,le_rfl,hT0⟩ ⟨T,hT0,le_rfl⟩).continuous
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PoincareVectorVariance
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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

lemma stdGaussian_sq_norm (d : ℕ) :
    (∫z : Point d,‖z‖^2 ∂stdGaussian (Point d))=d := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hei (j : Fin d) : Integrable (fun z : Point d => (inner ℝ (b j) z)^2) (stdGaussian (Point d)) :=
    ((IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).continuousLinearMap_comp (innerSL ℝ (b j))).integrable_sq
  calc
    _ = ∫z,∑j : Fin d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs,sq_abs] using (b.sum_sq_norm_inner_right z).symm
    _ = ∑j : Fin d,∫z,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := integral_finsetSum _ (fun j _ => hei j)
    _ = _ := by
      have hj (j : Fin d) : (∫z : Point d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d))=1 := by
        change (∫z : Point d,((innerSL ℝ (b j)) z)^2 ∂stdGaussian (Point d))=1
        rw [GaussianPoincare.integral_dual_sq,innerSL_apply_norm,b.norm_eq_one,one_pow]
      simp_rw [hj]
      simp
end LogConcaveSampling

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
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_TriangularEquiv
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

namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in

theorem spaceTimeBackward_differentiableAt (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (spaceTimeBackward hab hc hL) p := by
  have hh := spaceTimeForward_hasFDerivAt hab hc hL hD hf
    (spaceTimeBackward hab hc hL p) hp
  exact (hh.of_local_left_inverse (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))).differentiableAt
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

lemma backwardTest_eq (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) :
    backwardTest hab hc hL T φ p=φ (flow hL hc (projIcc a b hab p.1) p.2 T) := by
  unfold backwardTest spaceTimeBackward
  rw [flow_cocycle hL hc (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩ T]

lemma backwardTest_continuous (T : Icc a b) {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (backwardTest hab hc hL T φ) :=
  hφ.comp ((flow_lipschitz hL hc ⟨a,le_rfl,hab⟩ T).continuous.comp
    (spaceTimeBackward_continuous hab hc hL).snd)

lemma backwardTest_lipschitz (T : Icc a b) {φ : E → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (t : ℝ) :
    LipschitzWith (L*⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩)
      (fun z => backwardTest hab hc hL T φ (t,z)) := by
  simp only [backwardTest_eq]
  apply hφ.comp
  apply (flow_lipschitz hL hc (projIcc a b hab t) T).weaken
  change Real.exp _≤Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [T.2.1,T.2.2,(projIcc a b hab t).2.1,(projIcc a b hab t).2.2]

variable [ProperSpace E] {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in
lemma backwardTest_differentiableAt (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (backwardTest hab hc hL T φ) p :=
  (hφ _).comp p (((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num) _).comp p
    (spaceTimeBackward_differentiableAt hab hc hL hD hf p hp).snd)

include hD hf in

theorem backwardTest_material_zero (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    fderiv ℝ (backwardTest hab hc hL T φ) p (1,f p.1 p.2)=0 := by
  let B := spaceTimeBackward hab hc hL
  let G := fun z => φ (flow hL hc ⟨a,le_rfl,hab⟩ z T)
  have hG : Differentiable ℝ G := hφ.comp
    ((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num))
  have hv : f (B p).1 (spaceTimeForward hab hc hL (B p)).2=f p.1 p.2 := by
    rw [spaceTime_right_inverse hab hc hL p]
    rfl
  have hB := (spaceTimeForward_hasFDerivAt hab hc hL hD hf (B p) hp).of_local_left_inverse
    (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))
  have hcomp := (hG (B p).2).hasFDerivAt.comp p hB.snd
  change (fderiv ℝ (G ∘ fun x => (spaceTimeBackward hab hc hL x).2) p) (1,f p.1 p.2)=0
  rw [hcomp.fderiv]
  change (fderiv ℝ G (B p).2) _=0
  have he : (((triangularEquiv (f (B p).1 (spaceTimeForward hab hc hL (B p)).2)
      (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD (B p).2)
        (flowSpatialCoefficient_bound hab hc hL hf (B p).2) ⟨a,le_rfl,hab⟩
          ⟨(B p).1,hp.1.le,hp.2.le⟩)).symm : (ℝ × E) →L[ℝ] (ℝ × E)) (1,f p.1 p.2)).2=0 := by
    change (fundamentalEquiv _ _ _ _).symm (f p.1 p.2-1 • _)=0
    rw [hv,one_smul,sub_self,map_zero]
  convert! (congrArg (fderiv ℝ G (B p).2) he).trans (map_zero _) using 1
  all_goals try with_reducible_and_instances rfl
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [ProperSpace E] {a b : ℝ} (hab : a≤b) {f : ℝ → E → E}
    (hc : Continuous (uncurry f)) {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in

theorem backwardTest_chain (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) {γ : ℝ → E} {γ' : E} {t : ℝ}
    (ht : t∈Ioo a b) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => backwardTest hab hc hL T φ (s,γ s))
      (fderiv ℝ (fun z => backwardTest hab hc hL T φ (t,z)) (γ t) (γ'-f t (γ t))) t := by
  let A := fderiv ℝ (backwardTest hab hc hL T φ) (t,γ t)
  have hd := (backwardTest_differentiableAt hab hc hL hD hf T hφ (t,γ t) ht).hasFDerivAt
  have hsp := hd.comp (γ t) ((hasFDerivAt_const (𝕜:=ℝ) t (γ t)).prodMk (hasFDerivAt_id _))
  have hchain := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)
  have hzero : A (1,f t (γ t))=0 := backwardTest_material_zero hab hc hL hD hf T hφ _ ht
  have he : A (1,γ')=A (0,γ'-f t (γ t)) := by
    have hp : ((1:ℝ),γ')=(1,f t (γ t))+(0,γ'-f t (γ t)) := by ext <;> simp
    rw [hp,map_add,hzero,zero_add]
  convert! hchain using 1
  all_goals try with_reducible_and_instances rfl
  change (fderiv ℝ (backwardTest hab hc hL T φ ∘ Prod.mk t) (γ t)) (γ'-f t (γ t))=A (1,γ')
  rw [hsp.fderiv]
  change A (0,γ'-f t (γ t))=A (1,γ')
  exact he.symm

end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology

theorem transport_expectation_of_flux {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b)
    {f : ℝ → Point d → Point d} (hc : Continuous (uncurry f)) {K : ℝ≥0}
    (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → Point d → Point d →L[ℝ] Point d} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)
    {X X' : ℝ → Ω → Point d}
    (hXm : ∀ t,Measurable (X t)) (hXc : ∀ ω,Continuous (fun t => X t ω))
    (hXp : ∀ t∈Ioo a b,∀ ω,HasDerivAt (fun t => X t ω) (X' t ω) t)
    (hX'm : ∀ t,Measurable (X' t))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hgb : ∀ t∈Ioo a b,∀ ω,‖X' t ω-f t (X t ω)‖≤g ω)
    (hflux : ∀ t∈Ioo a b,∀ S : Point d → Point d →L[ℝ] ℝ,Measurable S →
      (∃ C : ℝ,∀ y,‖S y‖≤C) → (∫ ω,S (X t ω) (X' t ω-f t (X t ω)) ∂μ)=0)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hφB : ∀ z,‖φ z‖≤B) :
    (∫ ω,φ (X b ω) ∂μ) =
      ∫ ω,φ (flow hL hc ⟨a,le_rfl,hab.le⟩ (X a ω) b) ∂μ := by
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc hL T φ
  let S := fun t => fderiv ℝ (fun z => ψ (t,z))
  let U := fun t ω => ψ (t,X t ω)
  let U' := fun t ω => S t (X t ω) (X' t ω-f t (X t ω))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hSm : ∀ t,Measurable (S t) := fun t => measurable_fderiv ℝ _
  have hSb : ∀ t y,‖S t y‖≤C := by
    intro t y
    exact norm_fderiv_le_of_lipschitz ℝ (backwardTest_lipschitz hab.le hc hL T hφL t)
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc hL T hφ.continuous
  have hUm : ∀ t,Measurable (U t) := fun t => hψ.measurable.comp (measurable_const.prodMk (hXm t))
  have hUb : ∀ t ω,‖U t ω‖≤B := by intro t ω; exact hφB _
  have hU'm : ∀ t,Measurable (U' t) := by
    intro t
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp
      (((hSm t).comp (hXm t)).prodMk ((hX'm t).sub
        (hc.measurable.comp (measurable_const.prodMk (hXm t)))))
  have hUi : ∀ t,Integrable (U t) μ := fun t =>
    (integrable_const B).mono' (hUm t).aestronglyMeasurable (Eventually.of_forall (hUb t))
  have hU'b : ∀ t∈Ioo a b,∀ ω,‖U' t ω‖≤C*g ω := by
    intro t ht ω
    exact ((S t (X t ω)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hSb t _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hgb t ht ω) hC))
  have hUd : ∀ t∈Ioo a b,∀ ω,HasDerivAt (fun t => U t ω) (U' t ω) t := by
    intro t ht ω
    exact backwardTest_chain hab.le hc hL hD hf T hφ ht (hXp t ht ω)
  have hQd : ∀ t∈Ioo a b,HasDerivAt (fun t => ∫ ω,U t ω ∂μ) 0 t := by
    intro t ht
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=U) (F':=U')
      (Ioo_mem_nhds ht.1 ht.2) (Eventually.of_forall fun s => (hUm s).aestronglyMeasurable)
      (hUi t) (hU'm t).aestronglyMeasurable
      (Eventually.of_forall fun ω s hs => hU'b s hs ω) (hg.const_mul C)
      (Eventually.of_forall fun ω s hs => hUd s hs ω)
    have hz := hflux t ht (S t) (hSm t) ⟨C,hSb t⟩
    change (∫ ω,U' t ω ∂μ)=0 at hz
    rw [hz] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫ ω,U t ω ∂μ) :=
    continuous_of_dominated (fun t => (hUm t).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hUb t)) (integrable_const B)
      (Eventually.of_forall fun ω => hψ.comp (continuous_id.prodMk (hXc ω)))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫ ω,U t ω ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫ ω,U b ω ∂μ)=(∫ ω,U a ω ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  convert! heq using 1 <;> apply integral_congr_ae <;> filter_upwards [] with ω
  · simp only [U,ψ,backwardTest_eq]
    rw [projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact (congrArg φ (flow_initial hL hc ⟨b,hab.le,le_rfl⟩ (X b ω))).symm
  · simp only [U,ψ,backwardTest_eq]
    rw [projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ProbabilityFlowIntegral
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
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

theorem probabilityFlow_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hφB : ∀ z,‖φ z‖≤B) :
    (∫ y,φ y ∂interpolationLaw F x r T) =
      ∫ z,φ (probabilityFlow hF x hr hl hT0.le hT1 z) ∂stdGaussian (Point d) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := clampedProbabilityVelocity_continuous hF x hr hl hT0.le hT1
  have hL := fun t (_ : t∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr hl hT0.le hT1 t
  obtain ⟨g,hg,hgb⟩ := interpolationPath_defect_bound hF x hr hl hT0.le hT1
  have hh := GlobalODE.transport_expectation_of_flux (μ:=μ.prod ν) hT0 hc hL
    (clampedProbabilityDerivative_continuous hF x hr hl hT0.le hT1)
    (clampedProbabilityVelocity_hasFDerivAt hF x hr hl hT0.le hT1)
    (X:=interpolationPath) (X':=interpolationPathDerivative)
    interpolationPath_measurable interpolationPath_continuous
    (fun t ht p => interpolationPath_hasDerivAt (by
      have hh := (probability_time ht.1.le (ht.2.trans hT1)).1; linarith) p)
    interpolationPathDerivative_measurable hg (fun t ht => hgb t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht S hS ⟨C,hC⟩ => by
      simp_rw [clampedProbabilityVelocity_eq F x r T hT0.le ⟨ht.1.le,ht.2.le⟩]
      exact interpolationPath_flux hF x hr hl ht.1.le (ht.2.trans hT1) hS hC)
    hφ hφL hφB
  have hfc := probabilityFlow_continuous hF x hr hl hT0.le hT1
  have he := integral_map (μ:=μ.prod ν) measurable_snd.aemeasurable
    (hφ.continuous.comp hfc).aestronglyMeasurable
  rw [Measure.map_snd_prod,measure_univ,one_smul] at he
  change (∫ y,φ y ∂(μ.prod ν).map (interpolationPath T))=_
  rw [integral_map (interpolationPath_measurable T).aemeasurable hφ.continuous.aestronglyMeasurable]
  change (∫ p,φ (interpolationPath T p) ∂μ.prod ν)=_
  rw [hh]
  trans ∫ p,φ (probabilityFlow hF x hr hl hT0.le hT1 p.2) ∂μ.prod ν
  · apply integral_congr_ae
    filter_upwards [] with p
    rw [show interpolationPath 0 p=p.2 by simp [interpolationPath]]
    rfl
  · exact he.symm
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeasureSmoothLipschitz
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
open MeasureTheory Filter
open scoped Topology NNReal

theorem measure_eq_of_smooth_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : E → ℝ),ContDiff ℝ 1 f → (∃ L : ℝ≥0,LipschitzWith L f) →
      (∃ B : ℝ,∀ x,‖f x‖≤B) → (∫ x,f x ∂μ)=(∫ x,f x ∂ν)) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have huf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  obtain ⟨B,hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hε (n : ℕ) : 0<1/((n:ℝ)+1) := by positivity
  choose g hgc hgd using fun n : ℕ => huf.exists_contDiff_dist_le (hε n)
  have hge (n : ℕ) : 1/((n:ℝ)+1)≤1 := by
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hgb : ∀ n x,‖g n x‖≤B+1 := by
    intro n x
    have hd := (hgd n x).le.trans (hge n)
    rw [dist_eq_norm] at hd
    exact (norm_le_norm_add_norm_sub' (g n x) (f x)).trans (add_le_add (hB x) hd)
  have hgt (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hgd n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n => PoincareCutoff.truncation (g n) n
  have huc (n : ℕ) : ContDiff ℝ 1 (u n) :=
    PoincareCutoff.truncation_smooth ((hgc n).of_le (by simp)) n
  have huk (n : ℕ) : HasCompactSupport (u n) := PoincareCutoff.truncation_compact _ _
  have hub : ∀ n x,‖u n x‖≤B+1 := by
    intro n x
    exact (PoincareCutoff.truncation_abs (g n) n x).trans (hgb n x)
  have huL (n : ℕ) : ∃ L : ℝ≥0,LipschitzWith L (u n) := by
    obtain ⟨C,hC⟩ := ((huk n).fderiv ℝ).exists_bound_of_continuous
      ((huc n).continuous_fderiv (by norm_num))
    let L : ℝ≥0 := ⟨C,(norm_nonneg _).trans (hC 0)⟩
    exact ⟨L,lipschitzWith_of_nnnorm_fderiv_le ((huc n).differentiable (by norm_num)) hC⟩
  have hut (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    simpa only [u,PoincareCutoff.truncation,one_mul] using (PoincareCutoff.cutoff_tendsto x).mul (hgt x)
  have hlim (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x,u n x ∂η) atTop (𝓝 (∫ x,f x ∂η)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => B+1)
      (fun n => (huc n).continuous.aestronglyMeasurable) (integrable_const (B+1))
      (fun n => Eventually.of_forall (hub n)) (Eventually.of_forall hut)
  have he : (fun n => ∫ x,u n x ∂μ)=(fun n => ∫ x,u n x ∂ν) :=
    funext fun n => h (u n) (huc n) (huL n) ⟨B+1,hub n⟩
  exact tendsto_nhds_unique (hlim μ) (he ▸ hlim ν)
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ProbabilityFlowPushforward
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
open MeasureTheory ProbabilityTheory

theorem probabilityFlow_pushforward {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) :
    (stdGaussian (Point d)).map (probabilityFlow hF x hr hl hT0.le hT1)=
      interpolationLaw F x r T := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := probabilityFlow_continuous hF x hr hl hT0.le hT1
  let hprob : IsProbabilityMeasure (interpolationLaw F x r T) := by
    unfold interpolationLaw
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ ⟨L,hL⟩ ⟨B,hB⟩
  rw [integral_map hc.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact (probabilityFlow_integral hF x hr hl hT0 hT1 (hφ.differentiable (by norm_num)) hL hB).symm
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_VariationalField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

lemma flow_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f g : ℝ → E → E} {K L : ℝ≥0}
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hL : ∀t∈Icc a b,LipschitzWith K (f t))
    (hJ : ∀t∈Icc a b,LipschitzWith L (g t))
    (he : ∀t∈Icc a b,∀x,f t x=g t x) (s t : Icc a b) (x : E) :
    flow hL hf s x t=flow hJ hg s x t := by
  have hd (u : ℝ) (hu : u∈Icc a b) := flow_deriv hJ hg s x u hu
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hJ hg s x).continuousOn
    (fun u hu => (he u hu _) ▸ flow_deriv hJ hg s x u hu) s t
  simpa only [flow_initial,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.GlobalODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TimeBump
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
open Set Function Filter Metric
open scoped Topology NNReal

lemma probabilityTransport_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  let f := smoothProbabilityVelocity F x r hT0 hT1
  have hf := smoothProbabilityVelocity_contDiff hF x hr hl hT0 hT1 n
  have hL : ∀u∈Icc 0 T,LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (f u) := by
    intro u hu
    change LipschitzWith _ (fun y => probabilityVelocity F x r (smoothTimeClip hT0 hT1 u) y)
    rw [smoothTimeClip_eq hT0 hT1 hu]
    exact probabilityVelocity_lipschitz hF x hr hl hu hT1
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      (fun z => GlobalODE.flow hL hf.continuous s z t) := by
    funext z
    apply GlobalODE.flow_congr
    intro u hu y
    rw [clampedProbabilityVelocity_eq F x r T hT0 hu]
    dsimp [f,smoothProbabilityVelocity]
    rw [smoothTimeClip_eq hT0 hT1 hu]
  rw [he]
  exact GlobalODE.smooth_flow hf hL hT0 s t
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalBackward
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_continuous (s t : Icc (0:ℝ) T) :
    Continuous (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  (GlobalODE.flow_lipschitz _ _ s t).continuous

include hF hr hl in
lemma interpolationLaw_zero : interpolationLaw F x r 0=stdGaussian (Point d) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  simp only [interpolationLaw,zero_smul,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
    Real.sqrt_one,one_smul,zero_add]
  simpa only [measure_univ,one_smul] using (Measure.map_snd_prod (μ:=gibbs (primitivePotential F x r)) (ν:=stdGaussian (Point d)))

lemma probabilityTransport_from_zero (t : Icc (0:ℝ) T) :
    (stdGaussian (Point d)).map
      (probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t)=
        interpolationLaw F x r t := by
  by_cases ht : (t:ℝ)=0
  · have he : t=⟨0,le_rfl,hT0⟩ := Subtype.ext ht
    rw [he]
    have hz : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ ⟨0,le_rfl,hT0⟩=id :=
      funext (probabilityTransport_initial hF x hr hl hT0 hT1 _)
    rw [hz,Measure.map_id,interpolationLaw_zero hF x hr hl]
  · have htp : 0<(t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have ht1 : (t:ℝ)<1 := t.2.2.trans_lt hT1
    have he : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t=
        probabilityFlow hF x hr hl htp.le ht1 := by
      funext z
      exact (GlobalODE.flow_restrict
        (clampedProbabilityVelocity_continuous hF x hr hl htp.le ht1)
        (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl htp.le ht1 u)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
        (Icc_subset_Icc_right t.2.2)
        (fun u hu y => by rw [clampedProbabilityVelocity_eq F x r t htp.le hu,
          clampedProbabilityVelocity_eq F x r T hT0 ⟨hu.1,hu.2.trans t.2.2⟩])
        ⟨0,le_rfl,htp.le⟩ ⟨t,htp.le,le_rfl⟩ z).symm
    rw [he]
    exact probabilityFlow_pushforward hF x hr hl htp ht1

theorem probabilityTransport_pushforward (s t : Icc (0:ℝ) T) :
    (interpolationLaw F x r s).map (probabilityTransport hF x hr hl hT0 hT1 s t)=
      interpolationLaw F x r t := by
  rw [←probabilityTransport_from_zero hF x hr hl hT0 hT1 s,
    Measure.map_map (probabilityTransport_continuous hF x hr hl hT0 hT1 s t).measurable
      (probabilityTransport_continuous hF x hr hl hT0 hT1 _ s).measurable]
  simp only [comp_def,probabilityTransport_cocycle]
  exact probabilityTransport_from_zero hF x hr hl hT0 hT1 t
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
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma covariance_field_synthesis {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {f : Point d → ℝ} {g : Point d → Point d} (hf : MemLp f 2 μ)
    (hg : ∀u,MemLp (fun z => inner ℝ u (g z)) 2 μ) (v : Point d) :
    (∑i : Fin d,inner ℝ v ((EuclideanSpace.basisFun (Fin d) ℝ) i)*
      cov[f,(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) (g z));μ])=
      cov[f,(fun z => inner ℝ v (g z));μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hh := covariance_fun_sum_right
    (fun i : Fin d => (hg (b i)).const_mul (inner ℝ v (b i))) hf
  simp only [covariance_const_mul_right] at hh
  simpa only [b.sum_inner_mul_inner v] using hh.symm

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)

include hF hr hlam hl hρ0 hρ1 in
lemma conditionalFirstJet_inner (u v y : Point d) :
    inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v)=
      (1/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr.le hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr.le hl hρ0 hρ1 y
  have hi (v : Point d) : MemLp (fun z => inner ℝ v z) 2 μ :=
    (Appell.HasGrowth.linear (innerSL ℝ v)).memLp (by fun_prop) hm.hasMoments
  have hg (u : Point d) : MemLp (fun z => inner ℝ u (primitiveField F x r z)) 2 μ :=
    (primitiveField_inner_growth hF x u hr.le).memLp
      (continuous_const.inner (primitiveField_contDiff hF x r).continuous).aestronglyMeasurable hm.hasMoments
  simp only [conditionalFirstJet,sum_apply,smul_apply,
    inner_sum,inner_smul_right,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,conditionalU_one_cov hF x hr hlam hl hρ0 hρ1]
  change (∑i,∑j,(1/(1-ρ^2))*cov[(fun z => inner ℝ (b j) z),
    (fun z => inner ℝ (b i) (primitiveField F x r z));μ]*(inner ℝ (b j) v*inner ℝ u (b i)))=_
  calc
    _=(1/(1-ρ^2))*(∑i,inner ℝ u (b i)*(∑j,inner ℝ v (b j)*
        cov[(fun z => inner ℝ (b j) z),(fun z => inner ℝ (b i) (primitiveField F x r z));μ])) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) v]
      ring
    _=_ := by
      have hs (i : Fin d) := covariance_inner_synthesis hm (hg (b i)) v
      dsimp [μ,b] at hs ⊢
      simp only [hs]
      rw [covariance_field_synthesis (hi v) hg u]

include hF hr hlam hl hρ0 hρ1 in
lemma conditionalFirstJet_deriv (y : Point d) :
    fderiv ℝ (conditionalFieldMean F x r ρ) y=
      ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  simp only [smul_apply,inner_smul_right,
    conditionalFieldMean_inner_deriv hF x hr.le hl hρ0 hρ1,
    conditionalFirstJet_inner hF x hr hlam hl hρ0 hρ1]
  ring
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

lemma terminalJacobian_norm_le (t : Icc (0:ℝ) T) (y : Point d) :
    ‖terminalJacobian hF x hr hl hT0 hT1 (t,y)‖≤Real.exp (Real.pi^2/4) := by
  rw [terminalJacobian_eq]
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=terminalBackward hF x hr.le hl hT0 hT1 (t,y))
    (GlobalODE.flow_lipschitz
      (fun u (_ : u∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr.le hl hT0 hT1 u)
      (clampedProbabilityVelocity_continuous hF x hr.le hl hT0 hT1) t ⟨T,hT0,le_rfl⟩)
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have ht : 0≤T-(t:ℝ) := sub_nonneg.mpr t.2.2
  rw [abs_of_nonneg ht]
  have htt : T-(t:ℝ)≤1 := by linarith [t.2.1]
  have hbase : (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2/4 := by nlinarith [sq_nonneg Real.pi]
  exact (mul_le_of_le_one_right (by positivity : 0≤(Real.pi^2/2)*(lam:ℝ)*r^2) htt).trans hbase

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
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma productPointEquiv_volume (d e : ℕ) :
    MeasurePreserving (productPointEquiv d e) := by
  have h₁ := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)).measurePreserving
  have h₂ := (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin d ⊕ Fin e => ℝ)).measurePreserving
  have h₃ := WithLp.volume_preserving_ofLp (Point d) (Point e)
  exact h₃.comp (h₂.comp h₁)

lemma productPotential_density {d e : ℕ} (H : Point d → ℝ) (G : Point e → ℝ)
    (y : Point (d+e)) : gibbsDensity (productPotential H G) y=
      gibbsDensity H (productPointEquiv d e y).1*gibbsDensity G (productPointEquiv d e y).2 := by
  simp only [gibbsDensity,productPotential,neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_ProductPotentialMeasurable
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
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

lemma productPotential_measurable {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) : Measurable (productPotential H G) :=
  (hH.comp ((productPointEquiv d e).continuous.measurable.fst)).add
    (hG.comp ((productPointEquiv d e).continuous.measurable.snd))

lemma productPotential_unnormalized {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) :
    (volume.withDensity (gibbsDensity (productPotential H G))).map (productPointEquiv d e)=
      (volume.withDensity (gibbsDensity H)).prod (volume.withDensity (gibbsDensity G)) := by
  let E := (productPointEquiv d e).toHomeomorph.toMeasurableEquiv
  have hd : Measurable (gibbsDensity (productPotential H G)) :=
    (Real.measurable_exp.comp (productPotential_measurable hH hG).neg).ennreal_ofReal
  have hHd : Measurable (gibbsDensity H) := (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hGd : Measurable (gibbsDensity G) := (Real.measurable_exp.comp hG.neg).ennreal_ofReal
  rw [show (productPointEquiv d e : Point (d+e) → Point d × Point e)=E from rfl,
    map_withDensity_of_measurePreserving E (productPointEquiv_volume d e) hd,
    prod_withDensity hHd hGd]
  congr 1
  funext p
  rw [productPotential_density]
  change gibbsDensity H (E (E.symm p)).1*gibbsDensity G (E (E.symm p)).2=_
  rw [E.apply_symm_apply]

lemma productPotential_partition {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) :
    partition (productPotential H G)=partition H*partition G := by
  have he := congrArg (fun μ : Measure (Point d × Point e) => μ univ)
    (productPotential_unnormalized hH hG)
  rw [Measure.map_apply (productPointEquiv d e).continuous.measurable MeasurableSet.univ,
    preimage_univ] at he
  have hp : ((volume.withDensity (gibbsDensity H)).prod (volume.withDensity (gibbsDensity G))) univ=
      (volume.withDensity (gibbsDensity H)) univ*(volume.withDensity (gibbsDensity G)) univ := by
    rw [← univ_prod_univ,Measure.prod_prod]
  rw [hp] at he
  simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,partition] using he

theorem productPotential_gibbs {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Continuous H) (hG : Continuous G) :
    (gibbs (productPotential H G)).map (productPointEquiv d e)=(gibbs H).prod (gibbs G) := by
  unfold gibbs
  rw [Measure.map_smul,
    productPotential_unnormalized hH.measurable hG.measurable,productPotential_partition hH.measurable hG.measurable,
    ENNReal.mul_inv (Or.inl (partition_pos_of_continuous hH).ne') (Or.inr (partition_pos_of_continuous hG).ne'),Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]

lemma gaussianPotential_gibbs (d : ℕ) :
    gibbs (fun y : Point d => ‖y‖^2/2)=stdGaussian (Point d) := by
  have he := congrArg (fun μ : Measure (Point d) => μ univ) (EulerDensity.standard_density d)
  have hmul : EulerDensity.gaussianCoefficient d*partition (fun y : Point d => ‖y‖^2/2)=1 := by
    simpa only [measure_univ,Measure.smul_apply,smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,partition,gibbsDensity,neg_div] using he.symm
  have hi : (partition (fun y : Point d => ‖y‖^2/2))⁻¹=EulerDensity.gaussianCoefficient d := by
    exact (ENNReal.eq_inv_of_mul_eq_one_left hmul).symm
  rw [EulerDensity.standard_density,gibbs,hi]
  congr 2
  funext y
  simp only [gibbsDensity,neg_div]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorTerm
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

namespace TensorSum
variable {S T : Type}
lemma relabel_eval {d : ℕ} (A : TensorSum S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

end TensorSum
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

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialL2
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_material_direction {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {A : ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hA : DifferentiableAt ℝ A (ρ,y)) :
    (fderiv ℝ A (ρ,y)) (1,-r • conditionalFieldMean F x r ρ y)=
      JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y) := by
  have ht := joint_mdir_eq_material F x r hA
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y)=_ at ht
  rw [ht]
  unfold materialScalar
  rw [JetCalculus.dir_left_slice_at hA]
  change _=JetCalculus.dir (1,0) A (ρ,y)-r*JetCalculus.dir (conditionalFieldMean F x r ρ y)
    (fun z => A (ρ,z)) y
  rw [JetCalculus.dir_right_slice_at hA]
  unfold JetCalculus.dir
  have he : ((1:ℝ),-r • conditionalFieldMean F x r ρ y)=
      (1,0)+(-r) • (0,conditionalFieldMean F x r ρ y) := by simp
  rw [he,map_add,map_smul]
  simp only [smul_eq_mul,neg_mul]
  ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalMean
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
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalBackward_deriv {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => terminalBackward hF x hr.le hl hT0 hT1 (t,y))
      (-r • conditionalFieldMean F x r ρ (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) ρ := by
  have he : smoothTimeClip hT0 hT1=ᶠ[nhds ρ] id := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with t ht
    exact smoothTimeClip_eq hT0 hT1 ⟨ht.1.le,ht.2.le⟩
  have hclip := (hasDerivAt_id ρ).congr_of_eventuallyEq he
  have hh := GlobalODE.flow_deriv (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr.le hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr.le hl hT0 hT1).continuous
    ⟨T,by constructor <;> linarith only [hT0]⟩ y ρ (by constructor <;> linarith)
  have hlow : (-1:ℝ)<ρ := by linarith only [hρ0]
  have hhigh : ρ<T+1 := by linarith only [hρT]
  have hflow := hh.hasDerivAt (Icc_mem_nhds hlow hhigh)
  have hs : smoothTimeClip hT0 hT1 ρ=ρ := he.eq_of_nhds
  rw [←hs] at hflow
  have hd := hflow.scomp ρ hclip
  simp only [hs,smoothProbabilityVelocity,probabilityVelocity,one_smul] at hd
  convert hd using 1 <;> first | rfl | simp only [terminalBackward,hs]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_LogMeshLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

lemma logMeshCount_bound {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (logMeshCount T h:ℝ)<logMeshLength T/h+1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (logMeshLength_pos hT0 hT1) hh))

lemma logMeshStep_le {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshStep T h≤h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  apply (div_le_iff₀ hN).mpr
  have he := (div_le_iff₀ hh).mp (Nat.le_ceil (logMeshLength T/h))
  change logMeshLength T≤(logMeshCount T h:ℝ)*h at he
  nlinarith

lemma logMeshStep_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) : h/2≤logMeshStep T h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  have he : (logMeshCount T h:ℝ)<(logMeshLength T+h)/h := by
    simpa only [add_div,div_self (ne_of_gt hh)] using logMeshCount_bound hT0 hT1 hh
  have hN' := (lt_div_iff₀ hh).mp he
  apply (le_div_iff₀ hN).mpr
  nlinarith

lemma logMeshCell_upper {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤h*(1-logMeshNode T h j) := by
  have hb : 1-Real.exp (-logMeshStep T h)≤h := by
    have hx := Real.add_one_le_exp (-logMeshStep T h)
    have hs := logMeshStep_le hT0 hT1 hh
    linarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm h]
  exact mul_le_mul_of_nonneg_left hb hp

lemma logMeshCell_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hsmall : h≤Real.log 2) (j : ℕ) :
    h/4*(1-logMeshNode T h j)≤logMeshNode T h (j+1)-logMeshNode T h j := by
  have hs0 := logMeshStep_pos hT0 hT1 hh
  have hs := logMeshStep_le hT0 hT1 hh
  have hs' := logMeshStep_lower hT0 hT1 hh hL
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have he' : (1:ℝ)/2≤Real.exp (-logMeshStep T h) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos _) he)
  have hw : logMeshStep T h*Real.exp (-logMeshStep T h)≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (logMeshStep T h))
      (Real.exp_pos (-logMeshStep T h)).le
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hx
    nlinarith
  have hb : h/4≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_left he' hs0.le
    nlinarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm (h/4)]
  exact mul_le_mul_of_nonneg_left hb hp
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature

lemma logMeshCell_upper_right {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hsmall : h≤Real.log 2) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤2*h*(1-logMeshNode T h (j+1)) := by
  have hs := logMeshStep_le hT0 hT1 hh
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have hid : (1-logMeshNode T h (j+1))*Real.exp (logMeshStep T h)=1-logMeshNode T h j := by
    simp only [logMeshNode,sub_sub_cancel,←Real.exp_add]
    congr 1
    push_cast
    ring
  have hn : 0≤1-logMeshNode T h (j+1) := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos _).le
  have hb := mul_le_mul_of_nonneg_left he hn
  rw [hid] at hb
  calc
    _ ≤ h*(1-logMeshNode T h j) := logMeshCell_upper hT0 hT1 hh j
    _ ≤ h*((1-logMeshNode T h (j+1))*2) := mul_le_mul_of_nonneg_left hb hh.le
    _ = _ := by ring

lemma cell_singularity_cancel {a b t h : ℝ} (ha : 0≤a) (hat : a≤t) (htb : t≤b)
    (hb : b<1) (hh : 0≤h) (hcell : b-a≤h*(1-b)) (n : ℕ) :
    (t-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)≤h^(n+1) := by
  have hb0 : 0≤b := ha.trans (hat.trans htb)
  have hp : 0<1-b^2 := by nlinarith
  have hlen : t-a≤h*(1-b^2) := by
    have he : 1-b≤1-b^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he hh
    linarith
  have hr : (t-a)*(1-b^2)⁻¹≤h := by
    rw [←div_eq_mul_inv,div_le_iff₀ hp]
    exact hlen
  rw [show 2*n+2=2*(n+1) by omega,pow_mul,inv_pow,Real.sq_sqrt hp.le,←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hat) (inv_nonneg.mpr hp.le)) hr _

end LogConcaveSampling.Quadrature

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

end LogConcaveSampling.TensorEnergy

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

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma taylor_kernel_bound {a x t : ℝ} (hat : a≤t) (htx : t≤x) (n : ℕ) :
    |(x-t)^n/(n.factorial:ℝ)|≤(x-a)^n/(n.factorial:ℝ) := by
  have hn : (0:ℝ)<n.factorial := by positivity
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) n) hn.le
end LogConcaveSampling.Quadrature

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
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

lemma weighted_sum_sq_varying (w : I → ℝ) (f : I → Ω → E) (B : I → ℝ)
    (hm : ∀i,AEStronglyMeasurable (f i) μ)
    (hi : ∀i,Integrable (fun y => ‖f i y‖^2) μ)
    (hB : ∀i,(∫y,‖f i y‖^2 ∂μ)≤B i) :
    Integrable (fun y => ‖∑i,w i • f i y‖^2) μ ∧
      (∫y,‖∑i,w i • f i y‖^2 ∂μ)≤(∑i,|w i|)*(∑i,|w i| *B i) := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun y => (∑i,|w i|)*(∑i,|w i| *‖f i y‖^2)) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun y => ‖∑i,w i • f i y‖^2) μ := by
    have h := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun y => ‖∑i,w i • f i y‖^2) μ :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i y)))
  refine ⟨ho,(integral_mono ho hs (fun y => norm_weighted_sum_sq w (fun i => f i y))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))) hw0
  · exact fun i _ => (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

theorem weighted_time_seed {f : α × β → E} {w : α → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hw : AEStronglyMeasurable w μ)
    {K B : ℝ} (hB0 : 0≤B) (hK : ∀ᵐ t ∂μ,|w t|≤K)
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,w t • f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,w t • f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*K^2*B := by
  have he (t : α) (z : β) : ‖w t • f (t,z)‖^2=(w t)^2*‖f (t,z)‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖w t • f (t,z)‖^2) ν := by
    filter_upwards [hslice] with t ht
    simp only [he]
    exact ht.const_mul _
  have hb : ∀ᵐ t ∂μ,(∫z,‖w t • f (t,z)‖^2 ∂ν)≤K^2*B := by
    filter_upwards [hK,hB] with t ht hb
    simp only [he,integral_const_mul]
    have ht2 : (w t)^2≤K^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w t)) ht 2
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right ht2 hB0)
  simpa only [mul_assoc] using time_seed_uniform (f:=fun p => w p.1 • f p)
    (hw.comp_fst.smul hf) hs hb
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma iteratedDerivWithin_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) (n : ℕ) :
    EqOn (iteratedDerivWithin n (J 0) s) (J n) s := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr ih (ih ht)]
    exact (hJ n t ht).derivWithin (hs t ht)

omit [CompleteSpace E] in
lemma contDiffOn_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) :
    ContDiffOn ℝ (⊤:ℕ∞) (J 0) s := by
  rw [contDiffOn_infty]
  intro n
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs]
  constructor
  · intro m _
    apply (show ContinuousOn (J m) s from fun t ht => (hJ m t ht).continuousWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht
  · intro m _
    apply (show DifferentiableOn ℝ (J m) s from fun t ht => (hJ m t ht).differentiableWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht

omit [CompleteSpace E] in
lemma chainTaylor_eq {J : ℕ → ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    (n : ℕ) {a : ℝ} (ha : a∈s) (x : ℝ) :
    taylorWithinEval (J 0) n s a x=chainTaylor J n a x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_chain J hs hJ k ha]

lemma chainTaylor_remainder {J : ℕ → ℝ → E} {s : Set ℝ}
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    {a x : ℝ} (hsub : uIcc a x⊆s) (n : ℕ) :
    J 0 x-chainTaylor J n a x=
      ∫t in a..x,((x-t)^n/(n.factorial:ℝ)) • J (n+1) t := by
  by_cases hax : a=x
  · subst x
    simp [chainTaylor, Finset.sum_range_succ']
  have hs := uniqueDiffOn_uIcc hax
  have hJ' (n : ℕ) (t : ℝ) (ht : t∈uIcc a x) :
      HasDerivWithinAt (J n) (J (n+1) t) (uIcc a x) t := (hJ n t (hsub ht)).mono hsub
  rw [←chainTaylor_eq hs hJ' n left_mem_uIcc x,
    taylor_integral_remainder ((contDiffOn_chain J hs hJ').of_le (by exact_mod_cast (show (n+1:ℕ∞)≤⊤ from le_top)))]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [iteratedDerivWithin_chain J hs hJ' _ ht]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β} [SFinite ν]

theorem chainTaylor_remainder_rms {J : ℕ → ℝ → β → E} {s : Set ℝ} {n : ℕ} {a x B : ℝ}
    (hax : a≤x) (hB0 : 0≤B) (hsub : uIcc a x⊆s)
    (hf : ∀z n t,t∈s → HasDerivWithinAt (fun t => J n t z) (J (n+1) t z) s t)
    (hm : AEStronglyMeasurable (fun p : ℝ × β => J (n+1) p.1 p.2)
      ((volume.restrict (Ioc a x)).prod ν))
    (hi : ∀t∈Ioc a x,Integrable (fun z => ‖J (n+1) t z‖^2) ν)
    (hB : ∀t∈Ioc a x,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2) ν ∧
      (∫z,‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2 ∂ν)≤
        ((x-a)^(n+1)/(n.factorial:ℝ))^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc a x)
  let w : ℝ → ℝ := fun t => (x-t)^n/(n.factorial:ℝ)
  have hw : AEStronglyMeasurable w μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [w]; fun_prop
  have hk : ∀ᵐ t ∂μ,|w t|≤(x-a)^n/(n.factorial:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact taylor_kernel_bound ht.1.le ht.2 n
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖J (n+1) t z‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw hB0 hk hs hb
  have he (z : β) : J 0 x z-chainTaylor (fun k t => J k t z) n a x=
      ∫t,w t • J (n+1) t z ∂μ := by
    rw [chainTaylor_remainder (hf z) hsub,intervalIntegral.integral_of_le hax]
  have hμ : μ.real univ=x-a := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hax
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hμ,pow_succ]
  ring
end LogConcaveSampling.Quadrature

end

end

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

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialVector
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

lemma inverse_sqrt_time_mono {t T : ℝ} (h0 : 0≤t) (ht : t≤T) (hT : T<1) :
    (Real.sqrt (1-t^2))⁻¹≤(Real.sqrt (1-T^2))⁻¹ := by
  have hT0 : 0≤T := h0.trans ht
  have hpos : 0<1-T^2 := by nlinarith
  have hle : 1-T^2≤1-t^2 := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
    (Real.sqrt_le_sqrt hle)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
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
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma probabilityMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (probabilityMeanVelocity F x r t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have he := (conditionalFieldMean_lipschitz hF x hr hl ht0 ht1).dist_le_mul y z
  simp only [probabilityMeanVelocity,dist_smul₀,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr,
    probabilityMeanLipschitz]
  have hh := mul_le_mul_of_nonneg_left he hr
  have hp : 0≤(Real.pi^2/2)*(lam:ℝ)*r^2*dist y z := by positivity
  calc
    _ ≤ r*((Real.pi^2/2)*t*((lam:ℝ)*r)*dist y z) := hh
    _ = t*((Real.pi^2/2)*(lam:ℝ)*r^2*dist y z) := by ring
    _ ≤ _ := mul_le_of_le_one_left hp ht1.le

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma harmonicFree_lipschitz {d : ℕ} (n : ℕ) (z : ℝ) :
    LipschitzWith 2 (harmonicFree (d:=d) n z) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have he := (((lipschitzWith_smul (Real.cos (z*probabilityNodes n i))).comp
    (LipschitzWith.prod_fst (α:=Point d) (β:=Point d))).add
    ((lipschitzWith_smul (Real.sin (z*probabilityNodes n i))).comp
      (LipschitzWith.prod_snd (α:=Point d) (β:=Point d)))).dist_le_mul p q
  have hc : ‖Real.cos (z*probabilityNodes n i)‖+‖Real.sin (z*probabilityNodes n i)‖≤2 := by
    have hc := add_le_add (Real.abs_cos_le_one (z*probabilityNodes n i)) (Real.abs_sin_le_one (z*probabilityNodes n i))
    simpa only [Real.norm_eq_abs,show (1:ℝ)+1=2 by norm_num] using hc
  change dist (harmonicFree n z p i) (harmonicFree n z q i)≤_ at he
  simp only [NNReal.coe_add,mul_one,coe_nnnorm] at he
  exact he.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)

lemma harmonicMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (harmonicMeanVelocity F x r ρ) := by
  apply ((lipschitzWith_smul ρ).comp (probabilityMeanVelocity_lipschitz hF x hr hl hρ0 hρ1)).weaken
  change ‖ρ‖*(probabilityMeanLipschitz lam r:ℝ)≤_
  rw [Real.norm_eq_abs,abs_of_nonneg hρ0]
  exact mul_le_of_le_one_left (probabilityMeanLipschitz lam r).2 hρ1.le

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodesContinuous
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
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

lemma FinitePicard.nodes_continuous {I E X : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
    (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    (hφ : ∀i,Continuous (φ i)) (ha : Continuous a) (N : ℕ) :
    Continuous (nodes w φ a N) := by
  induction N with
  | zero => exact ha
  | succ N ih =>
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp ha).add (continuous_finsetSum _ (fun j _ =>
      ((hφ j).comp ((continuous_apply j).comp ih)).const_smul (w i j)))

lemma probabilityAnchored_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (N : ℕ) (s i : ProbabilityNode T h n) :
    Continuous (fun y => probabilityAnchoredPicard F x r T h n N s y i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · intro j
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    exact (probabilityMeanVelocity_lipschitz hF x hr hl hj.1 (hj.2.trans_lt hT1)).continuous
  · exact continuous_pi (fun _ => continuous_id)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringJointLaw
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
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

lemma centering_joint_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (productPointEquiv d d)=
      (interpolationLaw F x r T).prod (stdGaussian (Point d)) := by
  rw [interpolationLaw_eq_gibbs hF x hr (by linarith) (by nlinarith)]
  exact (productPotential_gibbs
    (interpolationPotential_smooth hF x hr hl hT0 hT1).continuous
      (gaussianPotential_polySmooth d).smooth.continuous).trans
    (by rw [gaussianPotential_gibbs])

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_KernelCorrectionPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
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
open scoped NNReal

variable {Ω E H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

lemma add_error_sq {f g k : Ω → E} (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hfg : Integrable (fun y => ‖f y-g y‖^2) μ)
    (hgk : Integrable (fun y => ‖g y-k y‖^2) μ)
    {A B : ℝ} (hA : (∫y,‖f y-g y‖^2 ∂μ)≤A) (hB : (∫y,‖g y-k y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖f y-k y‖^2) μ ∧ (∫y,‖f y-k y‖^2 ∂μ)≤2*A+2*B := by
  have he (y : Ω) : f y-k y=(f y-g y)-(k y-g y) := by abel
  have hi : Integrable (fun y => ‖k y-g y‖^2) μ := by simpa only [norm_sub_rev] using hgk
  have hb : (∫y,‖k y-g y‖^2 ∂μ)≤B := by simpa only [norm_sub_rev] using hB
  simp_rw [he]
  exact sub_sq_bound (hf.sub hg).aestronglyMeasurable (hk.sub hg).aestronglyMeasurable hfg hi hA hb

end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma harmonicPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (z : ℝ) (n N : ℕ) (i : Fin (n+1)) :
    Continuous (fun p => harmonicPicard F x r ρ z n N p i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · exact fun _ => (harmonicMeanVelocity_lipschitz hF x hr hl hρ0 hρ1).continuous
  · exact (harmonicFree_lipschitz n z).continuous

lemma kernelCorrectionPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (z : ℝ) (n : ℕ) (hn : 0<n) (N : ℕ) (s e : ProbabilityNode T h n) :
    Continuous (kernelCorrectionPicard F x r T h z n N s e) := by
  have hb : Continuous (fun p : Point d × Point d => probabilityAnchoredPicard F x r T h n N e p.1 s) :=
    (probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn N e s).comp continuous_fst
  have ht := probabilityNodeTime_mem hT0 hT1 hh hn s
  have hw := (harmonicPicard_continuous hF x hr hl ht.1 (ht.2.trans_lt hT1) z n N (Fin.last n)).comp
    (hb.prodMk continuous_snd)
  exact ((probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn (N+1) s e).comp hw).sub hw
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityEndpoint
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
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

lemma centering_transport_joint_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T) :
    (gibbs (centeringPotential F x r s)).map
      (fun y => (probabilityTransport hF x hr hl hT0 hT1 s e (productPointEquiv d d y).1,
        (productPointEquiv d d y).2))=
      (interpolationLaw F x r e).prod (stdGaussian (Point d)) := by
  let := interpolationLaw_probability hF x hr (by linarith) (s:ℝ)
  have hfw := (probabilityTransport_continuous hF x hr hl hT0 hT1 s e).measurable
  change (gibbs (centeringPotential F x r s)).map
    ((Prod.map (probabilityTransport hF x hr hl hT0 hT1 s e) id) ∘ productPointEquiv d d)=_
  rw [←Measure.map_map (hfw.prodMap measurable_id) (productPointEquiv d d).continuous.measurable,
    centering_joint_law hF x hr hl s.2.1 (s.2.2.trans_lt hT1),←Measure.map_prod_map _ _ hfw measurable_id,
    Measure.map_id,probabilityTransport_pushforward hF x hr hl hT0 hT1 s e]

lemma kernelTransportAction_terminal {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s : Icc (0:ℝ) T) (p : Point (d+d)) :
    kernelTransportAction (probabilityTransport hF x hr.le hl hT0 hT1 s ⟨T,hT0,le_rfl⟩) p=
      (terminalJacobian hF x hr hl hT0 hT1
        (s,terminalForward hF x hr.le hl hT0 hT1 (s,(productPointEquiv d d p).1))-
          ContinuousLinearMap.id ℝ (Point d)) (productPointEquiv d d p).2 := by
  rw [terminalJacobian_eq,terminalBackward_forward]
  rfl

lemma rms_bound_pushforward {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : Measurable f) (hlaw : μ.map f=ν)
    {e : Y → E} (he : Measurable e) (hi : Integrable (fun x => ‖e (f x)‖^2) μ)
    {B : ℝ} (hB : (∫x,‖e (f x)‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖e y‖^2) ν ∧ (∫y,‖e y‖^2 ∂ν)≤B := by
  rw [←hlaw]
  refine ⟨(integrable_map_measure (he.norm.pow_const 2).aestronglyMeasurable hf.aemeasurable).mpr hi,?_⟩
  rw [integral_map hf.aemeasurable (he.norm.pow_const 2).aestronglyMeasurable]
  exact hB
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Quadrature

lemma probabilityEndpoint_time {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) : probabilityNodeTime T h n (probabilityEndpoint hT0 hT1 hh n)=T := by
  have hlast : probabilityNodes n (Fin.last n)=1 := by
    change (n:ℝ)/(n:ℝ)=1
    exact div_self (by exact_mod_cast hn.ne')
  have hN : logMeshCount T h-1+1=logMeshCount T h := by have := logMeshCount_pos hT0 hT1 hh; omega
  simp only [probabilityNodeTime,probabilityEndpoint,hlast,mul_one,probabilityCellLength]
  rw [hN,logMeshNode_last hT0 hT1 hh]
  ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionRmsBudget
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
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

lemma kernelActionPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (ψ : ℝ) (n : ℕ) (hn : 0<n) (m N : ℕ) (s e : ProbabilityNode T h n) :
    Continuous (kernelActionPicard F x r T h ψ n m N s e) := by
  change Continuous (fun p => ∑i,(derivativeWeight (angleNodes m) i/ψ) •
    kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e p)
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
  exact hc.comp (kernelCorrectionPicard_continuous hF x hr hl hT0 hT1 hh (ψ*angleNodes m i) n hn N s e)

theorem kernelActionPicard_terminal_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      ∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let err := fun p : Point d × Point d =>
        kernelActionPicard F x r T h ψ n m N s (probabilityEndpoint hT0 hT1 hh n) p-
          (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hA⟩ := kernelActionPicard_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let ep := probabilityEndpoint hT0 hT1 hh n
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n ep,probabilityNodeTime_mem hT0 hT1 hh hn ep⟩
  have hE : E=⟨T,hT0.le,le_rfl⟩ := Subtype.ext (probabilityEndpoint_time hT0 hT1 hh n hn)
  intro R hR hRT m hm1 ψ hψ hψm
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩
  let inp := fun y : Point (d+d) => (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)
  let err := fun p : Point d × Point d => kernelActionPicard F x r T h ψ n m N s ep p-
    (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  have ha := hA hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s ep R hR hRT m hm1 ψ hψ hψm
  let aerr := fun f : Point d → Point d => fun y : Point (d+d) =>
    kernelActionPicard F x r T h ψ n m N s ep
      (f (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction f y
  change Integrable (fun y => ‖aerr (probabilityTransport hF x hr.le hl hT0.le hT1 S E) y‖^2)
      (gibbs (centeringPotential F x r S)) ∧
    (∫y,‖aerr (probabilityTransport hF x hr.le hl hT0.le hT1 S E) y‖^2
      ∂gibbs (centeringPotential F x r S))≤kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N at ha
  rw [hE] at ha
  have heq (y : Point (d+d)) : err (inp y)=kernelActionPicard F x r T h ψ n m N s ep (inp y)-kernelTransportAction fw y := by
    dsimp only [err,inp]
    rw [kernelTransportAction_terminal,terminalForward_eq]
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩).measurable
  have hinp : Measurable inp := (hfw.comp ((productPointEquiv d d).continuous.measurable.fst)).prodMk
    ((productPointEquiv d d).continuous.measurable.snd)
  have hlaw := centering_transport_joint_law hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩
  have hK : Continuous (fun p : Point d × Point d =>
      (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2) :=
    (((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
      (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd
  have he : Measurable err := ((kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ n hn m N s ep).sub hK).measurable
  have hi : Integrable (fun y => ‖err (inp y)‖^2) (gibbs (centeringPotential F x r S)) := by
    simpa only [heq] using ha.1
  have hb : (∫y,‖err (inp y)‖^2 ∂gibbs (centeringPotential F x r S))≤
      kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N := by
    simpa only [heq] using ha.2
  exact rms_bound_pushforward hinp hlaw he hi hb
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_numerical_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      ∀w : ProbabilityNode T h n → ℝ,
      let err := fun p : Point d × Point d =>
        kernelQuadraturePicard F x r T h ψ n m N (probabilityEndpoint hT0 hT1 hh n) w p-
          ∑s,w s • (terminalJacobian hF x hr hl hT0.le hT1
            (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        (∑s,|w s|)*(∑s,|w s| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h n s) h ψ C J k n m N) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hA⟩ := kernelActionPicard_terminal_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N R hR hRT m hm1 ψ hψ hψm w
  dsimp only
  let ep := probabilityEndpoint hT0 hT1 hh n
  let f := fun (s : ProbabilityNode T h n) (p : Point d × Point d) =>
    kernelActionPicard F x r T h ψ n m N s ep p-
      (terminalJacobian hF x hr hl hT0.le hT1
        (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  have hs (s : ProbabilityNode T h n) :=
    hA hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s R hR hRT m hm1 ψ hψ hψm
  have hfc (s : ProbabilityNode T h n) : Continuous (f s) := by
    have hK : Continuous (fun p : Point d × Point d =>
        (terminalJacobian hF x hr hl hT0.le hT1
          (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2) :=
      (((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd
    exact (kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ n hn m N s ep).sub hK
  have he (p : Point d × Point d) :
      kernelQuadraturePicard F x r T h ψ n m N ep w p-
        ∑s,w s • (terminalJacobian hF x hr hl hT0.le hT1
          (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2=
        ∑s,w s • f s p := by
    simp only [kernelQuadraturePicard,f,smul_sub,Finset.sum_sub_distrib]
  simp_rw [show probabilityEndpoint hT0 hT1 hh n=ep from rfl,he]
  exact weighted_sum_sq_varying w f
    (fun s => kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h n s) h ψ C J k n m N)
    (fun s => (hfc s).aestronglyMeasurable) (fun s => (hs s).1) (fun s => (hs s).2)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma zeroNodePolynomial_eval (u : I → ℝ) (i₀ : I) (hu0 : u i₀=0) (j : I) :
    (zeroNodePolynomial u i₀).eval (u j)=0 := by
  by_cases hj : j=i₀
  · simp [hj,hu0,zeroNodePolynomial]
  · simp only [zeroNodePolynomial,eval_mul,eval_X,eval_prod,eval_sub,eval_C]
    have hz : (∏i∈Finset.univ.erase i₀,(u j-u i))=0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩) (sub_self _)
    rw [hz,mul_zero]

lemma zeroNodePolynomial_derivative (u : I → ℝ) (i₀ : I) :
    (zeroNodePolynomial u i₀).derivative.eval 0=∏i∈Finset.univ.erase i₀,-u i := by
  simp only [zeroNodePolynomial,derivative_mul,derivative_X,eval_add,eval_mul,eval_X,one_mul,zero_mul,add_zero]
  simp only [eval_prod,eval_sub,eval_X,eval_C,zero_sub]

lemma zeroNodePolynomial_derivative_ne (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) : (zeroNodePolynomial u i₀).derivative.eval 0≠0 := by
  rw [zeroNodePolynomial_derivative]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (fun hz => (Finset.mem_erase.mp hi).1 (hu (hz.trans hu0.symm)))

lemma zeroHermiteBasis_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i j : I) :
    (zeroHermiteBasis u i₀ i).eval (u j)=if i=j then 1 else 0 := by
  simp only [zeroHermiteBasis,eval_sub,eval_mul,eval_C,zeroNodePolynomial_eval u i₀ hu0 j,mul_zero,sub_zero]
  by_cases h : i=j
  · subst i
    simp only [ite_true]
    exact Lagrange.eval_basis_self hu.injOn (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

lemma zeroHermiteBasis_derivative_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i : I) :
    (zeroHermiteBasis u i₀ i).derivative.eval 0=0 := by
  simp only [zeroHermiteBasis,derivative_sub,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_sub,eval_mul,eval_C]
  change derivativeWeight u i-(derivativeWeight u i/(zeroNodePolynomial u i₀).derivative.eval 0)*
    (zeroNodePolynomial u i₀).derivative.eval 0=0
  rw [div_mul_cancel₀ _ (zeroNodePolynomial_derivative_ne u hu i₀ hu0),sub_self]

lemma zeroHermitePolynomial_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → ℝ) (j : I) :
    (zeroHermitePolynomial u i₀ v).eval (u j)=v j := by
  simp only [zeroHermitePolynomial,eval_finsetSum,eval_mul,eval_C,zeroHermiteBasis_eval u hu i₀ hu0]
  simp

lemma zeroHermitePolynomial_derivative_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → ℝ) :
    (zeroHermitePolynomial u i₀ v).derivative.eval 0=0 := by
  simp only [zeroHermitePolynomial,derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_finsetSum,eval_mul,eval_C,zeroHermiteBasis_derivative_zero u hu i₀ hu0,mul_zero,Finset.sum_const_zero]

lemma polynomial_divX_eval {p : ℝ[X]} (hp : p.eval 0=0) {z : ℝ} (hz : z≠0) :
    p.divX.eval z=p.eval z/z := by
  have hp0 : p.coeff 0=0 := (coeff_zero_eq_eval_zero p).trans hp
  have hh := congrArg (fun q : ℝ[X] => q.eval z) (X_mul_divX_add p)
  simp only [eval_add,eval_mul,eval_X,eval_C,hp0,add_zero] at hh
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using hh

lemma zeroHermiteRegularized_eval (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (i : I) {z : ℝ} (hz : z≠0) :
    (zeroHermiteRegularized u i₀ i).eval z=(zeroHermiteBasis u i₀ i).derivative.eval z/z :=
  polynomial_divX_eval (zeroHermiteBasis_derivative_zero u hu i₀ hu0 i) hz

lemma zeroHermite_weights_abs (u : I → ℝ) (i₀ : I) {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∑i,|zeroHermiteWeight u i₀ i/ℓ|)=(∑i,|zeroHermiteWeight u i₀ i|)/ℓ := by
  simp only [abs_div,abs_of_pos hℓ,Finset.sum_div]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma zeroNodePolynomial_natDegree (u : I → ℝ) (i₀ : I) :
    (zeroNodePolynomial u i₀).natDegree≤Fintype.card I := by
  have hI : 0<Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hp := natDegree_prod_le (Finset.univ.erase i₀) (fun i => (X-C (u i):ℝ[X]))
  simp only [natDegree_X_sub_C,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i₀),
    Finset.card_univ,Nat.nsmul_eq_mul,mul_one] at hp
  have hm := natDegree_mul_le (p:=(X:ℝ[X])) (q:=∏i∈Finset.univ.erase i₀,(X-C (u i)))
  change (zeroNodePolynomial u i₀).natDegree≤_ at hm
  simp only [natDegree_X] at hm
  exact hm.trans (by omega)

lemma zeroHermiteBasis_natDegree (u : I → ℝ) (hu : Function.Injective u) (i₀ i : I) :
    (zeroHermiteBasis u i₀ i).natDegree≤Fintype.card I := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · rw [Lagrange.natDegree_basis hu.injOn (Finset.mem_univ i),Finset.card_univ]
    omega
  · exact (natDegree_C_mul_le _ _).trans (zeroNodePolynomial_natDegree u i₀)

lemma zeroHermitePolynomial_degree (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (v : I → ℝ) :
    (zeroHermitePolynomial u i₀ v).degree≤Fintype.card I := by
  apply (degree_sum_le _ _).trans
  exact Finset.sup_le (fun i _ => degree_le_of_natDegree_le
    ((natDegree_C_mul_le _ _).trans (zeroHermiteBasis_natDegree u hu i₀ i)))

lemma zeroHermite_unique_zero (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (p : ℝ[X])
    (hp : p.degree≤Fintype.card I) (hpder : p.derivative.eval 0=0)
    (hpval : ∀i,p.eval (u i)=0) : p=0 := by
  by_contra hpne
  have hp0 : p.eval 0=0 := by simpa only [hu0] using hpval i₀
  have hp1 : p.coeff 1=0 := by
    simpa only [←coeff_zero_eq_eval_zero,coeff_derivative,Nat.cast_zero,zero_add,mul_one] using hpder
  have hqval (i : I) : p.divX.eval (u i)=0 := by
    by_cases hi : i=i₀
    · subst i
      rw [hu0,←coeff_zero_eq_eval_zero,coeff_divX]
      exact hp1
    · have hn : u i≠0 := fun h => hi (hu (h.trans hu0.symm))
      rw [polynomial_divX_eval hp0 hn,hpval i,zero_div]
  have hqdegree := (degree_divX_lt hpne).trans_le hp
  have he := Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn
    (by simpa only [Finset.card_univ] using hqdegree)
  have hqzero : p.divX=0 := by
    rw [he]
    simp only [Lagrange.interpolate_apply,hqval,C_0,zero_mul,Finset.sum_const_zero]
  have heq := divX_eq_zero_iff.mp hqzero
  have hpc0 := (coeff_zero_eq_eval_zero p).trans hp0
  rw [hpc0,C_0] at heq
  exact hpne heq

theorem zeroHermite_reproduces (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (p : ℝ[X])
    (hp : p.degree≤Fintype.card I) (hpder : p.derivative.eval 0=0) :
    zeroHermitePolynomial u i₀ (fun i => p.eval (u i))=p := by
  apply sub_eq_zero.mp
  apply zeroHermite_unique_zero u hu i₀ hu0
  · exact (degree_sub_le _ _).trans (max_le (zeroHermitePolynomial_degree u hu i₀ _) hp)
  · simp only [derivative_sub,eval_sub,zeroHermitePolynomial_derivative_zero u hu i₀ hu0,hpder,sub_self]
  · intro i
    simp only [eval_sub,zeroHermitePolynomial_eval u hu i₀ hu0,sub_self]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω] {μ : Measure Ω}

lemma zeroHermiteInterpolation_hasDerivAt (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) :
    HasDerivAt (zeroHermiteInterpolation u i₀ v)
      (∑i,(zeroHermiteBasis u i₀ i).derivative.eval t • v i) t := by
  exact HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => ((zeroHermiteBasis u i₀ i).hasDerivAt t).smul_const (v i))

lemma zeroHermiteAction_eq (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (v : I → E) {t : ℝ} (ht : t≠0) :
    zeroHermiteAction u i₀ v t=t⁻¹ • deriv (zeroHermiteInterpolation u i₀ v) t := by
  rw [(zeroHermiteInterpolation_hasDerivAt u i₀ v t).deriv]
  simp only [zeroHermiteAction,zeroHermiteRegularized_eval u hu i₀ hu0 _ ht,
    Finset.smul_sum,smul_smul,div_eq_mul_inv,mul_comm]

lemma zeroHermiteAction_integral [CompleteSpace E] (u : I → ℝ) (i₀ : I) (v : I → E) :
    (∫t in (0:ℝ)..1,zeroHermiteAction u i₀ v t)=∑i,zeroHermiteWeight u i₀ i • v i := by
  unfold zeroHermiteAction
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_smul_const _ _
  · intro i _
    exact ((Polynomial.continuous _).smul continuous_const).intervalIntegrable 0 1

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma zeroHermite_reproduces_power (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (k : ℕ) (hk : k≤Fintype.card I) (hk1 : k≠1) (t : ℝ) :
    (∑i,(zeroHermiteBasis u i₀ i).eval t*(u i)^k)=t^k := by
  have hd : ((X:ℝ[X])^k).derivative.eval 0=0 := by
    rcases k with _|k
    · simp
    rcases k with _|k
    · exact (hk1 rfl).elim
    · simp
  have hh := congrArg (fun p : ℝ[X] => p.eval t)
    (zeroHermite_reproduces u hu i₀ hu0 (X^k) (by simpa using hk) hd)
  simpa only [zeroHermitePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,mul_comm] using hh

theorem zeroHermite_reproduces_vector (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hn : 1≤n) (hcard : n≤Fintype.card I)
    (v : Fin (n+1) → E) (hv : v ⟨1,by omega⟩=0) (t : ℝ) :
    zeroHermiteInterpolation u i₀ (fun i => ∑k : Fin (n+1),(u i)^(k:ℕ) • v k) t=
      ∑k : Fin (n+1),t^(k:ℕ) • v k := by
  unfold zeroHermiteInterpolation
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (k:ℕ)=1
  · have he : k=⟨1,by omega⟩ := Fin.ext hk
    simp only [he,hv,smul_zero,Finset.sum_const_zero]
  · rw [←Finset.sum_smul,zeroHermite_reproduces_power u hu i₀ hu0 k (by omega) hk]

lemma zeroHermite_reproduces_chainTaylor (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hn : 1≤n) (hcard : n≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJ : J 1 0=0) (ℓ t : ℝ) :
    zeroHermiteInterpolation u i₀ (fun i => chainTaylor J n 0 (ℓ*u i)) t=
      chainTaylor J n 0 (ℓ*t) := by
  have he (v : ℝ) := chainTaylor_scaled_eval J n 0 ℓ v
  simp only [zero_add] at he
  simp_rw [he]
  apply zeroHermite_reproduces_vector u hu i₀ hu0 n hn hcard
  simp only [hJ,smul_zero]

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BasisDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma chainTaylor_hasDerivAt (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) :
    HasDerivAt (chainTaylor J (n+1) a)
      (chainTaylor (fun k => J (k+1)) n a x) x := by
  have he (t : ℝ) : chainTaylor J (n+1) a t=
      (∑k∈Finset.range (n+1), (((k+1).factorial:ℝ)⁻¹*(t-a)^(k+1)) • J (k+1) a)+J 0 a := by
    simp only [chainTaylor,Finset.sum_range_succ',Nat.factorial_zero,Nat.cast_one,
      inv_one,pow_zero,mul_one,one_smul]
  rw [funext he]
  have h (k : ℕ) : HasDerivAt
      (fun t : ℝ => (((k+1).factorial:ℝ)⁻¹*(t-a)^(k+1)) • J (k+1) a)
      (((k.factorial:ℝ)⁻¹*(x-a)^k) • J (k+1) a) x := by
    have hh := ((((hasDerivAt_id x).sub_const a).pow (k+1)).const_mul
      (((k+1).factorial:ℝ)⁻¹)).smul_const (J (k+1) a)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hk : (k:ℝ)+1≠0 := by positivity
    have hkf : (k.factorial:ℝ)≠0 := by positivity
    simp only [Nat.add_sub_cancel,mul_one]
    field_simp
    rfl
  exact (HasDerivAt.fun_sum (fun k _ => h k)).add_const (J 0 a)

omit [CompleteSpace E] in
lemma chainTaylor_joint_continuous {X : Type*} [TopologicalSpace X]
    (J : ℕ → ℝ → X → E) (a : ℝ) (hJ : ∀k,Continuous (J k a)) (n : ℕ) :
    Continuous (fun p : ℝ × X => chainTaylor (fun k t => J k t p.2) n a p.1) := by
  unfold chainTaylor
  exact continuous_finsetSum _ (fun k _ =>
    (continuous_const.mul ((continuous_fst.sub continuous_const).pow k)).smul ((hJ k).comp continuous_snd))
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma basisDerivative_continuous (u : I → ℝ) (i : I) : Continuous (basisDerivative u i) :=
  Polynomial.continuous _

omit [CompleteSpace E] in
lemma interpolation_hasDerivAt (u : I → ℝ) (v : I → E) (t : ℝ) :
    HasDerivAt (interpolation u v) (derivativeInterpolation u v t) t := by
  exact HasDerivAt.fun_sum (fun i _ =>
    ((Lagrange.basis Finset.univ u i).hasDerivAt t).smul_const (v i))

omit [CompleteSpace E] in
lemma derivativeInterpolation_chainTaylor (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : n+2≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    derivativeInterpolation u (fun i => chainTaylor J (n+1) a (a+ℓ*u i)) t=
      ℓ • chainTaylor (fun k => J (k+1)) n a (a+ℓ*t) := by
  have he : interpolation u (fun i => chainTaylor J (n+1) a (a+ℓ*u i))=
      fun t => chainTaylor J (n+1) a (a+ℓ*t) :=
    funext (reproduces_cell_chainTaylor u hu (n+1) hn J a ℓ)
  have h := interpolation_hasDerivAt u (fun i => chainTaylor J (n+1) a (a+ℓ*u i)) t
  rw [he] at h
  have ht := ((chainTaylor_hasDerivAt J n a (a+ℓ*t)).scomp t
    (((hasDerivAt_id t).const_mul ℓ).const_add a))
  have ht' : HasDerivAt (fun t => chainTaylor J (n+1) a (a+ℓ*t))
      (ℓ • chainTaylor (fun k => J (k+1)) n a (a+ℓ*t)) t := by
    simpa only [Function.comp_def,mul_one,id_eq] using ht
  exact h.unique ht'

omit [CompleteSpace E] in
lemma derivativeInterpolation_sub (u : I → ℝ) (v w : I → E) (t : ℝ) :
    derivativeInterpolation u (fun i => v i-w i) t=
      derivativeInterpolation u v t-derivativeInterpolation u w t := by
  simp only [derivativeInterpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma derivative_cell_chain_error_eq (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : n+2≤Fintype.card I) (J : ℕ → ℝ → E)
    (a t : ℝ) {ℓ : ℝ} (hℓ : ℓ≠0) :
    J 1 (a+ℓ*t)-ℓ⁻¹ • derivativeInterpolation u (fun i => J 0 (a+ℓ*u i)) t=
      (J 1 (a+ℓ*t)-chainTaylor (fun k => J (k+1)) n a (a+ℓ*t))-
        ℓ⁻¹ • derivativeInterpolation u
          (fun i => J 0 (a+ℓ*u i)-chainTaylor J (n+1) a (a+ℓ*u i)) t := by
  rw [derivativeInterpolation_sub,derivativeInterpolation_chainTaylor u hu n hn,
    smul_sub,smul_smul,inv_mul_cancel₀ hℓ,one_smul]
  abel

lemma exists_basisDerivative_budget (u : I → ℝ) :
    ∃C : ℝ,1≤C ∧ ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative u i t|≤C := by
  have hc : Continuous (fun t => ∑i,|basisDerivative u i t|) :=
    continuous_finsetSum _ (fun i _ => (basisDerivative_continuous u i).abs)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,fun t ht => ?_⟩
  have hn : 0≤∑i,|basisDerivative u i t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (∑i,|basisDerivative u i t|)≤C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hC t ht
  exact hh.trans (le_max_left _ _)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Filter
open scoped BigOperators

namespace RMSIntegral
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma smul_sq_bound (c : ℝ) {f : Ω → E}
    (hi : Integrable (fun z => ‖f z‖^2) μ) {B : ℝ}
    (hB : (∫z,‖f z‖^2 ∂μ)≤B) :
    Integrable (fun z => ‖c • f z‖^2) μ ∧
      (∫z,‖c • f z‖^2 ∂μ) ≤ c^2*B := by
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact ⟨hi.const_mul _,by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hB (sq_nonneg c)⟩
end RMSIntegral

namespace Quadrature
variable {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

lemma chainTaylor_cell_rms (J : ℕ → ℝ × Ω → E)
    (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (n : ℕ) {a x b B : ℝ} (hax : a≤x) (hxb : x≤b) (hB0 : 0≤B)
    (hi : ∀t∈Icc a b,Integrable (fun z => ‖J (n+1) (t,z)‖^2) μ)
    (hB : ∀t∈Icc a b,(∫z,‖J (n+1) (t,z)‖^2 ∂μ)≤B) :
    Integrable (fun z => ‖J 0 (x,z)-chainTaylor (fun k t => J k (t,z)) n a x‖^2) μ ∧
      (∫z,‖J 0 (x,z)-chainTaylor (fun k t => J k (t,z)) n a x‖^2 ∂μ)≤
        ((x-a)^(n+1))^2*B := by
  have hh := chainTaylor_remainder_rms (J:=fun k t z => J k (t,z)) (s:=univ) (n:=n)
    hax hB0 (subset_univ _) (fun z k t _ => (hJ k t z).hasDerivWithinAt)
    (hJc (n+1)).aestronglyMeasurable
    (fun t ht => hi t ⟨ht.1.le,ht.2.trans hxb⟩)
    (fun t ht => hB t ⟨ht.1.le,ht.2.trans hxb⟩)
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hB0
  apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (sub_nonneg.mpr hax) _) (Nat.cast_nonneg _))
  apply div_le_self (pow_nonneg (sub_nonneg.mpr hax) _)
  exact_mod_cast Nat.factorial_pos n

lemma chainTaylor_regularized_derivative_rms (J : ℕ → ℝ × Ω → E)
    (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (n : ℕ) {ℓ z B : ℝ} (hℓ : 0<ℓ) (hz : z∈Icc (0:ℝ) 1) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) ℓ,Integrable (fun y => ‖J (n+2) (t,y)‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) ℓ,(∫y,‖J (n+2) (t,y)‖^2 ∂μ)≤B) :
    let f := fun y => z⁻¹ • (J 1 (ℓ*z,y)-
      chainTaylor (fun k t => J (k+1) (t,y)) n 0 (ℓ*z))
    Integrable (fun y => ‖f y‖^2) μ ∧
      (∫y,‖f y‖^2 ∂μ)≤(ℓ^(n+1))^2*B := by
  dsimp only
  have h0 : 0≤ℓ*z := mul_nonneg hℓ.le hz.1
  have h1 : ℓ*z≤ℓ := by nlinarith [hz.2]
  have hh := chainTaylor_cell_rms (fun k => J (k+1)) (fun k => hJc (k+1))
    (fun k t y => hJ (k+1) t y) n h0 h1 hB0 hi hB
  simp only [Nat.zero_add,sub_zero] at hh
  have hv := RMSIntegral.smul_sq_bound z⁻¹ hh.1 hh.2
  refine ⟨hv.1,hv.2.trans ?_⟩
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hB0
  by_cases hzne : z=0
  · simp only [hzne,inv_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]
    exact sq_nonneg _
  · have he : z⁻¹^2*((ℓ*z)^(n+1))^2=(ℓ^(n+1))^2*(z^n)^2 := by
      rw [mul_pow,pow_succ z]
      field_simp
    rw [he]
    apply mul_le_of_le_one_right (sq_nonneg _)
    exact pow_le_one₀ (pow_nonneg hz.1 _) (pow_le_one₀ hz.1 hz.2)
end Quadrature
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

theorem derivative_cell_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (hun : ∀i,u i∈Icc (0:ℝ) 1) (n : ℕ) (hcard : n+2≤Fintype.card I)
    (J : ℕ → ℝ × Ω → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    {a ℓ t B : ℝ} (hℓ : 0<ℓ) (ht : t∈Icc (0:ℝ) 1) (hB0 : 0≤B)
    (hi : ∀s∈Icc a (a+ℓ),Integrable (fun z => ‖J (n+2) (s,z)‖^2) μ)
    (hB : ∀s∈Icc a (a+ℓ),(∫z,‖J (n+2) (s,z)‖^2 ∂μ)≤B) :
    let err := fun z => J 1 (a+ℓ*t,z)-ℓ⁻¹ •
      derivativeInterpolation u (fun i => J 0 (a+ℓ*u i,z)) t
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤
        2*(1+(∑i,|basisDerivative u i t|)^2)*(ℓ^(n+1))^2*B := by
  dsimp only
  let P := fun (t : ℝ) (z : Ω) => J 0 (t,z)-chainTaylor (fun k v => J k (v,z)) (n+1) a t
  let R := fun z => J 1 (a+ℓ*t,z)-chainTaylor (fun k v => J (k+1) (v,z)) n a (a+ℓ*t)
  have hpoint (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      a≤a+ℓ*v ∧ a+ℓ*v≤a+ℓ := by
    constructor <;> nlinarith [hv.1,hv.2]
  have hR := chainTaylor_cell_rms (fun k => J (k+1)) (fun k => hJc (k+1))
    (fun k s z => hJ (k+1) s z) n (hpoint t ht).1 (hpoint t ht).2 hB0 hi hB
  have hRb : (∫z,‖R z‖^2 ∂μ)≤(ℓ^(n+1))^2*B := by
    refine hR.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hB0
    apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr (hpoint t ht).1) _)
    exact pow_le_pow_left₀ (sub_nonneg.mpr (hpoint t ht).1) (by linarith [(hpoint t ht).2]) _
  have hnode (i : I) : Integrable (fun z => ‖P (a+ℓ*u i) z‖^2) μ ∧
      (∫z,‖P (a+ℓ*u i) z‖^2 ∂μ)≤(ℓ^(n+2))^2*B := by
    have hh := chainTaylor_cell_rms J hJc hJ (n+1)
      (hpoint (u i) (hun i)).1 (hpoint (u i) (hun i)).2 hB0 hi hB
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hB0
    apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr (hpoint (u i) (hun i)).1) _)
    exact pow_le_pow_left₀ (sub_nonneg.mpr (hpoint (u i) (hun i)).1)
      (by linarith [(hpoint (u i) (hun i)).2]) _
  have hPc : Continuous (fun p : ℝ × Ω => P p.1 p.2) :=
    (hJc 0).sub (chainTaylor_joint_continuous (fun k v z => J k (v,z)) a
      (fun k => (hJc k).comp (continuous_const.prodMk continuous_id)) (n+1))
  have hnm (i : I) : AEStronglyMeasurable (P (a+ℓ*u i)) μ :=
    (hPc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basisDerivative u i t)
    (fun i => P (a+ℓ*u i)) hnm (fun i => (hnode i).1) (fun i => (hnode i).2)
  have hscaled := RMSIntegral.smul_sq_bound ℓ⁻¹ hsum.1 hsum.2
  have hRc : Continuous R :=
    ((hJc 1).comp (continuous_const.prodMk continuous_id)).sub
      ((chainTaylor_joint_continuous (fun k v z => J (k+1) (v,z)) a
        (fun k => (hJc (k+1)).comp (continuous_const.prodMk continuous_id)) n).comp
          (continuous_const.prodMk continuous_id))
  have hsm : AEStronglyMeasurable
      (fun z => ℓ⁻¹ • ∑i,basisDerivative u i t • P (a+ℓ*u i) z) μ := by
    exact (Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hnm i).const_smul _)).const_smul _
  have hdiff := RMSIntegral.sub_sq_bound hRc.aestronglyMeasurable hsm
    hR.1 hscaled.1 hRb hscaled.2
  have he (z : Ω) := derivative_cell_chain_error_eq u hu n hcard
    (fun k s => J k (s,z)) a t hℓ.ne'
  simp_rw [he]
  refine ⟨hdiff.1,hdiff.2.trans_eq ?_⟩
  rw [pow_succ ℓ (n+1)]
  field_simp
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma regularized_intervalIntegrable {f : ℝ → E} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (h0 : f 0=0) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume 0 1 := by
  have hc : Continuous (dslope f 0) := continuousOn_univ.mp
    ((continuousOn_dslope (s:=univ) (by simp)).mpr ⟨hf.continuousOn,hd⟩)
  apply (hc.intervalIntegrable 0 1).congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)] at ht
  simp only [dslope_of_ne f ht.1.ne',slope_def_module,h0,sub_zero]

lemma zeroHermite_chainTaylor_integral (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJ : J 1 0=0) {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∫t in (0:ℝ)..1,t⁻¹ • chainTaylor (fun k => J (k+1)) n 0 (ℓ*t))=
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • chainTaylor J (n+1) 0 (ℓ*u i) := by
  let v := fun i => chainTaylor J (n+1) 0 (ℓ*u i)
  have he := funext (zeroHermite_reproduces_chainTaylor u hu i₀ hu0 (n+1)
    (by omega) hcard J hJ ℓ)
  have heD (t : ℝ) : deriv (zeroHermiteInterpolation u i₀ v) t=
      ℓ • chainTaylor (fun k => J (k+1)) n 0 (ℓ*t) := by
    dsimp only [v]
    rw [he]
    simpa only [Function.comp_def,mul_one] using
      ((chainTaylor_hasDerivAt J n 0 (ℓ*t)).scomp t
        ((hasDerivAt_id t).const_mul ℓ)).deriv
  calc
    _ = ∫t in (0:ℝ)..1,ℓ⁻¹ • zeroHermiteAction u i₀ v t := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [zeroHermiteAction_eq u hu i₀ hu0 v ht.1.ne',heD]
      simp only [smul_smul]
      congr 1
      field_simp
    _ = ℓ⁻¹ • ∑i,zeroHermiteWeight u i₀ i • v i := by
      rw [intervalIntegral.integral_smul,zeroHermiteAction_integral]
    _ = _ := by
      simp only [Finset.smul_sum,smul_smul,div_eq_mul_inv,mul_comm,v]

lemma zeroHermite_derivative_error_eq (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t,HasDerivAt (J k) (J (k+1) t) t) (hz : J 1 0=0)
    {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∫t in (0:ℝ)..1,t⁻¹ • J 1 (ℓ*t))-
      (∑i,(zeroHermiteWeight u i₀ i/ℓ) • J 0 (ℓ*u i))=
    (∫t in (0:ℝ)..1,t⁻¹ • (J 1 (ℓ*t)-chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)))-
      (∑i,(zeroHermiteWeight u i₀ i/ℓ) • (J 0 (ℓ*u i)-chainTaylor J (n+1) 0 (ℓ*u i))) := by
  have h1 := regularized_intervalIntegrable ((hJc 1).comp (continuous_const.mul continuous_id))
    (((hJ 1 (ℓ*0)).scomp 0 ((hasDerivAt_id 0).const_mul ℓ)).differentiableAt)
    (by simpa using hz)
  change IntervalIntegrable (fun t => t⁻¹ • J 1 (ℓ*t)) volume 0 1 at h1
  have hp : Continuous (fun t => chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)) := by
    unfold chainTaylor
    fun_prop
  have hpd : DifferentiableAt ℝ (fun t => chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)) 0 := by
    unfold chainTaylor
    fun_prop
  have hp0 : chainTaylor (fun k => J (k+1)) n 0 (ℓ*0)=0 := by
    simp [chainTaylor,Finset.sum_range_succ',hz]
  have h2 := regularized_intervalIntegrable hp hpd hp0
  simp only [smul_sub,Finset.sum_sub_distrib]
  rw [intervalIntegral.integral_sub h1 h2,zeroHermite_chainTaylor_integral u hu i₀ hu0 n hcard J hz hℓ]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

theorem zeroHermite_derivative_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (hun : ∀i,u i∈Icc (0:ℝ) 1)
    (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ × Ω → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (hz : ∀z,J 1 (0,z)=0) {ℓ B : ℝ} (hℓ : 0<ℓ) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) ℓ,Integrable (fun z => ‖J (n+2) (t,z)‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) ℓ,(∫z,‖J (n+2) (t,z)‖^2 ∂μ)≤B) :
    let err := fun z => (∫t in (0:ℝ)..1,t⁻¹ • J 1 (ℓ*t,z))-
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • J 0 (ℓ*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤
        2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)*(ℓ^(n+1))^2*B := by
  dsimp only
  let R := fun (t : ℝ) (z : Ω) => J 1 (ℓ*t,z)-
    chainTaylor (fun k v => J (k+1) (v,z)) n 0 (ℓ*t)
  let f := fun p : ℝ × Ω => p.1⁻¹ • R p.1 p.2
  let η : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  have hRc : Continuous (fun p : ℝ × Ω => R p.1 p.2) := by
    apply Continuous.sub
    · exact (hJc 1).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
    · exact (chainTaylor_joint_continuous (fun k v z => J (k+1) (v,z)) 0
        (fun k => (hJc (k+1)).comp (continuous_const.prodMk continuous_id)) n).comp
          ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hfm : AEStronglyMeasurable f (η.prod μ) :=
    measurable_fst.inv.aestronglyMeasurable.smul hRc.aestronglyMeasurable
  have hrms (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    chainTaylor_regularized_derivative_rms J hJc hJ n hℓ ht hB0 hi hB
  have hint := RMSIntegral.time_seed_uniform hfm
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => (hrms t ⟨ht.1.le,ht.2⟩).1))
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => (hrms t ⟨ht.1.le,ht.2⟩).2))
  have heta : η.real univ=1 := by
    simp only [η,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
      ENNReal.ofReal_one,ENNReal.toReal_one]
  rw [heta,one_pow,one_mul] at hint
  let P := fun (t : ℝ) (z : Ω) => J 0 (t,z)-chainTaylor (fun k v => J k (v,z)) (n+1) 0 t
  have hPc : Continuous (fun p : ℝ × Ω => P p.1 p.2) :=
    (hJc 0).sub (chainTaylor_joint_continuous (fun k v z => J k (v,z)) 0
      (fun k => (hJc k).comp (continuous_const.prodMk continuous_id)) (n+1))
  have hnode (i : I) : Integrable (fun z => ‖P (ℓ*u i) z‖^2) μ ∧
      (∫z,‖P (ℓ*u i) z‖^2 ∂μ)≤(ℓ^(n+2))^2*B := by
    have h0 : 0≤ℓ*u i := mul_nonneg hℓ.le (hun i).1
    have h1 : ℓ*u i≤ℓ := mul_le_of_le_one_right hℓ.le (hun i).2
    obtain ⟨hi',hb'⟩ := chainTaylor_cell_rms J hJc hJ (n+1) h0 h1 hB0 hi hB
    refine ⟨hi',hb'.trans ?_⟩
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (pow_nonneg h0 _) (pow_le_pow_left₀ h0 h1 _) 2) hB0
  have hnm (i : I) : AEStronglyMeasurable (P (ℓ*u i)) μ :=
    (hPc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hsum := RMSIntegral.weighted_sum_sq (fun i => zeroHermiteWeight u i₀ i/ℓ)
    (fun i => P (ℓ*u i)) hnm (fun i => (hnode i).1) (fun i => (hnode i).2)
  rw [zeroHermite_weights_abs u i₀ hℓ] at hsum
  have hsm : AEStronglyMeasurable
      (fun z => ∑i,(zeroHermiteWeight u i₀ i/ℓ) • P (ℓ*u i) z) μ := by
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hnm i).const_smul _)
  have hdiff := RMSIntegral.sub_sq_bound hfm.prod_swap.integral_prod_right' hsm hint.1 hsum.1 hint.2 hsum.2
  have he (z : Ω) := zeroHermite_derivative_error_eq u hu i₀ hu0 n hcard
    (fun k t => J k (t,z)) (fun k => (hJc k).comp (continuous_id.prodMk continuous_const))
    (fun k t => hJ k t z) (hz z) hℓ
  simp_rw [he,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  refine ⟨hdiff.1,hdiff.2.trans_eq ?_⟩
  rw [pow_succ ℓ (n+1)]
  field_simp
end LogConcaveSampling.Quadrature

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialJacobianTimeDeriv
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

theorem spatialJacobian_time_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℝ × E → E} (hX : ContDiff ℝ (⊤:ℕ∞) X) (V : E → E) (t : ℝ)
    (hODE : ∀y,HasDerivAt (fun u => X (u,y)) (V (X (t,y))) t) (y : E) :
    HasDerivAt (fun u => fderiv ℝ (fun z => X (u,z)) y)
      (fderiv ℝ (fun z => V (X (t,z))) y) t := by
  let D := fderiv ℝ X
  let S := fderiv ℝ D (t,y)
  let R : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have hD : ContDiff ℝ (⊤:ℕ∞) D := hX.fderiv_right (by simp)
  have hc (u : ℝ) : fderiv ℝ (fun z => X (u,z)) y=(D (u,y)).comp R := by
    have hd := ((hX.differentiable (by simp) (u,y)).hasFDerivAt).comp y
      ((hasFDerivAt_const u y).prodMk (hasFDerivAt_id y))
    exact hd.fderiv
  have hd := ((hD.differentiable (by simp) (t,y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hdc : HasDerivAt (fun u => (D (u,y)).comp R) ((S (1,0)).comp R) t := by
    simpa only [S,Function.comp_def,id_eq,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero]
      using hd.clm_comp (hasDerivAt_const t R)
  have he : (fun z => D (t,z) (1,0))=fun z => V (X (t,z)) := by
    funext z
    exact (((hX.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))).unique (hODE z)
  have hh := (((hD.differentiable (by simp) (t,y)).hasFDerivAt).comp y
    ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))).clm_apply
      (hasFDerivAt_const (1,0) y)
  change HasFDerivAt (fun z => D (t,z) (1,0)) _ y at hh
  rw [he] at hh
  have hSym := (hX.contDiffAt (x:=(t,y))).isSymmSndFDerivAt (by simp)
  have heq : (S (1,0)).comp R=fderiv ℝ (fun z => V (X (t,z))) y := by
    rw [hh.fderiv]
    ext v
    simpa [S,D,R,ContinuousLinearMap.comp_apply] using hSym (1,0) (0,v)
  simp_rw [hc]
  exact heq ▸ hdc
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalJacobianInverse
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
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

theorem terminalJacobian_inverse (t : Icc (0:ℝ) T) (y : Point d) :
    let C := fderiv ℝ (fun z => terminalBackward hF x hr.le hl hT0 hT1 (t,z)) y
    let B := terminalJacobian hF x hr hl hT0 hT1 (t,y)
    B.comp C=ContinuousLinearMap.id ℝ (Point d) ∧
      C.comp B=ContinuousLinearMap.id ℝ (Point d) := by
  dsimp only
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩
  have hf : Differentiable ℝ f :=
    (probabilityTransport_contDiff hF x hr.le hl hT0 hT1 _ _ 1).differentiable (by norm_num)
  have hg : Differentiable ℝ g :=
    (probabilityTransport_contDiff hF x hr.le hl hT0 hT1 _ _ 1).differentiable (by norm_num)
  have hfg : f ∘ g=id := by
    funext z
    exact (probabilityTransport_cocycle hF x hr.le hl hT0 hT1 _ _ _ z).trans
      (probabilityTransport_initial hF x hr.le hl hT0 hT1 t z)
  have hgf : g ∘ f=id := by
    funext z
    exact (probabilityTransport_cocycle hF x hr.le hl hT0 hT1 _ _ _ z).trans
      (probabilityTransport_initial hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ z)
  have he : (fun z => terminalBackward hF x hr.le hl hT0 hT1 (t,z))=f :=
    funext (terminalBackward_eq hF x hr.le hl hT0 hT1 t)
  rw [he,terminalJacobian_eq,terminalBackward_eq]
  change (fderiv ℝ g (f y)).comp (fderiv ℝ f y)=_ ∧
    (fderiv ℝ f y).comp (fderiv ℝ g (f y))=_
  constructor
  · rw [←fderiv_comp y (hg (f y)) (hf y),hgf]
    exact fderiv_id
  · have hid : g (f y)=y := congrFun hgf y
    nth_rw 1 [←hid]
    rw [←fderiv_comp (f y) (hf (g (f y))) (hg (f y)),hfg]
    exact fderiv_id

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam

theorem terminalJacobian_deriv {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0 hT1 (u,y))
      ((r*ρ) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        (conditionalFirstJet F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  let X := terminalBackward hF x hr.le hl hT0 hT1
  let B := fun u => terminalJacobian hF x hr hl hT0 hT1 (u,y)
  let C := fun u => fderiv ℝ (fun z => X (u,z)) y
  let U := conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,X (ρ,y))
  let K := (-r*ρ) • U
  let B' := fderiv ℝ (terminalJacobian hF x hr hl hT0 hT1) (ρ,y) (1,0)
  have hX : ContDiff ℝ (⊤:ℕ∞) X := terminalBackward_smooth hF x hr.le hl hT0 hT1
  have hY : Differentiable ℝ (fun z => X (ρ,z)) :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hM := (conditionalFieldMean_smooth hF x hr.le hl hρ0.le (hρT.trans hT1)).differentiable (by simp)
  have hV : Differentiable ℝ (fun z => -r • conditionalFieldMean F x r ρ z) :=
    hM.const_smul (-r)
  have hK : fderiv ℝ (fun z => -r • conditionalFieldMean F x r ρ z) (X (ρ,y))=K := by
    rw [fderiv_fun_const_smul (hM (X (ρ,y))) (-r),conditionalFirstJet_deriv hF x hr hlam hl hρ0.le (hρT.trans hT1)]
    simp only [K,U,smul_smul]
  have hC : HasDerivAt C (K.comp (C ρ)) ρ := by
    have hh := spatialJacobian_time_deriv hX
      (fun z => -r • conditionalFieldMean F x r ρ z) ρ
      (fun z => terminalBackward_deriv hF x hr hl hT0 hT1 hρ0 hρT z) y
    change HasDerivAt C (fderiv ℝ ((fun z => -r • conditionalFieldMean F x r ρ z) ∘
      (fun z => X (ρ,z))) y) ρ at hh
    rw [fderiv_comp y (hV (X (ρ,y))) (hY y),hK] at hh
    exact hh
  have hB : HasDerivAt B B' ρ := by
    have hh := ((terminalJacobian_smooth hF x hr hl hT0 hT1).differentiable (by simp) (ρ,y)).hasFDerivAt.comp_hasDerivAt ρ
      ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y))
    simpa only [B,B',Function.comp_def,id_eq] using hh
  have he : (fun u => (B u).comp (C u))=ᶠ[nhds ρ] fun _ => ContinuousLinearMap.id ℝ (Point d) := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with u hu
    exact (terminalJacobian_inverse hF x hr hl hT0 hT1 ⟨u,hu.1.le,hu.2.le⟩ y).1
  have hz := (hB.clm_comp hC).unique
    ((hasDerivAt_const ρ (ContinuousLinearMap.id ℝ (Point d))).congr_of_eventuallyEq he)
  have hCB : (C ρ).comp (B ρ)=ContinuousLinearMap.id ℝ (Point d) :=
    (terminalJacobian_inverse hF x hr hl hT0 hT1 ⟨ρ,hρ0.le,hρT.le⟩ y).2
  have hlin := congrArg (fun A : Point d →L[ℝ] Point d => A.comp (B ρ)) hz
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_assoc,hCB,
    ContinuousLinearMap.comp_id,ContinuousLinearMap.zero_comp] at hlin
  have hB' : B'=(r*ρ) • (B ρ).comp U := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun A : Point d →L[ℝ] Point d => A v) (eq_neg_of_add_eq_zero_left hlin)
    simpa only [K,neg_apply,ContinuousLinearMap.comp_apply,smul_apply,
      map_smul,map_neg,neg_mul,neg_smul,neg_neg] using hv
  exact hB' ▸ hB
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam

theorem terminalJacobian_deriv_closed (ρ : Icc (0:ℝ) T) (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0.le hT1 (u,y))
      ((r*(ρ:ℝ)) • steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) ρ := by
  let B := terminalJacobian hF x hr hl hT0.le hT1
  let G := fun u => fderiv ℝ B (u,y) (1,0)
  let H := fun u => (r*u) • steinIntegrand hF x hr hl hT0.le hT1 (u,y)
  have hB : ContDiff ℝ (⊤:ℕ∞) B := terminalJacobian_smooth hF x hr hl hT0.le hT1
  have hBs : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hG : Continuous G :=
    ((hBs.continuous.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hH : Continuous H :=
    (continuous_const.mul continuous_id).smul
      ((steinIntegrand_smooth hF x hr hlam hl hT0.le hT1).continuous.comp (continuous_id.prodMk continuous_const))
  have hD (u : ℝ) : HasDerivAt (fun t => B (t,y)) (G u) u := by
    have hh := (hB.differentiable (by simp) (u,y)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))
    simpa only [G,Function.comp_def,id_eq] using hh
  have he : EqOn G H (Ioo 0 T) := by
    intro u hu
    have hd := (hD u).unique (terminalJacobian_deriv hF x hr hlam hl hT0.le hT1 hu.1 hu.2 y)
    simpa only [B,H,steinIntegrand,smoothTimeClip_eq hT0.le hT1 ⟨hu.1.le,hu.2.le⟩] using hd
  have hz : G ρ=H ρ := he.closure hG hH (by rw [closure_Ioo hT0.ne]; exact ρ.2)
  have hh := hD (ρ:ℝ)
  rw [hz] at hh
  simpa only [B,H] using hh

lemma terminalJacobian_initial_deriv (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0.le hT1 (u,y)) 0 0 := by
  have hh := terminalJacobian_deriv_closed hF x hr hlam hl hT0 hT1 ⟨0,le_rfl,hT0.le⟩ y
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [mul_zero,smul_apply,zero_smul,zero_apply]

lemma terminalJacobian_action_initial_deriv (y v : Point d) :
    HasDerivAt (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v) 0 0 := by
  have hh := ((terminalJacobian_initial_deriv hF x hr hlam hl hT0 hT1 y).sub
    (hasDerivAt_const 0 (ContinuousLinearMap.id ℝ (Point d)))).clm_apply (hasDerivAt_const 0 v)
  simpa only [Pi.sub_apply,sub_zero,zero_apply,map_zero,add_zero] using hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam

theorem terminalJacobian_action_deriv (ρ : Icc (0:ℝ) T) (y v : Point d) :
    HasDerivAt (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v)
      ((r*(ρ:ℝ)) • (steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) v) ρ := by
  have hh := ((terminalJacobian_deriv_closed hF x hr hlam hl hT0 hT1 ρ y).sub
    (hasDerivAt_const (ρ:ℝ) (ContinuousLinearMap.id ℝ (Point d)))).clm_apply
      (hasDerivAt_const (ρ:ℝ) v)
  simpa only [Pi.sub_apply,sub_zero,smul_apply,map_zero,add_zero] using hh

theorem terminalJacobian_action_quotient (ρ : Ioc (0:ℝ) T) (y v : Point d) :
    (ρ:ℝ)⁻¹ • deriv (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v) ρ =
      r • (steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) v := by
  rw [(terminalJacobian_action_deriv hF x hr hlam hl hT0 hT1
    ⟨(ρ:ℝ),ρ.2.1.le,ρ.2.2⟩ y v).deriv,smul_smul]
  congr 1
  have hρ : (ρ:ℝ)≠0 := ne_of_gt ρ.2.1
  field_simp

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayMatrix
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy

lemma matrixArray_arrayMatrix {d : ℕ} (a : (Unit ⊕ Unit → Fin d) → ℝ) :
    matrixArray d (arrayMatrix a) = a := by
  funext c
  simp only [matrixArray_apply,arrayMatrix,sum_apply,
    smul_apply,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,inner_sum,innerSL_apply_apply]
  simp only [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  congr 1
  funext s
  cases s with
  | inl u => cases u; rfl
  | inr u => cases u; rfl

lemma matrixArray_injective (d : ℕ) : Function.Injective (matrixArray d) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  change (A (EuclideanSpace.basisFun (Fin d) ℝ j)).ofLp i =
    (B (EuclideanSpace.basisFun (Fin d) ℝ j)).ofLp i
  have hh := congrFun h (Sum.elim (fun _ => i) (fun _ => j))
  simpa only [matrixArray_apply,Sum.elim_inl,Sum.elim_inr,
    EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,map_one,one_mul] using hh

lemma arrayMatrix_add {d : ℕ} (a b : (Unit ⊕ Unit → Fin d) → ℝ) :
    arrayMatrix (a+b)=arrayMatrix a+arrayMatrix b := by
  apply matrixArray_injective d
  simp only [matrixArray_arrayMatrix,map_add]

lemma arrayMatrix_smul {d : ℕ} (c : ℝ) (a : (Unit ⊕ Unit → Fin d) → ℝ) :
    arrayMatrix (c • a)=c • arrayMatrix a := by
  apply matrixArray_injective d
  simp only [matrixArray_arrayMatrix,map_smul]
end TensorEnergy

namespace TensorSum

lemma matrixEval_add {d : ℕ} (A B : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.add B).matrixEval F x r L p=A.matrixEval F x r L p+B.matrixEval F x r L p := by
  simp only [matrixEval,add_eval]
  exact TensorEnergy.arrayMatrix_add _ _

lemma matrixEval_scale {d : ℕ} (A : TensorSum (Unit ⊕ Unit)) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.scale n P).matrixEval F x r L p=
      ((r*L)^n*P.eval p.1) • A.matrixEval F x r L p := by
  simp only [matrixEval,scale_eval]
  exact TensorEnergy.arrayMatrix_smul _ _

lemma matrixEval_comp {d : ℕ} (A B : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) :
    (A.matrixComp B).matrixEval F x r L p=
      (A.matrixEval F x r L p).comp (B.matrixEval F x r L p) := by
  apply TensorEnergy.matrixArray_injective d
  funext c
  rw [matrixEval,TensorEnergy.matrixArray_arrayMatrix]
  rw [TensorEnergy.matrixArray_comp]
  simp only [matrixComp,contract_eval,relabel_eval,matrixEval,
    TensorEnergy.matrixArray_arrayMatrix]
  rfl

lemma matrixEval_smoothAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : -1<ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (y : Point d) :
    ContDiffAt ℝ (⊤:ℕ∞) (A.matrixEval F x r ((lam:ℝ)*r)) (ρ,y) := by
  unfold matrixEval TensorEnergy.arrayMatrix
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (A.timeSmooth hF x hr hlam hl _ (ρ,y) h0 h1).smul contDiffAt_const

lemma HasMaterial.matrixEval_path {A D : TensorSum (Unit ⊕ Unit)} (hA : A.HasMaterial D)
    {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam) (x : Point d)
    {r T ρ : ℝ} (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hT0 : 0≤T) (hT1 : T<1) (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => A.matrixEval F x r ((lam:ℝ)*r)
      (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y)))
      (D.matrixEval F x r ((lam:ℝ)*r)
        (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) ρ := by
  unfold matrixEval TensorEnergy.arrayMatrix
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hS := (A.timeSmooth hF x hr hlam hl
    (Sum.elim (fun _ => i) (fun _ => j))
    (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) (by dsimp; linarith)
    (hT.trans hT1)).differentiableAt (by simp)
  have hd := hS.hasFDerivAt.comp_hasDerivAt ρ ((hasDerivAt_id ρ).prodMk
    (terminalBackward_deriv hF x hr hl hT0 hT1 h0 hT y))
  rw [joint_material_direction F x r hS,hA hF x hr hlam hl h0.le (hT.trans hT1)] at hd
  exact hd.smul_const (coordinateRankOne d i j)

lemma firstMatrix_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    firstMatrix.matrixEval F x r L p=L⁻¹ • conditionalFirstJet F x r L p := by
  apply TensorEnergy.matrixArray_injective d
  funext c
  rw [matrixEval,TensorEnergy.matrixArray_arrayMatrix,map_smul]
  simp only [firstMatrix,relabel_eval,pure_eval,TensorAtom.jetList_eval,
    Equiv.sumComm_apply,Function.comp_apply,Sum.swap_inl,Sum.swap_inr,Pi.smul_apply,
    smul_eq_mul]
  rw [matrixArray_firstJet]
  rfl
end TensorSum

namespace TensorSum

lemma material_spec {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    A.HasMaterial (A.material hw) := (Classical.choose_spec (A.hasMaterial hw)).2

lemma terminalQ_zero_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    (terminalQ 0).val.matrixEval F x r L p = (p.1*L⁻¹) • conditionalFirstJet F x r L p := by
  rw [terminalQ,matrixEval_scale,firstMatrix_eval]
  simp only [pow_zero,one_mul,Polynomial.eval_X,smul_smul]

lemma terminalQ_succ_eval {d : ℕ} (n : ℕ) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) :
    (terminalQ (n+1)).val.matrixEval F x r L p =
      ((r*L)*p.1) • ((firstMatrix.matrixEval F x r L p).comp
        ((terminalQ n).val.matrixEval F x r L p)) +
      ((terminalQ n).val.material (terminalQ n).property).matrixEval F x r L p := by
  conv_lhs => unfold terminalQ
  rw [matrixEval_add,matrixEval_scale,matrixEval_comp]
  simp only [pow_one,Polynomial.eval_X]
end TensorSum

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam

lemma terminalJacobian_first_Q {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y))
      ((r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ 0).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  have hL : (lam:ℝ)*r≠0 := mul_ne_zero (ne_of_gt hlam) hr.ne'
  convert terminalJacobian_deriv hF x hr hlam hl hT0 hT1 h0 hT y using 1
  all_goals try with_reducible_and_instances rfl
  rw [TensorSum.terminalQ_zero_eval,ContinuousLinearMap.comp_smul,smul_smul]
  congr 1
  field_simp [ne_of_gt (show (0:ℝ)<lam from hlam),hr.ne']

lemma terminalJacobian_Q_deriv (n : ℕ) {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T) (y : Point d) :
    HasDerivAt (fun t => (r*((lam:ℝ)*r)) •
      (terminalJacobian hF x hr hl hT0 hT1 (t,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))))
      ((r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ (n+1)).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  let Q := (TensorSum.terminalQ n).val
  have hD := TensorSum.HasMaterial.matrixEval_path (Q.material_spec (TensorSum.terminalQ n).property)
    hF x hr hlam hl hT0 hT1 h0 hT y
  have hB := terminalJacobian_deriv hF x hr hlam hl hT0 hT1 h0 hT y
  have hh := (hB.clm_comp hD).const_smul (r*((lam:ℝ)*r))
  convert hh using 1 <;> first | rfl | skip
  rw [TensorSum.terminalQ_succ_eval,TensorSum.firstMatrix_eval,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_assoc,smul_smul]
  congr 2
  have hL : (lam:ℝ)*r≠0 := mul_ne_zero (ne_of_gt hlam) hr.ne'
  congr 1
  field_simp [ne_of_gt (show (0:ℝ)<lam from hlam),hr.ne']

theorem terminalJacobian_iteratedDeriv_Q (n : ℕ) {ρ : ℝ} (h0 : 0<ρ) (hT : ρ<T)
    (y : Point d) :
    iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) ρ =
      (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) := by
  induction n generalizing ρ with
  | zero =>
    rw [zero_add,iteratedDeriv_one]
    exact (terminalJacobian_first_Q hF x hr hlam hl hT0 hT1 h0 hT y).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) =ᶠ[nhds ρ]
        (fun t => (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (t,y)).comp
          ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
            (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y)))) := by
      filter_upwards [Ioo_mem_nhds h0 hT] with t ht
      exact ih ht.1 ht.2
    rw [he.deriv_eq]
    exact (terminalJacobian_Q_deriv hF x hr hlam hl hT0 hT1 n h0 hT y).deriv

theorem terminalJacobian_iteratedDeriv_Q_closed (hTpos : 0<T) (n : ℕ)
    (ρ : Icc (0:ℝ) T) (y : Point d) :
    iteratedDeriv (n+1) (fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)) ρ =
      (r*((lam:ℝ)*r)) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) := by
  let B := fun t => terminalJacobian hF x hr hl hT0 hT1 (t,y)
  let X := fun t => terminalBackward hF x hr.le hl hT0 hT1 (t,y)
  let H := fun t => (r*((lam:ℝ)*r)) • (B t).comp
    ((TensorSum.terminalQ n).val.matrixEval F x r ((lam:ℝ)*r) (t,X t))
  have hB : ContDiff ℝ (⊤:ℕ∞) B :=
    (terminalJacobian_smooth hF x hr hl hT0 hT1).comp (contDiff_id.prodMk contDiff_const)
  have hX : Continuous X :=
    (terminalBackward_smooth hF x hr.le hl hT0 hT1).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hH : ContinuousOn H (Icc 0 T) := by
    intro t ht
    have hq := TensorSum.matrixEval_smoothAt hF x hr hlam hl
      (by linarith [ht.1] : -1<t) (ht.2.trans_lt hT1) (TensorSum.terminalQ n).val (X t)
    have hs : ContinuousAt (fun _ : ℝ => r*((lam:ℝ)*r)) t := continuousAt_const
    exact (hs.smul (hB.continuous.continuousAt.clm_comp
      (hq.continuousAt.comp (x:=t) (f:=fun u : ℝ => (u,X u))
        (continuousAt_id.prodMk hX.continuousAt)))).continuousWithinAt
  have hD : Continuous (iteratedDeriv (n+1) B) :=
    hB.continuous_iteratedDeriv (n+1) (by exact_mod_cast (le_top : ((n+1):ℕ∞)≤⊤))
  have hc : IsClosed {t | t∈Icc (0:ℝ) T ∧ iteratedDeriv (n+1) B t=H t} :=
    isClosed_Icc.isClosed_eq hD.continuousOn hH
  have hs : Ioo (0:ℝ) T ⊆ {t | t∈Icc (0:ℝ) T ∧ iteratedDeriv (n+1) B t=H t} := by
    intro t ht
    exact ⟨⟨ht.1.le,ht.2.le⟩,terminalJacobian_iteratedDeriv_Q hF x hr hlam hl hT0 hT1 n ht.1 ht.2 y⟩
  have hh := closure_minimal hs hc
  rw [closure_Ioo hTpos.ne] at hh
  exact (hh ρ.2).2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy
lemma matrixArray_mulVec {d : ℕ} (A : Point d →L[ℝ] Point d) (v : Point d) :
    (fun i => ∑j,matrixArray d A (Sum.elim (fun _ => i) (fun _ => j))*v.ofLp j) =
      (A v).ofLp := by
  funext i
  have hv : ∑j,v.ofLp j • EuclideanSpace.basisFun (Fin d) ℝ j=v := by
    simpa only [OrthonormalBasis.repr_apply_apply,EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left,map_one,one_mul] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hh := congrArg (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (A z)) hv
  simpa only [map_sum,map_smul,inner_sum,real_inner_smul_right,
    matrixArray_apply,Sum.elim_inl,Sum.elim_inr,EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left,map_one,one_mul,mul_comm,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul] using hh

lemma AllSplitBound.matrixArray_norm_le {d : ℕ} {A : Point d →L[ℝ] Point d}
    {M : ℝ} (h : AllSplitBound (matrixArray d A) M) (hM : 0≤M) : ‖A‖≤M := by
  have hb := (h Unit Unit (Equiv.sumComm Unit Unit)).reindex
    (Equiv.funUnique Unit (Fin d)).symm (Equiv.funUnique Unit (Fin d)).symm
  change Bound (fun i j => matrixArray d A (Sum.elim (fun _ => i) (fun _ => j))) (M^2) at hb
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg v))).mp
  have hv := hb v.ofLp
  have he (i : Fin d) := congrFun (matrixArray_mulVec A v) i
  dsimp only at he
  simp_rw [he] at hv
  simpa only [←EuclideanSpace.real_norm_sq_eq,mul_pow] using hv

lemma AllSplitBound.of_spatialTensor_zero {d : ℕ} {S : Type} [Fintype S]
    (f : (S → Fin d) → Point d → ℝ) (y : Point d) {M : ℝ}
    (h : AllSplitBound (spatialTensor f (List.finRange 0) y) M) :
    AllSplitBound (fun c => f c y) M := by
  let e : Fin 0 ⊕ S ≃ S :=
    ⟨Sum.elim Fin.elim0 id,Sum.inr,by rintro (a|a); exact Fin.elim0 a; rfl,by intro a; rfl⟩
  have hh := h.reindex e
  change AllSplitBound (fun c => f (fun s => c s) y) M at hh
  exact hh

end TensorEnergy
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

namespace TensorSum
lemma matrixEval_norm_le {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (y : Point d) :
    ‖A.matrixEval F x r ((lam:ℝ)*r) (ρ,y)‖≤A.spatialBound F x r ρ ((lam:ℝ)*r) 0 y := by
  have hh := (A.spatialBound_allSplit hF x hr hlam hl h0 h1 0 y).of_spatialTensor_zero
    (A.slice F x r ρ ((lam:ℝ)*r)) y
  apply TensorEnergy.AllSplitBound.matrixArray_norm_le _ (A.spatialBound_nonneg _ _ _ _ _ _ _)
  simpa only [matrixEval,TensorEnergy.matrixArray_arrayMatrix,slice] using hh
end TensorSum

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

lemma terminalBackward_measurePreserving (t : Icc (0:ℝ) T) :
    MeasurePreserving (fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y))
      (interpolationLaw F x r T) (interpolationLaw F x r t) := by
  have he : (fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y))=
      probabilityTransport hF x hr.le hl hT0.le hT1 ⟨T,hT0.le,le_rfl⟩ t :=
    funext (terminalBackward_eq hF x hr.le hl hT0.le hT1 t)
  rw [he]
  exact ⟨(probabilityTransport_continuous hF x hr.le hl hT0.le hT1 _ _).measurable,
    probabilityTransport_pushforward hF x hr.le hl hT0.le hT1 _ _⟩

include hlam in
lemma terminalJacobian_iteratedDeriv_norm_le (n : ℕ) (t : Icc (0:ℝ) T) (y : Point d) :
    ‖iteratedDeriv (n+1) (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t‖≤
      (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
        (TensorSum.terminalQ n).val.spatialBound F x r t ((lam:ℝ)*r) 0
          (terminalBackward hF x hr.le hl hT0.le hT1 (t,y)) := by
  rw [terminalJacobian_iteratedDeriv_Q_closed hF x hr hlam hl hT0.le hT1 hT0,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ r*((lam:ℝ)*r))]
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)).trans
  have hb := mul_le_mul (terminalJacobian_norm_le hF x hr hl hT0.le hT1 t y)
    (TensorSum.matrixEval_norm_le hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1)
      (TensorSum.terminalQ n).val (terminalBackward hF x hr.le hl hT0.le hT1 (t,y)))
    (norm_nonneg _) (Real.exp_pos _).le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
    (show 0 ≤ r*((lam:ℝ)*r) by positivity)

include hlam in

theorem terminalJacobian_iteratedDeriv_eLpNorm (hd : 1≤d) (n : ℕ)
    (t : Icc (0:ℝ) T) {p : ℝ≥0∞} (hp : 1≤p) (hpf : p≠⊤) :
    eLpNorm (fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t) p
      (interpolationLaw F x r T)≤
      ENNReal.ofReal (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
        ((TensorSum.terminalQ n).val.momentBudget d 0 p)*
        ENNReal.ofReal ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n) := by
  let A := (TensorSum.terminalQ n).val
  let g := fun y => terminalBackward hF x hr.le hl hT0.le hT1 (t,y)
  let V := A.spatialBound F x r t ((lam:ℝ)*r) 0
  let c := r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4)
  have hV : AEStronglyMeasurable V (interpolationLaw F x r t) := (A.spatialBound_measurable hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) 0).aestronglyMeasurable
  have hDerivative : Continuous (fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t) := by
    simp_rw [terminalJacobian_iteratedDeriv_Q_closed hF x hr hlam hl hT0.le hT1 hT0]
    have hJacobian : Continuous (fun point : Point d =>
        terminalJacobian hF x hr hl hT0.le hT1 ((t:ℝ),point)) :=
      (terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_id)
    have hBackward : Continuous g :=
      (terminalBackward_smooth hF x hr.le hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_id)
    apply continuous_iff_continuousAt.mpr
    intro point
    have hMatrix := TensorSum.matrixEval_smoothAt hF x hr hlam hl
      (by linarith [t.2.1] : -1<(t:ℝ)) (t.2.2.trans_lt hT1)
      (TensorSum.terminalQ n).val (g point)
    have hScalar : ContinuousAt (fun _ : Point d => r*((lam:ℝ)*r)) point :=
      continuousAt_const
    exact hScalar.smul (hJacobian.continuousAt.clm_comp
      (hMatrix.continuousAt.comp (x:=point) (f:=fun value : Point d => ((t:ℝ),g value))
        (continuousAt_const.prodMk hBackward.continuousAt)))
  have hb := eLpNorm_mono_real (μ:=interpolationLaw F x r T) (p:=p)
    (terminalJacobian_iteratedDeriv_norm_le hF x hr hlam hl hT0 hT1 n t)
  have he : (fun y => c*V (g y))=c • (V ∘ g) := rfl
  change _ ≤ eLpNorm (fun y => c*V (g y)) p _ at hb
  rw [he,eLpNorm_const_smul,
    eLpNorm_comp_measurePreserving hV (terminalBackward_measurePreserving hF x hr hl hT0 hT1 t),
    Real.enorm_eq_ofReal_abs,abs_of_nonneg (by positivity : 0 ≤ c)] at hb
  apply hb.trans
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  simpa only [Nat.add_zero] using A.spatialBound_Lp hF x hr hlam hl t.2.1
    (t.2.2.trans_lt hT1) hd (TensorSum.terminalQ n).property 0 hp hpf
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Jet
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped NNReal ENNReal

namespace TimeJet
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth {f : ℝ × X → E} (hf : ContDiff ℝ (⊤:ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (⊤:ℕ∞) (jet f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma hasDerivAt (f : ℝ × X → E) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (n : ℕ) (t : ℝ) (y : X) :
    HasDerivAt (fun s => jet f n (s,y)) (jet f (n+1) (t,y)) t := by
  exact (((smooth hf n).differentiable (by simp)) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))

lemma eq_iteratedDeriv (f : ℝ × X → E) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (n : ℕ) (t : ℝ) (y : X) :
    jet f n (t,y)=iteratedDeriv n (fun s => f (s,y)) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,←funext (fun t => ih t)]
    exact (hasDerivAt f hf n t y).deriv.symm
end TimeJet

namespace RMSIntegral
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω}

lemma integral_norm_sq_eq_eLpNorm (f : Ω → E) (hf : MemLp f 2 μ) :
    (∫x,‖f x‖^2 ∂μ)=(eLpNorm f 2 μ).toReal^2 := by
  have hh := MemLp.eLpNorm_eq_integral_rpow_norm (f:=f) (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤) hf
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
  rw [show (2:ℝ)⁻¹=1/2 by norm_num,←Real.sqrt_eq_rpow] at hh
  rw [hh,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt]
  exact integral_nonneg (fun _ => sq_nonneg _)

lemma integral_norm_sq_le_of_eLpNorm {f : Ω → E}
    (_hm : AEStronglyMeasurable f μ) {B : ℝ≥0∞} (hB : B≠⊤)
    (hb : eLpNorm f 2 μ≤B) :
    Integrable (fun x => ‖f x‖^2) μ ∧ (∫x,‖f x‖^2 ∂μ)≤B.toReal^2 := by
  have hf : MemLp f 2 μ := ⟨_hm, lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hB)⟩
  refine ⟨hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0),?_⟩
  rw [integral_norm_sq_eq_eLpNorm f hf]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hB hb) 2
end RMSIntegral

lemma gaussian_operator_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [SFinite μ] {d : ℕ} (A : Ω → Point d →L[ℝ] Point d)
    (hA : Measurable A) (hi : Integrable (fun y => ‖A y‖^2) μ) {B : ℝ}
    (hB : (∫y,‖A y‖^2 ∂μ)≤B) :
    Integrable (fun p : Ω × Point d => ‖A p.1 p.2‖^2) (μ.prod (ProbabilityTheory.stdGaussian (Point d))) ∧
      (∫p : Ω × Point d,‖A p.1 p.2‖^2 ∂(μ.prod (ProbabilityTheory.stdGaussian (Point d))))≤B*d := by
  have hg : Integrable (fun z : Point d => ‖z‖^2) (ProbabilityTheory.stdGaussian (Point d)) := by
    simpa only [id_eq] using
      (ProbabilityTheory.IsGaussian.memLp_two_id (μ:=ProbabilityTheory.stdGaussian (Point d))).integrable_norm_pow
        (by norm_num : (2:ℕ)≠0)
  have hiB := hi.mul_prod hg
  have hb (p : Ω × Point d) : ‖A p.1 p.2‖^2≤‖A p.1‖^2*‖p.2‖^2 := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
  have hm : Measurable (fun p : Ω × Point d => A p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hA.comp measurable_fst).prodMk measurable_snd)
  have his : Integrable (fun p : Ω × Point d => ‖A p.1 p.2‖^2)
      (μ.prod (ProbabilityTheory.stdGaussian (Point d))) :=
    hiB.mono' (hm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hb p))
  refine ⟨his,?_⟩
  calc
    _ ≤ ∫p : Ω × Point d,‖A p.1‖^2*‖p.2‖^2 ∂(μ.prod (ProbabilityTheory.stdGaussian (Point d))) :=
      integral_mono his hiB hb
    _ = (∫y,‖A y‖^2 ∂μ)*d := by rw [integral_prod_mul (fun y => ‖A y‖^2) (fun z : Point d => ‖z‖^2),stdGaussian_sq_norm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

lemma terminalActionChain_smooth (n : ℕ) :
    ContDiff ℝ (⊤:ℕ∞) (terminalActionChain hF x hr hl hT0 hT1 n) := by
  cases n with
  | zero => exact (((terminalJacobian_smooth hF x hr hl hT0.le hT1).comp
      (contDiff_fst.prodMk contDiff_snd.fst)).sub contDiff_const).clm_apply contDiff_snd.snd
  | succ n => exact ((TimeJet.smooth (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1)).comp
      (contDiff_fst.prodMk contDiff_snd.fst)).clm_apply contDiff_snd.snd

lemma terminalActionChain_hasDerivAt (n : ℕ) (t : ℝ) (p : Point d × Point d) :
    HasDerivAt (fun s => terminalActionChain hF x hr hl hT0 hT1 n (s,p))
      (terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)) t := by
  have hd (n : ℕ) := (TimeJet.hasDerivAt _
    (terminalJacobian_smooth hF x hr hl hT0.le hT1) n t p.1).clm_apply (hasDerivAt_const t p.2)
  cases n with
  | zero =>
    have hh := (hd 0).sub_const p.2
    simpa only [terminalActionChain,TimeJet.jet,Function.comp_apply,
      sub_apply,ContinuousLinearMap.id_apply,map_zero,
      add_zero] using hh
  | succ n =>
    simpa only [terminalActionChain,map_zero,add_zero] using hd (n+1)

include hlam in
lemma terminalActionChain_first_zero (p : Point d × Point d) :
    terminalActionChain hF x hr hl hT0 hT1 1 (0,p)=0 := by
  exact (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 0 0 p).unique
    (terminalJacobian_action_initial_deriv hF x hr hlam hl hT0 hT1 p.1 p.2)

include hlam in

theorem terminalActionChain_sq (hd : 1≤d) (n : ℕ) (t : Icc (0:ℝ) T) :
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let b := (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
      ((TensorSum.terminalQ n).val.momentBudget d 0 2).toReal*
      ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n)
    Integrable (fun p => ‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2) μ ∧
      (∫p,‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2 ∂μ)≤b^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let A := fun y => TimeJet.jet (terminalJacobian hF x hr hl hT0.le hT1) (n+1) (t,y)
  have hAc : Continuous A := (TimeJet.smooth
    (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have he : A=fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t :=
    funext (fun y => TimeJet.eq_iteratedDeriv _
      (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1) t y)
  let B : ℝ≥0∞ := ENNReal.ofReal (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
    (TensorSum.terminalQ n).val.momentBudget d 0 2*
      ENNReal.ofReal ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n)
  have hB : B≠⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (TensorSum.momentBudget_ne_top _ _ _ _))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hb : eLpNorm A 2 (interpolationLaw F x r T)≤B := by
    rw [he]
    exact terminalJacobian_iteratedDeriv_eLpNorm hF x hr hlam hl hT0 hT1 hd n t
      (by norm_num) (by norm_num)
  have hi := RMSIntegral.integral_norm_sq_le_of_eLpNorm hAc.aestronglyMeasurable hB hb
  have hh := gaussian_operator_sq A hAc.measurable hi.1 hi.2
  simpa only [B,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4)),
    ENNReal.toReal_ofReal (by positivity : 0≤(Real.sqrt (1-(t:ℝ)^2))⁻¹),
    terminalActionChain,A] using hh

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_TerminalDerivativeBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma terminalDerivativeBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r : ℝ) :
    0≤terminalDerivativeBudget n d lam r := by
  unfold terminalDerivativeBudget
  have h : 0 ≤ r*((lam:ℝ)*r) := by nlinarith [sq_nonneg r,lam.coe_nonneg]
  positivity

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in
lemma terminalActionChain_sq_uniform (hd : 1≤d) (n : ℕ) {a b : ℝ}
    (ha : 0≤a) (hb : b≤T) (t : ℝ) (ht : t∈Icc a b) :
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let B := (terminalDerivativeBudget n d lam r*
      ((Real.sqrt (1-b^2))⁻¹)^(2*n))^2*d
    Integrable (fun p => ‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2) μ ∧
      (∫p,‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2 ∂μ)≤B := by
  dsimp only
  have hh := terminalActionChain_sq hF x hr hlam hl hT0 hT1 hd n
    ⟨t,ha.trans ht.1,ht.2.trans hb⟩
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (terminalDerivativeBudget_nonneg n d lam r)
  exact pow_le_pow_left₀ (by positivity)
    (inverse_sqrt_time_mono (ha.trans ht.1) ht.2 (hb.trans_lt hT1)) _

lemma terminal_cell_budget_cancel (n : ℕ) {a b h : ℝ} (ha : 0≤a)
    (hab : a≤b) (hb : b<1) (hh : 0≤h) (hc : b-a≤h*(1-b)) :
    ((b-a)^(n+1))^2*((terminalDerivativeBudget (n+1) d lam r*
      ((Real.sqrt (1-b^2))⁻¹)^(2*(n+1)))^2*d)≤
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  have he := cell_singularity_cancel ha hab le_rfl hb hh hc n
  have hA := terminalDerivativeBudget_nonneg (n+1) d lam r
  have hs : 0≤((Real.sqrt (1-b^2))⁻¹)^(2*(n+1)) := by positivity
  have he' : (b-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*(n+1))≤h^(n+1) := by
    simpa only [Nat.mul_add,Nat.mul_one] using he
  calc
    _ = ((terminalDerivativeBudget (n+1) d lam r)*
        ((b-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*(n+1))))^2*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hA (mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hs))
        (mul_le_mul_of_nonneg_left he' hA) 2) (Nat.cast_nonneg _)

include hlam in

theorem terminal_derivative_cell_rms {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → ℝ) (hu : Function.Injective u) (hun : ∀i,u i∈Icc (0:ℝ) 1)
    (n : ℕ) (hn : n+2≤Fintype.card I) (hd : 1≤d)
    {a b h t : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤T)
    (hh : 0≤h) (hc : b-a≤h*(1-b)) (ht : t∈Icc (0:ℝ) 1) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => J 1 (a+(b-a)*t,z)-(b-a)⁻¹ •
      derivativeInterpolation u (fun i => J 0 (a+(b-a)*u i,z)) t
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤2*(1+(∑i,|basisDerivative u i t|)^2)*
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  have hm (s : ℝ) (hs : s∈Icc a (a+(b-a))) :=
    terminalActionChain_sq_uniform hF x hr hlam hl hT0 hT1 hd (n+1) ha hb s
      (by simpa only [add_sub_cancel] using hs)
  have hv := derivative_cell_error_rms u hu hun n hn J
    (fun k => (terminalActionChain_smooth hF x hr hl hT0 hT1 k).continuous)
    (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1)
    (sub_pos.mpr hab) ht (by positivity)
    (fun s hs => (hm s hs).1) (fun s hs => (hm s hs).2)
  refine ⟨hv.1,hv.2.trans ?_⟩
  have he := terminal_cell_budget_cancel (d:=d) (lam:=lam) (r:=r) n ha hab.le
    (hb.trans_lt hT1) hh hc
  convert mul_le_mul_of_nonneg_left he (by positivity : 0≤2*(1+(∑i,|basisDerivative u i t|)^2)) using 1 <;> ring

include hlam in

theorem terminal_hermite_cell_rms {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → ℝ) (hu : Function.Injective u) (i₀ : I) (hu0 : u i₀=0)
    (hun : ∀i,u i∈Icc (0:ℝ) 1) (n : ℕ) (hn : n+1≤Fintype.card I) (hd : 1≤d)
    {b h : ℝ} (hb0 : 0<b) (hb : b≤T) (hh : 0≤h) (hc : b≤h*(1-b)) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => (∫t in (0:ℝ)..1,t⁻¹ • J 1 (b*t,z))-
      ∑i,(zeroHermiteWeight u i₀ i/b) • J 0 (b*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)*
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  have hm (s : ℝ) (hs : s∈Icc (0:ℝ) b) :=
    terminalActionChain_sq_uniform hF x hr hlam hl hT0 hT1 hd (n+1) le_rfl hb s hs
  have hv := zeroHermite_derivative_error_rms u hu i₀ hu0 hun n hn J
    (fun k => (terminalActionChain_smooth hF x hr hl hT0 hT1 k).continuous)
    (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1)
    (terminalActionChain_first_zero hF x hr hlam hl hT0 hT1)
    hb0 (by positivity) (fun s hs => (hm s hs).1) (fun s hs => (hm s hs).2)
  refine ⟨hv.1,hv.2.trans ?_⟩
  have he := terminal_cell_budget_cancel (d:=d) (lam:=lam) (r:=r) n
    (a:=0) le_rfl hb0.le (hb.trans_lt hT1) hh (by simpa only [sub_zero] using hc)
  simp only [sub_zero] at he
  convert mul_le_mul_of_nonneg_left he (by positivity : 0≤2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)) using 1 <;> ring
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_OrdinaryDerivativeWeight
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma ordinaryDerivativeWeight_integrand_continuousOn (u : I → ℝ) (a b : ℝ) (i : I)
    (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun t => (b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_const.mul (continuousOn_id.inv₀
    (fun t ht => ne_of_gt (ha.trans_le ht.1)))).mul
      ((basisDerivative_continuous u i).comp
        ((continuous_id.sub continuous_const).div_const _)).continuousOn

lemma ordinaryDerivativeWeight_integral (u : I → ℝ) (v : I → E) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    (∫t in a..b,t⁻¹ • ((b-a)⁻¹ • derivativeInterpolation u v ((t-a)/(b-a))))=
      ∑i,ordinaryDerivativeWeight u a b i • v i := by
  simp only [derivativeInterpolation,Finset.smul_sum,smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    unfold ordinaryDerivativeWeight
    rw [←intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr
    intro t _
    module
  · intro i _
    have hh := ((ordinaryDerivativeWeight_integrand_continuousOn u a b i ha hab).smul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => v i) (uIcc a b))).intervalIntegrable (μ:=volume)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    congr 1
    ring

omit [CompleteSpace E] in
lemma derivativeInterpolation_joint_continuous {Ω : Type*} [TopologicalSpace Ω]
    (u : I → ℝ) (v : I → Ω → E) (hv : ∀i,Continuous (v i)) :
    Continuous (fun p : ℝ × Ω => derivativeInterpolation u (fun i => v i p.2) p.1) := by
  exact continuous_finsetSum _ (fun i _ =>
    ((basisDerivative_continuous u i).comp continuous_fst).smul ((hv i).comp continuous_snd))

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω] {μ : Measure Ω} [SFinite μ]

lemma ordinaryDerivativeWeight_error_rms (u : I → ℝ) (f g : ℝ × Ω → E)
    (hf : Continuous f) (hg : Continuous g) {a b B : ℝ}
    (ha : 0<a) (hab : a<b) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) 1,Integrable (fun z =>
      ‖g (a+(b-a)*t,z)-(b-a)⁻¹ • derivativeInterpolation u (fun i => f (a+(b-a)*u i,z)) t‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) 1,(∫z,
      ‖g (a+(b-a)*t,z)-(b-a)⁻¹ • derivativeInterpolation u (fun i => f (a+(b-a)*u i,z)) t‖^2 ∂μ)≤B) :
    let err := fun z => (∫t in a..b,t⁻¹ • g (t,z))-
      ∑i,ordinaryDerivativeWeight u a b i • f (a+(b-a)*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤((b-a)/a)^2*B := by
  dsimp only
  let η := volume.restrict (Ioc a b)
  let R := fun p : ℝ × Ω => g p-(b-a)⁻¹ • derivativeInterpolation u
    (fun i => f (a+(b-a)*u i,p.2)) ((p.1-a)/(b-a))
  have hRc : Continuous R := hg.sub
    (((derivativeInterpolation_joint_continuous u (fun i z => f (a+(b-a)*u i,z))
      (fun i => hf.comp (continuous_const.prodMk continuous_id))).comp
        (((continuous_fst.sub continuous_const).div_const _).prodMk continuous_snd)).const_smul _)
  have hrange {t : ℝ} (ht : t∈Ioc a b) : (t-a)/(b-a)∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1.le) (sub_pos.mpr hab).le
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
  have hcoord (t : ℝ) : a+(b-a)*((t-a)/(b-a))=t := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have hri : ∀ᵐ t ∂η,Integrable (fun z => ‖R (t,z)‖^2) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [R,hcoord] using hi _ (hrange ht)
  have hrB : ∀ᵐ t ∂η,(∫z,‖R (t,z)‖^2 ∂μ)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [R,hcoord] using hB _ (hrange ht)
  have hw : AEStronglyMeasurable (fun t : ℝ => t⁻¹) η := measurable_id.inv.aestronglyMeasurable
  have hwb : ∀ᵐ t ∂η,|t⁻¹|≤a⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [abs_of_nonneg (inv_nonneg.mpr (ha.trans ht.1).le)]
    exact inv_anti₀ ha ht.1.le
  have hv := RMSIntegral.weighted_time_seed hRc.aestronglyMeasurable hw hB0 hwb hri hrB
  have hη : η.real univ=b-a := by
    dsimp only [η,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hab.le
  have he (z : Ω) : (∫t in a..b,t⁻¹ • g (t,z))-
      ∑i,ordinaryDerivativeWeight u a b i • f (a+(b-a)*u i,z)=
        ∫t,t⁻¹ • R (t,z) ∂η := by
    rw [←ordinaryDerivativeWeight_integral u _ ha hab.le]
    have hg' : IntervalIntegrable (fun t => t⁻¹ • g (t,z)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab.le]
      exact (continuousOn_id.inv₀ (fun t ht => ne_of_gt (ha.trans_le ht.1))).smul
        (hg.comp (continuous_id.prodMk continuous_const)).continuousOn
    have hp' : IntervalIntegrable (fun t => t⁻¹ • ((b-a)⁻¹ • derivativeInterpolation u
        (fun i => f (a+(b-a)*u i,z)) ((t-a)/(b-a)))) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab.le]
      apply (continuousOn_id.inv₀ (fun t ht => ne_of_gt (ha.trans_le ht.1))).smul
      apply Continuous.continuousOn
      apply Continuous.const_smul
      exact (derivativeInterpolation_joint_continuous u (fun i (_ : Unit) => f (a+(b-a)*u i,z))
        (fun _ => continuous_const)).comp
          (((continuous_id.sub continuous_const).div_const _).prodMk
            (continuous_const : Continuous (fun _ : ℝ => ())))
    rw [←intervalIntegral.integral_sub hg' hp',intervalIntegral.integral_of_le hab.le]
    congr 1
    funext t
    exact (smul_sub _ _ _).symm
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hη]
  ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

lemma probabilityNodes_zero (n : ℕ) : probabilityNodes n 0=0 := by
  simp [probabilityNodes]

lemma logMeshNode_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {j : ℕ} (hj : 0<j) : 0<logMeshNode T h j := by
  simpa only [logMeshNode_zero] using logMeshNode_strictMono hT0 hT1 hh hj

lemma probabilityCellLength_le_h {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (i : Fin (logMeshCount T h)) : probabilityCellLength T h i≤h := by
  have he := logMeshCell_upper hT0 hT1 hh i.val
  have ha := (logMeshNode_mem hT0 hT1 hh i.2.le).1
  dsimp only [probabilityCellLength]
  nlinarith

lemma logMeshFirst_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hs : h≤Real.log 2) : h/4≤logMeshNode T h 1 := by
  simpa only [logMeshNode_zero,zero_add,sub_zero,mul_one] using
    logMeshCell_lower hT0 hT1 hh hL hs 0

lemma probabilityCellLength_ratio {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hs : h≤Real.log 2)
    (i : Fin (logMeshCount T h)) (hi : i.val≠0) :
    probabilityCellLength T h i/logMeshNode T h i.val≤4 := by
  have ha := logMeshFirst_lower hT0 hT1 hh hL hs
  have hm : logMeshNode T h 1≤logMeshNode T h i.val :=
    (logMeshNode_strictMono hT0 hT1 hh).monotone (Nat.one_le_iff_ne_zero.mpr hi)
  have hp := logMeshNode_pos hT0 hT1 hh (Nat.pos_of_ne_zero hi)
  rw [div_le_iff₀ hp]
  have hc := probabilityCellLength_le_h hT0 hT1 hh i
  linarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma regularized_intervalIntegrable_nonneg {f : ℝ → E} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (h0 : f 0=0)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume a b := by
  have hc : Continuous (dslope f 0) := continuousOn_univ.mp
    ((continuousOn_dslope (s:=univ) (by simp)).mpr ⟨hf.continuousOn,hd⟩)
  apply (hc.intervalIntegrable a b).congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  simp only [dslope_of_ne f (ne_of_gt (ha.trans_lt ht.1)),slope_def_module,h0,sub_zero]

lemma regularized_integral_scale (f : ℝ → E) {b : ℝ} (hb : b≠0) :
    (∫t in (0:ℝ)..b,t⁻¹ • f t)=(∫t in (0:ℝ)..1,t⁻¹ • f (b*t)) := by
  have he := intervalIntegral.smul_integral_comp_mul_left (a:=0) (b:=1)
    (fun t => t⁻¹ • f t) b
  simp only [mul_zero,mul_one] at he
  rw [←he,←intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [smul_smul,mul_inv_rev]
  congr 1
  field_simp

end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_cell_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T)
    (c : Fin (logMeshCount T h)) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
    let err := fun z => (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
      ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤32*(1+D^2+H^2)*
        (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
  let A := (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d
  let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
  have hA : 0≤A := by dsimp only [A]; positivity
  have ha := logMeshNode_mem hT0 hT1 hh c.2.le
  have hb := logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)
  have hab := logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self c.val)
  have hc := logMeshCell_upper_right hT0 hT1 hh hs c.val
  by_cases hc0 : c.val=0
  · have hb0 := logMeshNode_pos hT0 hT1 hh (by omega : 0 < c.val+1)
    have hv := terminal_hermite_cell_rms hF x hr hlam hl hT0 hT1
      (probabilityNodes (n+1)) (probabilityNodes_injective (by omega)) 0
      (probabilityNodes_zero _) (probabilityNodes_mem (by omega)) n (by simp) hd
      hb0 hb.2 (by positivity : 0≤2*h) (by simpa only [hc0,logMeshNode_zero,sub_zero] using hc)
    dsimp only at hv
    have hEq (z : Point d × Point d) :
        (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
          ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)=
        (∫t in (0:ℝ)..1,t⁻¹ • J 1 (logMeshNode T h (c.val+1)*t,z))-
          ∑i,(zeroHermiteWeight (probabilityNodes (n+1)) 0 i/logMeshNode T h (c.val+1)) •
            J 0 (logMeshNode T h (c.val+1)*probabilityNodes (n+1) i,z) := by
      simp only [terminalQuadratureWeight,probabilityNodeTime,probabilityCellLength,
        hc0,ite_true,logMeshNode_zero,sub_zero,zero_add]
      rw [regularized_integral_scale _ (ne_of_gt (logMeshNode_pos hT0 hT1 hh (by omega : 0<1)))]
    dsimp only [J] at hEq
    simp_rw [hEq]
    refine ⟨hv.1,hv.2.trans ?_⟩
    have he : 2*(1+H^2)≤32*(1+D^2+H^2) := by nlinarith [sq_nonneg D,sq_nonneg H]
    convert mul_le_mul_of_nonneg_right he hA using 1 <;> ring
  · have ha0 := logMeshNode_pos hT0 hT1 hh (by omega : 0 < c.val)
    have hv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
      terminal_derivative_cell_rms hF x hr hlam hl hT0 hT1
        (probabilityNodes (n+1)) (probabilityNodes_injective (by omega))
        (probabilityNodes_mem (by omega)) n (by simp) hd ha.1 hab hb.2
        (by positivity : 0≤2*h) hc ht
    have hi (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := (hv t ht).1
    have hB (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        (∫z,‖J 1 (logMeshNode T h c.val+probabilityCellLength T h c*t,z)-
          (probabilityCellLength T h c)⁻¹ • derivativeInterpolation (probabilityNodes (n+1))
            (fun i => J 0 (logMeshNode T h c.val+probabilityCellLength T h c*probabilityNodes (n+1) i,z)) t‖^2 ∂μ)
          ≤2*(1+D^2)*A := by
      apply (hv t ht).2.trans
      have hps := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => abs_nonneg
        (basisDerivative (probabilityNodes (n+1)) i t))) (hDu t ht) 2
      have he : 2*(1+(∑i,|basisDerivative (probabilityNodes (n+1)) i t|)^2)≤2*(1+D^2) := by linarith
      convert mul_le_mul_of_nonneg_right he hA using 1 <;> first | rfl | ring
    have he := ordinaryDerivativeWeight_error_rms (μ:=μ) (probabilityNodes (n+1)) (J 0) (J 1)
      (terminalActionChain_smooth hF x hr hl hT0 hT1 0).continuous
      (terminalActionChain_smooth hF x hr hl hT0 hT1 1).continuous
      ha0 hab (by positivity : 0≤2*(1+D^2)*A) hi hB
    dsimp only at he
    simp only [terminalQuadratureWeight,hc0,ite_false,probabilityNodeTime]
    refine ⟨he.1,he.2.trans ?_⟩
    have hr0 : 0≤probabilityCellLength T h c/logMeshNode T h c.val :=
      div_nonneg (probabilityCellLength_pos hT0 hT1 hh c).le ha0.le
    have hr4 := probabilityCellLength_ratio hT0 hT1 hh hL hs c hc0
    have hr16 : (probabilityCellLength T h c/logMeshNode T h c.val)^2≤16 := by
      nlinarith [sq_nonneg (4-probabilityCellLength T h c/logMeshNode T h c.val)]
    calc
      _ ≤ 16*(2*(1+D^2)*A) := mul_le_mul_of_nonneg_right hr16 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg H) hA]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma stronglyMeasurable_parametric_intervalIntegral (f : ℝ × Ω → E)
    (hf : StronglyMeasurable f) (a b : ℝ) :
    StronglyMeasurable (fun z => ∫t in a..b,f (t,z)) := by
  have he : StronglyMeasurable (fun z : Ω × ℝ => f (z.2,z.1)) :=
    hf.comp_measurable measurable_swap
  unfold intervalIntegral
  exact (he.integral_prod_right').sub (he.integral_prod_right')

lemma quadrature_error_sum {N : ℕ} {I : Type*} [Fintype I]
    (a : ℕ → ℝ) (f : ℝ → E) (v : Fin N → I → E) (w : Fin N → I → ℝ)
    (hi : ∀j,j<N → IntervalIntegrable f volume (a j) (a (j+1))) :
    (∫t in a 0..a N,f t)-(∑p : Fin N × I,w p.1 p.2 • v p.1 p.2)=
      ∑j : Fin N,((∫t in a j.val..a (j.val+1),f t)-∑i,w j i • v j i) := by
  rw [Finset.sum_sub_distrib,Fintype.sum_prod_type]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => ∫t in a j..a (j+1),f t)]
  exact (intervalIntegral.sum_integral_adjacent_intervals hi).symm
end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_analytic_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
    let err := fun z => (∫t in (0:ℝ)..T,t⁻¹ • J 1 (t,z))-
      ∑s,terminalQuadratureWeight T h n s • J 0 (probabilityNodeTime T h (n+1) s,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤(logMeshCount T h:ℝ)^2*(32*(1+D^2+H^2)*
        (terminalDerivativeBudget (n+1) d lam r*(2*h)^(n+1))^2*d) := by
  dsimp only
  let J := terminalActionChain hF x hr hl hT0 hT1
  let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
  let e := fun c : Fin (logMeshCount T h) => fun z =>
    (∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),t⁻¹ • J 1 (t,z))-
      ∑i,terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)
  have hc := terminalActionChain_smooth hF x hr hl hT0 hT1
  have hm (c : Fin (logMeshCount T h)) : StronglyMeasurable (e c) := by
    apply StronglyMeasurable.sub
    · refine stronglyMeasurable_parametric_intervalIntegral (fun p => p.1⁻¹ • J 1 p) ?_ _ _
      exact (measurable_fst.inv.smul (hc 1).continuous.measurable).stronglyMeasurable
    · have hcj (i : Fin (n+2)) : Continuous (fun z : Point d × Point d =>
          terminalQuadratureWeight T h n (c,i) • J 0 (probabilityNodeTime T h (n+1) (c,i),z)) := by
        have hscalar : Continuous (fun v : Point d => terminalQuadratureWeight T h n (c,i) • v) := continuous_const_smul _
        convert! hscalar.comp ((hc 0).continuous.comp
          ((continuous_const : Continuous (fun _ : Point d × Point d => probabilityNodeTime T h (n+1) (c,i))).prodMk continuous_id)) using 1
        all_goals try with_reducible_and_instances rfl
      exact (continuous_finsetSum _ (fun i _ => hcj i)).stronglyMeasurable
  have he := weighted_sum_sq (ν:=μ) (fun _ : Fin (logMeshCount T h) => (1:ℝ)) e
    (fun c => (hm c).aestronglyMeasurable)
    (fun c => (terminalQuadrature_cell_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL c).1)
    (fun c => (terminalQuadrature_cell_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL c).2)
  have heq (z : Point d × Point d) :
      (∫t in (0:ℝ)..T,t⁻¹ • J 1 (t,z))-
        ∑s,terminalQuadratureWeight T h n s • J 0 (probabilityNodeTime T h (n+1) s,z)=
      ∑c : Fin (logMeshCount T h),e c z := by
    have ht := quadrature_error_sum (logMeshNode T h) (fun t => t⁻¹ • J 1 (t,z))
      (fun c i => J 0 (probabilityNodeTime T h (n+1) (c,i),z))
      (fun c i => terminalQuadratureWeight T h n (c,i)) (fun j hj =>
        regularized_intervalIntegrable_nonneg
          ((hc 1).continuous.comp (continuous_id.prodMk continuous_const))
          (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 1 0 z).differentiableAt
          (terminalActionChain_first_zero hF x hr hlam hl hT0 hT1 z)
          (logMeshNode_mem hT0 hT1 hh hj.le).1
          (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self j)).le)
    simpa only [logMeshNode_zero,logMeshNode_last hT0 hT1 hh] using ht
  dsimp only [J] at heq
  simp_rw [heq]
  simpa only [one_smul,abs_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using he
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalActionChainQuotient
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in
lemma terminalActionChain_quotient {t : ℝ} (ht : t∈Ioc (0:ℝ) T) (p : Point d × Point d) :
    t⁻¹ • terminalActionChain hF x hr hl hT0 hT1 1 (t,p)=
      r • (steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
  have he := terminalJacobian_action_quotient hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ p.1 p.2
  rw [←(terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 0 t p).deriv]
  exact he

include hlam in

theorem terminalActionChain_integral (p : Point d × Point d) :
    (∫t in (0:ℝ)..T,t⁻¹ • terminalActionChain hF x hr hl hT0 hT1 1 (t,p))=
      r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2 := by
  have hc : Continuous (fun t => steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) :=
    (steinIntegrand_smooth hF x hr hlam hl hT0.le hT1).continuous.comp
      (continuous_id.prodMk continuous_const)
  calc
    _ = ∫t in (0:ℝ)..T,r • (steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
      apply intervalIntegral.integral_congr_ae'
      · exact Filter.Eventually.of_forall (fun _ ht => terminalActionChain_quotient hF x hr hlam hl hT0 hT1 ht p)
      · exact Filter.Eventually.of_forall (fun _ ht => False.elim (not_lt_of_ge (le_trans ht.2 hT0.le) ht.1))
    _ = r • (∫t in (0:ℝ)..T,steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
      rw [intervalIntegral.integral_smul,ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable _ _)]
    _ = _ := by
      rw [centeringKernel,ContinuousLinearMap.adjoint_adjoint,integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hT0.le]
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

lemma logMeshCount_mul_step {T h : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hL : h≤logMeshLength T) :
    (logMeshCount T h:ℝ)*h≤2*logMeshLength T := by
  have he := mul_lt_mul_of_pos_right (logMeshCount_bound hT0 hT1 hh) hh
  have hh0 := ne_of_gt hh
  field_simp at he
  nlinarith

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_kernel_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => (∑s,terminalQuadratureWeight T h n s •
      J 0 (probabilityNodeTime T h (n+1) s,z))-
        r • (centeringKernel hF x hr hl hT0.le hT1 z.1).adjoint z.2
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤kernelAnalyticBudget n d lam r T h D := by
  dsimp only
  have he := terminalQuadrature_analytic_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL
  dsimp only at he
  simp_rw [terminalActionChain_integral hF x hr hlam hl hT0 hT1,norm_sub_rev] at he
  refine ⟨he.1,he.2.trans ?_⟩
  have hN := logMeshCount_mul_step hT0 hT1 hh hL
  have hmul := mul_le_mul_of_nonneg_right hN
    (show 0≤terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n from
      mul_nonneg (mul_nonneg (terminalDerivativeBudget_nonneg _ _ _ _) (by positivity)) (by positivity))
  have hsq := pow_le_pow_left₀
    (show 0≤(logMeshCount T h:ℝ)*h*(terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n) by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.le)
        (by positivity [terminalDerivativeBudget_nonneg (n+1) d lam r])) hmul 2
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq
      (show 0≤32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2) by positivity))
    (Nat.cast_nonneg (α:=ℝ) d)
  convert! hscaled using 1 <;> (try dsimp only [kernelAnalyticBudget]) <;> (try simp only [mul_pow,pow_succ]) <;> first | rfl | ring
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringVelocityPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_full_rms_oai (n : ℕ) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0≤C ∧ 1≤J ∧ 1≤D ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 → h≤logMeshLength T →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let w := terminalQuadratureWeight T h n
      let err := fun p : Point d × Point d =>
        kernelQuadraturePicard F x r T h ψ (n+1) m N (probabilityEndpoint hT0 hT1 hh (n+1)) w p-
          r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        2*((∑s,|w s|)*(∑s,|w s| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) s) h ψ C J k (n+1) m N))+
        2*kernelAnalyticBudget n d lam r T h D := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hN⟩ := kernelQuadraturePicard_numerical_rms (n+1) (by omega)
  obtain ⟨D,hD,hDu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  refine ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hs hL hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm
  dsimp only
  let w := terminalQuadratureWeight T h n
  let ep := probabilityEndpoint hT0 hT1 hh (n+1)
  let f := kernelQuadraturePicard F x r T h ψ (n+1) m N ep w
  let g := fun p : Point d × Point d => ∑s,w s •
    (terminalJacobian hF x hr hl hT0.le hT1 (probabilityNodeTime T h (n+1) s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  let q := fun p : Point d × Point d => r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_const_smul (w i)).comp
      (kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ (n+1) (by omega) m N i ep)
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_const_smul (w i)).comp
      ((((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd)
  have hq : Continuous q := by
    apply (continuous_const_smul r).comp
    exact ((ContinuousLinearMap.adjoint.continuous.comp
      ((centeringKernel_smooth hF x hr hlam hl hT0.le hT1).continuous.comp continuous_fst)).clm_apply continuous_snd)
  have hn := hN hF x hr hlam hl hd hT0 hT1 hh hs hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm w
  have ha := terminalQuadrature_kernel_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL
  exact add_error_sq (μ:=((interpolationLaw F x r T).prod (stdGaussian (Point d))))
    hf.measurable hg.measurable hq.measurable hn.1 ha.1 hn.2 ha.2
end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms_oai := @OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms_oai
