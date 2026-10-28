-- Prove2me | solution 1 for OAI.LogConcaveSampling.exists_centering_stationaryPath
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:43:48.947677+00:00
-- url     : https://prove2.me/submissions/b76f3d2f-e7ed-40ee-b0e9-cd9f95d47a54

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ContinuousFirstOrderReply
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

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.contDiff_gradient {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : ContDiff ℝ 1 (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hV.smooth.fderiv_right (by norm_num))

theorem Admissible.quadratic_bounds {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) :
    ‖x‖ ^ 2 / 2 ≤ V x ∧ V x ≤ ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hV.smooth.differentiable (by norm_num) (t • x)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    change inner ℝ x (gradient V (t • x)) = fderiv ℝ V (t • x) x
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using
      (hasDerivAt_const t x).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg
    (fun t => hV.hessian_bounds (t • x) x)
  dsimp only [f, g] at ht
  rw [zero_smul, one_smul, hV.value_zero, hV.gradient_zero, inner_zero_right, zero_add] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem Admissible.integrable_exp_neg {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Integrable (fun x => Real.exp (-V x)) := by
  apply (integrable_gaussian_envelope d (b := 1 / 2) (by norm_num)).mono'
    ((Real.continuous_exp.comp hV.smooth.continuous.neg).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (hV.quadratic_bounds x).1
    linarith

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianProposalPotential
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

lemma gaussianProposalPotential_eq (d : ℕ) (x : Point d) :
    gaussianProposalPotential d x = ‖x‖^2/2 := by
  simp [gaussianProposalPotential]

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
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CompactGibbsIbp
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
open MeasureTheory Function
open scoped RealInnerProductSpace

lemma compact_gibbs_ibp {d : ℕ} {H g : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,directional v g z ∂gibbs H)=
      ∫z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have he : ContDiff ℝ 1 (fun z => Real.exp (-H z)) := hH.neg.exp
  have hdg : Continuous (directional v g) := (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdgc : HasCompactSupport (directional v g) := hgc.fderiv_apply ℝ v
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (((he.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous
      |>.integrable_of_hasCompactSupport hgc.mul_left)
    ((he.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left)
    ((he.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    (fun z _ => he.differentiable (by norm_num) z)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simpa only [smul_eq_mul,directional] using congrArg (fun a => (∫z,Real.exp (-H z))⁻¹*a) hh

lemma adjointCoordinate_compact_pairing {d : ℕ} {H f g : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,adjointCoordinate H v f z*g z ∂gibbs H)=
      ∫z,f z*directional v g z ∂gibbs H := by
  have hdf : Continuous (directional v f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (directional v g) := (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdH : Continuous (directional v H) := (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  have h1 : Integrable (fun z => directional v f z*g z) (gibbs H) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h2 : Integrable (fun z => f z*directional v g z) (gibbs H) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have h3 : Integrable (fun z => (directional v H z*f z)*g z) (gibbs H) :=
    ((hdH.mul hf.continuous).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hh := compact_gibbs_ibp hH hi (hf.mul hg) hgc.mul_left v
  rw [directional_mul (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)),integral_add h1 h2] at hh
  simp only [←directional_gradient,mul_assoc] at h3 ⊢ hh
  change (∫z,(-directional v f z+directional v H z*f z)*g z ∂gibbs H)=_
  simp_rw [add_mul,neg_mul,mul_assoc]
  rw [integral_add (f:=fun z => -(directional v f z*g z)) h1.neg h3,integral_neg]
  linarith
lemma tensorAdjoint_compact_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    {H g : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hV : ∀i,ContDiff ℝ 1 (V i)) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (b : ι → Point d) :
    (∫z,tensorAdjoint H b V z*g z ∂gibbs H)=
      ∫z,∑i,V i z*directional (b i) g z ∂gibbs H := by
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  have h1 (i : ι) : Integrable (fun z => adjointCoordinate H (b i) (V i) z*g z) (gibbs H) :=
    ((((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
      (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)
      |>.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h2 (i : ι) : Integrable (fun z => V i z*directional (b i) g z) (gibbs H) :=
    ((hV i).continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ (b i)).mul_left
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => h1 i),integral_finsetSum Finset.univ (fun i _ => h2 i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_compact_pairing hH hi (hV i) hg hgc (b i))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory EulerDensity
open scoped RealInnerProductSpace ENNReal

lemma standardGaussian_eq_gibbs (d : ℕ) :
    stdGaussian (Point d)=gibbs (gaussianProposalPotential d) := by
  have he : (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2)))=
      gibbsDensity (gaussianProposalPotential d) := by
    funext z
    simp only [gibbsDensity,gaussianProposalPotential_eq,neg_div]
  have hd := standard_density d
  rw [he] at hd
  have hp := congrArg (fun μ : Measure (Point d) => μ Set.univ) hd
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hp
  change (1:ℝ≥0∞)=gaussianCoefficient d*partition (gaussianProposalPotential d) at hp
  rw [hd,ENNReal.eq_inv_of_mul_eq_one_left hp.symm]
  rfl

lemma compact_gaussian_ibp {d : ℕ} {g : Point d → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,fderiv ℝ g z v ∂stdGaussian (Point d))=
      ∫z,inner ℝ z v*g z ∂stdGaussian (Point d) := by
  rw [standardGaussian_eq_gibbs]
  have hH := (gaussianProposalPotential_admissible d).smooth.of_le (by norm_num : (1:WithTop ℕ∞)≤2)
  simpa only [directional,gaussianProposalPotential_gradient,id_eq] using
    compact_gibbs_ibp hH (gaussianProposalPotential_admissible d).integrable_exp_neg hg hgc v
end LogConcaveSampling

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

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_DerivSetIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CompactExpectation
open Set MeasureTheory Filter Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_setIntegral {f : ℝ × E → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set E} (hK : IsCompact K) (t : ℝ) :
    HasDerivAt (fun t => ∫y in K,f (t,y) ∂μ)
      (∫y in K,fderiv ℝ f (t,y) (1,0) ∂μ) t := by
  let D := fun p : ℝ × E => fderiv ℝ f p (1,0)
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod hK).exists_bound_of_continuousOn hD.continuousOn
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ.restrict K)
    (F:=fun t y => f (t,y)) (F':=fun t y => D (t,y))
    (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s => (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with y hy s hs
      exact hC (s,y) ⟨Metric.ball_subset_closedBall hs,hy⟩)
    (integrableOn_const (μ:=μ) hK.measure_ne_top)
    (by
      filter_upwards [] with y s _hs
      exact (hf.differentiable (by norm_num) (s,y)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s y)))
  exact hh.2

theorem compact_test_hasDerivAt {A : ℝ × E → ℝ} (hA : ContDiff ℝ 1 A)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun t => ∫y,A (t,y)*φ y ∂μ)
      (∫y,(fderiv ℝ A (t,y) (1,0))*φ y ∂μ) t := by
  let B := fun p : ℝ × E => A p*φ p.2
  have hB : ContDiff ℝ 1 B := hA.mul (hφ.comp contDiff_snd)
  have hD (s : ℝ) (y : E) : fderiv ℝ B (s,y) (1,0)=fderiv ℝ A (s,y) (1,0)*φ y := by
    have hd := (hA.differentiable (by norm_num) (s,y)).hasFDerivAt.mul
      ((hφ.differentiable (by norm_num) y).hasFDerivAt.comp (s,y)
        (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
    change HasFDerivAt B _ _ at hd
    rw [hd.fderiv]
    simp [ContinuousLinearMap.snd,mul_comm]
  have he (s : ℝ) : (∫y in tsupport φ,B (s,y) ∂μ)=∫y,A (s,y)*φ y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [B,image_eq_zero_of_notMem_tsupport hy,mul_zero]
  have hg : (∫y in tsupport φ,fderiv ℝ B (t,y) (1,0) ∂μ)=
      ∫y,fderiv ℝ A (t,y) (1,0)*φ y ∂μ := by
    simp only [hD]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  simpa only [he,hg] using hasDerivAt_setIntegral (μ:=μ) hB hφc t
end LogConcaveSampling.CompactExpectation

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_GradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GradientIntegral
open MeasureTheory Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gradient_bound {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∃C : ℝ,0≤C ∧ ∀y,‖fderiv ℝ φ y‖≤C := by
  obtain ⟨C,hC⟩ := (hφc.fderiv ℝ).exists_bound_of_continuousOn
    (hφ.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C 0,le_max_right _ _,fun y => ?_⟩
  by_cases hy : y∈tsupport (fderiv ℝ φ)
  · exact (hC y hy).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy,norm_zero]
    exact le_max_right _ _

lemma continuous_gradient_expectation {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X) (u : E) :
    Continuous (fun t => ∫y,fderiv ℝ φ y (X (t,y) u) ∂μ) := by
  have hc : Continuous (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (hX.clm_apply continuous_const)
  have he (t : ℝ) : (∫y in tsupport φ,fderiv ℝ φ y (X (t,y) u) ∂μ)=
      ∫y,fderiv ℝ φ y (X (t,y) u) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [(HasFDerivAt.of_notMem_tsupport ℝ hy).fderiv]
    rfl
  simpa only [he] using
    (continuous_parametric_integral_of_continuous (μ:=μ) (f:=fun t y => fderiv ℝ φ y (X (t,y) u)) hc hφc)

lemma gradient_time_space_integrable {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X)
    {T C : ℝ} (hC : 0≤C) (hbound : ∀t∈Icc (0:ℝ) T,∀y,‖X (t,y)‖≤C) (u : E) :
    Integrable (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) ((volume.restrict (Icc 0 T)).prod μ) := by
  obtain ⟨D,_,hDb⟩ := gradient_bound hφ hφc
  have hc : Continuous (fun p : ℝ × E => fderiv ℝ φ p.2 (X p u)) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (hX.clm_apply continuous_const)
  apply (integrable_const (D*C*‖u‖)).mono' hc.aestronglyMeasurable
  have ha : ∀ᵐ p ∂((volume.restrict (Icc (0:ℝ) T)).prod μ),p.1∈Icc (0:ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ha] with p hp
  calc
    ‖fderiv ℝ φ p.2 (X p u)‖≤‖fderiv ℝ φ p.2‖*‖X p u‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖fderiv ℝ φ p.2‖*(C*‖u‖) := mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbound p.1 hp p.2) (norm_nonneg _)))
      (norm_nonneg _)
    _≤D*(C*‖u‖) := mul_le_mul_of_nonneg_right (hDb p.2) (mul_nonneg hC (norm_nonneg _))
    _=D*C*‖u‖ := by ring

theorem gradient_exchange {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {X : ℝ × E → E →L[ℝ] E} (hX : Continuous X) {T C : ℝ}
    (hC : 0≤C) (hbound : ∀t∈Icc (0:ℝ) T,∀y,‖X (t,y)‖≤C) (u : E) :
    (∫t in Icc (0:ℝ) T,∫y,fderiv ℝ φ y (X (t,y) u) ∂μ)=
      ∫y,fderiv ℝ φ y ((∫t in Icc (0:ℝ) T,X (t,y)) u) ∂μ := by
  rw [integral_integral_swap (gradient_time_space_integrable (μ:=μ) hφ hφc hX hC hbound u)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hi : IntegrableOn (fun t => X (t,y)) (Icc (0:ℝ) T) :=
    (hX.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hh := ((fderiv ℝ φ y).comp (ContinuousLinearMap.apply ℝ E u)).integral_comp_comm hi
  exact hh
end LogConcaveSampling.GradientIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Curve
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
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hab hD hf in
lemma flow_contDiff_one_to_left (t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc t x a) := by
  let H := flowHomeomorph hL hc ⟨a,le_rfl,hab⟩ t
  let J (x : E) := fundamentalEquiv
    (flowSpatialCoefficient_continuous hab hc hL hD x)
    (flowSpatialCoefficient_bound hab hc hL hf x) ⟨a,le_rfl,hab⟩ t
  have hJ (x : E) : HasFDerivAt H (J x : E →L[ℝ] E) x :=
    flow_hasFDerivAt_left hab hc hL hD hf x t
  exact H.contDiff_symm hJ (flow_contDiff_one_left hab hc hL hD hf t)

include hab hD hf in

theorem flow_contDiff_one (s t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc s x t) := by
  have hh := (flow_contDiff_one_left hab hc hL hD hf t).comp
    (flow_contDiff_one_to_left hab hc hL hD hf s)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (flow_cocycle hL hc s ⟨a,le_rfl,hab⟩ t x).symm
end LogConcaveSampling.GlobalODE

end UpperProof
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
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Truncated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unique {f : E → E} (hf : ContDiff ℝ 1 f) {a b : ℝ} {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hdα : ∀t∈Icc a b,HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hdβ : ∀t∈Icc a b,HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (h0 : α a=β a) : Set.EqOn α β (Icc a b) := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  obtain ⟨L,hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num : (1:WithTop ℕ∞)≠0)
    (convex_closedBall (0:E) (max A B)) (isCompact_closedBall (0:E) (max A B))
  intro t ht
  have hh := dist_le_of_trajectories_ODE_of_mem (v:=fun (_ : ℝ) => f)
    (s:=fun _ => Metric.closedBall (0:E) (max A B))
    (fun _ _ => hL) hα (GlobalODE.right_deriv hdα)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hA u ⟨hu.1,hu.2.le⟩).trans (le_max_left A B))
    hβ (GlobalODE.right_deriv hdβ)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hB u ⟨hu.1,hu.2.le⟩).trans (le_max_right A B)) (show dist (α a) (β a)≤0 by simp [h0]) t ht
  simpa only [h0,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma growth_from_right {a b K B R : ℝ} {α β : ℝ → E}
    (hc : ContinuousOn α (Icc a b))
    (hd : ∀t∈Icc a b,HasDerivWithinAt α (β t) (Icc a b) t)
    (hb : ‖α b‖≤R) (hg : ∀t∈Icc a b,‖β t‖≤K*‖α t‖+B)
    (t : ℝ) (ht : t∈Icc a b) : ‖α t‖≤gronwallBound R K B (b-t) := by
  let q : ℝ → ℝ := fun u => a+b-u
  have hq (u : ℝ) (hu : u∈Icc a b) : q u∈Icc a b := by
    constructor <;> dsimp [q] <;> linarith [hu.1,hu.2]
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hαc : ContinuousOn (α ∘ q) (Icc a b) := hc.comp hqc.continuousOn hq
  have hαd (u : ℝ) (hu : u∈Icc a b) :
      HasDerivWithinAt (α ∘ q) (-β (q u)) (Icc a b) u := by
    have hqd : HasDerivWithinAt q (-1) (Icc a b) u := by
      convert! ((hasDerivWithinAt_const u (Icc a b) (a+b)).sub
        (hasDerivWithinAt_id u (Icc a b))) using 1
      all_goals try with_reducible_and_instances rfl
      simp
    simpa only [neg_one_smul] using (hd (q u) (hq u hu)).scomp u hqd hq
  have h0 : ‖(α ∘ q) a‖≤R := by simpa [q] using hb
  have hβb (u : ℝ) (_hu : u∈Ico a b) :
      ‖-β (q u)‖≤K*‖(α ∘ q) u‖+B := by
    simpa only [norm_neg,comp_apply] using hg (q u) (hq u ⟨_hu.1,_hu.2.le⟩)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hαc
    (GlobalODE.right_deriv (f := fun u (_ : E) => -β (q u)) hαd) h0 hβb (q t) (hq t ht)
  simpa only [comp_apply,q,show a+b-(a+b-t)=t by ring,show a+b-t-a=b-t by ring] using hh

lemma gronwallBound_initial_mono {R S K B t : ℝ} (h : R≤S) :
    gronwallBound R K B t≤gronwallBound S K B t := by
  unfold gronwallBound
  split_ifs <;> gcongr

variable [FiniteDimensional ℝ E]

lemma flow_continuous {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    Continuous (flow hf hK hB hg hab x) := (exists_curve hf hK hB hg hab x).choose_spec.1
lemma flow_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    flow hf hK hB hg hab x a=x := (exists_curve hf hK hB hg hab x).choose_spec.2.1
lemma flow_deriv {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∀t∈Icc a b,HasDerivWithinAt (flow hf hK hB hg hab x)
      (f (flow hf hK hB hg hab x t)) (Icc a b) t :=
  (exists_curve hf hK hB hg hab x).choose_spec.2.2.1
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma truncated_flow_growth {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (n : ℕ)
    {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (y : E) :
    ∀t∈Icc a b,‖GlobalODE.flow (fun _ _ => hL)
      (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ y t‖≤
        gronwallBound ‖y‖ K B (t-a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.right_deriv (GlobalODE.flow_deriv _ _ _ _))
    (by rw [GlobalODE.flow_initial])
  exact fun _ _ => truncated_growth hg n _

lemma eq_truncated_flow {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n))
    (hn : gronwallBound R K B (b-a)≤(n:ℝ)+1) {y : E} (hy : ‖y‖≤R) :
    EqOn (flow hf hK hB hg hab y)
      (GlobalODE.flow (fun _ _ => hL) (truncated_continuous hf n)
        ⟨a,le_rfl,hab⟩ y) (Icc a b) := by
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) (⟨a,le_rfl,hab⟩ : Icc a b) y
  have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt α (f (α t)) (Icc a b) t := by
    have hb := truncated_flow_growth hf hg hab n hL y t ht
    have hb' : ‖α t‖≤(n:ℝ)+1 := hb.trans ((gronwallBound_initial_mono hy).trans
      ((gronwallBound_mono ((norm_nonneg y).trans hy) hB hK (sub_le_sub_right ht.2 a)).trans hn))
    have he := truncated_eq (f:=f) hb'
    exact he ▸ GlobalODE.flow_deriv (fun _ _ => hL) _ _ y t ht
  apply unique hf (flow_continuous hf hK hB hg hab y).continuousOn
    (GlobalODE.flow_continuous _ _ _ _).continuousOn (flow_deriv hf hK hB hg hab y) hd
  rw [flow_initial,GlobalODE.flow_initial]

lemma flow_continuous_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (t : ℝ) (ht : t∈Icc a b) : Continuous (fun y => flow hf hK hB hg hab y t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (gronwallBound (‖x‖+1) K B (b-a))
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  have hh := (GlobalODE.flow_lipschitz (fun _ _ => hL)
    (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ ⟨t,ht⟩).continuous.continuousAt (x:=x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
  apply (eq_truncated_flow hf hK hB hg hab n hL (by linarith) ?_ ht)
  calc ‖y‖≤‖x‖+dist y x := norm_le_norm_add_const_of_dist_le le_rfl
       _≤‖x‖+1 := by gcongr; exact (Metric.mem_ball.mp hy).le

lemma backwardTest_vanish {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hR : 0≤R) {φ : E → ℝ} (hφ : ∀x,R<‖x‖ → φ x=0)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (t : ℝ) (y : E)
    (hy : gronwallBound R K B (b-a)<‖y‖) :
    GlobalODE.backwardTest (f:=fun (_ : ℝ) => truncated f n) hab
      (truncated_continuous hf n) (fun _ _ => hL)
      ⟨b,hab,le_rfl⟩ φ (t,y)=0 := by
  rw [GlobalODE.backwardTest_eq]
  apply hφ
  by_contra! h
  let s := projIcc a b hab t
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) s y
  have hh := growth_from_right (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.flow_deriv (fun _ _ => hL) _ s y) h
    (fun u _ => truncated_growth hg n (α u)) s s.2
  rw [GlobalODE.flow_initial] at hh
  have hm := gronwallBound_mono hR hB hK (sub_le_sub_left s.2.1 b)
  exact (not_lt_of_ge (hh.trans hm)) hy
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stationary_integral_of_backward_flux {f : E → E} (hf : ContDiff ℝ 1 f)
    {K : ℝ≥0} (hL : LipschitzWith K f) {μ : Measure E} [IsFiniteMeasure μ]
    (hfi : Integrable (fun x => ‖f x‖) μ)
    {a b : ℝ} (hab : a<b) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hφL : LipschitzWith L φ) {B : ℝ} (hφB : ∀x,‖φ x‖≤B)
    (hflux : ∀t : ℝ,(∫y,(fderiv ℝ (fun z =>
      backwardTest (f:=fun (_ : ℝ) => f) hab.le (hf.continuous.comp continuous_snd) (fun _ _ => hL)
        ⟨b,hab.le,le_rfl⟩ φ (t,z)) y) (f y) ∂μ)=0) :
    (∫y,φ (flow (fun _ _ => hL) (hf.continuous.comp continuous_snd)
      ⟨a,le_rfl,hab.le⟩ y b) ∂μ)=∫y,φ y ∂μ := by
  let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
  let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
    (hf.continuous_fderiv (by norm_num)).comp continuous_snd
  let hd : ∀ (u : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
    fun _ z => (hf.differentiable (by norm_num) z).hasFDerivAt
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc (fun _ _ => hL) T φ
  let S := fun t => fderiv ℝ (fun y => ψ (t,y))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc (fun _ _ => hL) T hφ.continuous
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun y => ψ (t,y)) := by
    have he : (fun y => ψ (t,y))=φ ∘ (fun y =>
        flow (fun _ _ => hL) hc (projIcc a b hab.le t) y T) := by
      funext y
      exact backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,y)
    rw [he]
    exact hφ.comp (flow_contDiff_one hab.le hc (fun _ _ => hL) hD hd _ T)
  have hψL (t : ℝ) := backwardTest_lipschitz hab.le hc (fun _ _ => hL) T hφL t
  have hψB (t : ℝ) (y : E) : ‖ψ (t,y)‖≤B := hφB _
  have hSb (t : ℝ) (y : E) : ‖S t y‖≤C := norm_fderiv_le_of_lipschitz ℝ (hψL t)
  have him (t : ℝ) : Integrable (fun y => ψ (t,y)) μ :=
    (integrable_const B).mono' (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (hψB t))
  have hdm (t : ℝ) : Measurable (fun y => -(S t y (f y))) :=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (fun y => ψ (t,y))).prodMk hf.continuous.measurable)).neg
  have hdb (t : ℝ) (y : E) : ‖-(S t y (f y))‖≤C*‖f y‖ := by
    rw [norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hSb t y) (norm_nonneg _))
  have hpd (t : ℝ) (ht : t∈Ioo a b) (y : E) :
      HasDerivAt (fun t => ψ (t,y)) (-(S t y (f y))) t := by
    have hh := backwardTest_chain hab.le hc (fun _ _ => hL) hD hd T
      (hφ.differentiable (by norm_num)) ht (hasDerivAt_const t y)
    simpa only [zero_sub,map_neg] using hh
  have hQd (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt (fun t => ∫y,ψ (t,y) ∂μ) 0 t := by
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F:=fun t y => ψ (t,y)) (F':=fun t y => -(S t y (f y)))
      (Ioo_mem_nhds ht.1 ht.2)
      (Eventually.of_forall fun _ =>
        (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (him t) (hdm t).aestronglyMeasurable
      (Eventually.of_forall fun y s _ => hdb s y) (hfi.const_mul C)
      (Eventually.of_forall fun y s hs => hpd s hs y)
    have hz := hflux t
    have he : (∫y,-(S t y (f y)) ∂μ)=0 := by rw [integral_neg]; exact neg_eq_zero.mpr hz
    rw [he] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫y,ψ (t,y) ∂μ) :=
    continuous_of_dominated
      (fun _ => (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hψB t)) (integrable_const B)
      (Eventually.of_forall fun y => hψ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫y,ψ (t,y) ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫y,ψ (b,y) ∂μ)=(∫y,ψ (a,y) ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have ha : (fun y => ψ (a,y))=(fun y => φ (flow (fun _ _ => hL) hc ⟨a,le_rfl,hab.le⟩ y b)) := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
  have hb : (fun y => ψ (b,y))=φ := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact congrArg φ (flow_initial (fun _ _ => hL) hc T y)
  rw [ha,hb] at heq
  exact heq.symm

end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma fderiv_zero_of_vanish_outside {ψ : E → ℝ} {C : ℝ}
    (hψ : ∀z,C<‖z‖ → ψ z=0) {y : E} (hy : C<‖y‖) : fderiv ℝ ψ y=0 := by
  have he : ψ =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact hψ z hz
  exact ((hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) y).congr_of_eventuallyEq he).fderiv

theorem stationary_integral_compact {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,φ (flow hf hK hB hg hab.le y b) ∂μ)=∫y,φ y ∂μ := by
  obtain ⟨R,hR,hRb⟩ := hφc.isCompact.isBounded.exists_pos_norm_le
  have hφv (z : E) (hz : R<‖z‖) : φ z=0 := by
    by_contra hh
    exact (not_lt_of_ge (hRb z (subset_tsupport φ hh))) hz
  let C := gronwallBound R K B (b-a)
  obtain ⟨n,hn⟩ := exists_nat_gt (max C (gronwallBound C K B (b-a)))
  have hnC : C≤(n:ℝ)+1 := by have := le_max_left C (gronwallBound C K B (b-a)); linarith
  have hnG : gronwallBound C K B (b-a)≤(n:ℝ)+1 := by
    have := le_max_right C (gronwallBound C K B (b-a)); linarith
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  let hc := truncated_continuous hf n
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := GlobalODE.backwardTest hab.le hc (fun _ _ => hL) T φ
  have hψv (t : ℝ) (z : E) (hz : C<‖z‖) : ψ (t,z)=0 :=
    backwardTest_vanish hf hK hB hg hab.le hR.le hφv n hL t z hz
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun z => ψ (t,z)) := by
    have he : (fun z => ψ (t,z))=φ ∘ (fun z =>
        GlobalODE.flow (fun _ _ => hL) hc (projIcc a b hab.le t) z T) := by
      funext z
      exact GlobalODE.backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,z)
    rw [he]
    apply hφ.comp
    apply GlobalODE.flow_contDiff_one (D:=fun _ => fderiv ℝ (truncated f n)) hab.le hc (fun _ _ => hL)
      (((truncated_smooth hf n).continuous_fderiv (by norm_num)).comp continuous_snd)
      (fun _ z => ((truncated_smooth hf n).differentiable (by norm_num) z).hasFDerivAt)
  have hψcompact (t : ℝ) : HasCompactSupport (fun z => ψ (t,z)) :=
    HasCompactSupport.intro (isCompact_closedBall (0:E) C) fun z hz =>
      hψv t z (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
  have hψflux (t : ℝ) : (∫y,(fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y) ∂μ)=0 := by
    rw [show (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y))=
      (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (f y)) by
        funext y
        by_cases hy : ‖y‖≤C
        · rw [truncated_eq (hy.trans hnC)]
        · rw [fderiv_zero_of_vanish_outside (hψv t) (lt_of_not_ge hy)]
          rfl]
    exact hflux _ (hψc t) (hψcompact t)
  have hni : Integrable (fun x => ‖truncated f n x‖) μ :=
    hfi.mono' (truncated_smooth hf n).continuous.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_norm,truncated,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (PoincareCutoff.cutoff_nonneg n x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (PoincareCutoff.cutoff_le_one n x))
  obtain ⟨J,hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  obtain ⟨D,hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hh := GlobalODE.stationary_integral_of_backward_flux (truncated_smooth hf n) hL hni
    hab hφ hJ hD hψflux
  rw [←hh]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : ‖y‖≤C
  · exact congrArg φ (eq_truncated_flow hf hK hB hg hab.le n hL hnG hy ⟨hab.le,le_rfl⟩)
  · have hy' : C<‖y‖ := lt_of_not_ge hy
    have hv : φ (flow hf hK hB hg hab.le y b)=0 := by
      apply hφv
      by_contra! h
      have hh := growth_from_right (flow_continuous hf hK hB hg hab.le y).continuousOn
        (flow_deriv hf hK hB hg hab.le y) h (fun _ _ => hg _) a ⟨le_rfl,hab.le⟩
      rw [flow_initial] at hh
      exact (not_lt_of_ge hh) hy'
    rw [hv]
    exact (by
      have hh := hψv a y hy'
      dsimp [ψ] at hh
      rw [GlobalODE.backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)] at hh
      exact hh.symm)
theorem stationary_law {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) :
    μ.map (fun y => flow hf hK hB hg hab.le y b)=μ := by
  let T := fun y => flow hf hK hB hg hab.le y b
  have hTc : Continuous T := flow_continuous_initial hf hK hB hg hab.le b ⟨hab.le,le_rfl⟩
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ _hφL hφB
  obtain ⟨D,hD⟩ := hφB
  let u := PoincareCutoff.truncation φ
  have hul (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫y,u n y ∂η) atTop (𝓝 (∫y,φ y ∂η)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D)
      (fun n => (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable)
      (integrable_const D)
    · exact fun n => Eventually.of_forall fun y =>
        (PoincareCutoff.truncation_abs φ n y).trans (hD y)
    · exact Eventually.of_forall (PoincareCutoff.truncation_tendsto φ)
  have he : (fun n => ∫y,u n y ∂μ.map T)=(fun n => ∫y,u n y ∂μ) := by
    funext n
    rw [integral_map hTc.aemeasurable
      (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable]
    exact stationary_integral_compact hf hK hB hg hab hfi hflux
      (PoincareCutoff.truncation_smooth hφ n) (PoincareCutoff.truncation_compact φ n)
  exact tendsto_nhds_unique (hul (μ.map T)) (he ▸ hul μ)
end LogConcaveSampling.LinearGrowthODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SkewCenteringField
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
open scoped RealInnerProductSpace

lemma compact_slice_left {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (z : F) :
    HasCompactSupport (fun y => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z,?_⟩
  convert isClosed_univ.prod (isClosed_singleton (x:=z)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,true_and]
  aesop

lemma compact_slice_right {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space E] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (y : E) :
    HasCompactSupport (fun z => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight y,?_⟩
  convert (isClosed_singleton (x:=y)).prod isClosed_univ using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,and_true]
  aesop

lemma compact_derivative_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : HasCompactSupport φ) (W : E → E) :
    HasCompactSupport (fun p => fderiv ℝ φ p (W p)) := by
  apply HasCompactSupport.intro hφ.isCompact
  intro p hp
  rw [(HasFDerivAt.of_notMem_tsupport ℝ hp).fderiv]
  rfl

theorem product_stein_flux {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : Continuous K) (hm : Continuous m)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    (s : ℝ) {φ : Point d × Point d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    (∫p,fderiv ℝ φ p (skewCenteringField K m s p) ∂μ.prod (stdGaussian (Point d)))=0 := by
  let ν := stdGaussian (Point d)
  let A := fun p : Point d × Point d => fderiv ℝ φ p ((K p.1).adjoint p.2,0)
  let B := fun p : Point d × Point d => fderiv ℝ φ p (0,m p.1)
  let C := fun p : Point d × Point d => inner ℝ p.2 (m p.1)*φ p
  have hD := hφ.continuous_fderiv (by norm_num)
  have hKA : Continuous (fun p : Point d × Point d => ((K p.1).adjoint p.2,(0:Point d))) :=
    (((ContinuousLinearMap.adjoint.continuous.comp hK).comp continuous_fst).clm_apply continuous_snd).prodMk continuous_const
  have hMB : Continuous (fun p : Point d × Point d => ((0:Point d),m p.1)) :=
    continuous_const.prodMk (hm.comp continuous_fst)
  have hAi : Integrable A (μ.prod ν) :=
    (hD.clm_apply hKA).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hBi : Integrable B (μ.prod ν) :=
    (hD.clm_apply hMB).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hCi : Integrable C (μ.prod ν) :=
    ((continuous_snd.inner (hm.comp continuous_fst)).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hA (g : Point d) : (∫y,A (y,g) ∂μ)=∫y,C (y,g) ∂μ := by
    have hh := hstein g (fun y => φ (y,g)) (hφ.comp (contDiff_id.prodMk contDiff_const)) (compact_slice_left hφc g)
    have hd (y : Point d) : fderiv ℝ (fun y => φ (y,g)) y=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inl ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const g y))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,A,C] using hh.symm
  have hB (y : Point d) : (∫g,B (y,g) ∂ν)=∫g,C (y,g) ∂ν := by
    have hh := compact_gaussian_ibp (g:=fun g => φ (y,g)) (hφ.comp (contDiff_const.prodMk contDiff_id)) (compact_slice_right hφc y) (m y)
    have hd (g : Point d) : fderiv ℝ (fun g => φ (y,g)) g=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inr ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp g
        ((hasFDerivAt_const y g).prodMk (hasFDerivAt_id g))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,B,C,ν] using hh
  have he (p : Point d × Point d) : fderiv ℝ φ p (skewCenteringField K m s p)=
      -s⁻¹*A p+s⁻¹*B p := by
    have he : skewCenteringField K m s p=
        (-s⁻¹) • ((K p.1).adjoint p.2,0)+s⁻¹ • (0,m p.1) := by
      ext <;> simp [skewCenteringField]
    rw [he,map_add,map_smul,map_smul]
    rfl
  simp_rw [he]
  rw [integral_add (hAi.const_mul _) (hBi.const_mul _),integral_const_mul,integral_const_mul]
  have hAC : (∫p,A p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod_symm _ hAi,integral_prod_symm _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hA)
  have hBC : (∫p,B p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod _ hBi,integral_prod _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hB)
  change -s⁻¹*(∫p,A p ∂μ.prod ν)+s⁻¹*(∫p,B p ∂μ.prod ν)=0
  rw [hAC,hBC]
  ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SkewCenteringFieldSmooth
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
open scoped NNReal RealInnerProductSpace

lemma skewCenteringField_smooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) (s : ℝ) :
    ContDiff ℝ 1 (skewCenteringField K m s) := by
  have hA : ContDiff ℝ 1 (fun y : Point d => (K y).adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Point d) (F:=Point d)).contDiff.comp hK
  have hAp : ContDiff ℝ 1 (fun p : Point d × Point d => (K p.1).adjoint p.2) :=
    (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hmp : ContDiff ℝ 1 (fun p : Point d × Point d => m p.1) := hm.comp contDiff_fst
  exact (hAp.const_smul (-s⁻¹)).prodMk (hmp.const_smul s⁻¹)

lemma skewCenteringField_growth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} {C : ℝ} {L : ℝ≥0} (hC : 0≤C) (hK : ∀y,‖K y‖≤C)
    (hm : LipschitzWith L m) {s : ℝ} (hs : 0 < s) (p : Point d × Point d) :
    ‖skewCenteringField K m s p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := by
  have hmn : ‖m p.1‖≤L*‖p.1‖+‖m 0‖ := by
    have h1 := hm.norm_sub_le p.1 0
    simpa only [sub_zero] using (norm_le_norm_sub_add (m p.1) (m 0)).trans (add_le_add h1 le_rfl)
  have hkn : ‖(K p.1).adjoint p.2‖≤C*‖p.2‖ := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr; exact hK _)
  change max ‖-s⁻¹ • (K p.1).adjoint p.2‖ ‖s⁻¹ • m p.1‖≤_
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hs)]
  apply max_le
  · calc
      _≤ s⁻¹*(C*‖p.2‖) := mul_le_mul_of_nonneg_left hkn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖)+s⁻¹*‖m 0‖ := by
        have hp : ‖p.2‖≤‖p‖ := norm_snd_le p
        have hL : C≤C+L := le_add_of_nonneg_right L.coe_nonneg
        have hh : C*‖p.2‖≤(C+L)*‖p‖ := mul_le_mul hL hp (norm_nonneg _) (by positivity)
        exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)).trans (le_add_of_nonneg_right (by positivity))
      _=_ := by ring
  · calc
      _≤ s⁻¹*(L*‖p.1‖+‖m 0‖) := mul_le_mul_of_nonneg_left hmn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖+‖m 0‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
        apply add_le_add_left
        exact mul_le_mul (le_add_of_nonneg_left hC) (norm_fst_le p) (norm_nonneg _) (by positivity)
      _=_ := by ring

lemma integrable_product_norm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x => ‖x‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    Integrable (fun p : E × F => ‖p‖) (μ.prod ν) := by
  apply ((hμ.comp_fst ν).add (hν.comp_snd μ)).mono' continuous_norm.aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_norm]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_FlowRestrict
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma flow_restrict {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b c : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hc : c∈Icc a b) (x : E) :
    EqOn (flow hf hK hB hg hab x) (flow hf hK hB hg hc.1 x) (Icc a c) := by
  apply unique hf (flow_continuous hf hK hB hg hab x).continuousOn
    (flow_continuous hf hK hB hg hc.1 x).continuousOn
  · intro t ht
    exact (flow_deriv hf hK hB hg hab x t ⟨ht.1,ht.2.trans hc.2⟩).mono
      (Icc_subset_Icc le_rfl hc.2)
  · exact flow_deriv hf hK hB hg hc.1 x
  · rw [flow_initial,flow_initial]

theorem stationary_at {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) {t : ℝ} (ht : t∈Icc a b) :
    μ.map (fun y => flow hf hK hB hg hab y t)=μ := by
  obtain he|hlt := ht.1.eq_or_lt
  · subst t
    simp only [flow_initial]
    exact Measure.map_id
  · have hEq : (fun y => flow hf hK hB hg hab y t)=
        (fun y => flow hf hK hB hg hlt.le y t) := by
      funext y
      exact flow_restrict hf hK hB hg hab ht y ⟨ht.1,le_rfl⟩
    rw [hEq]
    exact stationary_law hf hK hB hg hlt hfi hflux
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem exists_skew_centering_flow {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) {C : ℝ} {L : ℝ≥0}
    (hC : 0≤C) (hKb : ∀y,‖K y‖≤C) (hmL : LipschitzWith L m)
    (hμ : Integrable (fun y => ‖y‖) μ)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    {s a b : ℝ} (hs : 0 < s) (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p) (skewCenteringField K m s (Ψ p t)) (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,(μ.prod (stdGaussian (Point d))).map (fun p => Ψ p t)=μ.prod (stdGaussian (Point d))) := by
  let f := skewCenteringField K m s
  have hf : ContDiff ℝ 1 f := skewCenteringField_smooth hK hm s
  have hk : 0≤ s⁻¹*(C+L) := by positivity
  have hb : 0≤ s⁻¹*‖m 0‖ := by positivity
  have hg : ∀p,‖f p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := skewCenteringField_growth hC hKb hmL hs
  let Ψ := LinearGrowthODE.flow hf hk hb hg hab
  refine ⟨Ψ,?_,?_,?_⟩
  · intro p
    exact ⟨LinearGrowthODE.flow_continuous hf hk hb hg hab p,
      LinearGrowthODE.flow_initial hf hk hb hg hab p,
      LinearGrowthODE.flow_deriv hf hk hb hg hab p⟩
  · exact fun t ht => LinearGrowthODE.flow_continuous_initial hf hk hb hg hab t ht
  · have hi : Integrable (fun g : Point d => ‖g‖) (stdGaussian (Point d)) := IsGaussian.integrable_id.norm
    have hprod := integrable_product_norm hμ hi
    have hfi : Integrable (fun p => ‖f p‖) (μ.prod (stdGaussian (Point d))) := by
      apply ((hprod.const_mul (s⁻¹*(C+L))).add (integrable_const (s⁻¹*‖m 0‖))).mono' hf.continuous.norm.aestronglyMeasurable
      filter_upwards [] with p
      rw [norm_norm]
      exact hg p
    exact fun t ht => LinearGrowthODE.stationary_at hf hk hb hg hab hfi
      (fun φ hφ hφc => product_stein_flux hK.continuous hm.continuous hstein s hφ hφc) ht

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

lemma directional (hf : PolySmooth f) (v : Point d) : PolySmooth (LogConcaveSampling.directional v f) := by
  refine ⟨directional_smooth hf.smooth v,fun l => ?_⟩
  have he : JetCalculus.jet id [v] f=LogConcaveSampling.directional v f := rfl
  have hh := hf.growth (l++[v])
  rw [JetCalculus.jet_append,he] at hh
  exact hh

lemma polyC1 (hf : PolySmooth f) : PolyC1 f :=
  ⟨hf.smooth.of_le (by simp),hf.growth [],fun v => (hf.directional v).growth []⟩

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

lemma const (c : ℝ) : PolySmooth (fun _ : Point d => c) := by
  refine ⟨contDiff_const,fun l => ?_⟩
  rw [JetCalculus.jet_const]
  split_ifs <;> exact growth_const _

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
lemma conditionalFirstJet_norm_le (y : Point d) :
    ‖conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)‖≤(Real.pi^2/2)*((lam:ℝ)*r) := by
  have ha := (probability_time hρ0 hρ1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let w := conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v
  have he := conditionalFirstJet_inner hF x hr hlam hl hρ0 hρ1 w v y
  have hb := mul_le_mul_of_nonneg_left
    (conditional_covariance_le hF x hr.le hl hρ0 hρ1 w v y) (by positivity : 0≤1/(1-ρ^2))
  have hh : ‖w‖^2≤((Real.pi^2/2)*((lam:ℝ)*r))*‖w‖*‖v‖ := by
    rw [←real_inner_self_eq_norm_sq w,he]
    calc
      _≤(1/(1-ρ^2))*|cov[(fun z => inner ℝ v z),
          (fun z => inner ℝ w (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _≤_ := by convert! hb using 1; field_simp [ha.ne']
  change ‖w‖≤_
  by_cases hw : ‖w‖=0
  · rw [hw]; positivity
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))).mp
    convert! hh using 1 <;> ring

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

include hlam in
lemma steinIntegrand_norm_le (t : Icc (0:ℝ) T) (y : Point d) :
    ‖steinIntegrand hF x hr hl hT0 hT1 (t,y)‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) := by
  unfold steinIntegrand
  calc
    _≤‖terminalJacobian hF x hr hl hT0 hT1 (t,y)‖*
      ‖conditionalFirstJet F x r ((lam:ℝ)*r)
        (smoothTimeClip hT0 hT1 t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _≤Real.exp (Real.pi^2/4)*((Real.pi^2/2)*((lam:ℝ)*r)) := by
      rw [smoothTimeClip_eq hT0 hT1 t.2]
      exact mul_le_mul (terminalJacobian_norm_le hF x hr hl hT0 hT1 t y)
        (conditionalFirstJet_norm_le hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) _)
        (norm_nonneg _) (Real.exp_pos _).le
    _=_ := by ring

include hlam in
theorem centeringKernel_norm_le (y : Point d) :
    ‖centeringKernel hF x hr hl hT0 hT1 y‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) := by
  unfold centeringKernel
  rw [ContinuousLinearMap.adjoint.norm_map]
  have hb := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (s:=Icc (0:ℝ) T) (f:=fun t => steinIntegrand hF x hr hl hT0 hT1 (t,y))
    isCompact_Icc.measure_lt_top
    (fun t ht => steinIntegrand_norm_le hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ y)
  apply hb.trans
  simp only [Measure.real,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT0]
  exact mul_le_of_le_one_right (by positivity) hT1.le
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

lemma terminalMean_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalMean hF x hr hl hT0 hT1) := by
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  let q : ℝ × Point d := (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)
  have hA := conditionalFieldMean_joint_smooth hF x hr.le (by linarith only [hl]) q
    (smoothTimeClip_sq_lt hT0 hT1 p.1)
  have hB : ContDiffAt ℝ (⊤:ℕ∞)
      (fun w : ℝ × Point d => (smoothTimeClip hT0 hT1 w.1,terminalBackward hF x hr.le hl hT0 hT1 w)) p :=
    ((hclip.comp contDiff_fst).prodMk (terminalBackward_smooth hF x hr.le hl hT0 hT1)).contDiffAt
  exact hA.comp p hB

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

lemma terminalMean_direction {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (u y : Point d) :
    fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)=
      materialScalar F x r (fun t y => inner ℝ u (conditionalFieldMean F x r t y)) ρ
        (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) := by
  let A := fun p : ℝ × Point d => inner ℝ u (conditionalFieldMean F x r p.1 p.2)
  have hp : ρ^2<1 := by nlinarith [hρT.trans hT1]
  have ha : DifferentiableAt ℝ A (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) :=
    (contDiffAt_const.inner ℝ (conditionalFieldMean_joint_smooth hF x hr.le (by linarith only [hl]) (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)) hp)).differentiableAt (by simp)
  have hd := ha.hasFDerivAt.comp_hasDerivAt ρ
    ((hasDerivAt_id ρ).prodMk (terminalBackward_deriv hF x hr hl hT0 hT1 hρ0 hρT y))
  have he : (fun t => inner ℝ u (terminalMean hF x hr hl hT0 hT1 (t,y)))=ᶠ[nhds ρ]
      (fun t => A (t,terminalBackward hF x hr.le hl hT0 hT1 (t,y))) := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with t ht
    simp only [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨ht.1.le,ht.2.le⟩,A]
  have hh := (((contDiff_const (c:=u)).inner ℝ (terminalMean_smooth hF x hr hl hT0 hT1)).differentiable (by simp) (ρ,y)).hasFDerivAt.comp_hasDerivAt ρ
    ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y))
  have hder : fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)=
      fderiv ℝ A (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))
        (1,-r • conditionalFieldMean F x r ρ (terminalBackward hF x hr.le hl hT0 hT1 (ρ,y))) :=
    hh.unique (hd.congr_of_eventuallyEq he)
  rw [hder,joint_material_direction F x r ha]
  exact joint_mdir_eq_material F x r ha

lemma conditionalFieldMean_zero (y : Point d) :
    conditionalFieldMean F x r 0 y=∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r) := by
  unfold conditionalFieldMean
  have he : conditionalPotential F x r 0 y=primitivePotential F x r := by
    funext z
    simp [conditionalPotential,primitivePotential]
  rw [he]

lemma terminalMean_initial (y : Point d) :
    terminalMean hF x hr hl hT0 hT1 (0,y)=∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r) := by
  rw [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨le_rfl,hT0⟩,conditionalFieldMean_zero]

lemma terminalMean_final (y : Point d) :
    terminalMean hF x hr hl hT0 hT1 (T,y)=conditionalFieldMean F x r T y := by
  rw [terminalMean,smoothTimeClip_eq hT0 hT1 ⟨hT0,le_rfl⟩,
    terminalBackward_eq hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩,probabilityTransport_initial]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter Function
open scoped NNReal RealInnerProductSpace Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hlam hl in
lemma conditionalFirstJet_symmetric_pos (hρ0 : 0<ρ) (hρ1 : ρ<1) (y : Point d) :
    (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)).IsSymmetric := by
  have hH := interpolationPotential_smooth hF x hr.le hl hρ0.le hρ1
  have he : gradient (interpolationPotential F x r ρ)=fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y :=
    funext (interpolationPotential_gradient hF x hr.le hl hρ0.le hρ1)
  have hd := (hasFDerivAt_id (𝕜:=ℝ) y).add
    (((conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1).differentiable (by simp) y).hasFDerivAt.const_smul (r*ρ))
  change HasFDerivAt (fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y) _ _ at hd
  have hh := ContDiff.isSymmetric_gradient_derivative (hH.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))) y
  rw [he,hd.fderiv,conditionalFirstJet_deriv hF x hr hlam hl hρ0.le hρ1 y] at hh
  intro u v
  have hs := hh u v
  change inner ℝ (u+(r*ρ) • (ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) u)) v=
    inner ℝ u (v+(r*ρ) • (ρ • conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y) v)) at hs
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,conj_trivial] at hs
  exact (mul_left_cancel₀ hρ0.ne')
    ((mul_left_cancel₀ (mul_ne_zero hr.ne' hρ0.ne')) (add_left_cancel hs))

include hF hr hlam hl in
lemma conditionalFirstJet_symmetric (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,y)).IsSymmetric := by
  rcases eq_or_lt_of_le hρ0 with h0|hpos
  · subst ρ
    intro u v
    have hc : ContinuousAt (fun t => conditionalFirstJet F x r ((lam:ℝ)*r) (t,y)) 0 :=
      (conditionalFirstJet_smooth hF x hr hlam hl (0,y) (by norm_num)).continuousAt.comp
        (f:=fun t : ℝ => (t,y)) (continuousAt_id.prodMk continuousAt_const)
    have h1 : Tendsto (fun t => inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) u) v) (nhds 0)
        (nhds (inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (0,y) u) v)) :=
      ((hc.clm_apply continuousAt_const).inner continuousAt_const).tendsto
    have h2 : Tendsto (fun t => inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) v)) (nhds 0)
        (nhds (inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (0,y) v))) :=
      (continuousAt_const.inner (hc.clm_apply continuousAt_const)).tendsto
    have e : (fun t => inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) u) v)=ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun t => inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,y) v)) := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ)<1 from by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      exact conditionalFirstJet_symmetric_pos hF x hr hlam hl ht ht1 y u v
    exact tendsto_nhds_unique (h1.mono_left nhdsWithin_le_nhds)
      ((h2.mono_left nhdsWithin_le_nhds).congr' e.symm)
  · exact conditionalFirstJet_symmetric_pos hF x hr hlam hl hpos hρ1 y
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminal_integral_pushforward (t : Icc (0:ℝ) T) {f : Point d → ℝ} (hf : Continuous f) :
    (∫y,f y ∂interpolationLaw F x r T)=
      ∫z,f (terminalForward hF x hr.le hl hT0 hT1 (t,z)) ∂interpolationLaw F x r t := by
  rw [← probabilityTransport_pushforward hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩,
    integral_map (probabilityTransport_continuous hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩).measurable.aemeasurable hf.aestronglyMeasurable]
  simp only [terminalForward_eq]

include hF hr hlam hl hT1 in
lemma firstJet_pairing_sum (t : Icc (0:ℝ) T) (z u : Point d) (A : Point d →L[ℝ] ℝ) :
    (∑i : Fin d,conditionalU F x r t z u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()]*A (EuclideanSpace.basisFun (Fin d) ℝ i))=
      A (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he (i : Fin d) : conditionalU F x r t z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]=
      inner ℝ (b i) (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) := by
    rw [conditionalU_one_cov hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1),
      ←conditionalFirstJet_inner hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) u (b i) z]
    have hs := conditionalFirstJet_symmetric hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) z u (b i)
    change inner ℝ (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u) (b i)=
      inner ℝ u (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) (b i)) at hs
    exact hs.symm.trans (real_inner_comm _ _)
  change (∑i,conditionalU F x r t z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]*A (b i))=_
  simp only [he]
  have hh := congrArg A (b.sum_repr' (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z) u))
  simpa only [map_sum,map_smul,smul_eq_mul] using hh

include hlam in
lemma stein_pairing_integrand (t : Icc (0:ℝ) T) (z u : Point d)
    {φ : Point d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∑i : Fin d,conditionalU F x r t z u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()]*
        directional (EuclideanSpace.basisFun (Fin d) ℝ i)
          (fun y => φ (terminalForward hF x hr.le hl hT0 hT1 (t,y))) z)=
      fderiv ℝ φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))
        (steinIntegrand hF x hr hl hT0 hT1 (t,terminalForward hF x hr.le hl hT0 hT1 (t,z)) u) := by
  have hh := (hφ.differentiable (by norm_num) _).hasFDerivAt.comp z
    ((terminalForward_slice_smooth hF x hr hl hT0 hT1 t).differentiable (by simp) z).hasFDerivAt
  change HasFDerivAt (fun y => φ (terminalForward hF x hr.le hl hT0 hT1 (t,y))) _ _ at hh
  simp only [directional,hh.fderiv]
  rw [firstJet_pairing_sum hF x hr hlam hl hT1]
  simp only [steinIntegrand,smoothTimeClip_eq hT0 hT1 t.2,terminalBackward_forward,
    ContinuousLinearMap.comp_apply,terminalJacobian_eq]
  congr 2
  exact congrArg (fun f => fderiv ℝ f z) (funext (terminalForward_eq hF x hr.le hl hT0 hT1 t))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

lemma tensorAdjoint_continuous_C1 {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hV : ∀i,ContDiff ℝ 1 (V i)) (b : ι → Point d) :
    Continuous (tensorAdjoint H b V) := by
  apply continuous_finsetSum
  intro i _
  exact (((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
    (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam in
lemma stein_weak_derivative {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (u : Point d)
    {φ : Point d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,fderiv ℝ (fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)) (ρ,y) (1,0)*φ y
      ∂interpolationLaw F x r T)=
      ∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (ρ,y) u) ∂interpolationLaw F x r T := by
  let t : Icc (0:ℝ) T := ⟨ρ,hρ0.le,hρT.le⟩
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let V := fun i : Fin d => fun z => conditionalU F x r ρ z u ((lam:ℝ)*r) (fun _ : Unit => b i) [()]
  let H := interpolationPotential F x r ρ
  have hp : ρ^2<1 := by nlinarith only [hρ0,hρT,hT1]
  have hV (i : Fin d) : ContDiff ℝ 1 (V i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact ((conditionalU_joint_smooth hF x hr hlam hl (fun _ : Unit => b i) [()] (by simp) u
      (ρ,z) hp).comp z (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  have hH : ContDiff ℝ 1 H := (interpolationPotential_smooth hF x hr.le hl hρ0.le (hρT.trans hT1)).of_le (by simp)
  have hAi : Integrable (fun z => Real.exp (-H z)) :=
    (interpolationPotential_lowerTail hF x hr.le (by linarith only [hl]) hρ0.le (hρT.trans hT1)).integrable_exp hH.continuous
  have hA := tensorAdjoint_continuous_C1 hH hV b
  have htest : ContDiff ℝ 1 (fun z => φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) :=
    hφ.comp ((terminalForward_slice_smooth hF x hr hl hT0 hT1 t).of_le (by simp))
  have htestc : HasCompactSupport (fun z => φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) :=
    hφc.comp_homeomorph (terminalHomeomorph hF x hr hl hT0 hT1 t)
  have hcR : Continuous (fun y => fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (t,y) u)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply
      (((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  simp_rw [terminalMean_direction hF x hr hl hT0 hT1 hρ0 hρT u,
    material_conditionalFieldMean hF x hr hlam hl hρ0.le (hρT.trans hT1)]
  change (∫y,tensorAdjoint H b V (terminalBackward hF x hr.le hl hT0 hT1 (t,y))*φ y ∂interpolationLaw F x r T)=_
  have hleft := terminal_integral_pushforward hF x hr hl hT0 hT1 t
    ((hA.comp (terminalBackward_slice_smooth hF x hr hl hT0 hT1 t).continuous).mul hφ.continuous)
  change (∫y,tensorAdjoint H b V (terminalBackward hF x hr.le hl hT0 hT1 (t,y))*φ y ∂interpolationLaw F x r T)=_ at hleft
  rw [hleft]
  have hright := terminal_integral_pushforward hF x hr hl hT0 hT1 t hcR
  change (∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (ρ,y) u) ∂interpolationLaw F x r T)=_ at hright
  rw [hright]
  simp only [Function.comp_def,Pi.mul_apply,terminalBackward_forward]
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl]) hp]
  change (∫z,tensorAdjoint H b V z*(φ (terminalForward hF x hr.le hl hT0 hT1 (t,z))) ∂gibbs H)=_
  rw [tensorAdjoint_compact_pairing hH hAi hV htest htestc b]
  apply integral_congr_ae
  filter_upwards [] with z
  exact stein_pairing_integrand hF x hr hlam hl hT0 hT1 t z u hφ
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrimitiveExpectedField
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
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam in

theorem centeringKernel_weak (u : Point d) {φ : Point d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,inner ℝ u (conditionalFieldMean F x r T y-
      ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r))*φ y ∂interpolationLaw F x r T)=
      ∫y,fderiv ℝ φ y ((centeringKernel hF x hr hl hT0 hT1 y).adjoint u) ∂interpolationLaw F x r T := by
  let μ := interpolationLaw F x r T
  let : IsProbabilityMeasure μ := interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  let M := fun p => inner ℝ u (terminalMean hF x hr hl hT0 hT1 p)
  let A := fun t => ∫y,M (t,y)*φ y ∂μ
  let B := fun t => ∫y,fderiv ℝ φ y (steinIntegrand hF x hr hl hT0 hT1 (t,y) u) ∂μ
  have hM : ContDiff ℝ 1 M := ((contDiff_const (c:=u)).inner ℝ
    (terminalMean_smooth hF x hr hl hT0 hT1)).of_le (by simp)
  have hA (t : ℝ) : HasDerivAt A (∫y,fderiv ℝ M (t,y) (1,0)*φ y ∂μ) t :=
    CompactExpectation.compact_test_hasDerivAt hM hφ hφc t
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun t => (hA t).continuousAt)
  have hXi := (steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous
  have hBc : Continuous B := GradientIntegral.continuous_gradient_expectation hφ hφc hXi u
  have hAd (t : ℝ) (ht : t∈Ioo (0:ℝ) T) : HasDerivAt A (B t) t := by
    have he := stein_weak_derivative hF x hr hlam hl hT0 hT1 ht.1 ht.2 u hφ hφc
    change (∫y,fderiv ℝ M (t,y) (1,0)*φ y ∂μ)=B t at he
    exact (hA t).congr_deriv he
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0 hAc.continuousOn hAd (hBc.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_of_le hT0,←integral_Icc_eq_integral_Ioc] at hFTC
  have hBound : ∀t∈Icc (0:ℝ) T,∀y,‖steinIntegrand hF x hr hl hT0 hT1 (t,y)‖≤
      (Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r) :=
    fun t ht y => steinIntegrand_norm_le hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ y
  have hExchange := GradientIntegral.gradient_exchange (μ:=μ) hφ hφc hXi
    (by positivity : 0≤(Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r)) hBound u
  change (∫t in Icc (0:ℝ) T,B t)=_ at hExchange
  have hInt (t : ℝ) : Integrable (fun y => M (t,y)*φ y) μ :=
    (((hM.continuous.comp (continuous_const.prodMk continuous_id)).mul hφ.continuous)).integrable_of_hasCompactSupport hφc.mul_left
  have hEnds : A T-A 0=(∫y,inner ℝ u (conditionalFieldMean F x r T y-
      ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r))*φ y ∂μ) := by
    rw [← integral_sub (hInt T) (hInt 0)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [M,terminalMean_final,terminalMean_initial,inner_sub_right,sub_mul]
  change _=(∫y,fderiv ℝ φ y ((centeringKernel hF x hr hl hT0 hT1 y).adjoint u) ∂μ)
  rw [←hEnds,←hFTC,hExchange]
  simp only [centeringKernel,ContinuousLinearMap.adjoint_adjoint]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hF hr hl hT0 hT1 in
lemma interpolation_norm_integrable : Integrable (fun y : Point d => ‖y‖) (interpolationLaw F x r T) := by
  have hlt : (lam:ℝ)*r^2<1 := by linarith only [hl]
  rw [interpolationLaw_eq_gibbs hF x hr.le hlt (by nlinarith [probability_time hT0 hT1])]
  simpa only [pow_one] using
    ((interpolationPotential_lowerTail hF x hr.le hlt hT0 hT1).hasExpMoments
      (interpolationPotential_smooth hF x hr.le hl hT0 hT1).continuous).hasMoments 1

include hlam in

theorem exists_actual_centering_flow {s a b : ℝ} (hs : 0 < s) (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p)
          (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
            (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) s (Ψ p t))
          (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,((interpolationLaw F x r T).prod (stdGaussian (Point d))).map
        (fun p => Ψ p t)=(interpolationLaw F x r T).prod (stdGaussian (Point d))) := by
  let : IsProbabilityMeasure (interpolationLaw F x r T) :=
    interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  have hK := (centeringKernel_smooth hF x hr hlam hl hT0 hT1).of_le (by simp : (1:WithTop ℕ∞)≤(⊤:ℕ∞))
  have hM := (conditionalFieldMean_smooth hF x hr.le hl hT0 hT1).of_le (by simp : (1:WithTop ℕ∞)≤(⊤:ℕ∞))
  have hm : ContDiff ℝ 1 (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) :=
    hM.sub contDiff_const
  have hmL : LipschitzWith ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩
      (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_right] using
      (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).dist_le_mul y z
  exact exists_skew_centering_flow hK hm
    (by positivity : 0≤(Real.exp (Real.pi^2/4)*(Real.pi^2/2))*((lam:ℝ)*r))
    (centeringKernel_norm_le hF x hr hlam hl hT0 hT1) hmL
    (interpolation_norm_integrable hF x hr hl hT0 hT1)
    (fun u φ hφ hφc => centeringKernel_weak hF x hr hlam hl hT0 hT1 u hφ hφc) hs hab

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GibbsOpenPos
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
open MeasureTheory MeasureTheory.Measure Function
open scoped Classical BigOperators RealInnerProductSpace NNReal

lemma gibbs_openPos {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) : IsOpenPosMeasure (gibbs H) := by
  have hd : Measurable (gibbsDensity H) := (Real.continuous_exp.comp hH.neg).measurable.ennreal_ofReal
  have hp : ∀ᵐ y : Point d ∂volume, gibbsDensity H y≠0 := Filter.Eventually.of_forall
    (fun y => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  let : IsOpenPosMeasure (volume.withDensity (gibbsDensity H)) :=
    (withDensity_absolutelyContinuous' hd.aemeasurable hp).isOpenPosMeasure
  exact isOpenPosMeasure_smul (volume.withDensity (gibbsDensity H))
    (ENNReal.inv_ne_zero.mpr (partition_ne_top_of_integrable hi))

lemma directional_adjoint_basis {d : ℕ} (A : Point d →L[ℝ] Point d)
    (u : Point d) (φ : Point d → ℝ) (y : Point d) :
    directional (A.adjoint u) φ y=∑i : Fin d,
      inner ℝ u (A (EuclideanSpace.basisFun (Fin d) ℝ i))*
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) φ y := by
  rw [directional_basis_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.repr_apply_apply,ContinuousLinearMap.adjoint_inner_right,real_inner_comm]

theorem stein_weak_to_strong {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    {K : Point d → (Point d →L[ℝ] Point d)} (hK : ContDiff ℝ 1 K)
    {m : Point d → Point d} (hm : Continuous m)
    (hw : ∀u φ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂gibbs H)=∫y,directional ((K y).adjoint u) φ y ∂gibbs H)
    (u : Point d) :
    tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (K y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (m y) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let V := fun (i : Fin d) y => inner ℝ u (K y (b i))
  have hV (i : Fin d) : ContDiff ℝ 1 (V i) :=
    contDiff_const.inner ℝ (hK.clm_apply contDiff_const)
  have hd : Continuous (tensorAdjoint H b V) := by
    apply continuous_finsetSum
    intro i _
    exact (((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
      (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)
  have hc : Continuous (fun y => inner ℝ u (m y)) := continuous_const.inner hm
  let : IsProbabilityMeasure (gibbs H) := probability_gibbs_of_partition
    (partition_pos_of_continuous hH.continuous).ne' (partition_ne_top_of_integrable hi)
  let : IsOpenPosMeasure (gibbs H) := gibbs_openPos hH.continuous hi
  apply Measure.eq_of_ae_eq (μ:=gibbs H) _ hd hc
  apply ae_eq_of_integral_contDiff_smul_eq (μ:=gibbs H) hd.locallyIntegrable hc.locallyIntegrable
  intro φ hφ hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hp := tensorAdjoint_compact_pairing hH hi hV hφ1 hφc b
  have ht := hw u φ hφ1 hφc
  simp only [smul_eq_mul]
  simp_rw [mul_comm (φ _)]; rw [hp,ht]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (directional_adjoint_basis (K y) u φ y).symm

theorem centeringKernel_strong {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (u : Point d) :
    tensorAdjoint (interpolationPotential F x r T) (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (centeringKernel hF x hr hl hT0 hT1 y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
  have hs := interpolationPotential_smooth hF x hr.le hl hT0 hT1
  have hi := (interpolationPotential_lowerTail hF x hr.le (by linarith only [hl]) hT0 hT1).integrable_exp hs.continuous
  apply stein_weak_to_strong (hs.of_le (by simp)) hi
    ((centeringKernel_smooth hF x hr hlam hl hT0 hT1).of_le (by simp))
    ((conditionalFieldMean_smooth hF x hr.le hl hT0 hT1).continuous.sub continuous_const) _ u
  intro u φ hφ hφc
  have hh := centeringKernel_weak hF x hr hlam hl hT0 hT1 u hφ hφc
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl])
    (by nlinarith [probability_time hT0 hT1])] at hh
  exact hh

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

end LogConcaveSampling

end

end

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

lemma skewLieField_coordinate {D : ℕ} (H : Point D → ℝ)
    (A : (Unit ⊕ Unit → Fin D) → Point D → ℝ) (y : Point D) (z : Fin D) :
    skewLieField H A y z=∑i : Fin D,adjointCoordinate H (EuclideanSpace.basisFun (Fin D) ℝ i)
      (A (Sum.elim (fun _ => i) (fun _ => z))) y := by
  simp [skewLieField,EuclideanSpace.basisFun_apply,Pi.single_apply]

lemma directional_gaussianPotential {d : ℕ} (v y : Point d) :
    directional v (fun z : Point d => ‖z‖^2/2) y=inner ℝ y v := by
  have hd := ((hasFDerivAt_id y).norm_sq.const_mul (1/2 : ℝ)).fderiv
  change (fderiv ℝ (fun z : Point d => ‖z‖^2/2) y) v=_
  have he : (fun z : Point d => ‖z‖^2/2)=(fun z : Point d => (1/2:ℝ)*‖z‖^2) := by funext z; ring
  dsimp only [id_eq] at hd
  rw [he,hd]
  simp

lemma adjointCoordinate_const_mul {d : ℕ} {H f : Point d → ℝ}
    (hf : Differentiable ℝ f) (v : Point d) (c : ℝ) :
    adjointCoordinate H v (fun y => c*f y)=fun y => c*adjointCoordinate H v f y := by
  unfold adjointCoordinate
  rw [directional_mul (differentiable_const c) hf]
  funext y
  simp only [directional,fderiv_fun_const]
  change -(0*f y+c*(fderiv ℝ f y) v)+(fderiv ℝ H y) v*(c*f y)=_
  ring

lemma adjointCoordinate_zero {d : ℕ} (H : Point d → ℝ) (v : Point d) :
    adjointCoordinate H v (fun _ => 0)=fun _ => 0 := by
  funext y
  simp [adjointCoordinate,directional]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AdjointCoordinateProductLeft
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
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma adjointCoordinate_product_left {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin d) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (fun z => f (productPointEquiv d e z).1) y=
      adjointCoordinate H (EuclideanSpace.basisFun (Fin d) ℝ i) f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_left hH hG,directional_comp_linear hf L]
  have hb := coordinateProjection_basis_in (leftCoordinates d e) i
  change L (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e)) = _ at hb
  rw [hb]
  simp only [L,coordinateProjection_left]

lemma adjointCoordinate_product_right {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin e) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (fun z => f (productPointEquiv d e z).1) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2*
        f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_right hH hG,directional_comp_linear hf L]
  have hb := congrArg Prod.fst (productPointEquiv_basis_right (d:=d) i)
  rw [←coordinateProjection_left] at hb
  change L _=0 at hb
  rw [hb]
  simp only [directional,map_zero,neg_zero,zero_add,L,coordinateProjection_left]

lemma jointSkewEntry_LL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.castAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,mul_zero]
lemma jointSkewEntry_RR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.natAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_right,mul_zero]
lemma jointSkewEntry_LR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.natAdd d)=fun y => s⁻¹*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right]
lemma jointSkewEntry_RL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.castAdd d)=fun y => (-s⁻¹)*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_neg,neg_mul]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InnerBasisCoordinate
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
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma inner_basis_coordinate {d : ℕ} (y : Point d) (i : Fin d) :
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) y=y i := by
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

theorem jointSkew_field {d : ℕ} {H : Point d → ℝ}
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hH : Differentiable ℝ H)
    (hK : ∀i j,Differentiable ℝ (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j))))
    (hstein : ∀u : Point d,tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (K y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (m y))
    (s : ℝ) (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
      (jointSkew K s) y)=skewCenteringField K m s (productPointEquiv d d y) := by
  let L := coordinateProjection (leftCoordinates d d)
  have hf (i j : Fin d) : Differentiable ℝ (fun z => inner ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d z).1 (EuclideanSpace.basisFun (Fin d) ℝ j))) :=
    (hK i j).comp L.differentiable
  have hG := (gaussianPotential_polySmooth d).smooth.differentiable (by simp)
  apply Prod.ext
  · ext z
    change skewLieField _ _ y (z.castAdd d)=(-s⁻¹ • (K (productPointEquiv d d y).1).adjoint
      (productPointEquiv d d y).2) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_LL,jointSkewEntry_RL,
      adjointCoordinate_zero,Finset.sum_const_zero,zero_add]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_right hH hG (hK _ _),directional_gaussianPotential]
    rw [←Finset.mul_sum]
    change (-s⁻¹)*(∑i : Fin d,inner ℝ (productPointEquiv d d y).2
      (EuclideanSpace.basisFun (Fin d) ℝ i)*inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ z)))=
      (-s⁻¹)*((K (productPointEquiv d d y).1).adjoint (productPointEquiv d d y).2) z
    congr 1
    rw [←inner_basis_coordinate,ContinuousLinearMap.adjoint_inner_right]
    simp_rw [real_inner_comm (productPointEquiv d d y).2,inner_basis_coordinate]
    rw [real_inner_comm,PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm,inner_basis_coordinate]
  · ext z
    change skewLieField _ _ y (z.natAdd d)=(s⁻¹ • m (productPointEquiv d d y).1) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_RR,jointSkewEntry_LR,
      adjointCoordinate_zero,Finset.sum_const_zero,add_zero]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_left hH hG (hK _ _)]
    rw [←Finset.mul_sum]
    change s⁻¹*tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i w => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ z)
        (K w (EuclideanSpace.basisFun (Fin d) ℝ i))) (productPointEquiv d d y).1=_
    rw [hstein]
    dsimp only
    rw [inner_basis_coordinate]
    rfl
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ActualJointCenteringFlow
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
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

theorem exists_actual_joint_centering_flow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) {s : ℝ} (hs : 0 < s) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      (∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (productPotential (interpolationPotential F x r T)
          (fun z : Point d => ‖z‖^2/2))
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (productPotential (interpolationPotential F x r T)
        (fun z : Point d => ‖z‖^2/2))).map (fun y => Ξ y t)=
        gibbs (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2))) := by
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_actual_centering_flow hF x hr hlam hl hT0 hT1 hs (by norm_num : (0:ℝ)≤1)
  let E := productPointEquiv d d
  let τ : ℝ → ℝ := fun t => min (max t 0) 1
  have hτ : Continuous τ := (continuous_id.max continuous_const).min continuous_const
  have hτmem (t : ℝ) : τ t∈Icc (0:ℝ) 1 :=
    ⟨le_min (le_max_right _ _) (by norm_num),min_le_right _ _⟩
  have hτeq (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : τ t=t := by
    exact (min_eq_left (by rw [max_eq_left ht.1]; exact ht.2)).trans (max_eq_left ht.1)
  let Ξ : Point (d+d) → ℝ → Point (d+d) := fun y t => E.symm (Ψ (E y) (τ t))
  have hΞc (y : Point (d+d)) : Continuous (Ξ y) := E.symm.continuous.comp ((hΨ (E y)).1.comp hτ)
  have hΞs (t : ℝ) : Continuous (fun y => Ξ y t) := E.symm.continuous.comp ((hc (τ t) (hτmem t)).comp E.continuous)
  have hH := interpolationPotential_smooth hF x hr.le hl hT0 hT1
  have hK (i j : Fin d) : Differentiable ℝ (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (centeringKernel hF x hr hl hT0 hT1 y (EuclideanSpace.basisFun (Fin d) ℝ j))) :=
    contDiff_const.inner ℝ ((centeringKernel_smooth hF x hr hlam hl hT0 hT1).clm_apply contDiff_const) |>.differentiable (by simp)
  let μ := gibbs (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2))
  let ν := (interpolationLaw F x r T).prod (stdGaussian (Point d))
  have hm : μ.map E=ν := by
    rw [productPotential_gibbs hH.continuous (gaussianPotential_polySmooth d).smooth.continuous,
      gaussianPotential_gibbs]
    dsimp only [ν]
    rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl]) (by nlinarith [probability_time hT0 hT1])]
  have hmi : ν.map E.symm=μ := by
    rw [←hm,Measure.map_map E.symm.continuous.measurable E.continuous.measurable]
    simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,Measure.map_id']
  refine ⟨Ξ,fun y => ⟨hΞc y,?_⟩,?_,?_,?_⟩
  · dsimp [Ξ]
    rw [hτeq 0 ⟨le_rfl,by norm_num⟩,(hΨ (E y)).2.1,E.symm_apply_apply]
  · intro y t ht
    have hd := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t ((hΨ (E y)).2.2 t ht)
    have hfield := jointSkew_field (hH.differentiable (by simp)) hK
      (centeringKernel_strong hF x hr hlam hl hT0 hT1) s (E.symm (Ψ (E y) t))
    change E _=skewCenteringField _ _ _ (E (E.symm (Ψ (E y) t))) at hfield
    rw [E.apply_symm_apply] at hfield
    have he := congrArg E.symm hfield
    rw [E.symm_apply_apply] at he
    change HasDerivWithinAt (fun u => E.symm (Ψ (E y) u))
      (E.symm (skewCenteringField _ _ _ (Ψ (E y) t))) _ _ at hd
    rw [←he] at hd
    have hde := hd.congr (f₁:=Ξ y) (fun u hu => by dsimp [Ξ]; rw [hτeq u hu])
      (by dsimp [Ξ]; rw [hτeq t ht])
    simpa only [Ξ,hτeq t ht] using hde
  · exact measurable_uncurry_of_continuous_of_measurable hΞc (fun t => (hΞs t).measurable)
  · intro t ht
    change μ.map (fun y => E.symm (Ψ (E y) (τ t)))=μ
    rw [hτeq t ht]
    have hc' := hc t ht
    calc
      _ = ((μ.map E).map (fun p => Ψ p t)).map E.symm := by
        rw [Measure.map_map E.symm.continuous.measurable hc'.measurable,
          Measure.map_map (E.symm.continuous.measurable.comp hc'.measurable) E.continuous.measurable]
        rfl
      _ = ν.map E.symm := by rw [hm,hlaw t ht]
      _ = μ := hmi
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_StationaryPath
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

theorem exists_centering_stationaryPath_oai {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T s : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s) :
    Nonempty (StationaryPath (gibbs (centeringPotential F x r T))
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s))) := by
  obtain ⟨Ξ,hc,hd,hm,hlaw⟩ := exists_actual_joint_centering_flow hF x hr hlam hl hT0 hT1 hs
  exact ⟨⟨Ξ,fun y => (hc y).1,fun y => (hc y).2,hd,hm,hlaw⟩⟩

end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.exists_centering_stationaryPath_oai := @OAI.LogConcaveSampling.exists_centering_stationaryPath_oai
