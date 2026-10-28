-- Prove2me | solution 1 for OAI.LogConcaveSampling.stationary_lie_taylor_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T14:04:14.257141+00:00
-- url     : https://prove2.me/submissions/2bf09c89-1556-4274-91cb-f402936c019b

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

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
lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ} (hf : ∀i∈s,PolyC1 (f i)) :
    PolyC1 (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),
    Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth),fun v => ?_⟩
  rw [directional_sum s (fun i hi => (hf i hi).differentiable)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).derivative_growth v)
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

lemma tensorAdjoint_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    {H g : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hV : ∀i,PolyC1 (V i)) (hg : PolyC1 g)
    (b : ι → Point d) :
    (∫x,tensorAdjoint H b V x*g x ∂gibbs H)=
      ∑i,∫x,V i x*directional (b i) g x ∂gibbs H := by
  have hi (i : ι) : Integrable (fun x => adjointCoordinate H (b i) (V i) x*g x) (gibbs H) := by
    apply integrable_polynomial_gibbs hH.continuous ht
    · exact (((hV i).directional_continuous _).neg.add
        (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)).mul hg.continuous
    · have hs : HasPolynomialGrowth (directional (b i) H) := by
        simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL (b i)
      exact Appell.HasGrowth.mul
        (Appell.HasGrowth.add (by
          simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) ((hV i).derivative_growth (b i)))
          (Appell.HasGrowth.mul hs (hV i).growth)) hg.growth
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_pairing hH ht hL (hV i) hg (b i))

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

lemma polyC1_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (b : ι → Point d) (hV : ∀i,PolyC1 (V i)) (hD : ∀i,PolyC1 (directional (b i) (V i))) :
    PolyC1 (tensorAdjoint H b V) :=
  PolyC1.sum Finset.univ (fun i _ => polyC1_adjointCoordinate hH hL (hV i) (b i) (hD i))

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

lemma directional_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i))
    (b : ι → Point d) (u : Point d) :
    directional u (tensorAdjoint H b V)=fun x =>
      tensorAdjoint H b (fun i => directional u (V i)) x+
      ∑i,directional u (directional (b i) H) x*V i x := by
  unfold tensorAdjoint
  rw [directional_sum Finset.univ
    (fun i _ => (adjointCoordinate_smooth hH (hV i) (b i)).differentiable (by simp))]
  simp_rw [directional_adjointCoordinate hH (hV _)]
  funext x
  exact Finset.sum_add_distrib

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
open scoped RealInnerProductSpace

lemma adjointCoordinate_continuous {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hf : PolyC1 f) (v : Point d) :
    Continuous (adjointCoordinate H v f) :=
  (hf.directional_continuous v).neg.add
    (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hf.continuous)

lemma adjointCoordinate_growth {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (v : Point d) :
    HasPolynomialGrowth (adjointCoordinate H v f) := by
  have hs : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  exact Appell.HasGrowth.add (by
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
      Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v))
    (Appell.HasGrowth.mul hs hf.growth)

lemma integrable_adjointCoordinate_mul {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    Integrable (fun x => adjointCoordinate H v f x*g x) (gibbs H) :=
  integrable_polynomial_gibbs hH.continuous ht
    ((adjointCoordinate_continuous hH hf v).mul hg.continuous)
    (Appell.HasGrowth.mul (adjointCoordinate_growth hL hf v) hg.growth)

theorem tensorAdjoint_energy_identity {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : ι → Point d)
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H)=
      ∑i,∑j,∫x,directional (b i) (V j) x*directional (b j) (V i) x+
        directional (b i) (directional (b j) H) x*V i x*V j x ∂gibbs H := by
  have hc : ContDiff ℝ 1 H := hH.of_le (by simp)
  have hA := polyC1_tensorAdjoint hH hL b hg (fun i => hD i i)
  have hs (i j : ι) : Integrable (fun x =>
      directional (b i) (directional (b j) H) x*V i x*V j x) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact integrable_polynomial_gibbs hc.continuous ht
      (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
      (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth)
  have hd (i j : ι) : Integrable (fun x => directional (b i) (V j) x*directional (b j) (V i) x) (gibbs H) :=
    integrable_polynomial_gibbs hc.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)
  have ha (i j : ι) : Integrable (fun x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x) (gibbs H) :=
    integrable_adjointCoordinate_mul hc ht hL (hD i j) (hg i) (b j)
  calc
    _ = ∫x,tensorAdjoint H b V x*tensorAdjoint H b V x ∂gibbs H := by simp only [pow_two]
    _ = ∑i,∫x,V i x*directional (b i) (tensorAdjoint H b V) x ∂gibbs H :=
      tensorAdjoint_pairing hc ht hL hg hA b
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun x => V i x*directional (b i) (tensorAdjoint H b V) x)=
          fun x => ∑j,(adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
            directional (b i) (directional (b j) H) x*V i x*V j x) := by
        rw [directional_tensorAdjoint hH hV]
        funext x
        simp only [tensorAdjoint,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
      rw [he,integral_finsetSum Finset.univ
        (f:=fun j x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
          directional (b i) (directional (b j) H) x*V i x*V j x)
        (fun j _ => (ha i j).add (hs i j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (ha i j) (hs i j),integral_add (hd i j) (hs i j),
        adjointCoordinate_pairing hc ht hL (hD i j) (hg i) (b j)]

end LogConcaveSampling
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

lemma matrix_cross_le_squares {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) :
    (∑i,∑j,a i j*a j i) ≤ ∑i,∑j,(a i j)^2 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈(Finset.univ:Finset ι)) =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈(Finset.univ:Finset ι)) =>
      show 2*(a i j*a j i) ≤ (a i j)^2+(a j i)^2 by nlinarith [sq_nonneg (a i j-a j i)]))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have he : (∑i,∑j,(a j i)^2)=∑i,∑j,(a i j)^2 := Finset.sum_comm
  rw [he] at hh
  linarith

lemma directional_hessian {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v x : Point d) :
    directional u (directional v H) x=inner ℝ (fderiv ℝ (gradient H) x u) v := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradient H) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp (hH.fderiv_right (by simp))
  have he : directional v H=(fun z => inner ℝ v (gradient H z)) := by
    funext z
    rw [directional_gradient,real_inner_comm]
  rw [he]
  have hd := (innerSL ℝ v).hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x) u=_
  have hde : fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x=
      (innerSL ℝ v).comp (fderiv ℝ (gradient H) x) := hd.fderiv
  rw [hde]
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm]

lemma hessian_quadratic_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {K : ℝ≥0} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (a : ι → ℝ) (x : Point d) :
    (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j) ≤
      (K:ℝ)*∑i,(a i)^2 := by
  classical
  let z : Point d := ∑i,a i • b i
  have hz (i : ι) : inner ℝ (b i) z=a i := by
    simp [z,inner_sum,inner_smul_right,orthonormal_iff_ite.mp b.orthonormal]
  have hn : ‖z‖^2=∑i,(a i)^2 := by simpa only [hz] using (b.sum_sq_inner_right z).symm
  have he : (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j)=
      inner ℝ (fderiv ℝ (gradient H) x z) z := by
    simp only [z,map_sum,map_smul,directional_hessian hH,sum_inner,inner_smul_left,
      inner_sum,inner_smul_right,starRingEnd_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsym := congrFun (directional_commute hH (b i) (b j)) x
    rw [directional_hessian hH,directional_hessian hH] at hsym
    rw [hsym]
    ring
  rw [he]
  have h₁ := real_inner_le_norm (fderiv ℝ (gradient H) x z) z
  have h₂ := (fderiv ℝ (gradient H) x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hL) z
  exact h₁.trans ((mul_le_mul_of_nonneg_right h₂ (norm_nonneg z)).trans_eq (by calc
    (K:ℝ)*‖z‖*‖z‖=(K:ℝ)*‖z‖^2 := by ring
    _ = _ := by rw [hn]))

end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma integrable_directional_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (b : ι → Point d)
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    Integrable (fun x => ∑i,∑j,(directional (b i) (V j) x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_polynomial_gibbs hH ht ((hD i j).continuous.pow 2)
    (Appell.HasGrowth.pow (hD i j).growth 2)

lemma integrable_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (hV : ∀i,PolyC1 (V i)) :
    Integrable (fun x => ∑i,(V i x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  exact integrable_polynomial_gibbs hH ht ((hV i).continuous.pow 2)
    (Appell.HasGrowth.pow (hV i).growth 2)

theorem tensorAdjoint_energy_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H) ≤
      (∫x,∑i,∑j,(directional (b i) (V j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∫x,∑i,(V i x)^2 ∂gibbs H) := by
  let W : ι → ι → Point d → ℝ := fun i j x =>
    directional (b i) (V j) x*directional (b j) (V i) x+
    directional (b i) (directional (b j) H) x*V i x*V j x
  have hi (i j : ι) : Integrable (W i j) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact (integrable_polynomial_gibbs hH.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)).add
      (integrable_polynomial_gibbs hH.continuous ht
        (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
        (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth))
  have hirow (i : ι) : Integrable (fun x => ∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hiW : Integrable (fun x => ∑i,∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun i _ => hirow i)
  have hiD := integrable_directional_square_sum hH.continuous ht b hD
  have hiV := integrable_square_sum hH.continuous ht hg
  calc
    _ = ∑i,∑j,∫x,W i j x ∂gibbs H := tensorAdjoint_energy_identity hH ht hL b hV hg hD
    _ = ∫x,∑i,∑j,W i j x ∂gibbs H := by
      rw [integral_finsetSum Finset.univ (fun i _ => hirow i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ ≤ ∫x,((∑i,∑j,(directional (b i) (V j) x)^2)+(K:ℝ)*(∑i,(V i x)^2)) ∂gibbs H := by
      apply integral_mono hiW (hiD.add (hiV.const_mul (K:ℝ)))
      intro x
      simp only [W,Finset.sum_add_distrib]
      exact add_le_add (matrix_cross_le_squares (fun i j => directional (b i) (V j) x))
        (hessian_quadratic_le hH hL b (fun i => V i x) x)
    _ = _ := by
      rw [integral_add (f:=fun x => ∑i,∑j,(directional (b i) (V j) x)^2)
        (g:=fun x => (K:ℝ)*(∑i,(V i x)^2)) hiD (hiV.const_mul (K:ℝ)),integral_const_mul]

theorem tensorAdjoint_frobenius_squared {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {H : Point d → ℝ} {V : κ → ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀a i,ContDiff ℝ (⊤ : ℕ∞) (V a i)) (hg : ∀a i,PolyC1 (V a i))
    (hD : ∀a i j,PolyC1 (directional (b i) (V a j))) :
    (∑a,∫x,(tensorAdjoint H b (V a) x)^2 ∂gibbs H) ≤
      (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∑a,∫x,∑i,(V a i x)^2 ∂gibbs H) := by
  simpa only [Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_ : a∈(Finset.univ:Finset κ)) =>
      tensorAdjoint_energy_le hH ht hL b (hV a) (hg a) (hD a))

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ForestTensor
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

lemma AllSplitBound.singleContract_frobenius {d : ℕ} {S T : Type}
    [Fintype S] [Nonempty S] [Fintype T]
    {A : (S ⊕ Unit → Fin d) → ℝ} {M : ℝ}
    (hA : AllSplitBound A M) (B : (T ⊕ Unit → Fin d) → ℝ) :
    (∑c,(TensorEnergy.singleContract A B c)^2)≤M^2*(∑c,(B c)^2) := by
  have ha : Bound (fun (s : S → Fin d) (z : Fin d) => A (Sum.elim s (fun _ => z))) (M^2) := by
    convert (hA Unit S (Equiv.sumComm S Unit)).reindex
      (Equiv.refl (S → Fin d)) (Equiv.funUnique Unit (Fin d)).symm using 1
    all_goals try with_reducible_and_instances rfl
    funext s z
    congr 1
    funext t
    cases t <;> rfl
  have he (t : T → Fin d) :
      (∑s : S → Fin d,(∑z : Fin d,A (Sum.elim s (fun _ => z))*B (Sum.elim t (fun _ => z)))^2)≤
        M^2*∑z : Fin d,(B (Sum.elim t (fun _ => z)))^2 := ha (fun z => B (Sum.elim t (fun _ => z)))
  have hu := Equiv.sum_comp (Equiv.sumArrowEquivProdArrow S T (Fin d)).symm
    (fun c => (TensorEnergy.singleContract A B c)^2)
  rw [Fintype.sum_prod_type] at hu
  rw [←hu,Finset.sum_comm]
  have hb := Equiv.sum_comp (appendCoordinate (d:=d) T) (fun c => (B c)^2)
  rw [Fintype.sum_prod_type] at hb
  rw [←hb,Finset.mul_sum]
  exact Finset.sum_le_sum (fun t _ => he t)

end LogConcaveSampling.TensorEnergy

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

lemma spatialInside_polySmooth {K S : Type} {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) (z : Fin d) : PolySmooth (spatialInside F l c z) :=
  (hF _).jet _ l

end LogConcaveSampling

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
open scoped Classical BigOperators

namespace TensorEnergy

lemma sum_fintype_irrel {α : Type} (i j : Fintype α) (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i) f = @Finset.sum α ℝ _ (@Finset.univ α j) f := by
  cases Subsingleton.elim i j
  rfl

lemma squared_nonneg {S : Type} [Fintype S] {d : ℕ} (T : (S → Fin d) → ℝ) : 0 ≤ squared T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
lemma squared_reindex {S T : Type} [Fintype S] [Fintype T] {d : ℕ}
    (A : (S → Fin d) → ℝ) (e : S ≃ T) : squared (fun c => A (c ∘ e))=squared A := by
  exact Equiv.sum_comp ((Equiv.arrowCongr e (Equiv.refl (Fin d))).symm) (fun c => (A c)^2)
lemma squared_sum {S I : Type} [Fintype S] {d : ℕ} (s : Finset I)
    (A : I → (S → Fin d) → ℝ) :
    squared (fun c => ∑i∈s,A i c) ≤ s.card*(∑i∈s,squared (A i)) := by
  apply (Finset.sum_le_sum (fun _ _ => sq_sum_le_card_mul_sum_sq)).trans_eq
  rw [←Finset.mul_sum,Finset.sum_comm]
  rfl
lemma squared_add {S : Type} [Fintype S] {d : ℕ} (A B : (S → Fin d) → ℝ) :
    squared (fun c => A c+B c) ≤ 2*(squared A+squared B) := by
  apply (Finset.sum_le_sum (fun c _ => show (A c+B c)^2 ≤ 2*((A c)^2+(B c)^2) by nlinarith [sq_nonneg (A c-B c)])).trans_eq
  simp only [squared]
  rw [←Finset.mul_sum,←Finset.sum_add_distrib]
end TensorEnergy
open TensorEnergy

lemma spatialSquared_full {S K : Type} [Fintype S] [Fintype K] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    squared (spatialTensor F l y)=spatialSquared F (Fintype.card K) y := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := squared_reindex (spatialTensor F (List.finRange (Fintype.card K)) y) (e.sumCongr (Equiv.refl S))
  have he : (fun c => spatialTensor F (List.finRange (Fintype.card K)) y (c ∘ (e.sumCongr (Equiv.refl S))))=
      spatialTensor F l y := by
    funext c
    simpa only [Function.comp_def,Equiv.refl_apply] using
      spatialTensor_relabel F hF (Equiv.refl S) e _ _ hp y c
  rw [he] at hh
  exact hh

lemma extendedSpatial_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    squared (extendedSpatial F l y)=squared (spatialTensor F l y) :=
  squared_reindex _ (Equiv.sumAssoc K S Unit).symm

lemma spatialContractTerm_squared {d : ℕ} {S T K : Type} [Fintype S]
    [Fintype T] [Fintype K] (p : K → Prop) [DecidablePred p] [Nonempty ({k // p k} ⊕ S)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) {M : ℝ}
    (hF : AllSplitBound (spatialTensor F (selectList p l) y) M) :
    squared (spatialContractTerm p F G l y) ≤ M^2*spatialSquared G (Fintype.card {k // ¬p k}) y := by
  have hr := squared_reindex
    (singleContract (extendedSpatial F (selectList p l) y)
      (extendedSpatial G (selectList (fun k => ¬p k) l) y)) (contractSpatialSlots p)
  change squared (spatialContractTerm p F G l y)=_ at hr
  rw [hr]
  have ha : AllSplitBound (extendedSpatial F (selectList p l) y) M := extendedSpatial_allSplit hF
  have hh := AllSplitBound.singleContract_frobenius ha (extendedSpatial G (selectList (fun k => ¬p k) l) y)
  have he : squared (extendedSpatial G (selectList (fun k => ¬p k) l) y)=
      spatialSquared G (Fintype.card {k // ¬p k}) y := by
    rw [extendedSpatial_squared,spatialSquared_full G hG _
      (selectList_nodup _ hl) (selectList_full _ hall)]
  exact (sum_fintype_irrel _ _ _).trans_le (hh.trans_eq
    (congrArg (fun x => M^2*x) ((sum_fintype_irrel _ _ _).trans he)))

lemma spatialSquared_contract {d j : ℕ} {S T : Type} [Fintype S] [Nonempty S] [Fintype T]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (M : ℕ → ℝ) (y : Point d)
    (hb : ∀k ≤ j,AllSplitBound (spatialTensor F (List.finRange k) y) (M k)) :
    spatialSquared (fun a z => singleContract (fun c => F c z) (fun c => G c z) a) j y ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(M s.card)^2*spatialSquared G (j-s.card) y := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by ext k; simp
  have he : spatialTensor (fun a z => singleContract (fun c => F c z) (fun c => G c z) a) (List.finRange j) y=
      fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialContractTerm (fun k => k∈s) F G (List.finRange j) y c := by
    funext c
    simpa only [heq] using spatialTensor_singleContract F G hF hG _ (List.nodup_finRange _) y c
  unfold spatialSquared
  rw [he]
  apply (TensorEnergy.squared_sum _ _).trans
  simp only [Finset.card_powerset,Finset.card_univ,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s _
  have hs : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
  have hr : AllSplitBound (spatialTensor F (selectList (fun k => k∈s) (List.finRange j)) y) (M s.card) := by
    let e := (Fintype.equivFin s).symm
    have hp : ((List.finRange (Fintype.card s)).map e).Perm
        (selectList (fun k => k∈s) (List.finRange j)) :=
      fullList_perm ((List.nodup_finRange _).map e.injective) (selectList_nodup _ (List.nodup_finRange _))
        (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩)
        (selectList_full _ (by simp))
    have hcard : Fintype.card s=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    have hh := spatialTensor_allSplit_relabel F hF (Equiv.refl _) e _ _ hp y (M s.card)
      (by rw [hcard]; exact hb s.card hs)
    simpa only [Function.comp_def,Equiv.refl_apply] using hh
  have hcard : Fintype.card {k : Fin j // k∉s}=j-s.card := by
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hc,Fintype.card_fin]
  have hh := spatialContractTerm_squared (fun k => k∈s) F G hG _ (List.nodup_finRange _) (by simp) y hr
  simp only [Fintype.card_eq_nat_card] at hcard hh
  rw [hcard] at hh
  exact hh

end LogConcaveSampling

end

end

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

lemma spatialEnergy_contract {d j : ℕ} {S T : Type} [Fintype S] [Nonempty S] [Fintype T]
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (M : ℕ → ℝ)
    (hb : ∀k ≤ j,∀y,AllSplitBound (spatialTensor F (List.finRange k) y) (M k)) :
    spatialEnergy (fun a y => singleContract (fun c => F c y) (fun c => G c y) a) j (gibbs H) ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(M s.card)^2*spatialEnergy G (j-s.card) (gibbs H) := by
  have hs (k : ℕ) := (spatialSquared_polySmooth G hG k).integrable hH ht
  have hi := (spatialSquared_polySmooth _ (singleContract_polySmooth F G hF hG) j).integrable hH ht
  have hj := (integrable_finsetSum (Finset.univ : Finset (Fin j)).powerset
    (fun s _ => (hs (j-s.card)).const_mul ((M s.card)^2))).const_mul ((2:ℝ)^j)
  apply (integral_mono hi hj (fun y => spatialSquared_contract F G (fun c => (hF c).smooth)
    (fun c => (hG c).smooth) M y (fun k hk => hb k hk y))).trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun s _ => (hs (j-s.card)).const_mul ((M s.card)^2))]
  simp only [integral_const_mul,spatialEnergy]

lemma spatialInside_zero_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    (∑c,∑z : Fin d,(spatialInside F l c z y)^2)=squared (spatialTensor F l y) := by
  have hh := Equiv.sum_comp (insideZeroColor K S d) (fun c => (spatialTensor F l y c)^2)
  rw [Fintype.sum_prod_type] at hh
  exact hh.trans (sum_fintype_irrel _ _ _)

lemma spatialInside_one_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    (∑c,∑i : Fin d,∑z : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (spatialInside F l c z) y)^2)=
      squared (spatialTensor F (([()] : List Unit).map Sum.inl++l.map Sum.inr) y) := by
  have hh := Equiv.sum_comp (insideOneColor K S d)
    (fun c => (spatialTensor F (([()] : List Unit).map Sum.inl++l.map Sum.inr) y c)^2)
  simp only [Fintype.sum_prod_type] at hh
  refine Eq.trans ?_ (hh.trans (sum_fintype_irrel _ _ _))
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  unfold spatialTensor spatialInside
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  rfl

lemma spatialAdjointLeading_energy {d j : ℕ} {S : Type} [Fintype S]
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) :
    (∫y,squared (spatialAdjointLeading H F (List.finRange j) y) ∂gibbs H) ≤
      spatialEnergy F (j+1) (gibbs H)+(K:ℝ)*spatialEnergy F j (gibbs H) := by
  let V := spatialInside F (List.finRange j)
  have hV c z : PolySmooth (V c z) := spatialInside_polySmooth F hF _ c z
  have hi c := (hH.tensorAdjoint (hV c) (EuclideanSpace.basisFun (Fin d) ℝ)).sq.integrable hH.smooth.continuous ht
  have hi0 c := integrable_square_sum hH.smooth.continuous ht (fun z => (hV c z).polyC1)
  have hi1 c := integrable_directional_square_sum hH.smooth.continuous ht (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun _ z => ((hV c z).directional _).polyC1)
  have hh := tensorAdjoint_frobenius_squared hH.smooth ht hL (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun c z => (hV c z).smooth) (fun c z => (hV c z).polyC1) (fun c _ z => ((hV c z).directional _).polyC1)
  rw [←integral_finsetSum _ (fun c _ => hi c),←integral_finsetSum _ (fun c _ => hi1 c),
    ←integral_finsetSum _ (fun c _ => hi0 c)] at hh
  have hleft : (∫y,squared (spatialAdjointLeading H F (List.finRange j) y) ∂gibbs H)=
      ∫y,∑c,(tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (V c) y)^2 ∂gibbs H := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact sum_fintype_irrel _ _ _
  rw [←hleft] at hh
  have hz (y : Point d) : (∑c,∑z : Fin d,(V c z y)^2)=spatialSquared F j y := by
    exact (sum_fintype_irrel _ _ _).trans (spatialInside_zero_squared F _ y)
  have he (y : Point d) := spatialSquared_full F (fun c => (hF c).smooth)
    (([()] : List Unit).map Sum.inl++(List.finRange j).map Sum.inr)
    (JetCalculus.nodup_sum_append (by simp) (List.nodup_finRange _))
    (by intro a; cases a <;> simp) y
  simp only [Fintype.card_sum,Fintype.card_unique,Fintype.card_fin,Nat.add_comm 1] at he
  have ho (y : Point d) : (∑c,∑i : Fin d,∑z : Fin d,
      (directional (EuclideanSpace.basisFun (Fin d) ℝ i) (V c z) y)^2)=spatialSquared F (j+1) y := by
    exact (sum_fintype_irrel _ _ _).trans ((spatialInside_one_squared F _ y).trans (he y))
  simp_rw [hz,ho] at hh
  exact hh

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

lemma finset_sum_le_sum_of_eq {α : Type} (s t : Finset α) (f g : α → ℝ)
    (he : s=t) (h : ∀a∈s,f a ≤ g a) : (∑a∈s,f a) ≤ ∑a∈t,g a := by
  subst t
  exact Finset.sum_le_sum h

lemma adjointCommutator_squared {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : ContDiff ℝ (⊤:ℕ∞) H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (y : Point d) (M : ℕ → ℝ)
    (hM : ∀e,0<e → e ≤ j → AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    squared (adjointCommutator H F (List.finRange j) y) ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
        (M s.card)^2*spatialSquared F (j-s.card) y := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by ext k; simp
  unfold adjointCommutator
  rw [heq]
  apply (squared_sum _ _).trans
  have hc : (((Finset.univ : Finset (Fin j)).powerset.erase ∅).card : ℝ) ≤ 2^j := by
    exact_mod_cast (Finset.card_erase_le.trans_eq (by simp :
      (Finset.univ : Finset (Fin j)).powerset.card=2^j))
  apply (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun s _ => squared_nonneg _))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply finset_sum_le_sum_of_eq
  · ext s; simp
  intro s hs
  have hs0 : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
  let : Nonempty {k // k∈s} := ⟨⟨hs0.choose,hs0.choose_spec⟩⟩
  have hh := scoreField_arbitrary_allSplit hH (selectList (fun k => k∈s) (List.finRange j))
    (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y (M s.card)
    (by
      have hc : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
      rw [hc]
      exact hM s.card hs0.card_pos ((Finset.card_le_univ s).trans_eq (Fintype.card_fin j)))
  rw [squared_reindex]
  have hb := spatialContractTerm_squared (fun k => k∈s) (scoreField H) F hF _ (List.nodup_finRange _) (by simp) y hh
  have hc : Fintype.card {k : Fin j // k∉s}=j-s.card := by
    rw [Fintype.card_subtype_compl]
    have hs' : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hs',Fintype.card_fin]
  simp only [Fintype.card_eq_nat_card] at hb hc
  rw [hc] at hb
  exact hb

lemma tensorAdjoint_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (a : S → Fin d) : PolySmooth
      (tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => F (Sum.elim a (fun _ => z)))) :=
  hH.tensorAdjoint (fun _ => hF _) _

lemma spatialEnergy_adjoint {d j : ℕ} {S : Type} [Fintype S]
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (M : ℕ → ℝ)
    (hM : ∀e,0<e → e ≤ j → ∀y, AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    spatialEnergy (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j (gibbs H) ≤
      2*(spatialEnergy F (j+1) (gibbs H)+(K:ℝ)*spatialEnergy F j (gibbs H)+
        2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (M s.card)^2*spatialEnergy F (j-s.card) (gibbs H)) := by
  have hlead : Integrable (fun y => squared (spatialAdjointLeading H F (List.finRange j) y)) (gibbs H) :=
    integrable_finsetSum _ (fun c _ =>
      (hH.tensorAdjoint (fun z => spatialInside_polySmooth F hF _ c z) _).sq.integrable hH.smooth.continuous ht)
  have hf k := (spatialSquared_polySmooth F hF k).integrable hH.smooth.continuous ht
  have hsum := (integrable_finsetSum ((Finset.univ : Finset (Fin j)).powerset.erase ∅)
    (fun s _ => (hf (j-s.card)).const_mul ((M s.card)^2))).const_mul ((2:ℝ)^j)
  have hbase := (spatialSquared_polySmooth _ (tensorAdjoint_polySmooth hH F hF) j).integrable hH.smooth.continuous ht
  have hp (y : Point d) : spatialSquared (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j y ≤
      2*(squared (spatialAdjointLeading H F (List.finRange j) y)+
        2^j * ∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (M s.card)^2*spatialSquared F (j-s.card) y) := by
    unfold spatialSquared
    rw [spatialTensor_adjoint_sum hH F hF _ (List.nodup_finRange _) y]
    apply (squared_add _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add le_rfl
    exact adjointCommutator_squared hH.smooth F (fun c => (hF c).smooth) y M (fun e he hj => hM e he hj y)
  have hh := integral_mono hbase ((hlead.add hsum).const_mul 2) hp
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hlead hsum,integral_const_mul,
    integral_finsetSum _ (fun s _ => (hf (j-s.card)).const_mul ((M s.card)^2))] at hh
  simp only [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add
    (spatialAdjointLeading_energy hH ht hL F hF) le_rfl) (by norm_num))

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

lemma spatialSquared_reindex {S T : Type} [Fintype S] [Fintype T] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (e : S ≃ T) (y : Point d) :
    spatialSquared (fun c => F (c ∘ e)) j y=spatialSquared F j y := by
  have he : spatialTensor (fun c => F (c ∘ e)) (List.finRange j) y=
      fun c => spatialTensor F (List.finRange j) y (c ∘ (Equiv.sumCongr (Equiv.refl (Fin j)) e)) := by
    funext c
    symm
    exact spatialTensor_relabel F hF e (Equiv.refl _) _ _ (by simp) y c
  unfold spatialSquared
  rw [he]
  exact squared_reindex _ _

lemma spatialEnergy_reindex {S T : Type} [Fintype S] [Fintype T] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (e : S ≃ T) (μ : Measure (Point d)) :
    spatialEnergy (fun c => F (c ∘ e)) j μ=spatialEnergy F j μ := by
  unfold spatialEnergy
  congr 1
  funext y
  exact spatialSquared_reindex F hF e y

lemma tensorGrad_polySmooth {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S ⊕ Unit → Fin d) : PolySmooth (tensorGrad F c) :=
  (hF _).directional _

lemma spatialTensor_grad {S K : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (l : List K) (y : Point d) (c : K ⊕ (S ⊕ Unit) → Fin d) :
    spatialTensor (tensorGrad F) l y c=
      spatialTensor F (l.map Sum.inl++([()] : List Unit).map Sum.inr) y (c ∘ gradSpatialSlots K S) := by
  unfold spatialTensor tensorGrad
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  rfl

lemma spatialSquared_grad {S : Type} [Fintype S] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (y : Point d) :
    spatialSquared (tensorGrad F) j y=spatialSquared F (j+1) y := by
  unfold spatialSquared
  have he : spatialTensor (tensorGrad F) (List.finRange j) y=
      fun c => spatialTensor F ((List.finRange j).map Sum.inl++([()] : List Unit).map Sum.inr) y
        (c ∘ gradSpatialSlots (Fin j) S) := funext (spatialTensor_grad F _ y)
  rw [he,squared_reindex]
  have hh := spatialSquared_full F hF ((List.finRange j).map Sum.inl++([()] : List Unit).map Sum.inr)
    (JetCalculus.nodup_sum_append (List.nodup_finRange _) (by simp))
    (by intro k; cases k <;> simp) y
  have hc : Fintype.card (Fin j ⊕ Unit)=j+1 := by simp
  simp only [Fintype.card_eq_nat_card] at hh hc
  rw [hc] at hh
  exact hh

lemma spatialEnergy_grad {S : Type} [Fintype S] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (μ : Measure (Point d)) :
    spatialEnergy (tensorGrad F) j μ=spatialEnergy F (j+1) μ := by
  unfold spatialEnergy
  congr 1
  funext y
  exact spatialSquared_grad F hF y

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

lemma productEnergyBudget_mono (C : ℕ → ℝ) {E G : ℕ → ℝ} (j : ℕ)
    (h : ∀k,0<k → k ≤ j+1 → E k ≤ G k) : productEnergyBudget C E j ≤ productEnergyBudget C G j := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (h _ (by omega) (by omega)) (sq_nonneg _)

lemma adjointEnergyBudget_mono {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ) {E G : ℕ → ℝ} (j : ℕ)
    (h : ∀k ≤ j+1,E k ≤ G k) : adjointEnergyBudget K C E j ≤ adjointEnergyBudget K C G j := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · exact add_le_add (h _ le_rfl) (mul_le_mul_of_nonneg_left (h _ (by omega)) hK)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h _ (by omega)) (sq_nonneg _))

lemma lieInside_energy {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (C : ℕ → ℝ)
    (hb : ∀k ≤ j,∀y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k)) :
    spatialEnergy (lieInside A F) j (gibbs H) ≤ productEnergyBudget C (fun k => spatialEnergy F k (gibbs H)) j := by
  have hg := tensorGrad_polySmooth F hF
  have hh := spatialEnergy_contract hH ht A (tensorGrad F) hA hg C hb
  have he := spatialEnergy_reindex (j:=j) (fun c y => singleContract (fun a => A a y) (fun a => tensorGrad F a y) c)
    (fun c => (singleContract_polySmooth A (tensorGrad F) hA hg c).smooth) (Equiv.sumComm Unit S) (gibbs H)
  change spatialEnergy (lieInside A F) j (gibbs H)=_ at he
  rw [he]
  simp_rw [spatialEnergy_grad F (fun c => (hF c).smooth)] at hh
  exact hh

lemma tensorLie_energy {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (C D : ℕ → ℝ)
    (hb : ∀k ≤ j+1,∀y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k))
    (hs : ∀k,0<k → k ≤ j → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k)) :
    spatialEnergy (tensorLie H A F) j (gibbs H) ≤
      adjointEnergyBudget K D (productEnergyBudget C (fun k => spatialEnergy F k (gibbs H))) j := by
  have he := spatialEnergy_adjoint hH ht hL (lieInside A F) (lieInside_polySmooth A F hA hF) D hs
  apply he.trans
  exact adjointEnergyBudget_mono K.2 D j (fun k hk =>
    lieInside_energy hH.smooth.continuous ht A F hA hF C (fun i hi => hb i (hi.trans hk)))

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

lemma productEnergyBudget_scaled (C B : ℕ → ℝ) (α κ ρ : ℝ) (j : ℕ) :
    productEnergyBudget (fun k => C k*α*ρ^k) (fun k => κ*ρ^(2*k)*B k) j =
      κ*α^2*ρ^(2*(j+1))*productEnergyBudget C B j := by
  unfold productEnergyBudget
  calc
    _ = 2^j*(κ*α^2*ρ^(2*(j+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset,
        (C s.card)^2*B (j-s.card+1)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hc : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
      have hp : (ρ^s.card)^2*ρ^(2*(j-s.card+1))=ρ^(2*(j+1)) := by
        rw [← pow_mul,← pow_add]
        congr 1
        omega
      calc
        (C s.card*α*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+1))*B (j-s.card+1)) =
          κ*α^2*((ρ^s.card)^2*ρ^(2*(j-s.card+1)))*((C s.card)^2*B (j-s.card+1)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by ring

lemma adjointEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀j,0 ≤ B j) (j : ℕ) : 0 ≤ adjointEnergyBudget K C B j := by
  unfold adjointEnergyBudget
  apply mul_nonneg (by norm_num)
  apply add_nonneg (add_nonneg (hB _) (mul_nonneg hK (hB _)))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hB _)))

lemma adjointEnergyBudget_scaled {K κ ρ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ)
    (D B : ℕ → ℝ) (hB : ∀j,0 ≤ B j) (q j : ℕ) :
    adjointEnergyBudget K (fun k => D k*ρ^k) (fun k => κ*ρ^(2*(k+q))*B k) j ≤
      κ*ρ^(2*(j+q+1))*adjointEnergyBudget K D B j := by
  have hr : 0 ≤ ρ := zero_le_one.trans hρ
  have hp : ρ^(2*(j+q)) ≤ ρ^(2*(j+q+1)) := pow_le_pow_right₀ hρ (by omega)
  have hlead : κ*ρ^(2*(j+1+q))*B (j+1)=κ*ρ^(2*(j+q+1))*B (j+1) := by rw [show j+1+q=j+q+1 by omega]
  have hs : (∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
      (D s.card*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+q))*B (j-s.card))) ≤
      κ*ρ^(2*(j+q+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
        (D s.card)^2*B (j-s.card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hc : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
    have he : (ρ^s.card)^2*ρ^(2*(j-s.card+q))=ρ^(2*(j+q)) := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    calc
      (D s.card*ρ^s.card)^2*(κ*ρ^(2*(j-s.card+q))*B (j-s.card)) =
        κ*((ρ^s.card)^2*ρ^(2*(j-s.card+q)))*((D s.card)^2*B (j-s.card)) := by ring
      _ = κ*ρ^(2*(j+q))*((D s.card)^2*B (j-s.card)) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ)
        (mul_nonneg (sq_nonneg _) (hB _))
  unfold adjointEnergyBudget
  calc
    _ ≤ 2*(κ*ρ^(2*(j+q+1))*B (j+1)+K*(κ*ρ^(2*(j+q+1))*B j)+
        2^j*(κ*ρ^(2*(j+q+1))*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (D s.card)^2*B (j-s.card))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact add_le_add hlead.le (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ) (hB _)) hK)
      · exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end LogConcaveSampling

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

lemma tensorLie_scaled_energy {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) (hB : ∀k,0 ≤ B k)
    (hb : ∀k y, AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H) ≤ κ*ρ^(2*k)*B k) (j : ℕ) :
    spatialEnergy (tensorLie H A F) j (gibbs H) ≤
      κ*α^2*ρ^(2*(j+2))*adjointEnergyBudget K D (productEnergyBudget C B) j := by
  have hi (k : ℕ) : productEnergyBudget (fun k => C k*α*ρ^k)
      (fun k => spatialEnergy F k (gibbs H)) k ≤
      κ*α^2*ρ^(2*(k+1))*productEnergyBudget C B k := by
    apply (productEnergyBudget_mono _ k (fun i hi _ => he i hi)).trans_eq
    exact productEnergyBudget_scaled C B α κ ρ k
  have hstep := tensorLie_energy (j:=j) hH ht hL A F hA hF
    (fun k => C k*α*ρ^k) (fun k => D k*ρ^k) (fun k _ => hb k) (fun k hk _ => hs k hk)
  have hm := adjointEnergyBudget_mono K.2 (fun k => D k*ρ^k) j (fun k _ => hi k)
  have hscale := adjointEnergyBudget_scaled K.2 (mul_nonneg hκ (sq_nonneg α)) hρ
    D (productEnergyBudget C B) (productEnergyBudget_nonneg hB) 1 j
  apply (hstep.trans (hm.trans hscale)).trans_eq
  rw [show j+1+1=j+2 by omega]
  congr 1

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

theorem iterTensorLie_energy {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) (hB : ∀k,0 ≤ B k)
    (hb : ∀k y, AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H) ≤ κ*ρ^(2*k)*B k)
    (n j : ℕ) (hj : 0<n ∨ 0<j) :
    spatialEnergy (iterTensorLie H A F n) j (gibbs H) ≤
      κ*(α^2*ρ^4)^n*ρ^(2*j)*iterEnergyBudget K C D B n j := by
  induction n generalizing j with
  | zero => simpa [iterTensorLie,iterEnergyBudget] using he j (by omega)
  | succ n ih =>
    have hn : 0 ≤ κ*(α^2*ρ^4)^n := mul_nonneg hκ (pow_nonneg (mul_nonneg (sq_nonneg α) (by positivity)) _)
    have hh := tensorLie_scaled_energy hH ht hL A (iterTensorLie H A F n) hA
      (iterTensorLie_polySmooth hH A F hA hF n) C D (iterEnergyBudget K C D B n) hn hρ
      (iterEnergyBudget_nonneg K.2 C D hB n) hb hs (fun k hk => ih k (Or.inr hk)) j
    apply hh.trans_eq
    dsimp [iterEnergyBudget]
    rw [show 2*(j+2)=2*j+4 by omega,pow_add,pow_succ]
    ring

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

lemma spatialSquared_zero {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    spatialSquared F 0 y=∑c,(F c y)^2 := by
  have he : spatialTensor F (List.finRange 0) y=
      fun c => F (c ∘ (Equiv.emptySum (Fin 0) S).symm) y := rfl
  unfold spatialSquared
  rw [he]
  exact squared_reindex (fun c => F c y) (Equiv.emptySum (Fin 0) S).symm

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

lemma lie_chain {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) (c : S → Fin d) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => iterTensorLie H A F n c (γ u))
      (iterTensorLie H A F (n+1) c (γ t)) s t := by
  have hf := (iterTensorLie_polySmooth hH A F hA hF n c).smooth.differentiable (by simp)
  have hd := (hf (γ t)).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  change HasDerivWithinAt ((iterTensorLie H A F n c) ∘ γ)
    (tensorLie H A (iterTensorLie H A F n) c (γ t)) s t
  rw [tensorLie_eq_directional H A (iterTensorLie H A F n)
    (fun c => (hA c).smooth) (fun c => (iterTensorLie_polySmooth hH A F hA hF n c).smooth)
    hsk c (γ t)]
  exact hd

lemma tensorVector_norm_sq {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    ‖tensorVector F y‖^2=∑c,(F c y)^2 := EuclideanSpace.real_norm_sq_eq _

lemma tensorVector_contDiff {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) :
    ContDiff ℝ (⊤:ℕ∞) (tensorVector F) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hF)

lemma lie_vector_chain {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => tensorVector (iterTensorLie H A F n) (γ u))
      (tensorVector (iterTensorLie H A F (n+1)) (γ t)) s t := by
  have h := hasDerivWithinAt_pi.mpr (fun c => lie_chain hH A F hA hF hsk γ hγ n c ht)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t h
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_StationaryTensorVectorRms
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
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy Quadrature

lemma stationary_tensorVector_rms {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (f : Point d → Point d) (hf : Measurable f) (hlaw : (gibbs H).map f=gibbs H) :
    Integrable (fun y => ‖tensorVector F (f y)‖^2) (gibbs H) ∧
      (∫y,‖tensorVector F (f y)‖^2 ∂gibbs H)=spatialEnergy F 0 (gibbs H) := by
  have he (y : Point d) : ‖tensorVector F y‖^2=spatialSquared F 0 y := by
    rw [tensorVector_norm_sq,spatialSquared_zero]
  simp_rw [he]
  have hm := (spatialSquared_polySmooth F hF 0).smooth.continuous.aestronglyMeasurable
    (μ:=(gibbs H).map f)
  refine ⟨?_,?_⟩
  · apply (integrable_map_measure hm hf.aemeasurable).mp
    rw [hlaw]
    exact (spatialSquared_polySmooth F hF 0).integrable hH ht
  · exact (integral_map hf.aemeasurable hm).symm.trans (by rw [hlaw]; rfl)

theorem stationary_lie_taylor_rms_oai {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (htail : HasGaussianLowerTail H)
    [SFinite (gibbs H)] {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0≤κ) (hρ : 1≤ρ) (hB : ∀k,0≤B k)
    (hb : ∀k y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H)≤κ*ρ^(2*k)*B k)
    {s : Set ℝ} (Ψ : Point d → ℝ → Point d)
    (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
    (hm : Measurable (fun p : ℝ × Point d => Ψ p.2 p.1))
    (hlaw : ∀t∈s,(gibbs H).map (fun y => Ψ y t)=gibbs H)
    {a x : ℝ} (hax : a≤x) (hsub : uIcc a x⊆s) (n : ℕ) :
    Integrable (fun y => ‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2) (gibbs H) ∧
    (∫y,‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2 ∂gibbs H)≤
      ((x-a)^(n+1)/(n.factorial:ℝ))^2*
        (κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0) := by
  have hpoly := iterTensorLie_polySmooth hH A F hA hF
  have hfinite (t : ℝ) (ht : t∈s) := stationary_tensorVector_rms hH.smooth.continuous htail
    (iterTensorLie H A F (n+1)) (hpoly (n+1)) (fun y => Ψ y t)
    (hm.comp (measurable_const.prodMk measurable_id)) (hlaw t ht)
  have hpos : 0≤κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0 :=
    mul_nonneg (mul_nonneg hκ (pow_nonneg (mul_nonneg (sq_nonneg α) (by positivity)) _))
      (iterEnergyBudget_nonneg K.2 C D hB (n+1) 0)
  have htmem (t : ℝ) (ht : t∈Ioc a x) : t∈s :=
    hsub (by rw [uIcc_of_le hax]; exact ⟨ht.1.le,ht.2⟩)
  apply chainTaylor_remainder_rms hax hpos hsub
    (fun y k _ ht => lie_vector_chain hH A F hA hF hsk (Ψ y) (hΨ y) k ht)
  · exact ((tensorVector_contDiff _ (fun c => (hpoly (n+1) c).smooth)).continuous.measurable.comp hm).aestronglyMeasurable
  · exact fun t ht => (hfinite t (htmem t ht)).1
  · intro t ht
    rw [(hfinite t (htmem t ht)).2]
    simpa only [Nat.mul_zero,pow_zero,mul_one] using
      iterTensorLie_energy hH htail hL A F hA hF C D B hκ hρ hB hb hs he (n+1) 0 (Or.inl (by omega))
end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.stationary_lie_taylor_rms_oai := @OAI.LogConcaveSampling.stationary_lie_taylor_rms_oai
