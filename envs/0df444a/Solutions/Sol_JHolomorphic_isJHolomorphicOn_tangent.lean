-- Prove2me | solution 1 for JHolomorphic.isJHolomorphicOn_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T22:26:58.703508+00:00
-- url     : https://prove2.me/submissions/a8e74ec6-7b35-4613-9cda-5a01f92136d6

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem isJHolomorphicOn_tangent_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ 2 u U) (hhol : IsJHolomorphicOn J U u) (hmaps : Set.MapsTo u U O)
    (e : ℂ) :
    IsJHolomorphicOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      U (fun z => (u z, fderiv ℝ u z e)) := by
  intro z hz
  have hzU : U ∈ 𝓝 z := hU.mem_nhds hz
  have hcz : ContDiffAt ℝ 2 u z := hu.contDiffAt hzU
  have hd1 : DifferentiableAt ℝ u z := hcz.differentiableAt (by simp)
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hDu.contDiffAt hzU).differentiableAt (by simp)
  have hD := hd2.hasFDerivAt
  have hJd : DifferentiableAt ℝ J (u z) :=
    ((hJ.2.1.contDiffAt (hJ.1.mem_nhds (hmaps hz))).differentiableAt (by simp))
  -- the derivative of the lift
  have hv := hd1.hasFDerivAt.prodMk (hD.clm_apply (hasFDerivAt_const e z))
  refine ⟨hv.differentiableAt, ?_⟩
  -- differentiate `∂ₛu + J(u) ∂ₜu = 0` in the direction `e`
  have hg := (hD.clm_apply (hasFDerivAt_const (1 : ℂ) z)).add
    ((hJd.hasFDerivAt.comp z hd1.hasFDerivAt).clm_apply (hD.clm_apply (hasFDerivAt_const Complex.I z)))
  have hev : (fun w => fderiv ℝ u w 1 + (J ∘ u) w (fderiv ℝ u w Complex.I)) =ᶠ[𝓝 z]
      fun _ => (0 : E) := by
    filter_upwards [hzU] with w hw
    exact (hhol w hw).2
  have h0 := hg.unique ((hasFDerivAt_const (0 : E) z).congr_of_eventuallyEq hev)
  have h0e := congrArg (fun L => L e) h0
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    add_zero] at h0e
  -- symmetry of the second derivative
  have hsymm : IsSymmSndFDerivAt ℝ u z :=
    hcz.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField])
  have hs1 := hsymm e 1
  have hsI := hsymm e Complex.I
  unfold dbarJ
  rw [hv.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Prod.mk_add_mk, Prod.mk_eq_zero]
  refine ⟨(hhol z hz).2, ?_⟩
  rw [← hs1, ← hsI]
  rw [← h0e]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ 2 u U) (hhol : IsJHolomorphicOn J U u) (hmaps : Set.MapsTo u U O)
    (e : ℂ) :
    IsJHolomorphicOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      U (fun z => (u z, fderiv ℝ u z e)) :=
  isJHolomorphicOn_tangent_aux J O hJ U hU u hu hhol hmaps e
