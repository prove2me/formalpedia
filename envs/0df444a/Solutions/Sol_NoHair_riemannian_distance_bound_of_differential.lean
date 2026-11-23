-- Prove2me | solution 1 for NoHair.riemannian_distance_bound_of_differential
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:15:55.276935+00:00
-- url     : https://prove2.me/submissions/9de4c9fa-74f6-463c-bea0-1286fe86b91e

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Manifold MeasureTheory
open scoped NNReal ENNReal
private abbrev I := 𝓘(ℝ,ADMPoint)
private abbrev J := 𝓘(ℝ,ℝ)

theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] (f : Q → ℝ)
    (hf : ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 1 f) (K : NNReal) (hk : 0 < K)
    (bound : ∀ q, ∀ v : TangentSpace 𝓘(ℝ,ADMPoint) q,
      ‖mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) f q v‖ ≤ K * ‖v‖) : LipschitzWith K f := by
  intro x y
  rw [IsRiemannianManifold.out (I:=I) x y,riemannianEDist]
  have kn : (K:ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [ENNReal.mul_iInf_of_ne kn ENNReal.coe_ne_top]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let σ := γ.map hf.continuous
  have hs : CMDiff 1 σ := hf.comp hγ
  have first : edist (f x) (f y) ≤ ∫⁻ t, ‖mfderiv% σ t 1‖ₑ := by
    rw [IsRiemannianManifold.out (I:=J),riemannianEDist]
    exact iInf_le_of_le σ (iInf_le _ hs)
  apply first.trans
  rw [←lintegral_const_mul' (K:ℝ≥0∞) _ ENNReal.coe_ne_top]
  apply lintegral_mono
  intro t
  have chain := mfderiv_comp (I':=I) t (hf.contMDiffAt.mdifferentiableAt one_ne_zero)
    (hγ.contMDiffAt.mdifferentiableAt one_ne_zero)
  change ‖(mfderiv% (f ∘ γ) t) 1‖ₑ ≤ _
  rw [chain,ContinuousLinearMap.comp_apply]
  have estimate (q : Q) (v : TangentSpace I q) :
      ‖mfderiv I J f q v‖ₑ ≤ (K:ℝ≥0∞)*‖v‖ₑ := by
    simpa only [ofReal_norm,ENNReal.ofReal_mul (NNReal.coe_nonneg _),ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_le_ofReal (bound q v))
  exact estimate _ _
