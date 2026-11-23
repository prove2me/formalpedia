-- Prove2me | solution 1 for NoHair.ricci_variation_conformal_lapse_flux
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:29:51.419411+00:00
-- url     : https://prove2.me/submissions/516111d6-c969-4c01-9bcc-6766bf3a5c24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_nonzero_ricci_has_positive_compact_energy_test
import Theorems.Thm_NoHair_compact_ricci_deformation_lapse_flux_derivative
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q)
    (hric : ¬ RicciFlatInADMCharts Q) :
    ∃ F : ℝ → ℝ, F 0 = 0 ∧ 0 < deriv F 0 ∧ ∀ᶠ t in 𝓝 (0:ℝ),
      ∃ (L : ADMPoint → ℝ) (g : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (mass : ℝ),
        HasStaticFirstOrderFalloff L g ∧ Tendsto (staticADMFlux g) atTop (𝓝 0) ∧
        Tendsto (staticLapseFlux L) atTop (𝓝 (F t)) ∧
        Tendsto (staticADMFlux (staticPositiveMetric L g)) atTop (𝓝 mass) ∧ IsScalarFlatADMMass mass := by
  obtain ⟨e,he,χ,hn,hs,hc,hu,pos⟩ := nonzero_ricci_has_positive_compact_energy_test Q hric
  obtain ⟨F,h0,der,all⟩ := compact_ricci_deformation_lapse_flux_derivative Q hend e he χ hn hs hc hu
  refine ⟨F,h0,?_,all⟩
  rw [der]
  exact div_pos pos (mul_pos (by norm_num) Real.pi_pos)
