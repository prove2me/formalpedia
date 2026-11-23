-- Prove2me | solution 1 for NoHair.zero_mass_ricci_flat_by_first_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:50:45.523059+00:00
-- url     : https://prove2.me/submissions/9af14e58-6c50-4108-906a-0914cc67e405
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_ricci_variation_conformal_lapse_flux
import Theorems.Thm_NoHair_static_conformal_adm_flux_law
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
    (nonnegative : ∀ m : ℝ, IsScalarFlatADMMass m → 0 ≤ m) : RicciFlatInADMCharts Q := by
  by_contra bad
  obtain ⟨F,hzero,hder,hfamily⟩ := ricci_variation_conformal_lapse_flux Q hend bad
  have extreme : IsLocalMax F 0 := by
    filter_upwards [hfamily] with t ht
    obtain ⟨L,g,a,hfall,hbare,hflux,hnew,realized⟩ := ht
    have deform := static_conformal_adm_flux_law L g hfall
    have mass := tendsto_nhds_unique deform ((hnew.sub hbare).add hflux)
    change F t ≤ F 0
    rw [hzero]
    linarith only [mass,nonnegative a realized]
  exact hder.ne' extreme.deriv_eq_zero
