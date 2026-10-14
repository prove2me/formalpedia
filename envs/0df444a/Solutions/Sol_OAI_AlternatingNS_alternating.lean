-- Prove2me | solution 1 for OAI.AlternatingNS.alternating
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T01:26:04.285883+00:00
-- url     : https://prove2.me/submissions/6492a21e-e46d-4599-a99e-d344a1c2976b

import Mathlib
import Definitions.Def_NavierStokesAlternating
import Theorems.Thm_OAI_AlternatingNS_velocity_construction
import Theorems.Thm_OAI_AlternatingNS_trajectory_flow
import Theorems.Thm_OAI_AlternatingNS_residual_regular
import Theorems.Thm_OAI_AlternatingNS_force_compiler
import Theorems.Thm_OAI_AlternatingNS_zero_pressure_solution
import Theorems.Thm_OAI_AlternatingNS_energy_uniqueness

set_option autoImplicit false

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory
open OAI OAI.AlternatingNS

theorem solution (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν) :
    AlternatingConclusion ν := by
  obtain ⟨U, cu, K, hcu, hK, hU⟩ := velocity_construction
  obtain ⟨cf, hcf, hcfU⟩ := force_compiler ν hν hc
  refine ⟨fun Mw => cf (cu Mw), cu, hcf.comp hcu, hcu, K, hK, ?_⟩
  intro M w hM hw
  obtain ⟨hprog, hsm, hsupp, hrap, h0, hdiv, hhalt⟩ := hU M w hM hw
  obtain ⟨hfs, hfk, hfr⟩ := residual_regular ν (U (M, w)) K hK hsm hsupp hrap
  obtain ⟨hNS, hE⟩ := zero_pressure_solution ν (U (M, w)) K hK hsm hsupp hrap h0 hdiv
  obtain ⟨X, hX, hXu⟩ := trajectory_flow (U (M, w)) hsm hrap
  refine ⟨residual ν (U (M, w)), U (M, w), X,
    hcfU (cu (M, w)) (U (M, w)) K hK hsm hsupp hrap hprog, hprog, hfs, hsm, hfk, hsupp, hfr, hrap,
    rfl, hNS, hE, ?_, hX, hXu, hhalt (X observedParticle) (hX observedParticle)⟩
  intro v p hv hcv
  exact energy_uniqueness ν hν (U (M, w)) K hK hsm hsupp hrap hNS hE v p hv hcv
