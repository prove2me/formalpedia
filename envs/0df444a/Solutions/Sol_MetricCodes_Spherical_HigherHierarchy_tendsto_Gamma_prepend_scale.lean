-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_prepend_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/ac894e93-2a40-4eb2-8f36-c5957f13f751

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_interlacing_prepend_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_spectralAtom_atTop_half
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_prepend_eq_spectralAtom_add_retained
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_lagrangeWeight_prepend_scale_succ
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_prepend_spectral_limit_algebra

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b)) := by
  have hatom := tendsto_spectralAtom_atTop_half
  have hterm (i : Fin (r + 1)) :
      Tendsto
        (fun u : ℝ =>
          lagrangeWeight (prependAmbient u a)
              (prependStabilizer (scaleCoordinate (c ^ 2) u) b) i.succ *
            (spectralAtom (a i) - spectralAtom u))
        atTop
        (𝓝 ((c ^ 2 * lagrangeWeight a b i) *
          (spectralAtom (a i) - (1 / 2 : ℝ)))) :=
    (tendsto_lagrangeWeight_prepend_scale_succ h c i).mul
      ((tendsto_const_nhds (x := spectralAtom (a i))).sub hatom)
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => hterm i)
  have hlimit := hatom.add hsum
  rw [prepend_spectral_limit_algebra h c] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_interlacing_prepend_scale h hc hc']
    with u hu
  exact (Gamma_prepend_eq_spectralAtom_add_retained a b u
    (scaleCoordinate (c ^ 2) u) hu).symm
end MetricCodes.Spherical.HigherHierarchy
