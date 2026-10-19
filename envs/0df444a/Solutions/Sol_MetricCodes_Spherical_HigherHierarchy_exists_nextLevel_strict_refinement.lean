-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_nextLevel_strict_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/f8ded6c9-6e15-462a-8aa4-00dbf8051def

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_interlacing_append
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scaleCoordinate_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compensatedScalingSlope_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_compensated_append_gt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_Phi_compensated_append_lt

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
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ Gamma a b < Gamma A B ∧ Phi A B < Phi a b := by
  have hfactor : Continuous (compensatedScalingFactor a b) := by
    unfold compensatedScalingFactor quadraticCoordinate
    fun_prop
  have hmoderate :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, compensatedScalingFactor a b ε < 2 := by
    have hnear := hfactor.continuousAt.tendsto.eventually
      (Iio_mem_nhds
        (show compensatedScalingFactor a b 0 < 2 by simp))
    exact nhdsWithin_le_nhds hnear
  have hterminal :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < a (Fin.last r) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hlast)
  have hentropy := eventually_Phi_compensated_append_lt h hlast
  have hall :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
          Interlacing A B ∧ Gamma a b < Gamma A B ∧ Phi A B < Phi a b := by
    filter_upwards [hmoderate, hterminal, hentropy, self_mem_nhdsWithin]
      with ε hεtwo hεlast hεentropy (hε : 0 < ε)
    let c : ℝ := compensatedScalingFactor a b ε
    have hc : 0 < c := by
      have hslope := compensatedScalingSlope_pos h hlast
      have hquad : 0 < quadraticCoordinate ε := by
        unfold quadraticCoordinate
        positivity
      dsimp [c, compensatedScalingFactor]
      nlinarith
    let A := appendAmbient (scaleAmbient c a)
    let B := appendStabilizer (scaleStabilizer c b) (scaleCoordinate c ε)
    refine ⟨A, B, ?_, ?_, ?_⟩
    · apply interlacing_append (h.scale hc)
      · exact scaleCoordinate_pos hc hε
      · exact scaleCoordinate_strictMonoOn hc hε.le
          (h.ambient_nonneg (Fin.last r)) hεlast
    · exact Gamma_compensated_append_gt h hlast hε hεtwo.le
    · exact hεentropy
  obtain ⟨ε, hε⟩ := hall.exists
  exact hε
end MetricCodes.Spherical.HigherHierarchy
