-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.eventually_topEigenvalue_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/21fd5122-b005-4869-b9a8-ec6bf6276e2c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_terminal_block_fit
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralLimit_eq_hatted
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_hattedEdgeLimit_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_terminalRayleigh
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalRayleigh_le_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {d a b g u s : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hs : s < MetricCodes.Johnson.spectralLimit a b g u) :
    ∀ᶠ n : ℕ in atTop,
      s < MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  let E : ℝ := hattedEdgeLimit a b g u
  let S : ℝ := MetricCodes.Johnson.spectralLimit a b g u
  let ε : ℝ := (S - s) / 2
  have hE : 0 < E := hattedEdgeLimit_pos h
  have hε : 0 < ε := by
    dsimp [ε, S]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * E / ε)
  have hprod : 2 * E < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : 2 * E / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hidentity :
      (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
        2 * (m : ℝ) * hattedEdgeLimit a b g u) /
          ((m : ℝ) + 1) =
        S - 2 * E / ((m : ℝ) + 1) := by
    dsimp [S, E]
    rw [spectralLimit_eq_hatted h]
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s <
        (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1) := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalRayleigh h m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot, eventually_terminal_block_fit h m]
    with n hn hfit
  exact hn.trans_le
    (terminalRayleigh_le_top a b g u m n (by omega))
end MetricCodes.Johnson.SpectralAsymptotics
