-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminalRayleigh_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/4bb0e4c6-2888-472d-99a2-d9b12d623661

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminal_rayleigh_le_top

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
    (a b g u : ℝ) (m n : ℕ)
    (hfit : supportDegree b n + complementDegree g n + m ≤
      terminalDegree u n) :
    terminalRayleigh a b g u m n ≤
      MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  have hfirst :
      supportDegree b n + complementDegree g n ≤
        terminalDegree u n := by omega
  have hm :
      m ≤ terminalDegree u n -
        (supportDegree b n + complementDegree g n) := by omega
  have hdiag :
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m + 1 := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  have hedge :
      (∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  unfold terminalRayleigh
  rw [hdiag, hedge]
  exact terminal_rayleigh_le_top n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n) m hfirst hm
end MetricCodes.Johnson.SpectralAsymptotics
