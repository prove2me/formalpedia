-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_terminalRayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/8be59549-c28c-4e13-becd-b96dbf12ed46

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonHattedDiagonal
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonHattedEdge

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
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (m : ℕ) :
    Tendsto (terminalRayleigh a b g u m) atTop
      (nhds
        ((((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1))) := by
  have hdiagonal :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range (m + 1),
            MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range (m + 1),
          hattedDiagonalLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedDiagonal h (m - r)
  have hedge :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range m,
            MetricCodes.johnsonHattedEdge n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          hattedEdgeLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedEdge h (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (hdiagonal.add (htwo.mul hedge)).div_const
    ((m : ℝ) + 1)
  change Tendsto (fun n : ℕ => terminalRayleigh a b g u m n) atTop _
  simpa [terminalRayleigh, Nat.cast_add, Nat.cast_one,
    mul_comm, mul_left_comm, mul_assoc] using hquot
end MetricCodes.Johnson.SpectralAsymptotics
