-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonHattedEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/6cce064e-a77e-4107-96ff-d024a955065a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonEdge
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_zeroFibreParameters
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_edgeLimit_zero_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_edgeLimit_sq_div_zero

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
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedEdgeLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonEdge h r).pow 2
  have hden := tendsto_johnsonEdge hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalEdge n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (edgeLimit a 0 0 u)) := by
    simpa [MetricCodes.johnsonZonalEdge,
      supportDegree, complementDegree,
      MetricCodes.Hamming.longitudinalDegree] using hden
  have hquot := hnum.div hden' (edgeLimit_zero_pos h).ne'
  rw [edgeLimit_sq_div_zero h] at hquot
  exact hquot.congr' (Eventually.of_forall fun n => by
    rfl)
end MetricCodes.Johnson.SpectralAsymptotics
