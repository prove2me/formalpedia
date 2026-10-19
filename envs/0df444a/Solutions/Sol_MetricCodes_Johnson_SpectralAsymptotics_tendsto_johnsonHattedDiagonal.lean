-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonHattedDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/596d7a6b-336b-4031-8f28-97bd2c474145

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_terminal_block_fit
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonDiagonal
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_zeroFibreParameters
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_diagonalLimit_zero_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_diagonalLimit_sq_div_zero

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
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedDiagonalLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonDiagonal h r).pow 2
  have hden := tendsto_johnsonDiagonal hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalDiagonal n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (diagonalLimit a 0 0 u)) := by
    simpa [MetricCodes.johnsonZonalDiagonal,
      supportDegree, complementDegree,
      MetricCodes.Hamming.longitudinalDegree] using hden
  have hquot := hnum.div hden' (diagonalLimit_zero_pos h).ne'
  rw [diagonalLimit_sq_div_zero h] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_terminal_block_fit h r] with n hn
  have hpositive : 0 < terminalIndex u r n := by
    unfold terminalIndex
    omega
  simp [MetricCodes.johnsonHattedDiagonal, hpositive.ne']
end MetricCodes.Johnson.SpectralAsymptotics
