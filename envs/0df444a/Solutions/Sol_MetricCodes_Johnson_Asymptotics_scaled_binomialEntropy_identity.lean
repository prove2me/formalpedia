-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.scaled_binomialEntropy_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/1bc59b1c-e910-48ff-9596-45fe45d75c13

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (a * Real.log a - b * Real.log b -
      (a - b) * Real.log (a - b)) / Real.log 2 =
      a * MetricCodes.binaryEntropy (b / a) := by
  have hab : 0 < a - b := sub_pos.mpr hba
  have hratio : 0 < b / a := div_pos hb ha
  have hcomp : 0 < 1 - b / a := by
    apply sub_pos.mpr
    exact (div_lt_one ha).mpr hba
  have hblog :
      Real.log b = Real.log a + Real.log (b / a) := by
    calc
      Real.log b = Real.log (a * (b / a)) := by
        congr 1
        field_simp
      _ = Real.log a + Real.log (b / a) :=
        Real.log_mul ha.ne' hratio.ne'
  have hcomplog :
      Real.log (a - b) =
        Real.log a + Real.log (1 - b / a) := by
    calc
      Real.log (a - b) = Real.log (a * (1 - b / a)) := by
        congr 1
        field_simp

      _ = Real.log a + Real.log (1 - b / a) :=
        Real.log_mul ha.ne' hcomp.ne'
  rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
    Real.binEntropy, Real.log_inv, Real.log_inv,
    hblog, hcomplog]
  field_simp [ha.ne']
  ; ring
end MetricCodes.Johnson.Asymptotics
