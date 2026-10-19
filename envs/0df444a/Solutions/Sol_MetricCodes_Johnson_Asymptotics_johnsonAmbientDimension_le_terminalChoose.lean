-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.johnsonAmbientDimension_le_terminalChoose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/52dfbd78-692c-4d84-9aeb-98207401057f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_ambientDimension_eq

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
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L ≤ n.choose L := by
  rw [MetricCodes.Johnson.ambientDimension_eq h]
  exact Nat.sub_le _ _
end MetricCodes.Johnson.Asymptotics
