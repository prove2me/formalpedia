-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.terminalHarmonic_le_johnsonAmbientDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/e480e809-d5e3-4202-9c5a-80780234d1ea

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
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.booleanHarmonicDimension n L ≤
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  unfold MetricCodes.johnsonAmbientDimension
  have hmem : L ∈ Finset.Icc (p + q) L := by
    simp [h.first_le]
  exact Finset.single_le_sum
    (s := Finset.Icc (p + q) L)
    (f := fun j => MetricCodes.booleanHarmonicDimension n j)
    (fun _ _ => Nat.zero_le _) hmem
end MetricCodes.Johnson.Asymptotics
