-- Prove2me | solution 1 for MetricCodes.Numerics.packing_spectral_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/f94857c9-d732-46bb-9ef9-602632135f24

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_packing_sqrt_upper

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    packingS < 2 * MetricCodes.Gamma packingA packingB := by
  have hrad : 0 < packingA * (1 + packingA) := by
    norm_num [packingA]
  have hsqrt : 0 < Real.sqrt (packingA * (1 + packingA)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 <
      (1 + 2 * packingA) * Real.sqrt (packingA * (1 + packingA)) :=
    mul_pos (by norm_num [packingA]) hsqrt
  unfold MetricCodes.Gamma
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  have hupper := packing_sqrt_upper
  norm_num [packingS, packingA, packingB] at hupper ⊢
  nlinarith
end MetricCodes.Numerics
