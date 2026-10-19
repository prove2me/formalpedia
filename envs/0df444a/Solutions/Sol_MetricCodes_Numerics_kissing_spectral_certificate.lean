-- Prove2me | solution 1 for MetricCodes.Numerics.kissing_spectral_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/ba24c4b3-6412-43b9-a4a3-3d07f2762ab2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_kissing_sqrt_upper

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    (1 : ℝ) / 2 < 2 * MetricCodes.Gamma kissingA kissingB := by
  have hrad : 0 < kissingA * (1 + kissingA) := by
    norm_num [kissingA]
  have hsqrt : 0 < Real.sqrt (kissingA * (1 + kissingA)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 <
      (1 + 2 * kissingA) * Real.sqrt (kissingA * (1 + kissingA)) :=
    mul_pos (by norm_num [kissingA]) hsqrt
  unfold MetricCodes.Gamma
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  have hupper := kissing_sqrt_upper
  norm_num [kissingA, kissingB] at hupper ⊢
  nlinarith
end MetricCodes.Numerics
