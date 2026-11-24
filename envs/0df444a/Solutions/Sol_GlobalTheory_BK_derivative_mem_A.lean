-- Prove2me | solution 1 for GlobalTheory.BK.derivative_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:11.575679+00:00
-- url     : https://prove2.me/submissions/de898221-6098-492c-83c3-61901a5d4b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_norm_coeff_derivative_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} (hf : f ∈ A O K) : PowerSeries.derivative K f ∈ A O K :=
  fun n => (norm_coeff_derivative_le f n).trans (hf _)
end GlobalTheory.BK
