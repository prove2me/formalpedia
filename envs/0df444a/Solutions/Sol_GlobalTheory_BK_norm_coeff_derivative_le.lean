-- Prove2me | solution 1 for GlobalTheory.BK.norm_coeff_derivative_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:51.031168+00:00
-- url     : https://prove2.me/submissions/955e23f7-57a3-4e1b-b96a-ef38941ba430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

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
theorem _root_.solution (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (PowerSeries.derivative K f)‖ ≤ ‖coeff (n + 1) f‖ := by
  rw [coeff_derivative, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n + 1))
end GlobalTheory.BK
