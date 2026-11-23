-- Prove2me | solution 1 for GlobalTheory.BK.coeff_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:10.10136+00:00
-- url     : https://prove2.me/submissions/5324aa65-27b0-4102-80e2-9cd224f71f24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_N_apply

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
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (f : K⟦X⟧) (n : ℕ) : coeff n (N K f) = n * coeff n f := by
  cases n with
  | zero => simp [N_apply]
  | succ n => rw [N_apply, coeff_succ_X_mul, coeff_derivative]; push_cast; ring
end GlobalTheory.BK
