-- Prove2me | solution 1 for GlobalTheory.BK.frob_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:50.864301+00:00
-- url     : https://prove2.me/submissions/8188043b-43c8-495a-b309-96985ea263dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_coeff_frob

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (ha : Antitone w)
    (f : K⟦X⟧) (n : ℕ) : ‖coeff n (frob K l f)‖ * w n ≤ ‖coeff (n / l) f‖ * w (n / l) := by
  rw [coeff_frob]
  split_ifs
  · exact mul_le_mul_of_nonneg_left (ha (Nat.div_le_self _ _)) (norm_nonneg _)
  · simpa using mul_nonneg (norm_nonneg _) (hw _)
end GlobalTheory.BK
