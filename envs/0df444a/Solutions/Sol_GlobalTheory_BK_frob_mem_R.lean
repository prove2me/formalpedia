-- Prove2me | solution 1 for GlobalTheory.BK.frob_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:10.061397+00:00
-- url     : https://prove2.me/submissions/ec132f51-6d76-4194-8527-5e3479726cfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_rad_nonneg
import Theorems.Thm_GlobalTheory_BK_mem_R
import Theorems.Thm_GlobalTheory_BK_frob_bound
import Theorems.Thm_GlobalTheory_BK_rad_le_one

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    frob K l f ∈ R O K l k :=
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n))
    (frob_bound l (fun n => pow_nonneg (rad_nonneg l k) n)
      (fun _ _ h => pow_le_pow_of_le_one (rad_nonneg l k) (rad_le_one l hk) h) f)
    ((mem_R.1 hf).comp (Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero))
end GlobalTheory.BK
