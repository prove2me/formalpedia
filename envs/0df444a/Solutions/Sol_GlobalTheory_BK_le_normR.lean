-- Prove2me | solution 1 for GlobalTheory.BK.le_normR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:34.497857+00:00
-- url     : https://prove2.me/submissions/3bc2cbb2-355e-4910-964e-52b95ce26352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_mem_R

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
theorem _root_.solution {l : ℕ} {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) (n : ℕ) :
    ‖coeff n f‖ * rad l k ^ n ≤ normR l k f :=
  le_ciSup (mem_R.1 hf).bddAbove_range n
end GlobalTheory.BK
