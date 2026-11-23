-- Prove2me | solution 1 for GlobalTheory.BK.mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:28.807251+00:00
-- url     : https://prove2.me/submissions/62f89da2-f9b4-4b66-a441-2852f8de4133

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
theorem _root_.solution {e : ℕ} {f : K⟦X⟧} : f ∈ S O K e ↔ (∀ n, ‖coeff n f‖ * wS K e n ≤ 1) ∧
    Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := Iff.rfl
end GlobalTheory.BK
