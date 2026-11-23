-- Prove2me | solution 1 for GlobalTheory.BK.mem_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:12.209159+00:00
-- url     : https://prove2.me/submissions/bfd5b339-37d2-408a-847b-0c5f9b485865

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
theorem _root_.solution {l : ℕ} {k : ℝ} {f : K⟦X⟧} :
    f ∈ R O K l k ↔ Tendsto (fun n => ‖coeff n f‖ * rad l k ^ n) atTop (𝓝 0) :=
  PowerSeries.isRestricted_iff' _ _
end GlobalTheory.BK
