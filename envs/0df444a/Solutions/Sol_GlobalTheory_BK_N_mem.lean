-- Prove2me | solution 1 for GlobalTheory.BK.N_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:38.82087+00:00
-- url     : https://prove2.me/submissions/f76cb88b-0d0d-4d6a-93ff-de7a4459a982

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
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution {B : Subalgebra O K⟦X⟧} [HasU B] {f : K⟦X⟧} (hf : PowerSeries.derivative K f ∈ B) :
    N K f ∈ B := B.mul_mem HasU.X_mem hf
end GlobalTheory.BK
