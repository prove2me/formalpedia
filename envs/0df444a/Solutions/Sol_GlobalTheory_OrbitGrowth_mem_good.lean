-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.mem_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:17.559128+00:00
-- url     : https://prove2.me/submissions/65def956-06b0-473f-819a-00ccb1ff5988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.OrbitGrowth
theorem _root_.solution {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} :
    x ∈ good A ↔ FiniteDimensional ℂ (orb A x) := Iff.rfl
end GlobalTheory.OrbitGrowth
