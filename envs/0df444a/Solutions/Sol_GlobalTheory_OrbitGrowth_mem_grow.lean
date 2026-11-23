-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.mem_grow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:24.625641+00:00
-- url     : https://prove2.me/submissions/f6626f5c-6680-48bb-bb3e-820959ff1e77

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
theorem _root_.solution {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ W) : (a : M → M) x ∈ grow A W :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
end GlobalTheory.OrbitGrowth
