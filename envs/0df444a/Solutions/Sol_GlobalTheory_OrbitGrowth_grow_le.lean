-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.grow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:17.197508+00:00
-- url     : https://prove2.me/submissions/d4e54ba3-3af2-4661-a810-9dedddd0f72a

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
theorem _root_.solution {A : Subalgebra ℂ (Module.End ℂ M)} {W U : Submodule ℂ M} :
    grow A W ≤ U ↔ ∀ a ∈ A, ∀ x ∈ W, (a : M → M) x ∈ U := by
  unfold grow
  rw [Submodule.span_le]
  constructor
  · intro h a ha x hx; exact h ⟨a, ha, x, hx, rfl⟩
  · rintro h y ⟨a, ha, x, hx, rfl⟩; exact h a ha x hx
end GlobalTheory.OrbitGrowth
