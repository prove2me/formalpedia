-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.grow_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:05.637989+00:00
-- url     : https://prove2.me/submissions/2a35d34e-65c8-4382-8dc2-ae1b920d24a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_le
import Theorems.Thm_GlobalTheory_OrbitGrowth_mem_grow

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
    (ha : a ∈ A) {x : M} (hx : x ∈ grow A W) : (a : M → M) x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap a := grow_le.mpr (fun b hb y hy => by
    show a (b y) ∈ grow A W
    rw [← mul_apply']
    exact mem_grow (A.mul_mem ha hb) hy)
  exact h hx
end GlobalTheory.OrbitGrowth
