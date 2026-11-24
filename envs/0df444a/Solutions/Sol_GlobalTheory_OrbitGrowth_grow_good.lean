-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.grow_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:53.072788+00:00
-- url     : https://prove2.me/submissions/7cdfb1d7-4a0a-49e9-96fa-c72b6a315020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_mul_apply__1ef562d11778
import Theorems.Thm_GlobalTheory_OrbitGrowth_mem_good
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_le

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
theorem _root_.solution {A B : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} (hW : W ≤ good B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : grow A W ≤ good B :=
  grow_le.mpr (fun a ha x hx => by
    haveI : FiniteDimensional ℂ (orb B x) := mem_good.mp (hW hx)
    have hle : orb B (a x) ≤ (orb B x).map a := orb_le.mpr (fun b hb => by
      have e : b (a x) = a (b x) := by
        rw [← mul_apply', ← mul_apply', hcomm a ha b hb]
      rw [e]
      exact Submodule.mem_map_of_mem (mem_orb hb))
    exact mem_good.mpr (Submodule.finiteDimensional_of_le hle))
end GlobalTheory.OrbitGrowth
