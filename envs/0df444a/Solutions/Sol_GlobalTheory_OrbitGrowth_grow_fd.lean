-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.grow_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:52.118648+00:00
-- url     : https://prove2.me/submissions/6c84df3c-b4ad-4d97-8a82-8aea2174212b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
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
theorem _root_.solution {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} [FiniteDimensional ℂ W]
    (hW : W ≤ good A) : FiniteDimensional ℂ (grow A W) := by
  obtain ⟨s, hs⟩ : W.FG := (Submodule.fg_iff_finiteDimensional W).mpr inferInstance
  haveI : ∀ y : s, FiniteDimensional ℂ (orb A (y : M)) := fun y => by
    have hy : (y : M) ∈ W := by rw [← hs]; exact Submodule.subset_span y.2
    exact mem_good.mp (hW hy)
  have hle : grow A W ≤ ⨆ y : s, orb A (y : M) := grow_le.mpr (fun a ha x hx => by
    have h2 : W ≤ (⨆ y : s, orb A (y : M)).comap a := by
      rw [← hs, Submodule.span_le]
      intro y hy
      exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : s) (mem_orb ha)
    exact h2 hx)
  exact Submodule.finiteDimensional_of_le hle
end GlobalTheory.OrbitGrowth
