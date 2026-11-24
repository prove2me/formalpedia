-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.adjoin_compr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:21.458774+00:00
-- url     : https://prove2.me/submissions/dce663af-1d3b-446c-91e6-8d04d45ac831

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_eq_restrict
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommSplit
theorem _root_.solution {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨h i, ?_⟩
    rw [compr_eq_restrict W W' hc _ (h i)]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hw
    · rw [compr_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (hx.1 w hw) (hy.1 w hw)
    · rw [map_add]
      exact Subalgebra.add_mem _ hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.End.mul_apply]
      exact hx.1 _ (hy.1 w hw)
    · rw [compr_mul W W' hc x y hy.1]
      exact Subalgebra.mul_mem _ hx.2 hy.2
end GlobalTheory.CompanionTheory.CommSplit
