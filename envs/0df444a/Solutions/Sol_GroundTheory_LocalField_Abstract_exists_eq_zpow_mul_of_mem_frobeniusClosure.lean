-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.exists_eq_zpow_mul_of_mem_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:26.364814+00:00
-- url     : https://prove2.me/submissions/d7f97650-d21f-4534-a03e-2c2167c8a74d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_zpowers_sup_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ frobeniusClosure d L σ) : ∃ m : ℤ, ∃ l ∈ L, y = σ ^ m * l := by
  have hy' : y ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hy
  have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (L : Set G)) :=
    hL.preimage (continuous_const.mul continuous_id)
  have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' (L : Set G) := by
    show y⁻¹ * y ∈ L
    rw [inv_mul_cancel]
    exact L.one_mem
  obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
  obtain ⟨m, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhS
  refine ⟨m, j * (y⁻¹ * (σ ^ m * j))⁻¹, L.mul_mem hj.1 (L.inv_mem hhO), by group⟩
end GroundTheory.LocalField.Abstract
