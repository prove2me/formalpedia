-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_le_of_norm_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:58.015386+00:00
-- url     : https://prove2.me/submissions/c2d4bfbf-f994-43ff-8674-61faa75de34f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_forall_finset
import Theorems.Thm_GlobalTheory_linearMap_ext_of_linearIndependent
import Theorems.Thm_GlobalTheory_finite_and_ncard_setOf_norm_le_of_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {d R : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hL : ∀ x ∈ L, x ≠ 0 → d ≤ ‖x‖) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G) (hG : ∀ g ∈ G, ∀ i, ‖(φ g (v i) : E)‖ ≤ R) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * R / d) ^ (n ^ 2) := by
  classical
  haveI : IsAddTorsionFree E := IsAddTorsionFree.of_isTorsionFree ℝ E
  obtain ⟨hf, hc⟩ := finite_and_ncard_setOf_norm_le_of_rank L hn hv hd hR hL
  rw [Set.ncard_eq_toFinset_card _ hf] at hc
  refine finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_
  have h1 : s.card ≤ (Fintype.piFinset fun _ : Fin n => hf.toFinset).card := by
    refine Finset.card_le_card_of_injOn (fun g i => φ g (v i)) (fun g hg => ?_)
      (fun g hg g' hg' h => hφ (hs hg) (hs hg') ?_)
    · simp only [Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
      exact fun i => hG g (hs hg) i
    · exact linearMap_ext_of_linearIndependent hn hv fun i => congrFun h i
  rw [Fintype.card_piFinset_const] at h1
  calc (s.card : ℝ) ≤ (hf.toFinset.card : ℝ) ^ n := by exact_mod_cast h1
    _ ≤ ((1 + 2 * R / d) ^ n) ^ n := by gcongr
    _ = _ := by rw [← pow_mul, sq]
end GlobalTheory
