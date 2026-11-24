-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.exists_open_fixing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:37.900828+00:00
-- url     : https://prove2.me/submissions/1970e2fe-0f9b-407c-b4f3-4725e38b2102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_isOpen_stabIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution [TopologicalSpace G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (L : Subgroup G) (O : Subgroup L)
    (hO : IsOpen (O : Set L)) (v : V) (t : Finset W) :
    ∃ M : Subgroup L, IsOpen (M : Set L) ∧ M ≤ O ∧ (∀ m ∈ M, ρ (m : G) v = v) ∧
      ∀ w ∈ t, ∀ m ∈ M, σ (m : G) w = w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨O ⊓ stabIn ρ L v, ?_, inf_le_left, fun m hm => hm.2, by simp⟩
    rw [Subgroup.coe_inf]
    exact hO.inter (isOpen_stabIn ρ hρ L v)
  | insert a t _ ih =>
    obtain ⟨M, hM, hMO, hMv, hMt⟩ := ih
    refine ⟨M ⊓ stabIn σ L a, ?_, inf_le_left.trans hMO, fun m hm => hMv m hm.1, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hM.inter (isOpen_stabIn σ hσ L a)
    · intro w hw m hm
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hm.2
      · exact hMt w hw m hm.1
end GlobalTheory.CompanionTheory.PRep.JacExact
