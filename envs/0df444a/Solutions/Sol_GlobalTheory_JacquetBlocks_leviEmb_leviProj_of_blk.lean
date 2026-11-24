-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.leviEmb_leviProj_of_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:12.563709+00:00
-- url     : https://prove2.me/submissions/6907caa4-79d9-41f4-9a6b-83afe5498d66

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviProj_apply]
  · rw [leviEmb_apply_ne R e _ hab, h _ _ (by simpa using hab)]
end GlobalTheory.JacquetBlocks
