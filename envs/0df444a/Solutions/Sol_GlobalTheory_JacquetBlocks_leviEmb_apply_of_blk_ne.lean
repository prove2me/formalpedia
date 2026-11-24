-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.leviEmb_apply_of_blk_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:12.37762+00:00
-- url     : https://prove2.me/submissions/83757a63-6bf7-4506-820f-57f8e4d3f2a3

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
omit [LinearOrder α]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne R e g (by simpa using h) x y
end GlobalTheory.JacquetBlocks
