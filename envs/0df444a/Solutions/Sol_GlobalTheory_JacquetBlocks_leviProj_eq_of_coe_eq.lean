-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.leviProj_eq_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:40.039056+00:00
-- url     : https://prove2.me/submissions/ae13a55c-137b-41ff-820f-cccde68e8e9d

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
theorem _root_.solution (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  rcases p with ⟨p, hp⟩
  simp only at h
  subst h
  exact leviProj_leviEmb R e g
end GlobalTheory.JacquetBlocks
