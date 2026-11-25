-- Prove2me | solution 1 for GlobalTheory.T.card_blockParabolicSubgroupGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:44.388289+00:00
-- url     : https://prove2.me/submissions/5edf2508-e5f1-45ef-8082-41046cce9c97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGLStatement
import Theorems.Thm_GlobalTheory_StdLoc_card_blockPar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
end _root_.GlobalTheory.T
