-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff_llRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:11.653573+00:00
-- url     : https://prove2.me/submissions/2f5cb9e9-6de5-4a32-a985-e7d92a95f4a8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_perm_eq_of_llRank
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_eq_llRank_bruhatCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g g' : GL (Fin n) F} :
    bruhatCell g = bruhatCell g' ↔ ∀ i j, llRank i j g = llRank i j g' := by
  constructor
  · intro h i j
    rw [llRank_eq_llRank_bruhatCell i j g, llRank_eq_llRank_bruhatCell i j g', h]
  · intro h
    apply perm_eq_of_llRank (F := F)
    intro i j
    rw [← llRank_eq_llRank_bruhatCell, ← llRank_eq_llRank_bruhatCell]
    exact h i j
end GroundTheory.Automorphic.Whittaker
