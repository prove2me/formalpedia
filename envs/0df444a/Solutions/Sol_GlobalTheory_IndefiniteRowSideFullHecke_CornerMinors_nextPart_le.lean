-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:15.718897+00:00
-- url     : https://prove2.me/submissions/155c1d39-f61f-4c76-92ad-7fd66819414f

import Mathlib
import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
open MvPolynomial
namespace GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
theorem _root_.solution {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) (i : Fin l) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart a i ≤ a i := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart
  split_ifs with h
  · exact ha (show i ≤ (⟨i + 1, h⟩ : Fin l) from Fin.le_def.mpr (Nat.le_succ _))
  · exact Nat.zero_le _
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
end GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
