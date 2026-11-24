-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:21:19.21561+00:00
-- url     : https://prove2.me/submissions/a3b22c0b-708a-421c-9b20-477232a3845d

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
theorem _root_.solution {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen a := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hle : a j ≤ a i := ha hij.le
  have h1 : ((a j : ℕ) : ℚ) ≤ (a i : ℚ) := by exact_mod_cast hle
  have h2 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  linarith
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
end GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
