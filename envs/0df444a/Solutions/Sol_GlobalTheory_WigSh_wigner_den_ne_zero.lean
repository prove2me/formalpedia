-- Prove2me | solution 1 for GlobalTheory.WigSh.wigner_den_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:01.560901+00:00
-- url     : https://prove2.me/submissions/a45b1835-3f4b-4cca-9a8b-429773e24dc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have h1 : j ≠ l := (Finset.mem_erase.mp hj).1
  have h2 : L j ≠ L l := fun h => h1 (hL.injective h)
  exact sub_ne_zero.mpr (by exact_mod_cast h2)
end GlobalTheory.WigSh
