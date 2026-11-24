-- Prove2me | solution 1 for GlobalTheory.LatOrbIsLat.stdLat_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:22.022468+00:00
-- url     : https://prove2.me/submissions/50a55f07-b22a-4a71-9041-7415d1662a0b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullRankLatticeImageStandardLatticeGL
import Theorems.Thm_GlobalTheory_LatOrbIsLat_stdLat_eq_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbIsLat
namespace GlobalTheory.LatOrbIsLat
theorem _root_.solution {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)
end GlobalTheory.LatOrbIsLat
