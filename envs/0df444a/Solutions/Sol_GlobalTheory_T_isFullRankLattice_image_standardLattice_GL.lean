-- Prove2me | solution 1 for GlobalTheory.T.isFullRankLattice_image_standardLattice_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:06.741798+00:00
-- url     : https://prove2.me/submissions/02da160f-3172-41f2-bcf4-d25b4580db0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullRankLatticeImageStandardLatticeGL
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullRankLatticeImageStandardLatticeGLStatement
import Theorems.Thm_GlobalTheory_LatOrb_matLat_stdLat_isLatV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.matLat_stdLat_isLatV | exact GlobalTheory.LatOrb.matLat_stdLat_isLatV | (intros; apply GlobalTheory.LatOrb.matLat_stdLat_isLatV <;> assumption)
end _root_.GlobalTheory.T
