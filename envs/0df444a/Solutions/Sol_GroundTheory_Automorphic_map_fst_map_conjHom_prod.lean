-- Prove2me | solution 1 for GroundTheory.Automorphic.map_fst_map_conjHom_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:43.290796+00:00
-- url     : https://prove2.me/submissions/3d0d3c49-ea08-4cae-a601-d37a2c5d6dbc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitarySplit
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']
namespace GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.fst F F) = M.map (RingHom.snd F F) := by
  ext i j
  show (conj F (F × F) (M i j)).1 = (M i j).2
  rw [conj_prod]
end GroundTheory.Automorphic
