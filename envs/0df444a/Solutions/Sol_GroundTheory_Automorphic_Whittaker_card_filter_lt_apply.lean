-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.card_filter_lt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:27.817914+00:00
-- url     : https://prove2.me/submissions/387aeaf0-7c06-44ae-9282-88b197ea2d38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance

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
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]
end GroundTheory.Automorphic.Whittaker
