-- Prove2me | solution 1 for GlobalTheory.existsUnique_adicCompletion_ringHom_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:37.358374+00:00
-- url     : https://prove2.me/submissions/6cbe50ba-0059-444d-ae92-7bc519496bc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_adicCompletion_ringHom_ext_of_fg
import Theorems.Thm_GlobalTheory_exists_adicCompletion_ringHom_extend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) (hI : I.FG) (f : A →+* B)
    [IsAdicComplete (I.map f) B] :
    ∃! g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f := by
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend I f
  exact ⟨g, hg, fun g' hg' => adicCompletion_ringHom_ext_of_fg I hI f hg' hg⟩
end GlobalTheory
