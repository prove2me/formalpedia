-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tate_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:12.136169+00:00
-- url     : https://prove2.me/submissions/a997d0c3-48b4-4fb0-ba9e-329751d5d5f3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateZero_of_complete
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_of_complete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable {V : Type*} [CommGroup V]
variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]
namespace GroundTheory.LocalField
theorem _root_.solution (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr0 : ∀ n, Subsingleton (TateZero G (S.gr n)))
    (hgr1 : ∀ n, Subsingleton (TateNegOne G (S.gr n))) :
    Subsingleton (TateZero G V) ∧ Subsingleton (TateNegOne G V) :=
  ⟨subsingleton_tateZero_of_complete S h0 hc hs hgr0,
    subsingleton_tateNegOne_of_complete S h0 hc hs hgr1⟩
end GroundTheory.LocalField
