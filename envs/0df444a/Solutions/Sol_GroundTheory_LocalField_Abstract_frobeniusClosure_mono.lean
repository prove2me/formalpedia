-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.frobeniusClosure_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:55.462719+00:00
-- url     : https://prove2.me/submissions/b8467993-71f1-4e6f-8038-ff71edcad848

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_frobeniusClosure_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {d : G →* Multiplicative ℤ̂} {L L' : Subgroup G} (h : L' ≤ L) (x : G) :
    frobeniusClosure d L' x ≤ frobeniusClosure d L x :=
  frobeniusClosure_le isClosed_frobeniusClosure mem_frobeniusClosure_self
    ((inf_le_inf_right _ h).trans le_frobeniusClosure)
end GroundTheory.LocalField.Abstract
