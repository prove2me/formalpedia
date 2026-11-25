-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_subtype_indFun_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:05.188611+00:00
-- url     : https://prove2.me/submissions/7e60d18a-8df5-432c-a649-5dd87ca8ae7a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_indFun_comp_mulEquiv
import Theorems.Thm_GroundTheory_LocalField_indFun_indFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']
namespace GroundTheory.LocalField
theorem _root_.solution (T : Subgroup G) [Fintype T] (K : Subgroup T) [Fintype K]
    [Fintype (K.map T.subtype)] (ψ : K → ℂ) :
    indFun T.subtype (indFun K.subtype ψ) = indFun (K.map T.subtype).subtype
      (ψ ∘ (K.equivMapOfInjective T.subtype T.subtype_injective).symm) := by
  rw [indFun_indFun, ← indFun_comp_mulEquiv]
  congr 1
end GroundTheory.LocalField
