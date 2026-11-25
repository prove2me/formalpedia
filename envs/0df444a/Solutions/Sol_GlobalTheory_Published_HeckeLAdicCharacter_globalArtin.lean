-- Prove2me | solution 1 for GlobalTheory.Published.HeckeLAdicCharacter.globalArtin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:59.892294+00:00
-- url     : https://prove2.me/submissions/27e8fd64-aed8-43f3-bbf9-893b54664fe6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.Published
open GlobalTheory.HeckeGal
namespace GlobalTheory.Published
namespace HeckeLAdicCharacter
theorem _root_.solution (H : HeckeLAdicCharacter) : GlobalArtinReciprocity := fun E Ω _ _ _ _ _ =>
  let ⟨art, ha, _⟩ := H E Ω
  ⟨art, ha⟩
end HeckeLAdicCharacter
end GlobalTheory.Published
