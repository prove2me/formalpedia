-- Prove2me | solution 1 for GlobalTheory.coheight_apply_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:17.660737+00:00
-- url     : https://prove2.me/submissions/675e4819-c8b0-4cbc-a616-587b41b083a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    Order.coheight (f y) = Order.coheight y := by
  have := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
  exact_mod_cast this
end GlobalTheory
