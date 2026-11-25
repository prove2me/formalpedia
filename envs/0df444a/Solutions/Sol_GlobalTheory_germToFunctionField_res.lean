-- Prove2me | solution 1 for GlobalTheory.germToFunctionField_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:18.459604+00:00
-- url     : https://prove2.me/submissions/2ecac540-18c8-4116-99f6-f2ac4c41e5c4

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
theorem _root_.solution [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField W (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField V s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s
end GlobalTheory
