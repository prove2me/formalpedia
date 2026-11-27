-- Prove2me | solution 1 for GlobalTheory.exists_germToFunctionField_eq_iff_coheight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:10.237406+00:00
-- url     : https://prove2.me/submissions/bf7d4928-107e-4b53-af91-cca146f2c3e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_coheight_eq_one
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
theorem _root_.solution [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (V : X.Opens) [Nonempty V] (t : X.functionField) :
    (∃ s : Γ(X, V), X.germToFunctionField V s = t) ↔ ∀ x ∈ V, Order.coheight x = 1 →
      t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  ⟨fun ⟨s, hs⟩ _ hx _ ↦ hs ▸ germToFunctionField_mem_range_stalk V s hx,
    exists_germToFunctionField_eq_of_coheight_eq_one V t⟩
end GlobalTheory
