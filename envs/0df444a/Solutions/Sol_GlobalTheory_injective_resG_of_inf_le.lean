-- Prove2me | solution 1 for GlobalTheory.injective_resG_of_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:18.339171+00:00
-- url     : https://prove2.me/submissions/3ce82969-4540-40fe-9c97-71cb11096156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_GlobalTheory_bijective_res_of_eq_bot
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
variable [IsIntegral X]
namespace GlobalTheory
theorem _root_.solution (W : X.Opens) [Nonempty W] {T T' : X.Opens} (h : T' ≤ T)
    (hW : W ⊓ T ≤ T') : Function.Injective (resG X h) := by
  by_cases hT : T = ⊥
  · exact (bijective_res_of_eq_bot h hT).1
  have : Nonempty T := ((Opens.ne_bot_iff_nonempty _).mp hT).to_subtype
  have : Nonempty T' := ⟨⟨_, hW ⟨genericPoint_mem_opens W, genericPoint_mem_opens T⟩⟩⟩
  exact map_injective_of_isIntegral X (homOfLE h)
end GlobalTheory
