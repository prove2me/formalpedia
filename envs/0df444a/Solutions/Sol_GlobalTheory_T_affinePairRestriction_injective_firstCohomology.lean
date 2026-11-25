-- Prove2me | solution 1 for GlobalTheory.T.affinePairRestriction_injective_firstCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:33.952331+00:00
-- url     : https://prove2.me/submissions/3370dc50-0965-4979-995c-f0ae8022d6be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomologyStatement
import Theorems.Thm_GlobalTheory_CechDR_pairRes_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧ Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  first | exact @GlobalTheory.CechDR.pairRes_injective | exact GlobalTheory.CechDR.pairRes_injective | (intros; apply GlobalTheory.CechDR.pairRes_injective <;> assumption)
end _root_.GlobalTheory.T
