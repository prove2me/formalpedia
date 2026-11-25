-- Prove2me | solution 1 for GlobalTheory.T.structure_sheaf_comparison_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:39.455425+00:00
-- url     : https://prove2.me/submissions/5d5cc7bd-fa35-45f6-9397-20be8c93c3d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafComparisonInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafComparisonInjectiveStatement
import Theorems.Thm_GlobalTheory_CechDR_cmpO_injective


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Function.Injective (cmpO s) := by
  first | exact @GlobalTheory.CechDR.cmpO_injective | exact GlobalTheory.CechDR.cmpO_injective | (intros; apply GlobalTheory.CechDR.cmpO_injective <;> assumption)
end _root_.GlobalTheory.T
