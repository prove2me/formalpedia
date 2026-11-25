-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.powVal_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:50.327192+00:00
-- url     : https://prove2.me/submissions/4835999b-1c88-4612-b785-abe75513647f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Type} [CommRing S] {X Y Z : Scheme.{0}} {L : LB X} {g : Y ⟶ X} {k : ℤ}
  {π : Y ⟶ Spec (CommRingCat.of S)}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hL : L.IsLB) {a b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))}
    (h : ∀ y i, g y ∈ L.U i → powVal a (𝟙 Y) y i = powVal b (𝟙 Y) y i) : a = b :=
  sec_ext' hL fun y J hJ => h y _ (hJ (𝟙 Y ≫ g))
end GlobalTheory.FieldBaseChange
