-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.levPtCl_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:25.671082+00:00
-- url     : https://prove2.me/submissions/d21c09d5-7aca-4077-968a-197f76351234

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable (D : Datum H) (l : Level H)
variable {l}
variable {D}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
theorem _root_.solution (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (u : D.La) :
    levPtCl Xo x0 (Submodule.Quotient.mk u) = levPt Xo x0 u := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
