-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.levPt_levRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:14.721803+00:00
-- url     : https://prove2.me/submissions/e644cd22-ade0-48a1-b935-d3c910f9513c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_mk_levRep
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelSpanSeparation_levPtCl_mk


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
open GlobalTheory GlobalTheory.ShortDatumEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
namespace GlobalTheory.ShortDatumEq
theorem _root_.solution (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (q : LevQ D l) :
    levPt Xo x0 (levRep q) = levPtCl Xo x0 q := by
  rw [← levPtCl_mk, mk_levRep]
end GlobalTheory.ShortDatumEq
