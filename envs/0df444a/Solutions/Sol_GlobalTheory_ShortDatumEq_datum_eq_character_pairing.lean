-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.datum_eq_character_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:29:56.911446+00:00
-- url     : https://prove2.me/submissions/08412636-1c54-475c-84d5-0a23034fb20c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_pairL_levRep
import Theorems.Thm_GlobalTheory_ShortDatumEq_zetaM_eq
import Theorems.Thm_GlobalTheory_ShortDatumEq_zeta_zpow

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
theorem _root_.solution (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c x0 q = eChar D c (cls l x0) q := by
  rw [x0Dat, eChar, zetaM_eq, zeta_zpow, pairL_levRep]
end GlobalTheory.ShortDatumEq
