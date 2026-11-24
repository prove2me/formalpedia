-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.indCoeff_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:32.401165+00:00
-- url     : https://prove2.me/submissions/7eb99cc4-a2e9-4d3a-9693-b0b1f744877b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_datum_eq_character_pairing
import Theorems.Thm_GlobalTheory_ShortDatumEq_datum_neg_eq_inv
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelSpanSeparation_indCoeff_eq


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
    indCoeff c (cls l x0) q = (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c (-x0) q := by
  rw [indCoeff_eq, datum_neg_eq_inv, datum_eq_character_pairing, eChar]
end GlobalTheory.ShortDatumEq
