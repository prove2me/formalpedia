-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.normalized_datum_eq_induced_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:19.549206+00:00
-- url     : https://prove2.me/submissions/bee75805-14d4-41cf-8bb2-1803310e1306

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_cls_neg
import Theorems.Thm_GlobalTheory_ShortDatumEq_indCoeff_cls

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
    (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c x0 q = indCoeff c (-cls l x0) q := by
  rw [← cls_neg, indCoeff_cls, neg_neg]
end GlobalTheory.ShortDatumEq
