-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.pairL_levRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:02.628723+00:00
-- url     : https://prove2.me/submissions/4414056c-dee7-40f7-93db-bba38ad23fca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_mk_levRep
import Theorems.Thm_GlobalTheory_ShortDatumEq_pairL_cast

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
theorem _root_.solution {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    ((pairL (l := l) x0 (fun b => levRep (q b)) : ℤ) : ZMod l.M) = pairing D l (cls l x0) q := by
  rw [pairL_cast]; simp only [mk_levRep]
end GlobalTheory.ShortDatumEq
