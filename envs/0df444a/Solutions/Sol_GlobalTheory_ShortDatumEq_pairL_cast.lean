-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.pairL_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:19.615545+00:00
-- url     : https://prove2.me/submissions/e6c5836d-7966-46c8-bd7a-e82620d7ac62

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
import Theorems.Thm_GlobalTheory_ShortDatumEq_isSep_cSep
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelSpanSeparation_pairOne_mk


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
theorem _root_.solution {n : ℕ} (x0 x : Fin n → D.La) :
    ((pairL (l := l) x0 x : ℤ) : ZMod l.M) = pairing D l (cls l x0) (fun b => Submodule.Quotient.mk (x b)) := by
  simp only [pairL, pairing, cls, Int.cast_sum, pairOne_mk D l (isSep_cSep l)]
end GlobalTheory.ShortDatumEq
