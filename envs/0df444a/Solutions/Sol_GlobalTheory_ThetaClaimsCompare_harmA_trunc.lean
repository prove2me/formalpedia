-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.harmA_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:39.277873+00:00
-- url     : https://prove2.me/submissions/707a462e-15bd-4df0-9830-c44d153076e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_trunc_row

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
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    harmA (Dw := Dw) c (trunc Dw a) n = harmA (Dw := Dw) c a n := by
  ext P
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq, trunc_row]
end GlobalTheory.ThetaClaimsCompare
