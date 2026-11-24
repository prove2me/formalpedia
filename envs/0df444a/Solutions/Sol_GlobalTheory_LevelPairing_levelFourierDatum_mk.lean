-- Prove2me | solution 1 for GlobalTheory.LevelPairing.levelFourierDatum_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:50.924183+00:00
-- url     : https://prove2.me/submissions/d9059050-37f7-4c45-b1d8-eb95cc2d74db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_pairL_congr
import Theorems.Thm_GlobalTheory_LevelPairing_levRep_mk
import Theorems.Thm_GlobalTheory_LevelPairing_zpow_congr

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (c : Coeff l) {n : ℕ} (x0 x : Fin n → Dw.La) :
    x0Dat c x0 (fun b => (Submodule.Quotient.mk (x b) : LevQ Dw l)) = zetaM c ^ pairL (l := l) x0 x :=
  zpow_congr c (pairL_congr _ _ _ _ (fun b => by simp) (fun b => levRep_mk (x b)))
end GlobalTheory.LevelPairing
