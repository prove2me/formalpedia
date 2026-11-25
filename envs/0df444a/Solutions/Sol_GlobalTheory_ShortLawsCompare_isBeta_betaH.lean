-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.isBeta_betaH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:30.448018+00:00
-- url     : https://prove2.me/submissions/0fcd3571-0342-44ad-ba8a-62a13d67294e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_BetaEx_betaExists


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
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
namespace GlobalTheory.ShortLawsCompare
theorem _root_.solution (hK : KPsiIn (Dw := Dw) c) {n b : ℕ} {Λ : GenLat E n} (hU : Λ.Unimod) (hT : Λ.TrivAt b) :
    BlockLatticeAdmissibility.IsBeta Dw c Λ (betaH (Dw := Dw) c Λ) := by
  have h := GlobalTheory.BetaEx.betaExists E H Dw l c n b hK Λ hU hT
  unfold betaH
  rw [dif_pos h]
  exact h.choose_spec
end GlobalTheory.ShortLawsCompare
