-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.latAdm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:34.987374+00:00
-- url     : https://prove2.me/submissions/d135ca0b-94c0-4219-9271-146eacf61b9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm

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
variable (c : Coeff l) {n₁ n₂ : ℕ}
namespace GlobalTheory.ShortLawsCompare
theorem _root_.solution {n : ℕ} (bad : ℕ) (Λ : GenLat E n) : BlockLatticeAdmissibility.LatAdm l bad Λ ↔ BlockProductLattices.LatOK bad l.M Λ := Iff.rfl
end GlobalTheory.ShortLawsCompare
