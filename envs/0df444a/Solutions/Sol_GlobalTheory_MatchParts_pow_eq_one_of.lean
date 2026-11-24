-- Prove2me | solution 1 for GlobalTheory.MatchParts.pow_eq_one_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:50.979772+00:00
-- url     : https://prove2.me/submissions/40ef8bad-9462-491b-ad8c-a7521b86da6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
namespace GlobalTheory.MatchParts
theorem _root_.solution {k : ℕ} (p : N.QT k) (h : p.1.1 = 1) : p.1.2 ^ k = 1 := by
  have := N.mem_QT.1 p.2
  rw [this, h]; exact N.io_zero
end GlobalTheory.MatchParts
