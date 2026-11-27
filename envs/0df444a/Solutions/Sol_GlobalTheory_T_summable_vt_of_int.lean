-- Prove2me | solution 1 for GlobalTheory.T.summable_vt_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:03.61982+00:00
-- url     : https://prove2.me/submissions/af5c4936-1790-46a2-a20e-5ca782f50fd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQTStatement
import Theorems.Thm_GlobalTheory_Ex_summable_vt_QT


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by
  first | exact @GlobalTheory.Ex.summable_vt_QT | exact GlobalTheory.Ex.summable_vt_QT | (intros; apply GlobalTheory.Ex.summable_vt_QT <;> assumption)
end _root_.GlobalTheory.T
