-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing.gtSelectedPrefixWeight_finiteInterlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/bf0a18c6-7c0d-42b6-80da-a32e5e0c5176

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
set_option autoImplicit false
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
theorem _root_.solution
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (hn : 2 * r + 4 ≤ n) (hdom : Antitone mu) :
    FiniteInterlacing n mu (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · exact le_rfl
  · exact hdom (Fin.castSucc_le_succ j)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
