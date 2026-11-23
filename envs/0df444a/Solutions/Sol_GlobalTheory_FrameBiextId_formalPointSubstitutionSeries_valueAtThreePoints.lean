-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtThreePoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:37.772249+00:00
-- url     : https://prove2.me/submissions/db5bb0ac-5052-4df3-9a65-3243da2c49f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sb_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution (b : Fin n → Q k d l) (f : PS k 3 d) (u v w : Q k d n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  have h : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]
end GlobalTheory.FrameBiextId
