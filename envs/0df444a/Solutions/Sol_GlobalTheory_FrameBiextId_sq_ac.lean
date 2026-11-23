-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.sq_ac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:30.931078+00:00
-- url     : https://prove2.me/submissions/a8a32ca4-c357-4b09-bc36-0a29585ceed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_gen
import Theorems.Thm_GlobalTheory_FrameBiextId_sb_sb
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtThreePoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FrameBiextId.sq_gen
attribute [local simp] GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtTwoPoints
attribute [local simp] GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtThreePoints

set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u] (A.1 i)) = sb ![sq b u] (A.1 i)
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j
    fin_cases j
    rfl
  rw [sb_sb, h]
end GlobalTheory.FrameBiextId
