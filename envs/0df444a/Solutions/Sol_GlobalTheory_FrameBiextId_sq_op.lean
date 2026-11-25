-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.sq_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:37.906864+00:00
-- url     : https://prove2.me/submissions/bbd317e5-8e45-4f50-9a05-0c33ee252751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_gen
import Theorems.Thm_GlobalTheory_FrameBiextId_sb_sb
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtThreePoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_ac
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
attribute [local simp] GlobalTheory.FrameBiextId.sq_ac

set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution (b : Fin n → Q k d l) (F : Q k d 2) (u v : Q k d n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u, v] (F.1 i)) = sb ![sq b u, sq b v] (F.1 i)
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]
end GlobalTheory.FrameBiextId
