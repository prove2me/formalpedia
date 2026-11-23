-- Prove2me | solution 1 for GlobalTheory.FrameBiextId.sb_sb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:21.628699+00:00
-- url     : https://prove2.me/submissions/5f25eed8-dbb9-4a03-a3b2-bbc706d30cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
import Theorems.Thm_GlobalTheory_FrameBiextId_sq_gen
import Theorems.Thm_GlobalTheory_FormalLog_ev_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FrameBiextId.sq_gen

set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace GlobalTheory.FrameBiextId
theorem _root_.solution {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  show ev (fun j => (b j).1) ((a j).1 i) = sb b ((a j).1 i)
  rw [sb_apply]
end GlobalTheory.FrameBiextId
