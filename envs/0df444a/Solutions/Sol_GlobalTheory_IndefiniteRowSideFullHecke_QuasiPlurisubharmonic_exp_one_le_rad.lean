-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.exp_one_le_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:12.772482+00:00
-- url     : https://prove2.me/submissions/b7eb66f7-375e-4856-b067-3ae4a75009de

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuasiPlurisubharmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic
namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic
theorem _root_.solution {D : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas D Y}
    {L : LocPot Y} {s : Y → Y → ℂ} {m : ℕ} {W : Fin m → Set Y} (h : IsBoundary A L s W) (y : Y) :
    Real.exp 1 ≤ rad L s y := by
  have := Real.log_nonpos (by positivity) (h.2.2.2 y)
  unfold rad logNormSec
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic
