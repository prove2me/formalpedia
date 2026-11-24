-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.IsGood.condLE_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:54.855592+00:00
-- url     : https://prove2.me/submissions/1654581b-be05-4e74-9972-13c7666d626d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
namespace Grid.IsGood
theorem _root_.solution {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    {b : Edge} (hb : b.InGrid G.m) (X : ℕ × ℕ) : CondLE ϖ e (G.kappa b X) := by
  intro x hx
  have h1 : G.eta x = 1 := h.eta x hx.1
  cases b with
  | theta i j =>
    have := (h.square 0 (by have := hb.2; omega) j hb.2).condα x hx
    simpa [Grid.kappa, Grid.blockChar, Grid.alpha, h1] using this
  | ex i j =>
    have := (h.square i hb.1 0 (by have := hb.1; omega)).condβ x hx
    simpa [Grid.kappa, Grid.blockChar, Grid.beta, h1] using this
end Grid.IsGood
end GlobalTheory.SplitFlip
