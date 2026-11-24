-- Prove2me | solution 1 for GlobalTheory.Ex.summable_vt_QT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:20.84609+00:00
-- url     : https://prove2.me/submissions/bac218a4-04f5-46a5-82c1-da553ab44fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_tendsto_vt_QT

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
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex
theorem _root_.solution : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) :=
  fun _ _ _ _ _ _ h _ hk p =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (h.tendsto_vt_QT hk p)
end GlobalTheory.Ex
