-- Prove2me | solution 1 for GlobalTheory.ChartCompare.nEval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:49.780841+00:00
-- url     : https://prove2.me/submissions/49ce084f-2934-426a-930b-e2d3201b983a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
open GlobalTheory GlobalTheory.ChartCompare
variable {R₀ : Type} [CommRing R₀]
open MvPowerSeries
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]
open IsLocalRing TensorProduct
variable {R₀ : Type} [CommRing R₀]
open MvPowerSeries
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]
namespace GlobalTheory.ChartCompare
namespace _root_.GlobalTheory.ChartCompare
theorem _root_.solution (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (0 : MvPowerSeries σ R₀) a = 0 := by
  rw [nilpotent_eval_eq_finsum _ a ha]
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.evalTerm]
end _root_.GlobalTheory.ChartCompare
end GlobalTheory.ChartCompare
