-- Prove2me | solution 1 for GlobalTheory.ChartCmp.JCalc.mem_degLE_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:21.405522+00:00
-- url     : https://prove2.me/submissions/a6a848fd-6a0b-4f34-863e-e7ac7b71c04a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JCalc
variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}
namespace GlobalTheory.ChartCmp.JCalc
theorem _root_.solution [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp
end GlobalTheory.ChartCmp.JCalc
