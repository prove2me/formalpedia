-- Prove2me | solution 1 for GlobalTheory.AnVal.JetCorr.prod_zpow_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:35.324358+00:00
-- url     : https://prove2.me/submissions/c262efbc-21f8-44dd-a592-b6a4ef9ce7bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetCorr
open scoped Classical
namespace GlobalTheory.AnVal.JetCorr
theorem _root_.solution {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have h : ∀ ψ, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) = ∏ k, if φ k = ψ then w ψ ^ ε k else 1 := fun ψ => by
    have hz : ∀ t : Finset K, ∀ a : K → ℤ, w ψ ^ (∑ k ∈ t, a k) = ∏ k ∈ t, w ψ ^ a k := fun t a => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]
    rw [hz]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]
end GlobalTheory.AnVal.JetCorr
