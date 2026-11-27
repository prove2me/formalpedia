-- Prove2me | solution 1 for GlobalTheory.AnValGenCorr.prod_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:53.275175+00:00
-- url     : https://prove2.me/submissions/c423696c-fe07-4796-bfa6-5cc14cce9980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv

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
open GlobalTheory GlobalTheory.AnValGenCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical
namespace GlobalTheory.AnValGenCorr
theorem _root_.solution {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have key : ∀ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) =
      ∏ k, if φ k = ψ then f (φ k) ^ ε k else 1 := by
    intro ψ hψ
    have h : ∀ u : Finset K, f ψ ^ (∑ k ∈ u, if φ k = ψ then ε k else 0) =
        ∏ k ∈ u, if φ k = ψ then f (φ k) ^ ε k else 1 := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (hf ψ hψ), ih]
        congr 1
        split_ifs with h
        · rw [h]
        · simp
    exact h _
  rw [Finset.prod_congr rfl key, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]
end GlobalTheory.AnValGenCorr
