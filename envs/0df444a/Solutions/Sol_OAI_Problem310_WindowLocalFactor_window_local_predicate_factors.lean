-- Prove2me | solution 1 for OAI.Problem310.WindowLocalFactor.window_local_predicate_factors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:18:20.672467+00:00
-- url     : https://prove2.me/submissions/572912c6-cec2-4b0d-9cc8-aed0955a88a4

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean:L73-L121
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowLocalFactor.window_local_predicate_factors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Theorems.Thm_OAI_Problem310_FiniteLocalPredicate_finite_local_predicate_factors

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowLocalFactor ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.WindowLocalFactor

-- [generator] trimmed: open RoutingPath GridSeparation LocalPredicateFactor
open RoutingPath GridSeparation

/-- The concrete finite-table local predicate inherits its common grid from
WindowData's bound on endpoints of descendant edges. -/
theorem window_local_predicate_factors {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀)
    (bS : FiniteTableModel.Node M d → Fin M → ℕ)
    (bT : FiniteTableModel.Leaf M d → ℕ)
    (hbS : ∀ Q j, bS Q j = W.b (Q.val ++ [j.castSucc]))
    (hbT : ∀ L, bT L = W.b L.val)
    (ωS : FiniteTableModel.SelectorTable bS) (ωT : FiniteTableModel.TerminalTable bT)
    (choose : List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun j => FiniteTableModel.selectorValue bS ωS Q j x))
    (U : FiniteTableModel.Node M d) (i : Fin M) (r : ℕ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋) :
    (ωS (FiniteTableModel.selectorAddress bS U i x) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth x) x)) =
    (ωS (FiniteTableModel.selectorAddress bS U i y) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth y) y)) := by
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  apply FiniteLocalPredicate.finite_local_predicate_factors
    bS bT ωS ωT choose rule hchoose r (U.val ++ [i.castSucc]) hdepth U i
    (W.bstar (U.val ++ [i.castSucc]))
  · intro Q hPQ j
    rw [hbS]
    apply (W.descendant_bounds _ _ hP ?_ (hPQ.trans (List.prefix_append _ _))).2
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt Q.property
  · intro L hPL
    rw [hbT]
    apply (W.descendant_bounds _ _ hP ?_ hPL).2
    refine ⟨?_, L.property.le⟩
    intro hL
    have hD := L.property
    rw [hL] at hD
    simp only [List.length_nil] at hD
    have hU := U.property
    omega
  · rw [hbS]
    exact (W.descendant_bounds _ _ hP hP (List.prefix_refl _)).2
  · exact hxy

end Problem310.WindowLocalFactor

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowLocalFactor
open RoutingPath GridSeparation


theorem solution : type_of% @_root_.OAI.Problem310.WindowLocalFactor.window_local_predicate_factors := @_root_.OAI.Problem310.WindowLocalFactor.window_local_predicate_factors
