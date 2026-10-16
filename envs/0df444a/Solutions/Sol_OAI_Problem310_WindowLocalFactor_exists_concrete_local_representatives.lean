-- Prove2me | solution 1 for OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:20:13.307623+00:00
-- url     : https://prove2.me/submissions/3fce6268-615e-41fc-a57d-bc67ce8a43d0

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean:L123-L160
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_WindowLocalFactor_exists_uniform_window_representatives
import Theorems.Thm_OAI_Problem310_WindowLocalFactor_window_local_predicate_factors

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowLocalFactor ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.WindowLocalFactor

-- [generator] trimmed: open RoutingPath GridSeparation LocalPredicateFactor
open RoutingPath GridSeparation

/-- Canonical window data discharges the padding hypothesis for all nondefault
children of an internal node, whose incoming windows have the same length. -/
theorem exists_window_data_representatives {Ω : Type u_Ω} {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z,
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract z⌋ →
              Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  apply exists_uniform_window_representatives M (W.r (d - U.val.length))
    (fun i => W.a (U.val ++ [i.castSucc]))
    (fun i => W.bstar (U.val ++ [i.castSucc]))
  intro i
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  have hpad := W.padding _ hP
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_add_right] using hpad

/-- Complete concrete representative adapter. Here `Q` is the actual local test,
with only its defining equality retained as an input for convenient rewriting.
No grid-factorization or numerical span hypotheses remain. -/
theorem exists_concrete_local_representatives {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ)
    (choose : FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) →
      List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ ωS P y, choose ωS P y = rule P (fun j =>
      FiniteTableModel.selectorValue (FiniteTableModel.selectorEndpoints W) ωS P j y))
    (r : ℕ) (hdepth : ∀ i : Fin M, (U.val ++ [i.castSucc]).length + r = d)
    (Q : (FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) →
        Fin M → ℝ → Bool)
    (hQ : ∀ ω i y, Q ω i y =
      (ω.1 (FiniteTableModel.selectorAddress (FiniteTableModel.selectorEndpoints W) U i y) &&
        ω.2 (FiniteTableModel.terminalAddress (FiniteTableModel.terminalEndpoints W)
          (FiniteLocalPredicate.localLeaf (choose ω.1) r (U.val ++ [i.castSucc]) (hdepth i) y) y))) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
            Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_window_data_representatives (Ω :=
    FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) W U x
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', hsame⟩ := hrep t ht
  refine ⟨t', ht', hsame Q ?_⟩
  intro ω i y z hyz
  rw [hQ ω i y, hQ ω i z]
  exact window_local_predicate_factors W
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    (fun _ _ => rfl) (fun _ => rfl) ω.1 ω.2 (choose ω.1) rule (hchoose ω.1)
    U i r (hdepth i) hyz

end Problem310.WindowLocalFactor

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowLocalFactor
open RoutingPath GridSeparation


theorem solution : type_of% @_root_.OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives := @_root_.OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives
