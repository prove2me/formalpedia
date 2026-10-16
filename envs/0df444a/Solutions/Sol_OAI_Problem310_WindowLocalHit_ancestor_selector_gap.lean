-- Prove2me | solution 1 for OAI.Problem310.WindowLocalHit.ancestor_selector_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:21:44.496779+00:00
-- url     : https://prove2.me/submissions/d27990cf-30d2-489a-abe5-65ed5eac1e7e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalHit.lean:L21-L57
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowLocalHit.ancestor_selector_gap. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- A route can be resumed at any intermediate node. -/
theorem routeFrom_add (choose : List ι → X → ι)
    (n m : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + m) P x =
      routeFrom choose m (routeFrom choose n P x) x := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.add_succ, routeFrom_succ, ih]

/-- Every routed node extends the starting node. -/
theorem prefix_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) : P.IsPrefix (routeFrom choose n P x) := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      exact ih.trans (List.prefix_append _ _)

end Problem310.RoutingPath

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowLocalHit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_X

noncomputable section

namespace Problem310.WindowLocalHit

open RoutingPath StableRouting GridSeparation

variable {q d g r₀ : ℕ} {X : Type u_X}

/-- Every selector used at an earlier routed node precedes an incoming edge
below that route, provided its child index is no later than the chosen child. -/
theorem ancestor_selector_gap (W : WindowData q d g r₀)
    (choose : List (Fin q) → X → Fin q) (x : X)
    {k l : ℕ} (hkl : k < l) (hld : l < d) (i j : Fin q)
    (hj : j ≤ choose (routeFrom choose k [] x) x) :
    W.b (routeFrom choose k [] x ++ [j]) + g <
      W.a (routeFrom choose l [] x ++ [i]) := by
  have hvalid (n : ℕ) (hn : n < d) (c : Fin q) :
      ValidWindowEdge d (routeFrom choose n [] x ++ [c]) := by
    constructor
    · simp
    · simp only [List.length_append, length_routeFrom, List.length_nil,
        List.length_singleton, zero_add]
      omega
  have hpre : (routeFrom choose (k + 1) [] x).IsPrefix (routeFrom choose l [] x) := by
    have h := prefix_routeFrom choose (l - (k + 1)) (routeFrom choose (k + 1) [] x) x
    rw [← routeFrom_add, Nat.add_sub_of_le (by omega : k + 1 ≤ l)] at h
    exact h
  have hwhole : (routeFrom choose k [] x ++ [choose (routeFrom choose k [] x) x]).IsPrefix
      (routeFrom choose l [] x ++ [i]) :=
    hpre.trans (List.prefix_append _ _)
  rcases lt_or_eq_of_le hj with hj | rfl
  · obtain ⟨tail, htail⟩ := hwhole
    have heq : routeFrom choose k [] x ++ choose (routeFrom choose k [] x) x :: tail =
        routeFrom choose l [] x ++ [i] := by
      simpa only [List.append_assoc, List.singleton_append] using htail
    have hgap := W.gap_sibling (routeFrom choose k [] x) j
      (choose (routeFrom choose k [] x) x) tail hj
      (hvalid k (hkl.trans hld) j) (by rw [heq]; exact hvalid l hld i)
    rwa [heq] at hgap
  · apply W.gap_prefix _ _ (hvalid k (hkl.trans hld) _) (hvalid l hld i) hwhole
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append, length_routeFrom, List.length_nil,
      List.length_singleton, zero_add] at hlen
    omega

variable {M : ℕ}

end Problem310.WindowLocalHit

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowLocalHit
open RoutingPath StableRouting GridSeparation


theorem solution.{u_X} : type_of% @_root_.OAI.Problem310.WindowLocalHit.ancestor_selector_gap.{u_X} := @_root_.OAI.Problem310.WindowLocalHit.ancestor_selector_gap.{u_X}
