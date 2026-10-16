-- Prove2me | solution 1 for OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:02:28.655322+00:00
-- url     : https://prove2.me/submissions/76ef6fe1-8ab7-4413-8c5f-444f660dbd4a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutedExposure.lean:L50-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- A first default on a finite route has a well-defined first occurrence. -/
theorem exists_first_default (choose : List ι → X → ι)
    (d : ℕ) (P : List ι) (x : X) (default : ι)
    (h : ∃ k < d, choose (routeFrom choose k P x) x = default) :
    ∃ k < d, choose (routeFrom choose k P x) x = default ∧
      ∀ l < k, choose (routeFrom choose l P x) x ≠ default := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro l hl hdefault
  exact Nat.find_min h hl ⟨Nat.lt_trans hl (Nat.find_spec h).1, hdefault⟩

end Problem310.RoutingPath

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe u_ι u_X u_Y

noncomputable section

namespace Problem310.CenterRouteExposure
open Problem310.RoutingPath

/-- Equality of all node decisions at two samples identifies their entire routes,
even when the two decision functions have different parameter spaces. -/
theorem routeFrom_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    routeFrom chooseX n P x = routeFrom chooseY n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [routeFrom_succ, ih, h]

/-- The decision at every stage is also fixed by the node-decision data. -/
theorem route_decision_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    chooseX (routeFrom chooseX n P x) x =
      chooseY (routeFrom chooseY n P y) y := by
  rw [routeFrom_congr_at chooseX chooseY x y h]
  exact h _

/-- Full center exposure fixes whether a given stage is the first default. -/
theorem firstDefaultAt_congr {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (default : ι) (d k : ℕ) (P : List ι) :
    FirstDefaultAt chooseX default d k P x ↔
      FirstDefaultAt chooseY default d k P y := by
  simp only [FirstDefaultAt, route_decision_congr_at chooseX chooseY x y h]

open Problem310.FiniteTableModel Problem310.OrderedRouting

/-- Even the extended selector function is fixed by center exposure: invalid
nodes use the same constant false value in both outcomes. -/
theorem selectorValue_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (P : List (Child M)) (i : Fin M) :
    selectorValue b ω P i x = selectorValue b ω' P i x := by
  by_cases hP : P.length < d
  · have he := congrFun h (⟨P, hP⟩, i)
    simpa only [centerExposure, selectorValue, dite_eq_left hP] using he
  · simp only [selectorValue, dite_eq_right hP]

theorem centerChoice_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω') (P : List (Child M)) :
    centerChoice b x P ω = centerChoice b x P ω' := by
  exact chooseChild_congr _ _ (selectorValue_eq_of_centerExposure_eq b x h P)

/-- Every center route is constant on each full exposure atom. -/
theorem centerRoute_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    routeFrom (centerChoice b x) n P ω = routeFrom (centerChoice b x) n P ω' :=
  routeFrom_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- A good exposure atom has one fixed first-default stage and node, uniformly
for every completion of all unexposed selector coordinates. -/
theorem firstDefaultData_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : ℕ, ∃ U : List (Child M), k < d ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k [] ω = U ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k [] ω := by
  obtain ⟨k, hk, hdefault, hprior⟩ :=
    exists_first_default (centerChoice b x) d [] (centerCompletion b x ξ) (Fin.last M) hgood
  refine ⟨k, routeFrom (centerChoice b x) k [] (centerCompletion b x ξ), hk, ?_⟩
  intro ω hω
  have he : centerExposure b x ω = centerExposure b x (centerCompletion b x ξ) := by
    simpa only [centerExposure_completion] using hω
  refine ⟨centerRoute_eq_of_centerExposure_eq b x he k [], ?_⟩
  apply (firstDefaultAt_congr _ _ ω (centerCompletion b x ξ)
    (centerChoice_eq_of_centerExposure_eq b x he) (Fin.last M) d k []).mpr
  exact ⟨hk, hdefault, hprior⟩

/-- Version of the atomwise first-default witness with the actual bounded node
and stage types required to index the finite selector tables and window data. -/
theorem firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k.val [] ω = U.val ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k.val [] ω := by
  obtain ⟨k, U, hk, hU⟩ := firstDefaultData_on_atom b x ξ hgood
  have hroute := (hU (centerCompletion b x ξ) (centerExposure_completion b x ξ)).1
  have hlen : U.length = k := by
    rw [← hroute, length_routeFrom]
    simp
  exact ⟨⟨k, hk⟩, ⟨U, by simpa only [hlen] using hk⟩, hlen, hU⟩

end Problem310.CenterRouteExposure

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutedExposure ----
namespace OAI

noncomputable section

namespace Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

/-- Translate from spatial routing with tables fixed to routing the table outcome
with the center fixed. No decision or node representation is changed. -/
theorem routedPath_eq_centerRoute {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b) (x : ℝ)
    (n : ℕ) (P : List (Child M)) :
    routeFrom (selectorChoice b ω) n P x = routeFrom (centerChoice b x) n P ω :=
  routeFrom_congr_at _ _ x ω (fun _ => rfl) n P

/-- A good exposure supplies the actual bounded first-default node, fixed before
any remaining selector or terminal-table coordinates are revealed. -/
theorem actual_firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : GoodExposure b x ξ) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (selectorChoice b ω) k.val [] x = U.val ∧
        selectorChoice b ω U.val x = Fin.last M ∧
        ∀ l < k.val,
          selectorChoice b ω (routeFrom (selectorChoice b ω) l [] x) x ≠ Fin.last M := by
  obtain ⟨k, U, hlen, hU⟩ := firstDefaultNode_on_atom b x ξ hgood
  refine ⟨k, U, hlen, ?_⟩
  intro ω hω
  obtain ⟨hroute, _, hdefault, hprior⟩ := hU ω hω
  have hactual : routeFrom (selectorChoice b ω) k.val [] x = U.val := by
    rw [routedPath_eq_centerRoute]
    exact hroute
  refine ⟨hactual, ?_, ?_⟩
  · change centerChoice b x U.val ω = Fin.last M
    rwa [hroute] at hdefault
  · intro l hl
    simpa only [routedPath_eq_centerRoute, selectorChoice_eq_centerChoice] using hprior l hl

end Problem310.RoutedExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity


theorem solution : type_of% @_root_.OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom := @_root_.OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom
