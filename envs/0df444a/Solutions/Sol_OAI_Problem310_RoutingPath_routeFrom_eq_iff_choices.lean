-- Prove2me | solution 1 for OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:36:29.149205+00:00
-- url     : https://prove2.me/submissions/08a62b5b-4f22-4334-8302-54958a0c3562

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean:L123-L138
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath

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

/-- Every earlier routed node is a prefix of every later routed node. -/
theorem routeFrom_prefix_of_le (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose k P x).IsPrefix (routeFrom choose d P x) := by
  have h := prefix_routeFrom choose (d - k) (routeFrom choose k P x) x
  rw [← routeFrom_add, Nat.add_sub_of_le hkd] at h
  exact h

/-- Truncating a routed leaf recovers the intermediate routed node. -/
theorem take_routeFrom (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose d P x).take (P.length + k) = routeFrom choose k P x := by
  obtain ⟨suffix, heq⟩ := routeFrom_prefix_of_le choose P x hkd
  rw [← heq]
  have h : (routeFrom choose k P x ++ suffix).take
      (routeFrom choose k P x).length = routeFrom choose k P x := by simp
  simpa only [length_routeFrom] using h

/-- Prescribed decisions on all initial segments determine a route. -/
theorem routeFrom_eq_take_of_choices (choose : List ι → X → ι)
    (L : List ι) (x : X)
    (hchoice : ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k])
    {n : ℕ} (hn : n ≤ L.length) : routeFrom choose n [] x = L.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnl : n < L.length := by omega
      rw [routeFrom_succ, ih (by omega), hchoice n hnl,
        List.take_succ_eq_append_getElem hnl]

/-- Path-cylinder characterization: a terminal route equals a prescribed list
exactly when each successive decision follows that list. -/
theorem routeFrom_eq_iff_choices (choose : List ι → X → ι) (L : List ι) (x : X) :
    routeFrom choose L.length [] x = L ↔
      ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k] := by
  constructor
  · intro hroute k hk
    have hk0 := take_routeFrom choose [] x (Nat.le_of_lt hk)
    have hk1 := take_routeFrom choose [] x (Nat.succ_le_of_lt hk)
    rw [hroute] at hk0 hk1
    simp only [List.length_nil, Nat.zero_add] at hk0 hk1
    rw [routeFrom_succ, ← hk0, List.take_succ_eq_append_getElem hk] at hk1
    have h := List.append_cancel_left hk1
    simpa only [List.singleton_inj] using h.symm
  · intro hchoice
    simpa using routeFrom_eq_take_of_choices choose L x hchoice (le_refl L.length)

end Problem310.RoutingPath

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutingPath


theorem solution.{u_ι,u_X} : type_of% @_root_.OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices.{u_ι,u_X} := @_root_.OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices.{u_ι,u_X}
