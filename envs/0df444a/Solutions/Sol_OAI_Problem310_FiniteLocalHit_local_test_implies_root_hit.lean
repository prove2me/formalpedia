-- Prove2me | solution 1 for OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:23:02.717787+00:00
-- url     : https://prove2.me/submissions/7c3d88b3-cafc-477c-8fc7-11673349f4cf

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalHit.lean:L14-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_OrderedRouting_chooseChild_eq_nondefault_iff

-- ---- from OAI.MeasureTheory.DyadicAvoidance.OrderedRouting ----
namespace OAI

namespace Problem310.OrderedRouting

variable {M : ℕ}

theorem chooseChild_eq_default_iff (S : Fin M → Bool) :
    chooseChild S = Fin.last M ↔ ∀ i, S i = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_last, true_and]
  constructor
  · intro h i
    have hi := h i.castSucc (Fin.castSucc_lt_last i)
    simpa using hi
  · intro h j hj
    induction j using Fin.lastCases with
    | last => exact ((lt_irrefl _) hj).elim
    | cast i => simp [h i]

/-- Routing to a nondefault child depends only on selector entries up to it. -/
theorem chooseChild_preserved (S T : Fin M → Bool) (i : Fin M)
    (hS : chooseChild S = i.castSucc) (heq : ∀ j ≤ i, S j = T j) :
    chooseChild T = i.castSucc := by
  obtain ⟨hi, hmin⟩ := (chooseChild_eq_nondefault_iff S i).mp hS
  apply (chooseChild_eq_nondefault_iff T i).mpr
  constructor
  · rw [← heq i le_rfl]
    exact hi
  · intro j hj
    rw [← heq j (le_of_lt hj)]
    exact hmin j hj

/-- Rejected earlier children and a successful current selector determine a hit. -/
theorem chooseChild_of_local_success (S : Fin M → Bool) (i : Fin M)
    (hprev : ∀ j < i, S j = false) (hi : S i = true) :
    chooseChild S = i.castSucc :=
  (chooseChild_eq_nondefault_iff S i).mpr ⟨hi, hprev⟩

end Problem310.OrderedRouting

end OAI

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

/-- Preservation through an ancestor prefix followed by one specified local child
identifies the actual terminal leaf with the locally routed leaf. -/
theorem routeFrom_eq_local_route (choose : List ι → X → ι)
    (k r : ℕ) (P U : List ι) (x y : X) (i : ι)
    (hU : routeFrom choose k P x = U)
    (hchoice : ∀ l < k,
      choose (routeFrom choose l P x) y = choose (routeFrom choose l P x) x)
    (hi : choose U y = i) :
    routeFrom choose (k + 1 + r) P y = routeFrom choose r (U ++ [i]) y := by
  have hp := routeFrom_eq_of_choices_eq choose k P x y hchoice
  rw [hU] at hp
  rw [routeFrom_add, routeFrom_succ, hp, hi]

end Problem310.RoutingPath

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.StableRoutingBridge ----
namespace OAI

universe u_X

noncomputable section

namespace Problem310.StableRouting

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

/-- A nondefault decision is unchanged if all selectors up to that decision agree. -/
theorem select_eq_of_earlier_agreement
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x y : X)
    (hnd : select S P x ≠ Fin.last M)
    (hagree : ∀ j : Fin M, j.castSucc ≤ select S P x → S P j x = S P j y) :
    select S P y = select S P x := by
  generalize hc : select S P x = c at *
  induction c using Fin.lastCases with
  | last => exact (hnd rfl).elim
  | cast i =>
    exact chooseChild_preserved (fun j => S P j x) (fun j => S P j y) i hc
      (fun j hj => hagree j (Fin.castSucc_le_castSucc_iff.mpr hj))

/-- At a center's default node, preserving the earlier selectors rejects those children. -/
theorem rejects_earlier_at_default
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hdefault : select S U x = Fin.last M)
    (hagree : ∀ j < i, S U j x = S U j y) :
    ∀ j < i, S U j y = false := by
  intro j hj
  rw [← hagree j hj]
  exact (chooseChild_eq_default_iff (fun j => S U j x)).mp hdefault j

end Problem310.StableRouting

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FiniteLocalHit ----
namespace OAI

noncomputable section
namespace Problem310.FiniteLocalHit

open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate

variable {M d : ℕ}

/-- A successful concrete child-local test is a successful terminal lookup on the
actual root route. Only the earlier center-path selectors must be stable. -/
theorem local_test_implies_root_hit
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (select (selectorValue bS ωS)) k [] x = U.val)
    (hnd : ∀ l < k, select (selectorValue bS ωS)
      (routeFrom (select (selectorValue bS ωS)) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select (selectorValue bS ωS)
        (routeFrom (select (selectorValue bS ωS)) l [] x) x →
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j x =
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j y)
    (hdefault : select (selectorValue bS ωS) U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    ωT (terminalAddress bT
      (localLeaf (select (selectorValue bS ωS)) d [] (by simp) y) y) = true := by
  have hklength : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have htotal : k + 1 + r = d := by
    simpa only [List.length_append, List.length_singleton, ← hklength] using hdepth
  simp only [Bool.and_eq_true] at hlocal
  obtain ⟨hselector, hterminal⟩ := hlocal
  have hi : select (selectorValue bS ωS) U.val y = i.castSucc := by
    apply chooseChild_of_local_success
    · exact rejects_earlier_at_default (selectorValue bS ωS) U.val x y i hdefault hearlier
    · simpa using hselector
  have hroute : routeFrom (select (selectorValue bS ωS)) d [] y =
      routeFrom (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) y := by
    apply (congrArg (fun n => routeFrom (select (selectorValue bS ωS)) n [] y) htotal).symm.trans
    apply routeFrom_eq_local_route _ k r [] U.val x y i.castSucc hU ?_ hi
    intro l hl
    exact select_eq_of_earlier_agreement (selectorValue bS ωS) _ x y
      (hnd l hl) (hprefix l hl)
  have hleaf : localLeaf (select (selectorValue bS ωS)) d [] (by simp) y =
      localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y :=
    Subtype.ext hroute
  rw [hleaf]
  exact hterminal

end Problem310.FiniteLocalHit

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FiniteLocalHit
open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate


theorem solution : type_of% @_root_.OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit := @_root_.OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit
