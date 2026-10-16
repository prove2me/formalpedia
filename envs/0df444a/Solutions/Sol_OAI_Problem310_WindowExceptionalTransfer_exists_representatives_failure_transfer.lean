-- Prove2me | solution 1 for OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:25:13.682983+00:00
-- url     : https://prove2.me/submissions/7d6833c5-24a2-421c-9020-4583402c5f32

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowExceptionalTransfer.lean:L72-L116
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Theorems.Thm_OAI_Problem310_FiniteLocalHit_local_test_implies_root_hit
import Theorems.Thm_OAI_Problem310_WindowLocalFactor_exists_concrete_local_representatives
import Theorems.Thm_OAI_Problem310_WindowLocalHit_ancestor_selector_gap

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowTableModel ----
namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

lemma selectorEdge_valid (P : Node M d) (i : Fin M) :
    ValidWindowEdge d (selectorEdge P i) := by
  constructor
  · simp [selectorEdge]
  · have hP := P.property
    simp only [selectorEdge, List.length_append, List.length_singleton]
    omega

end Problem310.FiniteTableModel

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FiniteLocalHit ----
namespace OAI

noncomputable section
namespace Problem310.FiniteLocalHit

open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate

variable {M d : ℕ}

/-- Final canonical-set form of the local-hit implication. This uses precisely the
concrete `selectorChoice`, `localLeaf`, and `routedSet` definitions of the model. -/
theorem local_test_mem_routedSet
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (RoutedSetDensity.selectorChoice bS ωS) k [] x = U.val)
    (hnd : ∀ l < k, RoutedSetDensity.selectorChoice bS ωS
      (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ RoutedSetDensity.selectorChoice bS ωS
        (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x →
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j x =
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j y)
    (hdefault : RoutedSetDensity.selectorChoice bS ωS U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (RoutedSetDensity.selectorChoice bS ωS) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    y ∈ RoutedSetDensity.routedSet bS bT (ωS, ωT) := by
  exact local_test_implies_root_hit bS bT ωS ωT k r U i x y hdepth hU hnd
    hprefix hdefault hearlier hlocal

end Problem310.FiniteLocalHit

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowExceptionalTransfer ----
namespace OAI

noncomputable section
namespace Problem310.WindowExceptionalTransfer

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure

variable {M d g r₀ : ℕ}

lemma localQ_mem_routedSet (W : WindowData (M + 1) d g r₀)
    (U : Node M d) (k : ℕ) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (hU : routeFrom (selectorChoice (selectorEndpoints W) ω.1) k [] x = U.val)
    (hdefault : selectorChoice (selectorEndpoints W) ω.1 U.val x = Fin.last M)
    (hprior : ∀ l < k, selectorChoice (selectorEndpoints W) ω.1
      (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) (i : Fin M) (n : ℕ)
    (hn : W.a (U.val ++ [i.castSucc]) ≤ n)
    (hq : localQ W U ω i (x + t * (2 : ℝ)⁻¹ ^ n) = true) :
    x + t * (2 : ℝ)⁻¹ ^ n ∈ routedSet (selectorEndpoints W) (terminalEndpoints W) ω := by
  have hlen : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have hk : k < d := by rw [hlen]; exact U.property
  apply FiniteLocalHit.local_test_mem_routedSet (selectorEndpoints W) (terminalEndpoints W)
    ω.1 ω.2 k (d - (U.val.length + 1)) U i x (x + t * (2 : ℝ)⁻¹ ^ n)
    (local_depth U i) hU hprior ?_ hdefault ?_ hq
  · intro l hl j hj
    have hP : (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x).length < d := by
      simpa using hl.trans hk
    apply hstable ⟨_, hP⟩ j n ?_ t ht ω.1
    have hgap := WindowLocalHit.ancestor_selector_gap W
      (selectorChoice (selectorEndpoints W) ω.1) x hl hk i.castSucc j.castSucc hj
    rw [hU] at hgap
    exact hgap.trans_le hn
  · intro j hj
    apply hstable U j n ?_ t ht ω.1
    have hgap := W.gap_sibling U.val j.castSucc i.castSucc []
      (by simpa using hj) (selectorEdge_valid U j) (selectorEdge_valid U i)
    exact hgap.trans_le hn

/-- Raw exceptional failure on a fixed good center atom transfers to one finite
representative scale at which every actual local Boolean trial fails. -/
theorem exists_representatives_failure_transfer
    (W : WindowData (M + 1) d g r₀) (U : Node M d) (k : ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool)
    (hfirst : ∀ ω : SelectorTable (selectorEndpoints W),
      centerExposure (selectorEndpoints W) x ω = ξ →
      routeFrom (selectorChoice (selectorEndpoints W) ω) k [] x = U.val ∧
      selectorChoice (selectorEndpoints W) ω U.val x = Fin.last M ∧
      ∀ l < k, selectorChoice (selectorEndpoints W) ω
        (routeFrom (selectorChoice (selectorEndpoints W) ω) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W),
        centerExposure (selectorEndpoints W) x ω.1 = ξ →
        x ∈ Auxiliary.exceptionalCenters
          (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Set.Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n) →
        ∃ t ∈ R, ∀ (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          localQ W U ω i
            (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) = false := by
  obtain ⟨R, hR, hcard, hrep⟩ := WindowLocalFactor.exists_concrete_local_representatives
    W U x (selectorChoice (selectorEndpoints W))
    (fun _ => OrderedRouting.chooseChild) (fun _ _ _ => rfl)
    (d - (U.val.length + 1)) (local_depth U) (localQ W U) (fun _ _ _ => rfl)
  refine ⟨R, hR, hcard, ?_⟩
  intro ω hω hfail
  obtain ⟨t, ht, havoid⟩ := hfail
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i j
  rw [heq ω i j]
  obtain ⟨hU, hdefault, hprior⟩ := hfirst ω.1 hω
  have hn : 1 ≤ W.a (U.val ++ [i.castSucc]) + j.val := by
    have h : 3 ≤ W.a (U.val ++ [i.castSucc]) := W.start_three _ (selectorEdge_valid U i)
    omega
  cases hq : localQ W U ω i
      (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) with
  | false => rfl
  | true =>
    exact False.elim (havoid _ hn
      (localQ_mem_routedSet W U k x t ht ω hU hdefault hprior hstable i _
        (Nat.le_add_right _ _) hq))

end Problem310.WindowExceptionalTransfer

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowExceptionalTransfer
open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure


theorem solution : type_of% @_root_.OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer := @_root_.OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer
