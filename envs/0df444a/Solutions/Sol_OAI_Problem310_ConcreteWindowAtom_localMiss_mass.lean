-- Prove2me | solution 1 for OAI.Problem310.ConcreteWindowAtom.localMiss_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:41:48.691657+00:00
-- url     : https://prove2.me/submissions/153de155-7e35-4caf-b173-e3b8352a4341

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean:L47-L78
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ConcreteWindowAtom.localMiss_mass. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Theorems.Thm_OAI_Problem310_WindowTrialAddresses_window_fixed_scale_on_center_atom

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ConcreteWindowAtom ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Problem310.ConcreteWindowAtom

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses

variable {M d g r₀ : ℕ}

lemma centerAtom_mass (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) =
    ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W))
      {a | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} := by
  have heq : centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ =
      ({a : SelectorTable (selectorEndpoints W) | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} ×ˢ
        (Set.univ : Set (TerminalTable (terminalEndpoints W)))) := by
    ext ω
    simp only [centerAtom, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    exact funext_iff
  rw [heq, ConcreteLabels.outcomeLaw, Measure.prod_prod]
  simp

/-- Exact mass of the actual local Boolean failure event, with no remaining
address-injectivity or leaf-prefix obligations. -/
theorem localMiss_mass (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1 (localMiss W U x t ξ) =
    (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length)) *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  let leaf : SelectorTable (selectorEndpoints W) → LocalTrial W U → Leaf M d :=
    fun a z => localLeaf (selectorChoice (selectorEndpoints W) a)
      (d - (U.val.length + 1)) (U.val ++ [z.1.castSucc]) (local_depth U z.1)
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)
  have hprefix : ∀ a z, (selectorEdge U z.1).IsPrefix (leaf a z).val := by
    intro a z
    exact prefix_routeFrom _ _ _ _
  have h := window_fixed_scale_on_center_atom W U x t ht p hp0 hp1 ξ leaf hprefix
  have heq : localMiss W U x t ξ =
      {ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          ω.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c) ∧
        ∀ z : LocalTrial W U, ω.1 (localSelectorAddress W U x t z) = true →
          ω.2 (terminalAddress (terminalEndpoints W) (leaf ω.1 z)
            (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)) = false} := by
    ext ω
    simp only [localMiss, Set.mem_ofPred_eq, funext_iff, centerExposure,
      localQ, Bool.and_eq_false_imp, localSelectorAddress, leaf]
  rw [heq, h, centerAtom_mass]
  exact mul_comm _ _

end Problem310.ConcreteWindowAtom

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ConcreteWindowAtom
open Set MeasureTheory
open scoped ENNReal BigOperators
open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses


theorem solution : type_of% @_root_.OAI.Problem310.ConcreteWindowAtom.localMiss_mass := @_root_.OAI.Problem310.ConcreteWindowAtom.localMiss_mass
