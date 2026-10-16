-- Prove2me | solution 1 for OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:40:17.415103+00:00
-- url     : https://prove2.me/submissions/73e97ec6-32fd-409e-bbf3-1e88b7b1a382

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowFixedScale.lean:L17-L50
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_FixedScaleProbability_measure_fixed_scale_eq_atom_mass
import Theorems.Thm_OAI_Problem310_WindowTrialAddresses_center_local_sum_injective
import Theorems.Thm_OAI_Problem310_WindowTrialAddresses_localTerminalAddress_injective

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowFixedScale ----
namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.WindowTrialAddresses

open FiniteTableModel ConcreteLabels

variable {M d g r₀ : ℕ}

/-- Exact fixed-scale failure mass for the actual W-indexed finite table
model. All fresh-selector and adaptive-terminal injectivity obligations are
discharged here; local leaves only have to stay in their selected child. -/
theorem window_fixed_scale_on_center_atom
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (x t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (value : Node M d × Fin M → Bool)
    (leaf : SelectorTable (selectorEndpoints W) → LocalTrial W P → Leaf M d)
    (hprefix : ∀ a z, (selectorEdge P z.1).IsPrefix (leaf a z).val) :
    outcomeLaw (SelectorAddress (selectorEndpoints W)) (TerminalAddress (terminalEndpoints W))
      p hp0 hp1
      {z : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          z.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c) ∧
        ∀ i : LocalTrial W P, z.1 (localSelectorAddress W P x t i) = true →
          z.2 (terminalAddress (terminalEndpoints W) (leaf z.1 i)
            (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i))) = false} =
      selectorLaw (SelectorAddress (selectorEndpoints W))
        {a | ∀ c : Node M d × Fin M,
          a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c} *
      (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - P.val.length)) := by
  classical
  have h := FixedScaleProbability.measure_fixed_scale_eq_atom_mass
    fairLaw (bitLaw p hp0 hp1)
    (by simpa only [one_div] using fairLaw_singleton false)
    (by simpa only [one_div] using fairLaw_singleton true)
    (fun c : Node M d × Fin M => selectorAddress (selectorEndpoints W) c.1 c.2 x)
    (localSelectorAddress W P x t) (center_local_sum_injective W P x t ht) value
    (fun a i => terminalAddress (terminalEndpoints W) (leaf a i)
      (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i)))
    (fun a => localTerminalAddress_injective W P x t ht (leaf a) (hprefix a))
    p hp1 (bitLaw_false p hp0 hp1)
  simpa only [outcomeLaw, selectorLaw, terminalLaw, card_localTrial] using h

end Problem310.WindowTrialAddresses

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowTrialAddresses
open MeasureTheory
open FiniteTableModel ConcreteLabels


theorem solution : type_of% @_root_.OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom := @_root_.OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom
