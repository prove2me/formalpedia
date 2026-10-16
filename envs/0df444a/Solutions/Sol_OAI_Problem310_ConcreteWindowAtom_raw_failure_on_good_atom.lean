-- Prove2me | solution 1 for OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:43:51.52932+00:00
-- url     : https://prove2.me/submissions/2d0fed37-cad5-46dc-b145-cce9ed138fbc

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean:L80-L134
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_ConcreteWindowAtom_localMiss_mass
import Theorems.Thm_OAI_Problem310_RoutedExposure_actual_firstDefaultNode_on_atom
import Theorems.Thm_OAI_Problem310_WindowExceptionalTransfer_exists_representatives_failure_transfer

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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ConcreteWindowAtom ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Problem310.ConcreteWindowAtom

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses

variable {M d g r₀ : ℕ}

/-- The final good-atom bound for the actual window router. The only numerical
input is precisely the uniform entropy budget returned by RoutingBudget. -/
theorem raw_failure_on_good_atom
    (W : WindowData (M + 1) d g r₀) (hM : 1 ≤ M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbudget : ∀ r : ℕ, r₀ ≤ r → ∀ N : ℕ,
      N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
      (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) ≤ ENNReal.ofReal p)
    (x : ℝ) (hstable : StableAt W x)
    (ξ : Node M d × Fin M → Bool) (hgood : GoodExposure (selectorEndpoints W) x ξ) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      ({ω | x ∈ Auxiliary.exceptionalCenters
        (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
        (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
        centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) ≤
    ENNReal.ofReal p *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  classical
  obtain ⟨k, U, hlen, hfirst⟩ :=
    RoutedExposure.actual_firstDefaultNode_on_atom (selectorEndpoints W) x ξ hgood
  obtain ⟨R, hR, hcard, htransfer⟩ :=
    exists_representatives_failure_transfer W U k.val x ξ hfirst hstable
  let μ := ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
    (TerminalAddress (terminalEndpoints W)) p hp0 hp1
  let A := centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ
  let q := (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length))
  have hthreshold : r₀ ≤ W.r (d - U.val.length) := by
    have h := W.length_threshold (selectorEdge U (⟨0, by omega⟩ : Fin M))
      (selectorEdge_valid U _)
    simpa [WindowData.length, selectorEdge] using h
  have hsmall : (R.card : ENNReal) * q ≤ ENNReal.ofReal p :=
    hbudget _ hthreshold _ hcard
  have hsub : ({ω | x ∈ Auxiliary.exceptionalCenters
      (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
      (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩ A) ⊆
      ⋃ t ∈ R, localMiss W U x t ξ := by
    rintro ω ⟨hfail, hatom⟩
    obtain ⟨t, ht, hmiss⟩ := htransfer ω hatom hfail
    refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hatom, ?_⟩⟩
    intro z
    exact hmiss z.1 z.2
  change μ _ ≤ ENNReal.ofReal p * μ A
  calc
    μ _ ≤ μ (⋃ t ∈ R, localMiss W U x t ξ) := measure_mono hsub
    _ ≤ ∑ t ∈ R, μ (localMiss W U x t ξ) := measure_biUnion_finset_le _ _
    _ = ∑ _t ∈ R, q * μ A := by
      apply Finset.sum_congr rfl
      intro t ht
      exact localMiss_mass W U x t (hR t ht) p hp0 hp1 ξ
    _ = (R.card : ENNReal) * (q * μ A) := by simp [nsmul_eq_mul]
    _ = ((R.card : ENNReal) * q) * μ A := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal p * μ A := mul_le_mul hsmall le_rfl (by positivity) (by positivity)

end Problem310.ConcreteWindowAtom

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ConcreteWindowAtom
open Set MeasureTheory
open scoped ENNReal BigOperators
open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses


theorem solution : type_of% @_root_.OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom := @_root_.OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom
