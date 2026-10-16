-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:53:21.118411+00:00
-- url     : https://prove2.me/submissions/2c3f9cee-29f4-44a7-b65d-d75b3abdd74d

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RawRepair.lean:L15-L59
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Theorems.Thm_OAI_Problem310_Aux_exists_open_periodic_envelope
import Theorems.Thm_OAI_Problem310_Auxiliary_periodic_hitting_of_pointwise_failure_bound

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicEnlargement ----
namespace OAI

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Enlarging the test set can only remove exceptional centers. -/
theorem exceptionalCenters_antitone {B V : Set ℝ} (hBV : B ⊆ V)
    (N : Set ℕ) (a : ℕ → ℝ) :
    exceptionalCenters V N a ⊆ exceptionalCenters B N a := by
  rintro x ⟨t, ht, h⟩
  exact ⟨t, ht, fun n hn hm => h n hn (hBV hm)⟩

end Problem310.Auxiliary

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RawRepair ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Complete analytic passage from a finite random periodic grid construction to
an open periodic hitting set. The hypotheses are precisely the density, stability,
and raw-failure estimates supplied by the combinatorial construction. -/
theorem periodic_hitting_of_raw_construction
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  choose V hBV hVo hVp hVm using fun ω =>
    Problem310.Aux.exists_open_periodic_envelope (B ω) (hBp ω)
      (ENNReal.ofReal p) (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  apply periodic_hitting_of_pointwise_failure_bound μ p hp V hVo hVp N hN G hG hbad
  · calc
      (∫⁻ ω, volume (V ω ∩ Icc (0 : ℝ) 1) ∂μ)
          ≤ ∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal p ∂μ :=
        lintegral_mono hVm
      _ = (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) + ENNReal.ofReal p := by
        rw [lintegral_add_left (measurable_of_countable _)]
        simp
      _ ≤ ENNReal.ofReal p + ENNReal.ofReal p := add_le_add hBmean le_rfl
      _ = ENNReal.ofReal (2 * p) := by
        rw [← ENNReal.ofReal_add (le_of_lt hp) (le_of_lt hp)]
        congr 1
        ring
  · intro x hx
    calc
      μ {ω | x ∈ exceptionalCenters (V ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
          ≤ μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} := by
        apply measure_mono
        intro ω hω
        exact exceptionalCenters_antitone (hBV ω) N _ hω
      _ ≤ ENNReal.ofReal (2 * p) := hgood x hx

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set MeasureTheory


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction.{u_Ω} := @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction.{u_Ω}
