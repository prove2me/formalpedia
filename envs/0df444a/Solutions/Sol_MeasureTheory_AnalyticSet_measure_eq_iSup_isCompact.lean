-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:16.212183+00:00
-- url     : https://prove2.me/submissions/02109c53-79e0-4179-bb44-7631496bed67

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_isCompact_capBelow
import Theorems.Thm_isClosed_capW
import Theorems.Thm_capW_antitone
import Theorems.Thm_iInter_capW_subset
import Theorems.Thm_capKernel_eq_range
import Theorems.Thm_cap_exists_bound

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K := by
  refine le_antisymm ?_
    (iSup_le fun K => iSup_le fun _ => iSup_le fun hK => measure_mono hK)
  refine le_of_forall_lt fun c hc => ?_
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨π, hπ_cont, hπ_range⟩
  · simp at hc
  subst hπ_range
  obtain ⟨c', hcc', hc'A⟩ := exists_between hc
  have h0 : c' < μ (capKernel π) := by rwa [capKernel_eq_range hπ_cont]
  obtain ⟨β, hβ⟩ := cap_exists_bound π (fun S => μ S)
    (fun _ _ h => measure_mono h) (fun _ hs => hs.measure_iUnion) h0
  have h_iInter : μ (⋂ n, capW π β n) = ⨅ n, μ (capW π β n) :=
    Directed.measure_iInter
      (fun n => (isClosed_capW π β n).measurableSet.nullMeasurableSet)
      (fun i j => ⟨max i j, capW_antitone π β (le_max_left i j),
        capW_antitone π β (le_max_right i j)⟩)
      ⟨0, measure_ne_top μ _⟩
  have hKc : c' ≤ μ (π '' capBelow β) :=
    calc c' ≤ ⨅ n, μ (capW π β n) := le_iInf fun n => (hβ n).le
      _ = μ (⋂ n, capW π β n) := h_iInter.symm
      _ ≤ μ (π '' capBelow β) := measure_mono (iInter_capW_subset hπ_cont β)
  calc c < c' := hcc'
    _ ≤ μ (π '' capBelow β) := hKc
    _ ≤ ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ range π), μ K :=
        le_iSup_of_le (π '' capBelow β)
          (le_iSup_of_le ((isCompact_capBelow β).image hπ_cont)
            (le_iSup_of_le (image_subset_range π _) le_rfl))
end MeasureTheory.AnalyticSet
