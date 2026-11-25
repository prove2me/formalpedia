-- Prove2me | solution 1 for Kac.tsum_measure_lt_returnTime_of_isFiniteMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:27:25.069423+00:00
-- url     : https://prove2.me/submissions/8451c319-721d-44b3-be23-431ad8af54b4

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_antitone_notYet
public import Theorems.Thm_Kac_iInter_notYet
public import Theorems.Thm_Kac_inter_lt_returnTime
public import Theorems.Thm_Kac_measurableSet_notYet
public import Theorems.Thm_Kac_measurableSet_iUnion_preimage_iterate
public import Theorems.Thm_Kac_sum_measure_inter_notYet
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
variable [IsFiniteMeasure μ]
namespace Kac
theorem _root_.solution (hf : MeasurePreserving f μ μ)
    (hA : MeasurableSet A) :
    ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by
  simp only [inter_lt_returnTime]
  have hmeas := measurableSet_notYet hf.measurable hA
  have htail : Tendsto (fun N => μ (notYet f A N)) atTop (𝓝 (μ (⋂ n, notYet f A n))) :=
    tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) antitone_notYet
      ⟨0, measure_ne_top μ _⟩
  have hsum := (ENNReal.tendsto_nat_tsum fun n => μ (A ∩ f ⁻¹' notYet f A n)).add htail
  have heq : (fun N => ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A N))
      = fun _ : ℕ => μ univ :=
    funext (sum_measure_inter_notYet hf hA)
  rw [heq] at hsum
  have h1 := tendsto_nhds_unique hsum tendsto_const_nhds
  have hU := measurableSet_iUnion_preimage_iterate hf.measurable hA
  rw [iInter_notYet, ← measure_add_measure_compl hU] at h1
  exact (add_left_inj_of_ne_top (measure_ne_top μ _)).mp h1
end Kac
