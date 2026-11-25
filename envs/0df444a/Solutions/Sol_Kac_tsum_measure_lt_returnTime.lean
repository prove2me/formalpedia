-- Prove2me | solution 1 for Kac.tsum_measure_lt_returnTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:27:40.684805+00:00
-- url     : https://prove2.me/submissions/e839ab30-2b70-445c-a3d6-72a54f2410b1

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_inter_lt_returnTime
public import Theorems.Thm_Kac_pairwise_disjoint_firstHit
public import Theorems.Thm_Kac_iUnion_firstHit
public import Theorems.Thm_Kac_measurableSet_notYet
public import Theorems.Thm_Kac_measure_firstHit_eq
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) :
    ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by
  simp only [inter_lt_returnTime]
  by_cases hAfin : μ A = ∞
  · -- both sides are infinite
    have hsub : A ⊆ ⋃ k : ℕ, f^[k] ⁻¹' A := fun x hx => mem_iUnion.mpr ⟨0, by simpa using hx⟩
    have hU : μ (⋃ k : ℕ, f^[k] ⁻¹' A) = ∞ := top_unique (hAfin ▸ measure_mono hsub)
    have hS : ∑' n : ℕ, μ (A ∩ f ⁻¹' notYet f A n) = ∞ :=
      top_unique (le_trans (by simp [hAfin]) (ENNReal.le_tsum 0))
    rw [hU, hS]
  · rw [← iUnion_firstHit, measure_iUnion pairwise_disjoint_firstHit fun k =>
      (measurableSet_notYet hf.measurable hA k).inter (hf.measurable.iterate k hA)]
    exact tsum_congr fun n => (measure_firstHit_eq hf hA hAfin n).symm
end Kac
