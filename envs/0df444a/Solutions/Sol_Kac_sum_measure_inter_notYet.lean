-- Prove2me | solution 1 for Kac.sum_measure_inter_notYet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:24:26.40551+00:00
-- url     : https://prove2.me/submissions/79c59ac1-aab5-4756-bdf7-2b4107aad2e7

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_measure_notYet_succ
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
theorem _root_.solution (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) (N : ℕ) :
    ∑ n ∈ Finset.range N, μ (A ∩ f ⁻¹' notYet f A n) + μ (notYet f A N) = μ univ := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← measure_notYet_succ hf hA k]
    exact ih
end Kac
