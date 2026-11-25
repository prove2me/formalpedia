-- Prove2me | solution 1 for Kac.toENNReal_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:11:51.407607+00:00
-- url     : https://prove2.me/submissions/8854392b-e446-4ef2-ae3e-3b07fcd6e45a

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (k : ℕ∞) :
    (k : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < k then 1 else 0 := by
  induction k using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.natCast_lt_top, ite_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe m =>
    rw [ENat.toENNReal_coe, tsum_eq_sum (s := Finset.range m)]
    · rw [Finset.sum_congr rfl fun (n : ℕ) (hn : n ∈ Finset.range m) =>
        (show (if (n : ℕ∞) < (m : ℕ∞) then (1 : ℝ≥0∞) else 0) = 1 by
          simp [Finset.mem_range.mp hn])]
      simp
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp [hn]
end Kac
