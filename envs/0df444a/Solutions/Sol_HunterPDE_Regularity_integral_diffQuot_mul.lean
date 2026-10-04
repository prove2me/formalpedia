-- Prove2me | solution 1 for HunterPDE.Regularity.integral_diffQuot_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:56:29.361986+00:00
-- url     : https://prove2.me/submissions/cc49fcc7-1151-4dae-af54-b273b661a54e

import Mathlib
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

open MeasureTheory ENNReal HunterPDE.Regularity in
theorem solution {n : ℕ} (i : Fin n) (h : ℝ) (hh : h ≠ 0) (p q : ℝ≥0∞)
    (hpq : p.HolderConjugate q) (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : MemLp u p volume) (hv : MemLp v q volume) :
    ∫ x, diffQuot i h u x * v x = -∫ x, u x * diffQuot i (-h) v x := by
  have : ENNReal.HolderTriple p q 1 := hpq
  set e : EuclideanSpace ℝ (Fin n) := h • EuclideanSpace.single i (1 : ℝ) with he
  have hu' : MemLp (fun x => u (x + e)) p volume :=
    hu.comp_measurePreserving (measurePreserving_add_right volume e)
  have hv' : MemLp (fun x => v (x - e)) q volume :=
    hv.comp_measurePreserving (measurePreserving_sub_right volume e)
  have I1 : Integrable (fun x => u (x + e) * v x) volume := hu'.integrable_mul hv
  have I2 : Integrable (fun x => u x * v x) volume := hu.integrable_mul hv
  have I3 : Integrable (fun x => u x * v (x - e)) volume := hu.integrable_mul hv'
  have key : ∫ x, u (x + e) * v x = ∫ x, u x * v (x - e) := by
    have := integral_add_right_eq_self (μ := volume) (fun y => u y * v (y - e)) e
    simpa using this
  have hneg : (-h) • EuclideanSpace.single i (1 : ℝ) = -e := by rw [he, neg_smul]
  have L : (fun x => diffQuot i h u x * v x)
      = fun x => (u (x + e) * v x - u x * v x) / h := by
    funext x; simp only [diffQuot, ← he]; ring
  have R : (fun x => u x * diffQuot i (-h) v x)
      = fun x => -((u x * v (x - e) - u x * v x) / h) := by
    funext x; simp only [diffQuot, hneg, ← sub_eq_add_neg]; rw [div_neg]; ring
  rw [L, R, integral_neg, neg_neg, integral_div, integral_div, integral_sub I1 I2,
    integral_sub I3 I2, key]
