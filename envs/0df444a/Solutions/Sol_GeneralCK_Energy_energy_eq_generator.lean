-- Prove2me | solution 1 for GeneralCK.Energy.energy_eq_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:21:47.201254+00:00
-- url     : https://prove2.me/submissions/7fbebb4a-96fd-4bbd-aaa0-3113a349e4ae

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_energy_generator
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.CubeAnalysis
open scoped BigOperators







theorem sum_slices {n : ℕ} (v : Cube (n+1) → ℝ) :
    ∑ x, v x = (∑ x, slice v false x) + ∑ x, slice v true x := by
  have h := (consEquiv n).sum_comp v
  simpa [consEquiv, slice, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h.symm

theorem mean_succ {n : ℕ} (v : Cube (n+1) → ℝ) :
    mean v = (mean (slice v false) + mean (slice v true)) / 2 := by
  unfold mean
  rw [sum_slices]
  simp only [zpow_neg, zpow_natCast, pow_succ, mul_inv_rev]
  ring



















end GeneralCK.CubeAnalysis

namespace GeneralCK.Energy
open scoped BigOperators
open CubeAnalysis



@[simp] theorem flip_cons_zero {n : ℕ} (b : Bool) (x : Cube n) :
    flip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [flip]

@[simp] theorem flip_cons_succ {n : ℕ} (b : Bool) (x : Cube n) (i : Fin n) :
    flip (Fin.cons b x) i.succ = Fin.cons b (flip x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [flip, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases hk : k = i
    · subst k
      simp [flip]
    · simp [flip, hk]



theorem generatorDensity_cons {n : ℕ} (v : Cube (n+1) → ℝ) (b : Bool)
    (x : Cube n) :
    generatorDensity v (Fin.cons b x) =
      J (slice v b x) * (slice v (!b) x - slice v b x) +
      generatorDensity (slice v b) x := by
  simp only [generatorDensity, Fin.sum_univ_succ, flip_cons_zero, flip_cons_succ,
    slice, mul_add]

theorem mean_add {n : ℕ} (u v : Cube n → ℝ) :
    mean (fun x => u x + v x) = mean u + mean v := by
  simp [mean, Finset.sum_add_distrib, mul_add]



end GeneralCK.Energy
namespace GeneralCK.Energy
end GeneralCK.Energy

open GeneralCK GeneralCK.Energy in
open scoped BigOperators in
open CubeAnalysis in
theorem solution (n : ℕ) (v : Cube n → ℝ) :
    energy n v = mean (fun x => J (v x) * ∑ i, (v (flip x i) - v x)) := by
  change energy n v = mean (generatorDensity v)
  induction n with
  | zero => simp [energy, generatorDensity, mean]
  | succ n ih =>
    rw [energy, ih, ih, mean_succ]
    have hfalse : slice (generatorDensity v) false = fun x =>
        J (slice v false x) * (slice v true x - slice v false x) +
        generatorDensity (slice v false) x := by
      funext x
      exact generatorDensity_cons v false x
    have htrue : slice (generatorDensity v) true = fun x =>
        J (slice v true x) * (slice v false x - slice v true x) +
        generatorDensity (slice v true) x := by
      funext x
      exact generatorDensity_cons v true x
    rw [hfalse, htrue, mean_add, mean_add]
    have hedge : mean (fun x => interiorCost (slice v false x) (slice v true x)) =
        (mean (fun x => J (slice v false x) * (slice v true x - slice v false x)) +
        mean (fun x => J (slice v true x) * (slice v false x - slice v true x))) / 2 := by
      unfold mean interiorCost
      rw [← mul_add, ← Finset.sum_add_distrib, mul_div_assoc]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hedge]
    ring
