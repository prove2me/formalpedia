-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.parseval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:57:05.2207+00:00
-- url     : https://prove2.me/submissions/c7d3193d-a06a-49fa-b28f-cb7b62c6eb89

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierBasis.lean:L85-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.parseval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis

-- ---- from OAI.Combinatorics.SharpThreshold.FourierBasis ----
namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

theorem scalar_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    scalarWeight p c * (1 + chi p b * chi p c) = if b = c then 1 else 0 := by
  have hpos : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
    Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  cases b <;> cases c <;> simp only [scalarWeight, chi, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ite_true, zero_sub]
  all_goals field_simp
  all_goals nlinarith [hs]

theorem character_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : ι → Bool) :
    weight p y * (∑ S : Finset ι, char p S x * char p S y) =
      if x = y then 1 else 0 := by
  classical
  have hk : (∑ S : Finset ι, char p S x * char p S y) =
      ∏ i, (1 + chi p (x i) * chi p (y i)) := by
    simpa [char, Finset.prod_mul_distrib] using
      (Finset.prod_one_add (f := fun i : ι => chi p (x i) * chi p (y i))
        Finset.univ).symm
  rw [hk, weight, ← Finset.prod_mul_distrib]
  simp_rw [scalar_kernel hp hp1]
  simp [Fintype.prod_ite_zero, funext_iff]

theorem inversion {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ S : Finset ι, coeff p g S * char p S x = g x := by
  classical
  simp_rw [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ S : Finset ι, weight p y * g y * char p S y * char p S x) =
        ∑ y, g y * (weight p y * ∑ S : Finset ι, char p S x * char p S y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = ∑ y, g y * (if x = y then 1 else 0) := by
      simp_rw [character_kernel hp hp1]
    _ = g x := by simp

theorem parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S ^ 2) = ∑ x, weight p x * (g x) ^ 2 := by
  classical
  calc
    (∑ S : Finset ι, coeff p g S ^ 2) =
        ∑ S : Finset ι, ∑ x, weight p x * g x * (coeff p g S * char p S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      conv_lhs => rw [pow_two, coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      dsimp [coeff]
      ring
    _ = ∑ x, weight p x * g x * (∑ S : Finset ι, coeff p g S * char p S x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ x, weight p x * (g x) ^ 2 := by
      simp_rw [inversion hp hp1]
      apply Finset.sum_congr rfl
      intro x hx
      ring

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.parseval.{u} := @_root_.OAI.Problem313.BiasedFourier.parseval.{u}
