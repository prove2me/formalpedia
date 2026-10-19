-- Prove2me | solution 1 for OAI.FiniteResampling.Transition.common_atom_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:48:22.628634+00:00
-- url     : https://prove2.me/submissions/476627f2-510e-4dfe-821f-df56cc29771b

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling

open OAI OAI.FiniteResampling OAI.FiniteResampling.Transition
universe uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open scoped BigOperators Matrix
open Filter
variable {I : Type uI} [Fintype I] [Nonempty I]
variable (K : Transition I)
theorem hc_lower_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : lower f ≤ f j :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem hc_le_upper {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : f j ≤ upper f :=
  Finset.le_sup' _ (Finset.mem_univ j)

theorem hc_act_sub {I : Type*} [Fintype I] (K : Transition I) (f : I → ℝ) (c : ℝ) (i : I) :
    K.act f i - c = ∑ j, K.weight i j * (f j - c) := by
  simp only [act, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, K.total, one_mul]

theorem hc_atom_bounds {I : Type*} [Fintype I] [Nonempty I] (K : Transition I)
    (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  constructor
  · have h1 := hc_act_sub K f (lower f) i
    have h2 : K.weight i z * (f z - lower f) ≤ ∑ j, K.weight i j * (f j - lower f) :=
      Finset.single_le_sum (f := fun j => K.weight i j * (f j - lower f))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_lower_le f j))) (Finset.mem_univ z)
    have h3 : a * (f z - lower f) ≤ K.weight i z * (f z - lower f) :=
      mul_le_mul_of_nonneg_right (ha i) (sub_nonneg.mpr (hc_lower_le f z))
    nlinarith
  · have h1 := hc_act_sub K f (upper f) i
    have h2 : ∑ j, K.weight i j * (f j - upper f) ≤ K.weight i z * (f z - upper f) := by
      have := Finset.single_le_sum (f := fun j => K.weight i j * (upper f - f j))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_le_upper f j))) (Finset.mem_univ z)
      simp only [mul_sub, Finset.sum_sub_distrib] at this ⊢
      linarith
    have h3 : K.weight i z * (f z - upper f) ≤ a * (f z - upper f) :=
      mul_le_mul_of_nonpos_right (ha i) (sub_nonpos.mpr (hc_le_upper f z))
    nlinarith

theorem solution (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  exact hc_atom_bounds K z a ha f i

