-- Prove2me | solution 1 for OAI.EntropyRateDimension.ProductLaw.entropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:34:34.857655+00:00
-- url     : https://prove2.me/submissions/05770b13-84bd-4c8c-9328-c253ab882289

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
universe uι uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]
theorem h44_nml_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) :
    Real.negMulLog (∏ i, y i) = ∑ i, ∏ j, (if j = i then Real.negMulLog (y j) else y j) := by
  by_cases hz : ∃ k, y k = 0
  · obtain ⟨k, hk⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, Real.negMulLog_zero]
    symm
    refine Finset.sum_eq_zero fun i _ => Finset.prod_eq_zero (Finset.mem_univ k) ?_
    split_ifs <;> simp [hk]
  · push Not at hz
    have e : ∀ i, ∏ j, (if j = i then Real.negMulLog (y j) else y j) =
        -(∏ j, y j) * Real.log (y i) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
      simp only [Real.negMulLog]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum,
      ← Real.log_prod (s := Finset.univ) (f := y) (fun i _ => hz i), Real.negMulLog]

theorem h44_ent_pi {ι κ : Type*} [Fintype ι] [DecidableEq ι] (T : Finset κ) (q : ι → κ → ℝ) :
    ∑ x ∈ Fintype.piFinset (fun _ : ι => T), Real.negMulLog (∏ i, q i (x i)) =
      ∑ i, (∏ j ∈ Finset.univ.erase i, ∑ b ∈ T, q j b) * ∑ b ∈ T, Real.negMulLog (q i b) := by
  simp only [h44_nml_prod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_prod_piFinset T (fun j b => if j = i then Real.negMulLog (q j b) else q j b),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [if_pos rfl]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [if_neg (Finset.ne_of_mem_erase hj)]

theorem solution (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    FiniteEntropy.entropy Finset.univ (weight p) =
      ∑ i, FiniteEntropy.entropy Finset.univ (p i) := by
  unfold FiniteEntropy.entropy weight
  have h := h44_ent_pi (Finset.univ : Finset α) p
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_one (fun j _ => hp j), one_mul]

