-- Prove2me | solution 1 for Kyprianou.Ch04.physicalLargeGridWeightErrorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:41:07.298591+00:00
-- url     : https://prove2.me/submissions/180c3017-4dd5-4967-9bdf-c046e3cf21e2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clippedAffineGridWeightErrorV1
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The physical large-mark ledger gives a uniform finite-variation grid bound. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j Y H L : NNReal → ℝ) (b d : ℝ) (hd : 0 ≤ d)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂ R)
    (hH : ∀ k ∈ Finset.range n, |H (u k)-L (u k)| ≤ d) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n,H (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k)))) -
      (∑ k ∈ Finset.range n,L (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k))))| ≤
      (|b| * (T : ℝ)+(∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d := by
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}
  let a (r : NNReal) := if 1 ≤ |j r| then j r else 0
  have hD : MeasurableSet D := measurableSet_Icc.prod
    (measurableSet_lt measurable_const measurable_id.abs)
  have hledger : (∫ z in D, |z.2| ∂ R) = ∑ r ∈ S,|j r| := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR
      D hD (Subset.rfl) (fun z => |z.2|)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [if_pos]
    exact ⟨⟨r.coe_nonneg,by exact_mod_cast (hS r hr).2.1⟩,(hS r hr).2.2⟩
  have hAff (t : NNReal) (ht : t ≤ T) :
      Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then a r else 0 := by
    let A := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
    have hA : MeasurableSet A := measurableSet_Icc.prod
      (measurableSet_le measurable_const measurable_id.abs)
    have hAD : A ⊆ D := fun z hz =>
      ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast ht)⟩,
        (show (1/2 : ℝ) < 1 by norm_num).trans_le hz.2⟩
    rw [hY t ht,Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR
      A hA hAD (fun z => z.2)]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have he : ((r : ℝ),j r) ∈ A ↔ r ≤ t ∧ 1 ≤ |j r| := by
      simp [A,Set.mem_prod,Set.mem_Icc,r.coe_nonneg]
    by_cases h1 : r ≤ t <;> by_cases h2 : 1 ≤ |j r| <;> simp [he,h1,h2,a]
  intro t ht
  refine (Kyprianou.Ch04.clippedAffineGridWeightErrorV1 T S a Y H L b d hd u hu n
    hAff hH t ht).trans ?_
  change _ ≤ (|b| * (T : ℝ)+(∫ z in D, |z.2| ∂ R)) * d
  rw [hledger]
  apply mul_le_mul_of_nonneg_right _ hd
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro r hr
  by_cases h : 1 ≤ |j r| <;> simp [a,h]
