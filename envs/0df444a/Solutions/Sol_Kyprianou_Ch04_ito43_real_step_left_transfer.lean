-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_real_step_left_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:18:55.066138+00:00
-- url     : https://prove2.me/submissions/c5fdc297-822b-45f6-a348-825c9b44f0c0

import Mathlib
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false
/-- Every finite threshold indicator is eventually constant on a left neighbourhood; pass the uniform inequality to the left limit. -/
theorem solution
    (Y YL : ℝ → ℝ) (T : ℝ)
    (hl : ∀ s, 0 < s → s ≤ T → Tendsto Y (nhdsWithin s (Iio s)) (nhds (YL s)))
    (δ : ℝ) (m : ℕ) (b c : ℕ → ℝ)
    (h : ∀ r, 0 ≤ r → r ≤ T →
      |Y r - ∑ i ∈ Finset.range m, c i * (if b i ≤ r then (1:ℝ) else 0)| ≤ δ) :
    ∀ s, 0 < s → s ≤ T →
      |YL s - ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)| ≤ δ := by
  intro s hs ht
  let l := nhdsWithin s (Iio s)
  let W : ℝ → ℝ := fun r => ∑ i ∈ Finset.range m, c i * (if b i ≤ r then (1:ℝ) else 0)
  let L : ℝ := ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)
  have hlt : ∀ᶠ r in l, r < s := self_mem_nhdsWithin
  have hp : ∀ᶠ r in l, 0 < r := nhdsWithin_le_nhds (Ioi_mem_nhds hs)
  have hi : ∀ i : ℕ, ∀ᶠ r in l,
      (if b i ≤ r then (1:ℝ) else 0) = (if b i < s then (1:ℝ) else 0) := by
    intro i
    by_cases hbs : b i < s
    · have he : ∀ᶠ r in l, b i < r := nhdsWithin_le_nhds (Ioi_mem_nhds hbs)
      filter_upwards [he] with r hr
      simp [hbs,hr.le]
    · filter_upwards [hlt] with r hr
      have hnr : ¬ b i ≤ r := not_le_of_gt (hr.trans_le (le_of_not_gt hbs))
      simp [hbs,hnr]
  have hall : ∀ᶠ r in l, ∀ i ∈ Finset.range m,
      (if b i ≤ r then (1:ℝ) else 0) = (if b i < s then (1:ℝ) else 0) := by
    suffices ∀ S : Finset ℕ, ∀ᶠ r in l, ∀ i ∈ S,
        (if b i ≤ r then (1:ℝ) else 0) = (if b i < s then (1:ℝ) else 0) from this _
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hmem ih =>
      filter_upwards [ih,hi i] with r hsmall hlast j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hlast
      · exact hsmall j hj
  have hW : ∀ᶠ r in l, W r = L := by
    filter_upwards [hall] with r hr
    apply Finset.sum_congr rfl
    intro i him
    rw [hr i him]
  have hb : ∀ᶠ r in l, |Y r - L| ≤ δ := by
    filter_upwards [hW,hp,hlt] with r hw hpos hlt'
    rw [← hw]
    exact h r hpos.le (hlt'.le.trans ht)
  haveI : l.NeBot := nhdsWithin_Iio_neBot le_rfl
  have hlim : Tendsto (fun r => |Y r - L|) l (nhds |YL s - L|) :=
    ((hl s hs ht).sub tendsto_const_nhds).abs
  exact le_of_tendsto hlim hb
