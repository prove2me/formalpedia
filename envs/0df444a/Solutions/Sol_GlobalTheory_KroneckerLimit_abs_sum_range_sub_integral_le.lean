-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.abs_sum_range_sub_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:42.277888+00:00
-- url     : https://prove2.me/submissions/e998319a-75dc-4bbe-b6e8-487df691e915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology MeasureTheory Set
open scoped Real
namespace GlobalTheory.KroneckerLimit
private theorem le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici {f : ℝ → ℝ} (hm : MonotoneOn f (Iic 0))
    (ha : AntitoneOn f (Ici 0)) (t : ℝ) : f t ≤ f 0 := by
  rcases le_total t 0 with h | h
  · exact hm (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
  · exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
end GlobalTheory.KroneckerLimit
end

set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (x : ℝ) (k : ℕ) :
    |∑ i ∈ Finset.range k, f (x + i) - ∫ t in x..x + k, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hbd : ∀ (a lo hi : ℝ), (∀ t ∈ Icc a (a + 1), lo ≤ f t ∧ f t ≤ hi) →
      lo ≤ ∫ t in a..a + 1, f t ∧ ∫ t in a..a + 1, f t ≤ hi := by
    intro a lo hi h
    have hab : a ≤ a + 1 := by linarith
    constructor
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (continuous_const.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun t ht => (h t ht).1)
      simpa using this
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun t ht => (h t ht).2)
      simpa using this
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j : ℕ,
      D j = ∑ i ∈ Finset.range j, f (x + i) - ∫ t in x..x + j, f t := ⟨_, fun j => rfl⟩
  have hstep : ∀ j : ℕ, D (j + 1) = D j + (f (x + j) - ∫ t in (x + j)..(x + j + 1), f t) := by
    intro j
    rw [hD, hD, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring, Finset.sum_range_succ,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable x (x + j))
        (hc.intervalIntegrable (x + j) (x + j + 1))]
    ring
  have key : ∀ j : ℕ, (x + j ≤ 0 → D j ≤ 0) ∧ D j + f (x + j) ≤ f 0 ∧ -f 0 ≤ D j ∧
      (x + j ≤ 0 → -f (x + j) ≤ D j) := by
    intro j
    induction j with
    | zero =>
      have hD0 : D 0 = 0 := by simp [hD]
      simp only [Nat.cast_zero, add_zero, hD0]
      exact ⟨fun _ => le_rfl, by linarith [htop x], by linarith [h0 0], fun _ => by linarith [h0 x]⟩
    | succ j ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      rw [hstep j, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring]
      rcases le_or_gt (x + j + 1) 0 with hl | hl
      · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j)) (f (x + j + 1)) (fun t ht =>
          ⟨hm (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith [ht.2])) ht.1,
           hm (Set.mem_Iic.2 (by linarith [ht.2])) (Set.mem_Iic.2 hl) ht.2⟩)
        have e1 := ih1 (by linarith)
        have e4 := ih4 (by linarith)
        refine ⟨fun _ => by linarith, by linarith [htop (x + j + 1)],
          by linarith [htop (x + j + 1)], fun _ => by linarith⟩
      · rcases le_or_gt 0 (x + j) with hr | hr
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j + 1)) (f (x + j)) (fun t ht =>
            ⟨ha (Set.mem_Ici.2 (by linarith [ht.1])) (Set.mem_Ici.2 (by linarith)) ht.2,
             ha (Set.mem_Ici.2 hr) (Set.mem_Ici.2 (by linarith [ht.1])) ht.1⟩)
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j) + f (x + j + 1) - f 0) (f 0) (fun t ht => by
            refine ⟨?_, htop t⟩
            rcases le_total t 0 with h | h
            · have := hm (Set.mem_Iic.2 hr.le) (Set.mem_Iic.2 h) ht.1
              linarith [htop (x + j + 1)]
            · have := ha (Set.mem_Ici.2 h) (Set.mem_Ici.2 hl.le) ht.2
              linarith [htop (x + j)])
          have e1 := ih1 hr.le
          have e4 := ih4 hr.le
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
  obtain ⟨-, h2, h3, -⟩ := key k
  rw [hD] at h2 h3
  rw [abs_le]
  exact ⟨h3, by linarith [h0 (x + k)]⟩
end GlobalTheory.KroneckerLimit
