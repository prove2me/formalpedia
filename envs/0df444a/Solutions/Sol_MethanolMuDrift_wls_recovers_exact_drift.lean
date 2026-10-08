-- Prove2me | solution 1 for MethanolMuDrift.wls_recovers_exact_drift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:20:35.367971+00:00
-- url     : https://prove2.me/submissions/99ca0e7c-ce30-44f6-aeb9-4568ad943a24

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

open MethanolMuDrift in
lemma mmd15f_det_two_mul {n : ℕ} (K σ : Fin n → ℝ) :
    2 * wlsDet K σ = ∑ i, ∑ j, (1 / σ i ^ 2) * (1 / σ j ^ 2) * (K i - K j) ^ 2 := by
  have h : ∀ i j, (1 / σ i ^ 2) * (1 / σ j ^ 2) * (K i - K j) ^ 2 =
      (1 / σ i ^ 2) * (K j ^ 2 / σ j ^ 2) + (K i ^ 2 / σ i ^ 2) * (1 / σ j ^ 2)
        - (2 * (K i / σ i ^ 2)) * (K j / σ j ^ 2) := by
    intro i j; ring
  have hin : ∀ i, ∑ j, (1 / σ i ^ 2) * (1 / σ j ^ 2) * (K i - K j) ^ 2 =
      (1 / σ i ^ 2) * wSumKK K σ + (K i ^ 2 / σ i ^ 2) * wSum σ
        - (2 * (K i / σ i ^ 2)) * wSumK K σ := by
    intro i
    simp only [h]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  unfold wlsDet wSum wSumKK wSumK
  ring

open MethanolMuDrift in
lemma mmd15f_det_pos {n : ℕ} (K σ : Fin n → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hK : ∃ i j, K i ≠ K j) : 0 < wlsDet K σ := by
  have h2 := mmd15f_det_two_mul K σ
  have hw : ∀ i, 0 < 1 / σ i ^ 2 := fun i => by
    have := hσ i; positivity
  have hnn : ∀ i j, 0 ≤ (1 / σ i ^ 2) * (1 / σ j ^ 2) * (K i - K j) ^ 2 := fun i j => by
    have := hw i; have := hw j; positivity
  obtain ⟨i0, j0, hij⟩ := hK
  have hpos : 0 < ∑ i, ∑ j, (1 / σ i ^ 2) * (1 / σ j ^ 2) * (K i - K j) ^ 2 := by
    apply Finset.sum_pos'
    · intro i _; exact Finset.sum_nonneg (fun j _ => hnn i j)
    · refine ⟨i0, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro j _; exact hnn i0 j
      · refine ⟨j0, Finset.mem_univ _, ?_⟩
        have := hw i0; have := hw j0
        have : 0 < (K i0 - K j0) ^ 2 := by
          have : K i0 - K j0 ≠ 0 := sub_ne_zero.mpr hij
          positivity
        positivity
  linarith

open MethanolMuDrift in
theorem solution {n : ℕ} (K σ : Fin n → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hK : ∃ i j, K i ≠ K j) (a δ : ℝ) :
    muDriftEstimate K (fun i => a - speedOfLight * δ * K i) σ = δ ∧
      wlsIntercept K (fun i => a - speedOfLight * δ * K i) σ = a := by
  have hD := (mmd15f_det_pos K σ hσ hK).ne'
  have hc : speedOfLight ≠ 0 := by unfold speedOfLight; norm_num
  have hV : wSumV (fun i => a - speedOfLight * δ * K i) σ
      = a * wSum σ - speedOfLight * δ * wSumK K σ := by
    unfold wSumV wSum wSumK
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have hKV : wSumKV K (fun i => a - speedOfLight * δ * K i) σ
      = a * wSumK K σ - speedOfLight * δ * wSumKK K σ := by
    unfold wSumKV wSumK wSumKK
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  constructor
  · unfold muDriftEstimate wlsSlope
    rw [hV, hKV]
    have : wSum σ * (a * wSumK K σ - speedOfLight * δ * wSumKK K σ) -
        wSumK K σ * (a * wSum σ - speedOfLight * δ * wSumK K σ)
        = -(speedOfLight * δ) * wlsDet K σ := by unfold wlsDet; ring
    rw [this]; field_simp
  · unfold wlsIntercept
    rw [hV, hKV]
    have : wSumKK K σ * (a * wSum σ - speedOfLight * δ * wSumK K σ) -
        wSumK K σ * (a * wSumK K σ - speedOfLight * δ * wSumKK K σ)
        = a * wlsDet K σ := by unfold wlsDet; ring
    rw [this]; field_simp
