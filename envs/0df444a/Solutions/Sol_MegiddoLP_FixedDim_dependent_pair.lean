-- Prove2me | solution 1 for MegiddoLP.FixedDim.dependent_pair
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:00:34.207839+00:00
-- url     : https://prove2.me/submissions/b6e6dc8f-aecd-47d9-912a-01e7e341307a

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

namespace MegiddoLP.FixedDim

/-- The decision rule: `m` is the midpoint, `bi` the right-hand side of `Hᵢ`, `lam` the ratio. -/
noncomputable def aux_dp_F (bi m lam : ℝ) : Ordering → Bool × Ordering
  | .eq => (true, compare m bi)
  | .lt => if m ≤ bi then (true, .lt) else (false, if 0 < lam then .lt else .gt)
  | .gt => if bi ≤ m then (true, .gt) else (false, if 0 < lam then .gt else .lt)

end MegiddoLP.FixedDim

open MegiddoLP.FixedDim

theorem solution {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk lam : ℝ)
    (hlam : lam ≠ 0) (hdep : ai = lam • ak)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak) :
    (ai 0 = 0 ∧ ak 0 = 0) ∧
    ∃ F : Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (ai ⬝ᵥ x) ((bi + lam * bk) / 2))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by
  obtain ⟨hk1, hk0⟩ := hk
  have hi1 : ai 1 = lam * ak 1 := by rw [hdep]; rfl
  have hi0 : ai 0 = lam * ak 0 := by rw [hdep]; rfl
  have hai1 : ai 1 ≠ 0 := by rw [hi1]; exact mul_ne_zero hlam hk1
  have hq : -(ai 0) / ai 1 = -(ak 0) / ak 1 := by
    rw [hi0, hi1]; field_simp
  have h0 : ak 0 = 0 := by
    rcases hi with h | h
    · exact absurd h hai1
    · rw [hq] at h
      have : -(ak 0) / ak 1 = 0 := le_antisymm hk0 h
      rcases div_eq_zero_iff.mp this with h' | h'
      · linarith
      · exact absurd h' hk1
  refine ⟨⟨by rw [hi0, h0, mul_zero], h0⟩, ?_⟩
  refine ⟨aux_dp_F bi ((bi + lam * bk) / 2) lam, ?_⟩
  intro x
  have hs : ai ⬝ᵥ x = lam * (ak ⬝ᵥ x) := by rw [hdep, smul_dotProduct, smul_eq_mul]
  simp only
  rw [hs]
  generalize ak ⬝ᵥ x = t
  rcases lt_trichotomy (lam * t) ((bi + lam * bk) / 2) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    simp only [aux_dp_F]
    split_ifs with h1 h2
    · exact ⟨fun _ => compare_lt_iff_lt.mpr (by linarith), fun hh => absurd hh (by decide)⟩
    · refine ⟨fun hh => absurd hh (by decide), fun _ => compare_lt_iff_lt.mpr ?_⟩
      nlinarith
    · refine ⟨fun hh => absurd hh (by decide), fun _ => compare_gt_iff_gt.mpr ?_⟩
      have hl : lam < 0 := lt_of_le_of_ne (not_lt.mp h2) hlam
      nlinarith
  · rw [compare_eq_iff_eq.mpr h]
    simp only [aux_dp_F]
    exact ⟨fun _ => by rw [h], fun hh => absurd hh (by decide)⟩
  · rw [compare_gt_iff_gt.mpr h]
    simp only [aux_dp_F]
    split_ifs with h1 h2
    · exact ⟨fun _ => compare_gt_iff_gt.mpr (by linarith), fun hh => absurd hh (by decide)⟩
    · refine ⟨fun hh => absurd hh (by decide), fun _ => compare_gt_iff_gt.mpr ?_⟩
      nlinarith
    · refine ⟨fun hh => absurd hh (by decide), fun _ => compare_lt_iff_lt.mpr ?_⟩
      have hl : lam < 0 := lt_of_le_of_ne (not_lt.mp h2) hlam
      nlinarith
