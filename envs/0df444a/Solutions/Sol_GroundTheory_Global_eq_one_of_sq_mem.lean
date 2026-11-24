-- Prove2me | solution 1 for GroundTheory.Global.eq_one_of_sq_mem
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:33:25.385367+00:00
-- url     : https://prove2.me/submissions/be21e6b8-809b-4246-a26d-53a40ba961a0

import Mathlib



theorem solution {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  let T : Set ℝ := (fun w : ℂ => ‖w-1‖) '' s
  have bt : BddAbove T := ⟨1/2, by rintro _ ⟨w,hw,rfl⟩; exact (hs w hw).le⟩
  have nt : T.Nonempty := ⟨_,z,hz,rfl⟩
  have upper (w : ℂ) (hw : w ∈ s) : ‖w-1‖ ≤ (2/3) * sSup T := by
    have hclose := hs w hw
    have tri := norm_sub_le (w + 1) (w - 1)
    rw [show w + 1 - (w - 1) = (2 : ℂ) by ring] at tri
    norm_num at tri
    have big : (3/2 : ℝ) ≤ ‖w + 1‖ := by linarith
    have sq := le_csSup bt (show ‖w ^ 2 - 1‖ ∈ T from ⟨_,hsq w hw,rfl⟩)
    rw [show w ^ 2 - 1 = (w-1)*(w+1) by ring, norm_mul] at sq
    nlinarith [mul_le_mul_of_nonneg_left big (norm_nonneg (w-1))]
  have S := csSup_le nt (show ∀ t ∈ T, t ≤ (2/3) * sSup T by rintro _ ⟨w,hw,rfl⟩; exact upper w hw)
  have Z := upper z hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg _)))
