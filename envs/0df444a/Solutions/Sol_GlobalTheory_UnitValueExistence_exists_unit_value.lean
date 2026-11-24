-- Prove2me | solution 1 for GlobalTheory.UnitValueExistence.exists_unit_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:46.028795+00:00
-- url     : https://prove2.me/submissions/b609c19c-ff7d-4805-aebf-00bcc91257c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Theorems.Thm_GlobalTheory_UnitValueExistence_norm_add_lt_one
import Theorems.Thm_GlobalTheory_UnitValueExistence_norm_one_add_eq_one
import Theorems.Thm_GlobalTheory_UnitValueExistence_norm_det_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitValueExistence
open Matrix
namespace GlobalTheory.UnitValueExistence
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith
end GlobalTheory.UnitValueExistence
