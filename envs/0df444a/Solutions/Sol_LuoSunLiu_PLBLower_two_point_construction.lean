-- Prove2me | solution 1 for LuoSunLiu.PLBLower.two_point_construction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:25:23.521756+00:00
-- url     : https://prove2.me/submissions/97ed95e0-25b8-4db8-a055-89ed6850350a

import Mathlib
import Definitions.Def_LuoSunLiu_PLBLower_Model
import Definitions.Def_LuoSunLiu_PLBLower_TwoPoint
set_option autoImplicit false
open LuoSunLiu.PLBLower

theorem solution {d : ℕ} (ξc : Fin d → ℝ) (hpos : ∀ i, 0 < ξc i)
    (C : ℝ) (hC0 : 0 ≤ C) (ju jv : Fin d) (hne : ju ≠ jv)
    (hCu : C < ξc ju) (hCv : C < ξc jv) :
    xiU ξc C ju jv ∈ PB ξc (2 * C) ∧ xiV ξc C ju jv ∈ PB ξc (2 * C) ∧
    xiU ξc C ju jv ⬝ᵥ actU ξc C ju = (ξc ju - C) / (ξc ju + C) ∧
    (ξc ju - C) / (ξc ju + C) ≤ 1 ∧
    xiV ξc C ju jv ⬝ᵥ actU ξc C ju = 1 ∧
    xiV ξc C ju jv ⬝ᵥ actV ξc C jv = (ξc jv - C) / (ξc jv + C) ∧
    (ξc jv - C) / (ξc jv + C) ≤ 1 ∧
    xiU ξc C ju jv ⬝ᵥ actV ξc C jv = 1 := by
  have hu : 0 < ξc ju + C := by linarith
  have hv : 0 < ξc jv + C := by linarith
  have hne' : jv ≠ ju := hne.symm
  have hU_ju : xiU ξc C ju jv ju = ξc ju - C := by
    simp [xiU, Function.update_of_ne hne, ]
  have hU_jv : xiU ξc C ju jv jv = ξc jv + C := by simp [xiU]
  have hV_ju : xiV ξc C ju jv ju = ξc ju + C := by
    simp [xiV, Function.update_of_ne hne]
  have hV_jv : xiV ξc C ju jv jv = ξc jv - C := by simp [xiV]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold PB
    simp only [Set.mem_setOf_eq]
    have : 2 * C / 2 = C := by ring
    rw [this, pi_norm_le_iff_of_nonneg hC0]
    intro i
    by_cases h1 : i = jv
    · subst h1; simp [hU_jv, abs_of_nonneg hC0]
    · by_cases h2 : i = ju
      · subst h2; simp [hU_ju, abs_of_nonneg hC0]
      · simp [xiU, Function.update_of_ne h1, Function.update_of_ne h2, hC0]
  · unfold PB
    simp only [Set.mem_setOf_eq]
    have : 2 * C / 2 = C := by ring
    rw [this, pi_norm_le_iff_of_nonneg hC0]
    intro i
    by_cases h1 : i = jv
    · subst h1; simp [hV_jv, abs_of_nonneg hC0]
    · by_cases h2 : i = ju
      · subst h2; simp [hV_ju, abs_of_nonneg hC0]
      · simp [xiV, Function.update_of_ne h1, Function.update_of_ne h2, hC0]
  · simp only [actU, dotProduct_single, hU_ju]; ring
  · rw [div_le_one hu]; linarith
  · simp only [actU, dotProduct_single, hV_ju]; field_simp
  · simp only [actV, dotProduct_single, hV_jv]; ring
  · rw [div_le_one hv]; linarith
  · simp only [actV, dotProduct_single, hU_jv]; field_simp
