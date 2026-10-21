-- Prove2me | solution 1 for LittleCharity.MMS.efx_half_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:04:35.773384+00:00
-- url     : https://prove2.me/submissions/0d20c1f5-2f15-45c8-b9cb-8ade59fe8d10

-- Research direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Argument: Bhaskar Ray Chaudhury, Telikepalli Kavitha, Kurt Mehlhorn, Alkmini Sgouritsa, arXiv:1907.04596v3.
-- Platform formulation: mikedeng1; review: Shuze Chen.
import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
set_option autoImplicit false
open scoped BigOperators
open LittleCharity.MMS

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) :
    (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) ∧
      (1 / 2 : ℝ) * v i (X j) ≤ v i (X i) := by
  classical
  have hsum (g : Fin m) (hg : g ∈ X j) :
      v i (X j) - v i {g} ≤ v i (X i) := by
    have h := hEFX i j g hg
    rw [hadd.1 i ((X j).erase g)] at h
    have he := Finset.sum_erase_add (X j) (fun g => v i {g}) hg
    rw [← hadd.1 i (X j)] at he
    linarith
  have h := Finset.sum_le_sum hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [← hadd.1 i (X j)] at h
  have hc : (2 : ℝ) ≤ (X j).card := by exact_mod_cast hj
  have hp : (0 : ℝ) < (X j).card := by linarith
  have hfirst : (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) := by
    apply (mul_le_mul_iff_right₀ hp).mp
    field_simp
    nlinarith
  refine ⟨hfirst, ?_⟩
  have hfrac : 1 / ((X j).card : ℝ) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hc
  have hn := hadd.2 i (X j)
  nlinarith

