-- Prove2me | solution 1 for GlobalTheory.ZeroGapNearOne.exists_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:11.352967+00:00
-- url     : https://prove2.me/submissions/5fb315c0-6005-433a-886f-e8280f4b1b90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_weaken
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_of_region
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_real_case
import Theorems.Thm_GlobalTheory_DirichletDeriv_exists_norm_deriv_LFunction_le
import Theorems.Thm_GlobalTheory_LOneLower_exists_le_norm_LFunction_one
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_zero_free_region
import Theorems.Thm_GlobalTheory_ZeroFreePrincipal_zero_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.ZeroGapNearOne
namespace GlobalTheory.ZeroGapNearOne
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 →
      c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  obtain ⟨a, ha, Ha⟩ := GlobalTheory.LOneLower.exists_le_norm_LFunction_one
  obtain ⟨C, hC, HC⟩ := GlobalTheory.DirichletDeriv.exists_norm_deriv_LFunction_le
  obtain ⟨d, hd, Hd⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨e, he, He⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min (min 1 (a / (4 * C))) (min d e), by positivity, ?_⟩
  intro q _ χ ρ hne hz him
  have hc : 0 < min (min 1 (a / (4 * C))) (min d e) := by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  by_cases h1 : χ = 1
  · subst h1
    have hρ : ρ ≠ 1 := hne.resolve_left (by simp)
    exact of_region hq hc ((min_le_right _ _).trans (min_le_right _ _)) him (He q ρ hρ hz)
  by_cases h2 : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0
  · exact of_region hq hc ((min_le_right _ _).trans (min_le_left _ _)) him (Hd q χ ρ h1 hz h2)
  push_neg at h2
  obtain ⟨hsq, hreal⟩ := h2
  have hlt : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ hne (not_lt.1 h) hz
  by_cases h3 : 1 / Real.log (3 * q) ≤ 1 - ρ.re
  · exact (weaken hq hc ((min_le_left _ _).trans (min_le_left _ _))).trans h3
  push_neg at h3
  refine real_case hq hC (by linarith) hc ((min_le_left _ _).trans (min_le_right _ _)) ?_
  refine (Ha q χ h1 hsq).trans ?_
  have hconv : Convex ℝ {z : ℂ | z.im = 0 ∧ ρ.re ≤ z.re ∧ z.re ≤ 1} := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨by simp [hx1, hy1], ?_, ?_⟩
    · simp only [add_re, smul_re, smul_eq_mul]
      have : ρ.re = s * ρ.re + t * ρ.re := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx2 hs, mul_le_mul_of_nonneg_left hy2 ht]
    · simp only [add_re, smul_re, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx3 hs, mul_le_mul_of_nonneg_left hy3 ht]
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := LFunction χ)
    (C := C * Real.log (3 * q) ^ 2) (x := ρ) (y := 1)
    (fun z _ => differentiable_LFunction h1 z)
    (fun z hz' => by
      obtain ⟨h4, h5, h6⟩ := hz'
      have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h4])
      rw [this]
      exact HC q χ h1 z.re (by linarith) h6)
    hconv ⟨hreal, le_rfl, hlt.le⟩ ⟨by simp, by simpa using hlt.le, by simp⟩
  rw [hz, sub_zero] at key
  have hn : ‖(1 : ℂ) - ρ‖ = 1 - ρ.re := by
    have : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rwa [hn] at key
end GlobalTheory.ZeroGapNearOne
