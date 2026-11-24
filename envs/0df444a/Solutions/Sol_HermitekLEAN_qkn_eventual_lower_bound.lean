-- Prove2me | solution 1 for HermitekLEAN.qkn_eventual_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:04.603049+00:00
-- url     : https://prove2.me/submissions/25ea8e19-dd3b-4bda-8bc0-f3eae7862619

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_qkn_top_term_asymptotic
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ k n : ℕ,
      ∃ R c : ℝ,
        1 ≤ R ∧
          0 < c ∧
            ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := by
  intro k n
  obtain ⟨c₀, hc₀ne, hlim⟩ := qkn_top_term_asymptotic k n
  have hc₀pos : 0 < ‖(c₀ : ℂ)‖ := by
    simp_all only [ne_eq, ge_iff_le, norm_real, norm_eq_abs, abs_pos, not_false_eq_true]
  set ε := ‖(c₀ : ℂ)‖ / 2 with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨R₀, hR₀⟩ := hlim ε hε
  refine ⟨max R₀ 1, ε, le_max_right _ _, hε, fun r hr => ?_⟩
  have hrR₀ : r ≥ R₀ := le_trans (le_max_left _ _) hr
  have hrge1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hrge1
  have hspec := hR₀ r hrR₀
  -- We have ‖qkn/r^n - c₀‖ ≤ ε = ‖c₀‖/2
  -- So ‖qkn/r^n‖ ≥ ‖c₀‖ - ε = ε
  have hrnne : (r ^ n : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero n (ne_of_gt hr_pos)
  have hrn_pos : (0 : ℝ) < r ^ n := pow_pos hr_pos n
  have h_tri : ε ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ := by
    have h1 := norm_sub_norm_le (c₀ : ℂ) ((qkn k n r : ℂ) / (r ^ n : ℂ))
    -- h1 : ‖c₀‖ - ‖qkn/r^n‖ ≤ ‖c₀ - qkn/r^n‖
    rw [norm_sub_rev] at h1
    -- h1 : ‖c₀‖ - ‖qkn/r^n‖ ≤ ‖qkn/r^n - c₀‖
    linarith only [hε_def, hspec, h1]
  rw [norm_div] at h_tri
  have hrn_norm : ‖(r ^ n : ℂ)‖ = r ^ n := by
    rw [show (r : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (le_of_lt hrn_pos)]
  rw [hrn_norm] at h_tri
  rw [le_div_iff₀ hrn_pos] at h_tri
  linarith only [h_tri, Complex.norm_real (qkn k n r)]
end HermitekLEAN
