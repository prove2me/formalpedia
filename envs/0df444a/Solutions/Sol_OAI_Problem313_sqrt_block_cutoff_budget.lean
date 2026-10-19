-- Prove2me | solution 1 for OAI.Problem313.sqrt_block_cutoff_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:13:53.277646+00:00
-- url     : https://prove2.me/submissions/bbdff430-2d95-4619-92d4-7596edf03230

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean:L109-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.sqrt_block_cutoff_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Theorems.Thm_OAI_Problem313_block_capture_exp_lower
import Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds

-- ---- from OAI.Combinatorics.SharpThreshold.BlockSize ----
namespace OAI

noncomputable section

namespace Problem313

/-- Pair-inclusion correction for the square-root-sized uniform block. -/
theorem sqrt_block_pair_ratio (n : ℕ) (hn : 2 ≤ n) :
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1) ≤
      1 / Real.sqrt (n : ℝ) := by
  have hnreal : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtone : 1 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  have hfloor := Nat.floor_le (Real.sqrt_nonneg (n : ℝ))
  have hprod := mul_le_mul_of_nonneg_right hfloor (le_of_lt hsqrtpos)
  have hsquare := Real.sq_sqrt (le_of_lt hnpos)
  apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1) hsqrtpos).2
  nlinarith

theorem log_square_div_sqrt_le_half (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := block_capture_exp_lower (Real.log (n : ℝ)) ht
  rw [Real.exp_half, Real.exp_log hnpos] at h
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnpos)).2
  linarith

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphBlockCapture ----
namespace OAI

/-! The graph-combinatorial input to capture of low Fourier levels. -/

namespace Problem313

noncomputable section

/-- The biased Fourier cutoff for a square-root block never exceeds `log n`. -/
theorem sqrt_block_cutoff_le_log (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    0 ≤ sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ∧
      sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have hm := sqrt_block_size_bounds n hn ht
  have hmreal : (1 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega)
  have hlogm : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := Real.log_nonneg hmreal
  have hlogmn : Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by linarith)
    exact_mod_cast hm.2.1
  have hprod := mul_le_mul_of_nonneg_right hsigma1 hlogm
  exact ⟨div_nonneg (mul_nonneg hsigma hlogm) (by norm_num), by linarith⟩

/-- Uniform numerical budget used in detecting supports of at most `k²/2` edges. -/
theorem sqrt_block_cutoff_budget (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  have hsq := pow_le_pow_left₀ hk.1 hk.2 2
  calc
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_block_pair_ratio n hn) (sq_nonneg _)
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) := by ring
    _ ≤ 1 / 2 := log_square_div_sqrt_le_half n hn ht

end

end Problem313

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.sqrt_block_cutoff_budget := @_root_.OAI.Problem313.sqrt_block_cutoff_budget
