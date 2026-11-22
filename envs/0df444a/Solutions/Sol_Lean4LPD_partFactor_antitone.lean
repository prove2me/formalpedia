-- Prove2me | solution 1 for Lean4LPD.partFactor_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:26.091921+00:00
-- url     : https://prove2.me/submissions/5ec9d62e-b1f7-4deb-aece-f9f1c13e5cc8

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Theorems.Thm_Lean4LPD_partFactor_denom_pos

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} {s s' : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) (hss : s ≤ s') :
    partFactor j s' ≤ partFactor j s := by
  have hs' : (j : ℝ) ≤ s' := le_trans hs hss
  have hPpos := partFactor_denom_pos hs
  have hP'pos := partFactor_denom_pos hs'
  have hjfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  -- the key termwise product inequality
  have hkey : (s' + j - 1) ^ j * ∏ i ∈ range j, (s - j + 1 + i)
      ≤ (s + j - 1) ^ j * ∏ i ∈ range j, (s' - j + 1 + i) := by
    have hL : (s' + j - 1) ^ j * ∏ i ∈ range j, (s - j + 1 + i)
        = ∏ i ∈ range j, ((s' + j - 1) * (s - j + 1 + i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hR : (s + j - 1) ^ j * ∏ i ∈ range j, (s' - j + 1 + i)
        = ∏ i ∈ range j, ((s + j - 1) * (s' - j + 1 + i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hL, hR]
    refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
    · have hi' : (i : ℝ) ≥ 0 := Nat.cast_nonneg i
      have h1 : (0 : ℝ) ≤ s - j + 1 + i := by linarith
      nlinarith [h1, hs']
    · rw [Finset.mem_range] at hi
      have hij : (i : ℝ) ≤ (j : ℝ) - 1 := by
        have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hi
        linarith
      nlinarith [hss, hij, hj1]
  unfold partFactor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hjfac, hPpos, hP'pos]
end Lean4LPD
