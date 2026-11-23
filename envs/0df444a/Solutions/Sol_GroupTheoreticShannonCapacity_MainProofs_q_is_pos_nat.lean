-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.q_is_pos_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:27.86397+00:00
-- url     : https://prove2.me/submissions/00dcc645-7b53-40c4-8e4c-d46967e2cc38

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_p_q_are_integers

section
namespace GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
private lemma denom_pos_rat (n k b r : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (0 : ℚ) < (r : ℚ) + (k : ℚ) * (b : ℚ)^n := by
  have hbn_pos : (0 : ℚ) < (b : ℚ)^n := by positivity
  have hk_pos : (0 : ℚ) < (k : ℚ) := by positivity
  have hr_nonneg : (0 : ℚ) ≤ (r : ℚ) := by positivity
  linarith [mul_pos hk_pos hbn_pos]
private lemma a_pos_rat (n k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (0 : ℚ) < (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℚ) := by
  simp only [a]
  have hbn_pos : (0 : ℤ) < (b : ℤ)^n := by positivity
  have hk_pos : (0 : ℤ) < (k : ℤ) := by omega
  have hs_nonneg : (0 : ℤ) ≤ (s : ℤ) := by omega
  have hr_nonneg : (0 : ℤ) ≤ (r : ℤ) := by omega
  have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := by omega
  have h : (0 : ℤ) < (k : ℤ) * (b : ℤ)^n + (s : ℤ) * (b : ℤ) + (r : ℤ) := by
    have := mul_pos hk_pos hbn_pos
    have hsb := mul_nonneg hs_nonneg hb_nonneg
    linarith
  exact_mod_cast h
end GroupTheoreticShannonCapacity.MainProofs
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ q' : ℕ, 0 < q' ∧ (q' : ℚ) = Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by
  obtain ⟨_, q'_int, _, hq'_int⟩ := p_q_are_integers n k b r s hn hk hb
  have hq_pos : (0 : ℚ) < Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by
    simp only [Construction.q]
    have hdenom_pos := denom_pos_rat n k b r hk hb
    have ha_pos := a_pos_rat n k b r s hk hb
    have hnum_pos : (0 : ℚ) < (s : ℚ)^(n-1) * (r : ℚ) + (k : ℚ) * (b : ℚ) *
        (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℚ)^(n-1) := by
      have hk_pos : (0 : ℚ) < (k : ℚ) := by positivity
      have hb_pos : (0 : ℚ) < (b : ℚ) := by positivity
      have ha_pow_pos := pow_pos ha_pos (n-1)
      have hterm2_pos := mul_pos (mul_pos hk_pos hb_pos) ha_pow_pos
      have hterm1_nonneg : (0 : ℚ) ≤ (s : ℚ)^(n-1) * (r : ℚ) := by positivity
      linarith
    exact div_pos hnum_pos hdenom_pos
  -- Convert from ℤ to ℕ
  have hq'_int_pos : 0 < q'_int := by
    rw [hq'_int] at hq_pos
    exact_mod_cast hq_pos
  use q'_int.toNat
  constructor
  · exact Int.pos_iff_toNat_pos.mp hq'_int_pos
  · have h1 : (q'_int.toNat : ℤ) = q'_int := Int.toNat_of_nonneg (le_of_lt hq'_int_pos)
    have h2 : (q'_int.toNat : ℚ) = (q'_int : ℚ) := by exact_mod_cast h1
    rw [h2, hq'_int]
end GroupTheoreticShannonCapacity.MainProofs
