-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.p_is_pos_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:23.701866+00:00
-- url     : https://prove2.me/submissions/8dd9e6a3-5079-4796-bedd-00a8cf4ae77b

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
    ∃ p' : ℕ, 0 < p' ∧ (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by
  obtain ⟨p'_int, _, hp'_int, _⟩ := p_q_are_integers n k b r s hn hk hb
  have hp_pos : (0 : ℚ) < Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by
    simp only [Construction.p]
    have hdenom_pos := denom_pos_rat n k b r hk hb
    have ha_pos := a_pos_rat n k b r s hk hb
    have hnum_pos : (0 : ℚ) < (s : ℚ)^n * (r : ℚ) + (k : ℚ) *
        (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℚ)^n := by
      have hk_pos : (0 : ℚ) < (k : ℚ) := by positivity
      have ha_pow_pos : (0 : ℚ) < (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℚ)^n := pow_pos ha_pos n
      have hterm2_pos := mul_pos hk_pos ha_pow_pos
      have hterm1_nonneg : (0 : ℚ) ≤ (s : ℚ)^n * (r : ℚ) := by positivity
      linarith
    exact div_pos hnum_pos hdenom_pos
  -- Convert from ℤ to ℕ
  have hp'_int_pos : 0 < p'_int := by
    rw [hp'_int] at hp_pos
    exact_mod_cast hp_pos
  use p'_int.toNat
  constructor
  · exact Int.pos_iff_toNat_pos.mp hp'_int_pos
  · have h1 : (p'_int.toNat : ℤ) = p'_int := Int.toNat_of_nonneg (le_of_lt hp'_int_pos)
    have h2 : (p'_int.toNat : ℚ) = (p'_int : ℚ) := by exact_mod_cast h1
    rw [h2, hp'_int]
end GroupTheoreticShannonCapacity.MainProofs
