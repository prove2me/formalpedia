-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.construction_gives_shannon_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:53.735592+00:00
-- url     : https://prove2.me/submissions/99c637de-c7f6-4e20-a9f3-a4f57cf17353

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_lower_bound
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_ge_natCard_of_independent
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_ge_root


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n k b r s : ℕ) [NeZero n] (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hrb : r ≤ b) :
    let pVal := Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)
    let qVal := Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)
    ∃ (p' q' : ℕ) (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      shannonCapacity (fractionGraph p' q') ≥ (p' : ℝ) ^ (1 / (n : ℝ)) := by
  intro pVal qVal
  -- From construction_lower_bound: get independent set S with |S| ≥ p'
  -- Therefore α(E^⊠n) ≥ p', so Θ ≥ α^(1/n) ≥ p'^(1/n)
  obtain ⟨p', q', hp'_ne, hq'_pos, hp'_eq, hq'_eq, S, hS_indep, hS_card⟩ :=
    construction_lower_bound n k b r s hk hb hrb
  use p', q', hp'_ne, hq'_pos, hp'_eq, hq'_eq
  -- S is an independent set of size ≥ p' in the n-th strong power
  -- Therefore (strongPower (fractionGraph p' q') n).indepNum ≥ p'
  calc shannonCapacity (fractionGraph p' q')
      ≥ ((strongPower (fractionGraph p' q') n).indepNum : ℝ) ^ (1 / (n : ℝ)) :=
        shannonCapacity_ge_root (fractionGraph p' q') n (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    _ ≥ (p' : ℝ) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        -- Need: (p' : ℝ) ≤ independenceNumber (strongPower ...)
        -- From independenceNumber_ge_natCard_of_independent: α ≥ Nat.card S
        -- From hS_card: Nat.card S ≥ p'
        have hindep := independenceNumber_ge_natCard_of_independent
          (strongPower (fractionGraph p' q') n) (↑S) hS_indep
        calc (p' : ℝ) ≤ (Nat.card S : ℝ) := by exact_mod_cast hS_card
          _ ≤ ((strongPower (fractionGraph p' q') n).indepNum : ℝ) := by
              exact_mod_cast hindep
end GroupTheoreticShannonCapacity.MainProofs
