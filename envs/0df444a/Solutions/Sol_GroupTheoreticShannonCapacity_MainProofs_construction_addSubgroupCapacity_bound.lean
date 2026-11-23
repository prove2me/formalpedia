-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.construction_addSubgroupCapacity_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:54.219697+00:00
-- url     : https://prove2.me/submissions/8d8ed1ee-e027-47ee-b7ef-06fe3f7f17f0

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_lower_bound
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupIndependenceNumber_ge_card_of_independent
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_ge_root


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n : ℕ) [NeZero n] (k b r s : ℕ)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    let p' := Construction.p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let q' := Construction.q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    ∃ (p'' q'' : ℕ) (_ : NeZero p'') (_ : 0 < q''),
      (p'' : ℚ) = p' ∧ (q'' : ℚ) = q' ∧
      addSubgroupShannonCapacity (fractionGraph p'' q'') ≥ (p'' : ℝ) ^ (1 / (n : ℝ)) := by
  intro p' q'
  obtain ⟨p'', q'', hp''_ne, hq''_pos, hp''_eq, hq''_eq, S, hS_indep, hS_card⟩ :=
    construction_lower_bound n k b r s hk hb hrb
  use p'', q'', hp''_ne, hq''_pos, hp''_eq, hq''_eq
  calc addSubgroupShannonCapacity (fractionGraph p'' q'')
      ≥ (addSubgroupIndependenceNumber (strongPower (fractionGraph p'' q'') n) : ℝ) ^
          (1 / (n : ℝ)) := addSubgroupShannonCapacity_ge_root _ n
            (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    _ ≥ (Nat.card S : ℝ) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast addSubgroupIndependenceNumber_ge_card_of_independent _ S hS_indep
        · positivity
    _ ≥ (p'' : ℝ) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hS_card) (by positivity)
end GroupTheoreticShannonCapacity.MainProofs
