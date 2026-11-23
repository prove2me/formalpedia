-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.construction_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:59:27.458323+00:00
-- url     : https://prove2.me/submissions/51b45368-7d77-4ece-a104-bf0c35f7f7ba

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_matrixA_entries_integral
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_matrixB_entries_integral
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_p_is_pos_nat
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_q_is_pos_nat
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_AB_eq_pI_int
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_minDist_A_ge_q_int
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_det_B_eq_p_int
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_matrixToIndependentSet


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution
    (n k b r s : ℕ) [NeZero n] (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    -- Using Construction.lean definitions
    let pVal := Construction.p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let qVal := Construction.q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    -- pVal and qVal are integers (by p_q_are_integers) and positive
    -- The main result: there exists an independent AddSubgroup of size ≥ p
    -- in the n-fold strong power of the fraction graph E_{p/q}
    ∃ (p' q' : ℕ) (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      ∃ S : AddSubgroup (Fin n → ZMod p'),
        (strongPower (fractionGraph p' q') n).IsIndepSet (S : Set (Fin n → ZMod p')) ∧
        Nat.card S ≥ p' := by
  intro pVal qVal
  -- Step 1: Get natural number representatives for p and q
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  obtain ⟨p', hp'_pos, hp'_eq⟩ := p_is_pos_nat n k b r s hn hk hb
  obtain ⟨q', hq'_pos, hq'_eq⟩ := q_is_pos_nat n k b r s hn hk hb
  -- Step 2: Get integer matrix representatives
  obtain ⟨A', hA'⟩ := matrixA_entries_integral n k b r s hn hk hb
  obtain ⟨B', hB'⟩ := matrixB_entries_integral n k b r s hn hb
  -- Step 3: Use p' and q' with required properties
  use p', q'
  have hp'_ne : NeZero p' := ⟨Nat.pos_iff_ne_zero.mp hp'_pos⟩
  use hp'_ne, hq'_pos
  constructor
  · -- p' = pVal
    exact hp'_eq
  constructor
  · -- q' = qVal
    exact hq'_eq
  -- Step 4: Apply bridge lemmas to get the hypotheses for matrixToIndependentSet
  have hAB : A' * B' = p' • 1 := AB_eq_pI_int n k b r s hn hk hb A' B' p' hA' hB' hp'_eq
  have hMinDist : minDistance n (latticeOfMatrix n (A'.map (↑· : ℤ → ℝ))) ≥ q' :=
    minDist_A_ge_q_int n k b r s hk hb hrb A' q' hA' hq'_eq
  have hDetB : B'.det = p' := det_B_eq_p_int n k b r s hn hk hb B' p' hB' hp'_eq
  -- Step 5: Apply matrixToIndependentSet
  obtain ⟨S, hS_indep, hS_card⟩ := matrixToIndependentSet n A' B' p' q' hq'_pos hAB hMinDist
  use S
  constructor
  · exact hS_indep
  · -- Need: Nat.card S ≥ p'
    -- From matrixToIndependentSet: Nat.card S ≥ Int.natAbs B'.det
    -- From hDetB: B'.det = p', so Int.natAbs B'.det = p'
    calc Nat.card S ≥ Int.natAbs B'.det := hS_card
      _ = Int.natAbs (p' : ℤ) := by rw [hDetB]
      _ = p' := by simp
end GroupTheoreticShannonCapacity.MainProofs
