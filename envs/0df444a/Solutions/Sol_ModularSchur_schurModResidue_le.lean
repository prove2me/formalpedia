-- Prove2me | solution 1 for ModularSchur.schurModResidue_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:08:56.708368+00:00
-- url     : https://prove2.me/submissions/e131a403-0d0b-4a37-bf3b-09ce6b850fd3

-- Generated from lean/ModularSchur/Partition.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 1 file-scoped / sub-threshold helper(s)
--   rename  : schurModResidue_le -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_unsafe_witness_residue
import Mathlib

open Finset Nat
variable {m ℓ : ℕ}

namespace ModularSchur

theorem class_containing_n_not_sumFree (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (C : Finset (ZMod m))
    (hn : ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) ∈ C) :
    ¬ IsEllSumFree m ℓ C := by
  unfold IsEllSumFree;
  push_neg;
  refine' ⟨ fun _ => _, fun _ => hn, _, hn, _ ⟩;
  simp +decide;
  convert congr_arg ( fun x : ZMod m => x + ↑ ( m / m.gcd ( ℓ - 1 ) ) ) ( unsafe_witness_residue hm hℓ ) using 1 <;> ring

end ModularSchur

open ModularSchur in
theorem solution (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m k ℓ ≤ m / Nat.gcd m (ℓ - 1) - 1 := by
  -- By contradiction, assume that $n \leq \text{schurModResidue } m k \ell$.
  by_contra h_contra;
  obtain ⟨N, hN⟩ : ∃ N, N = schurModResidue m k ℓ ∧ N ≥ m / Nat.gcd m (ℓ - 1) ∧ ∃ P : Fin k → Finset (ZMod m), IsValidPartition m ℓ k (stableResidues m N) P := by
    refine' ⟨ _, rfl, _, _ ⟩;
    · exact Nat.le_of_pred_lt ( not_le.mp h_contra );
    · apply Classical.byContradiction
      intro h_no_partition;
      convert Nat.findGreatest_eq_iff.mp _;
      rotate_left;
      exact schurModResidue m k ℓ;
      exact m - 1;
      use fun N => ∃ P : Fin k → Finset ( ZMod m ), IsValidPartition m ℓ k ( stableResidues m N ) P;
      exact?;
      · rfl;
      · grind;
  obtain ⟨ hN₁, hN₂, P, hP ⟩ := hN; have := hP.covers ( ( m / Nat.gcd m ( ℓ - 1 ) : ℕ ) : ZMod m ) ; simp_all +decide ;
  obtain ⟨ i, hi ⟩ := this ( Finset.mem_image.mpr ⟨ m / m.gcd ( ℓ - 1 ), Finset.mem_Ioc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ ( by linarith ) ), by linarith ⟩, rfl ⟩ ) ; exact class_containing_n_not_sumFree hm hℓ _ hi ( hP.sumFree i ) ;
