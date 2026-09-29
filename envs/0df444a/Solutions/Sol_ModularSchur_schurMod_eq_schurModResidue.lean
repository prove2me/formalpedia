-- Prove2me | solution 1 for ModularSchur.schurMod_eq_schurModResidue
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:10:53.721003+00:00
-- url     : https://prove2.me/submissions/6fa9970b-a245-4428-9dce-9dfd86ca42b7

-- Generated from lean/ModularSchur/IntegerBridge.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 1 file-scoped / sub-threshold helper(s)
--   rename  : schurMod_eq_schurModResidue -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_nat_partition_of_residue
import Theorems.Thm_ModularSchur_residue_partition_of_nat
import Mathlib

open Finset
variable {m : ℕ}

namespace ModularSchur

/-- `Nat.findGreatest` only consults its predicate on `[0, n]`; agreement there
    suffices for equality. -/
lemma Nat.findGreatest_congr_aux {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (n : ℕ)
    (h : ∀ k ≤ n, P k ↔ Q k) :
    Nat.findGreatest P n = Nat.findGreatest Q n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hih : Nat.findGreatest P k = Nat.findGreatest Q k :=
      ih (fun j hj => h j (hj.trans (Nat.le_succ k)))
    simp only [Nat.findGreatest_succ]
    by_cases hP : P (k + 1)
    · have hQ : Q (k + 1) := (h (k + 1) le_rfl).mp hP
      rw [if_pos hP, if_pos hQ]
    · have hQ : ¬ Q (k + 1) := fun hQ => hP ((h (k + 1) le_rfl).mpr hQ)
      rw [if_neg hP, if_neg hQ, hih]

end ModularSchur

open ModularSchur in
theorem solution (m k ℓ : ℕ) (hm : 2 ≤ m) :
    schurMod m k ℓ = schurModResidue m k ℓ := by
  classical
  unfold schurMod schurModResidue
  apply Nat.findGreatest_congr_aux
  intro N hN
  constructor
  · rintro ⟨P, hP⟩; exact residue_partition_of_nat hm hN hP
  · rintro ⟨Q, hQ⟩; exact nat_partition_of_residue hm hN hQ
