-- Prove2me | solution 1 for ModularSchur.schurModResidue_k1
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:04:52.489981+00:00
-- url     : https://prove2.me/submissions/931ee80a-2222-4016-974e-024f29a36b94

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 3 platform node(s), 2 definition bundle(s)
--   inlined : 4 file-scoped / sub-threshold helper(s)
--   rename  : schurModResidue_k1 -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_k1_partition_iff
import Theorems.Thm_ModularSchur_not_sumFree_of_ge_quot
import Theorems.Thm_ModularSchur_sumFree_min
import Mathlib

open Finset Classical
variable {m ℓ : ℕ}

namespace ModularSchur

/-- For N ≥ ℓ with ℓ < m: ℓ ones sum to ℓ, which lies in stableResidues m N. -/
lemma not_sumFree_of_ge_ell (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlt : ℓ < m) {N : ℕ}
    (hN : ℓ ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  have h1_mem : ∀ _ : Fin ℓ, (1 : ZMod m) ∈ stableResidues m N :=
    fun _ => mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by linarith⟩, by norm_cast⟩
  have hell_mem : (ℓ : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨ℓ, mem_Ioc.mpr ⟨by linarith, hN⟩, by norm_cast⟩
  have hsum : ∑ _ : Fin ℓ, (1 : ZMod m) = ℓ := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact absurd hsum (h (fun _ => 1) h1_mem ℓ hell_mem)

private def k1Pred (m ℓ : ℕ) : ℕ → Prop :=
  fun N => ∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 (stableResidues m N) P

/-- The trivial all-empty partition witnesses the predicate at N=0. -/
private lemma partition_exists_zero (m ℓ k : ℕ) :
    (fun N => ∃ P : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) P) 0 := by
  refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_⟩
  · simp [stableResidues]
  · intro i j _; simp
  · intro i; simp
  · intro i; simp [IsEllSumFree]

/-- findGreatest_spec with k1Pred, so the predicate is syntactically manifest. -/
private lemma k1Pred_at_schur (m ℓ : ℕ) : k1Pred m ℓ (schurModResidue m 1 ℓ) :=
  Nat.findGreatest_spec (Nat.zero_le _) (partition_exists_zero m ℓ 1)

end ModularSchur

open ModularSchur in
theorem solution (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    schurModResidue m 1 ℓ = min (ℓ - 1) (m / ℓ) := by
  apply le_antisymm
  · rw [Nat.le_min]
    refine ⟨?_, ?_⟩
    · -- Upper bound ≤ ℓ-1
      rcases Nat.eq_or_lt_of_le hlm with rfl | hlt
      · exact Nat.findGreatest_le _  -- ℓ = m: trivially ≤ m-1 = ℓ-1
      · -- ℓ < m: if schurModResidue ≥ ℓ, extract violation at that N
        by_contra hc; push_neg at hc
        have hge : ℓ ≤ schurModResidue m 1 ℓ := by omega
        have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
          (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
        exact not_sumFree_of_ge_ell hm hℓ hlt hge hspec
    · -- Upper bound ≤ m/ℓ: if schurModResidue > m/ℓ, extract violation
      by_contra hc; push_neg at hc
      have hge : m / ℓ + 1 ≤ schurModResidue m 1 ℓ := by omega
      have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
        (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
      exact not_sumFree_of_ge_quot hm hℓ hlm hge hspec
  · -- Lower bound: min(ℓ-1, m/ℓ) is achievable
    apply Nat.le_findGreatest
    · have hlt : m / ℓ < m := Nat.div_lt_self (by linarith) (by linarith)
      calc min (ℓ - 1) (m / ℓ) ≤ m / ℓ := Nat.min_le_right _ _
           _ ≤ m - 1 := by omega
    · rw [k1_partition_iff]; exact sumFree_min hm hℓ hlm
