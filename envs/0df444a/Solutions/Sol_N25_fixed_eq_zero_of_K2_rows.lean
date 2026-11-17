-- Prove2me | solution 1 for N25.fixed_eq_zero_of_K2_rows
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:42.273239+00:00
-- url     : https://prove2.me/submissions/55947584-4bdd-48ef-9815-c22adf86da56

import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_psi_inertia_witness
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_chi71_frobenius_witness

noncomputable section

namespace N25

local instance prime71_N25_fixed_eq_zero_of_K2_rows_sc4550c : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The two nontrivial local characters annihilate invariants of the exact extension. -/
theorem _root_.solution
    {W : Type*} [AddCommGroup W]
    (act : Gal → W → W) (i : ZMod 71 →+ W) (q : W →+ ZMod 71)
    (hi : Function.Injective i) (hexact : q.ker = i.range)
    (hi_galois : ∀ (σ : Gal) (a : ZMod 71), act σ (i a) = i ((psi σ : ZMod 71) * a))
    (hq_galois : ∀ (σ : Gal) (v : W), q (act σ v) = (ExtCitation.cycloChar 71 σ : ZMod 71) * q v)
    (v : W) (hfixed : ∀ τ : G5, act (r5 τ) v = v) : v = 0 := by
  obtain ⟨φ, _, hφ⟩ := chi71_frobenius_witness
  have hq := hq_galois (r5 φ) v
  rw [hfixed φ, hφ] at hq
  change q v = (5 : ZMod 71) * q v at hq
  have hq0 : q v = 0 := by
    have hz : (1 - (5 : ZMod 71)) * q v = 0 := by linear_combination hq
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have hv : v ∈ i.range := by rw [← hexact]; exact hq0
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨τ, _, hτ⟩ := psi_inertia_witness
  have ha := hi_galois (r5 τ) a
  rw [hfixed τ, hτ] at ha
  have hae := hi ha
  change a = (57 : ZMod 71) * a at hae
  have ha0 : a = 0 := by
    have hz : (1 - (57 : ZMod 71)) * a = 0 := by linear_combination hae
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  rw [ha0, map_zero]

end N25
