-- Prove2me | solution 1 for GlobalTheory.ClosingLemma.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:44.365887+00:00
-- url     : https://prove2.me/submissions/eed184b6-14ce-43bf-b608-3e705021ce7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FractionalIdeal nonZeroDivisors
open GlobalTheory GlobalTheory.ClosingLemma
namespace GlobalTheory.ClosingLemma
theorem _root_.solution {Ω : Type} [Field Ω] (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S Ω] [IsFractionRing S Ω] (A : ValuationSubring Ω)
    (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  by_contra hcon
  push_neg at hcon
  have hSle : ∀ c : S, A.valuation (algebraMap S Ω c) ≤ 1 := fun c => (A.valuation_le_one_iff _).2 (hS c)
  let M : Submodule S Ω :=
    { carrier := {z | A.valuation z < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * A.valuation z := by
              gcongr; exact hSle c
          _ < 1 := by simpa using hz }
  let N : Submodule S Ω :=
    { carrier := {z | A.valuation z ≤ 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * 1 := by
              gcongr; exact hSle c
          _ = 1 := one_mul 1 }
  let J : FractionalIdeal S⁰ Ω := 1 + spanSingleton S⁰ x
  have hJ1 : (1 : FractionalIdeal S⁰ Ω) ≤ J := by
    show (1 : FractionalIdeal S⁰ Ω) ≤ 1 + spanSingleton S⁰ x
    rw [← sup_eq_add]; exact le_sup_left
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJ1
    exact one_ne_zero (le_antisymm hJ1 (zero_le _))
  have hJN : (J : Submodule S Ω) ≤ N := by
    simp only [J, coe_add, coe_one, coe_spanSingleton]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hz
      exact hSle c
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (A.valuation_le_one_iff _).2 hx
  have hinv : ((J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    intro y hy
    have hy' := (mem_inv_iff hJ0).1 hy
    obtain ⟨s, hs⟩ := (mem_one_iff S⁰).1 (by simpa using hy' 1 (hJ1 (one_mem_one _)))
    have hxJ : x ∈ J := by
      show x ∈ (J : Submodule S Ω)
      simp only [J, coe_add, coe_one, coe_spanSingleton]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    obtain ⟨t, ht⟩ := (mem_one_iff S⁰).1 (hy' x hxJ)
    show A.valuation y < 1
    rw [← hs] at ht ⊢
    exact lt_of_le_of_ne (hSle s) (fun h => hcon s t h ht.symm)
  have hmul : ((J * J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    rw [coe_mul, Submodule.mul_le]
    intro z hz y hy
    show A.valuation (z * y) < 1
    rw [map_mul]
    calc A.valuation z * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hJN hz
      _ < 1 := by rw [one_mul]; exact hinv hy
  rw [mul_inv_cancel₀ hJ0, coe_one] at hmul
  have := hmul (Submodule.one_le.1 le_rfl)
  exact absurd this (by show ¬ A.valuation 1 < 1; simp)
end GlobalTheory.ClosingLemma
