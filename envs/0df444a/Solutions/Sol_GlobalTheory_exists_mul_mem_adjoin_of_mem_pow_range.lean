-- Prove2me | solution 1 for GlobalTheory.exists_mul_mem_adjoin_of_mem_pow_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:59.833848+00:00
-- url     : https://prove2.me/submissions/bb4ada95-5e07-4902-adcb-e6e42cf34758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulMemAdjoinOfMemPowRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open scoped Pointwise
namespace GlobalTheory
theorem _root_.solution {K T : Type} [Field K] [CommRing T] [Algebra K T]
    {m : ℕ} (x : Fin m → T) (s : T)
    (hs : ∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) :
    ∃ N : ℕ, ∀ t ∈ (Set.range x) ^ N, s * t ∈ Algebra.adjoin K (Set.range x) := by
  set S := Algebra.adjoin K (Set.range x) with hS
  let x' : Fin m → S := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let C : Ideal S :=
    { carrier := {a | s * (a : T) ∈ S}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, mul_add] at *
        exact S.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul] at *
        rw [mul_left_comm]
        exact S.mul_mem c.2 ha }
  have hle : Ideal.span (Set.range x') ≤ C.radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hs i
    exact ⟨n, hn⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span (Set.finite_range x'))
  refine ⟨N, ?_⟩
  have key : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k,
      ∃ a ∈ Ideal.span (Set.range x') ^ k, (a : T) = t := by
    intro k
    induction k with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      subst ht
      exact ⟨1, by simp, rfl⟩
    | succ k ih =>
      intro t ht
      rw [pow_succ] at ht
      obtain ⟨a, ha, b, ⟨i, rfl⟩, rfl⟩ := ht
      obtain ⟨a', ha', rfl⟩ := ih a ha
      refine ⟨a' * x' i, ?_, rfl⟩
      rw [pow_succ]
      exact Ideal.mul_mem_mul ha' (Ideal.subset_span ⟨i, rfl⟩)
  intro t ht
  obtain ⟨a, ha, rfl⟩ := key N t ht
  exact hN ha
end GlobalTheory
