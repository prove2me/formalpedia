-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.odd_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:10.800182+00:00
-- url     : https://prove2.me/submissions/a1100e8d-39ef-492d-94b9-b7a5025b1f42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (k : Type) [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x)
    (q f : ℕ) (hc : Nat.card k = (q ^ 2) ^ f) (a : k) (ha : a ^ (q ^ 2) = a) (hta : τ a ≠ a) :
    Odd f := by
  classical
  let F : Subfield k := RingHom.eqLocusField τ (RingHom.id k)
  have hF : ∀ x, x ∈ F ↔ τ x = x := fun x => Iff.rfl
  have hδ : a - τ a ≠ 0 := sub_ne_zero.2 hta.symm
  let φ : F × F → k := fun p => p.1.1 + p.2.1 * a
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      have h1 : u + v * a = u' + v' * a := h
      have h2 := congrArg τ h1
      rw [map_add, map_add, map_mul, map_mul, (hF _).1 hu, (hF _).1 hv, (hF _).1 hu',
        (hF _).1 hv'] at h2
      have h3 : (v - v') * (a - τ a) = 0 := by linear_combination h1 - h2
      have h4 : v = v' := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hδ)
      subst h4
      have h5 : u = u' := add_right_cancel h1
      subst h5
      rfl
    · intro x
      have hδ' : τ a - a ≠ 0 := sub_ne_zero.2 hta
      have hv : τ ((x - τ x) / (a - τ a)) = (x - τ x) / (a - τ a) := by
        rw [map_div₀, map_sub, map_sub, hτ, hτ]
        field_simp
        ring
      have hu : τ (x - (x - τ x) / (a - τ a) * a) = x - (x - τ x) / (a - τ a) * a := by
        rw [map_sub, map_mul, hv]
        field_simp
        ring
      exact ⟨(⟨_, (hF _).2 hu⟩, ⟨_, (hF _).2 hv⟩), by simp [φ]⟩
  have hcard : Nat.card F = q ^ f := by
    have h1 := Nat.card_eq_of_bijective φ hbij
    rw [Nat.card_prod, hc, ← sq, ← pow_mul, mul_comm, pow_mul] at h1
    exact Nat.pow_left_injective two_ne_zero h1
  by_contra hodd
  obtain ⟨g, hg⟩ := Nat.not_odd_iff_even.1 hodd
  have hpow : ∀ m : ℕ, a ^ ((q ^ 2) ^ m) = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, ha]
  have has : a ^ (q ^ f) = a := by
    have : q ^ f = (q ^ 2) ^ g := by rw [hg, ← pow_mul, two_mul]
    rw [this, hpow]
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype F := Fintype.ofFinite F
  have hcF : Fintype.card F = q ^ f := by rw [← hcard, Nat.card_eq_fintype_card]
  have h1s : 1 < q ^ f := by rw [← hcF]; exact Fintype.one_lt_card
  have haF : a ∉ (F : Set k).toFinset := by
    rw [Set.mem_toFinset]; exact fun h => hta ((hF a).1 h)
  refine FiniteField.X_pow_card_sub_X_ne_zero k h1s ?_
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (insert a (F : Set k).toFinset) ?_ ?_
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simp [has]
    · rw [Set.mem_toFinset] at hx
      have := congrArg Subtype.val (FiniteField.pow_card (⟨x, hx⟩ : F))
      rw [hcF] at this
      simp only [eval_sub, eval_pow, eval_X]
      exact sub_eq_zero.2 this
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq k h1s, Finset.card_insert_of_notMem haF,
      Set.toFinset_card]
    have : Fintype.card (F : Set k) = q ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card]; exact Fintype.card_congr (Equiv.refl _)
    omega
end GlobalTheory.LocalFiniteOddFixed
