-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:19.363028+00:00
-- url     : https://prove2.me/submissions/f077c80e-58dd-4c79-9b24-5a4e13258a36

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_quotient_add_one_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
namespace IsRegularLocalRing
theorem _root_.solution [IsRegularLocalRing R] : IsDomain R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → IsDomain S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (hn.trans h0)
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have hdim : ringKrullDim S = (n : WithBot ℕ∞) := by
      rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hmin : ∀ P ∈ minimalPrimes S, ¬ maximalIdeal S ≤ P := by
      intro P hP hle
      have hPm : P = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.1.1.ne_top) hle
      have : (maximalIdeal S).height = 0 := by
        rw [Ideal.height_eq_zero_iff, ← hPm]; exact hP
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, this] at hdim
      exact h0 (by exact_mod_cast hdim.symm)
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      exact h0 (by rw [← hn, this]; simp)
    classical
    have hfin := minimalPrimes.finite_of_isNoetherianRing S
    obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
        x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
      by_contra! hcon
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
        (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h h1
          · exact ((Set.Finite.mem_toFinset _).mp h).1.1)).mp hcon
      rcases Finset.mem_insert.mp hi with h | h
      · exact hsq (h ▸ hle)
      · exact hmin i ((Set.Finite.mem_toFinset _).mp h) hle
    simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
      Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
    obtain ⟨hx2, hxP⟩ := hxn
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have := ih _ (by omega) (S ⧸ span {x}) rfl
    have hprime : (span {x} : Ideal S).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le
    have hxP' : x ∉ P := hxP P hP
    have hPsmul : P ≤ maximalIdeal S • P := by
      intro y hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp (hPle hy)
      have hz : z ∈ P := (hP.1.1.mem_or_mem hy).resolve_right hxP'
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hz
    have hPbot : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsmul hjac
    have : (⊥ : Ideal S).IsPrime := hPbot ▸ hP.1.1
    exact IsDomain.of_bot_isPrime S
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
