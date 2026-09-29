-- Prove2me | solution 1 for Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b79be3ff-fafa-5c09-ad44-3c3680b6b68f

import Mathlib
import Definitions.Def_SemilocalAdicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (H : ℕ → Type v) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (φ : ∀ n, H n →ₗ[R] H (n + 1)) (hφ : ∀ n, Function.Surjective (φ n))
    (N : ℕ) (hfin : ∀ n, N ≤ n → Module.Finite R (H n))
    (htors : ∀ n, N ≤ n → ∃ k : ℕ, ∀ x : H n, ϖ ^ k • x = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Function.Bijective (φ n) := by
  classical
  haveI : IsNoetherianRing R := inferInstance

  have hfl : ∀ n, N ≤ n → Module.length R (H n) ≠ ⊤ := by
    intro n hn
    obtain ⟨k, hk⟩ := htors n hn
    haveI := hfin n hn
    haveI : IsNoetherian R (H n) := inferInstance
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance
    haveI : IsArtinianRing (R ⧸ (maximalIdeal R) ^ k) := Ideal.isArtinianRing_quotient_pow _ k
    haveI : IsArtinian R (H n) := by
      refine isArtinian_of_finite_of_smul_eq_zero ((maximalIdeal R) ^ k) (fun i hi m => ?_)
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hi
      obtain ⟨r, rfl⟩ := hi
      rw [mul_smul, hk, smul_zero]
    exact Module.length_ne_top

  set ℓ : ℕ → ℕ := fun i => (Module.length R (H (N + i))).toNat with hℓ
  have hℓcoe : ∀ i, (ℓ i : ℕ∞) = Module.length R (H (N + i)) := fun i => ENat.coe_toNat (hfl _ (Nat.le_add_right N i))
  have hanti : ∀ i, ℓ (i + 1) ≤ ℓ i := by
    intro i
    have h := Module.length_le_of_surjective (φ (N + i)) (hφ (N + i))
    have : (ℓ (i + 1) : ℕ∞) ≤ ℓ i := by
      rw [hℓcoe, hℓcoe, show N + (i + 1) = N + i + 1 from (Nat.add_assoc N i 1).symm]; exact h
    exact_mod_cast this
  have hanti' : ∀ i j, i ≤ j → ℓ j ≤ ℓ i := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact (hanti _).trans ih

  obtain ⟨m, hm⟩ : ∃ m, ℓ m = sInf (Set.range ℓ) := by
    have := Nat.sInf_mem (Set.range_nonempty ℓ)
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩
  have hconst : ∀ i, m ≤ i → ℓ i = ℓ m := by
    intro i hi
    refine le_antisymm (hanti' m i hi) ?_
    rw [hm]; exact Nat.sInf_le ⟨i, rfl⟩
  refine ⟨N + m, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
  have hi : m ≤ i := by omega
  refine ⟨?_, hφ (N + i)⟩

  have hlen : Module.length R (H (N + i)) = Module.length R (H (N + i + 1)) := by
    rw [← hℓcoe, show N + i + 1 = N + (i + 1) from Nat.add_assoc N i 1, ← hℓcoe, hconst i hi,
      hconst (i + 1) (by omega)]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (φ (N + i))).subtype (φ (N + i))
    (Submodule.subtype_injective _) (hφ (N + i)) (LinearMap.exact_subtype_ker_map (φ (N + i)))
  have hker0 : Module.length R (LinearMap.ker (φ (N + i))) = 0 := by
    have hfin := hfl (N + i + 1) (by omega)
    have hKfin : Module.length R (LinearMap.ker (φ (N + i))) ≠ ⊤ :=
      ne_top_of_le_ne_top (hfl (N + i) (by omega))
        (Module.length_le_of_injective (LinearMap.ker (φ (N + i))).subtype (Submodule.subtype_injective _))
    rw [hlen] at hex
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hKfin
    obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hk, ← hl] at hex
    rw [← hk]
    have : l = k + l := by exact_mod_cast hex
    have : k = 0 := by omega
    simp [this]
  rw [Module.length_eq_zero_iff] at hker0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker (φ (N + i))) ⟨0, Submodule.zero_mem _⟩
  exact congrArg Subtype.val this

end S_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
end P2MW
export P2MW.S_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero (solution)
