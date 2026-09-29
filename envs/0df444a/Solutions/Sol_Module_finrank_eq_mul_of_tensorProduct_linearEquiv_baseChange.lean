-- Prove2me | solution 1 for Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e6da5785-9e84-5110-9cf5-82c32b68874b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange

set_option autoImplicit false

open TensorProduct

universe u

namespace TorsorRank

theorem isLocalRing_quotient_maximal_pow {R : Type*} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] {n : ℕ}
    (hn : n ≠ 0) : IsLocalRing (R ⧸ m ^ n) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (m ^ n)) := Ideal.Quotient.mk_surjective
  have hbot : Ideal.comap (Ideal.Quotient.mk (m ^ n)) ⊥ = m ^ n := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  refine IsLocalRing.of_unique_max_ideal ⟨m.map (Ideal.Quotient.mk (m ^ n)), ?_, ?_⟩
  · rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have := congrArg (Ideal.comap (Ideal.Quotient.mk (m ^ n))) h
      rw [Ideal.comap_map_of_surjective _ hsurj, hbot, Ideal.comap_top,
        sup_eq_left.mpr (Ideal.pow_le_self hn)] at this
      exact hm.ne_top this
    · exact h
  · intro J hJ
    have hJ' : (J.comap (Ideal.Quotient.mk (m ^ n))).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
    have hle : m ≤ J.comap (Ideal.Quotient.mk (m ^ n)) := by
      rw [← Ideal.IsPrime.pow_le_iff (I := m) hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have heq : J.comap (Ideal.Quotient.mk (m ^ n)) = m := (hm.eq_of_le hJ'.ne_top hle).symm
    rw [← Ideal.map_comap_of_surjective _ hsurj J, heq]

end TorsorRank

open TorsorRank in
theorem solution
    {κ : Type u} [Field κ] {B C D : Type u} [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    [Algebra B C] [IsScalarTower κ B C] [AddCommGroup D] [Module κ D]
    [Module.Finite κ B] [Module.Finite κ C] [Module.Finite κ D] [Module.FaithfullyFlat B C]
    (e : C ⊗[B] C ≃ₗ[C] C ⊗[κ] D) :
    Module.finrank κ C = Module.finrank κ D * Module.finrank κ B := by
  classical

  rcases subsingleton_or_nontrivial C with hC | hC
  · haveI : Subsingleton B := by
      by_contra h
      haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp h
      obtain ⟨m, hm⟩ := Ideal.exists_maximal B
      exact Module.FaithfullyFlat.submodule_ne_top (R := B) (M := C) hm (Subsingleton.elim _ _)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (R := κ) (M := B), mul_zero]
  haveI : Module.Finite B C := Module.Finite.of_restrictScalars_finite κ B C

  set d := Module.finrank κ D with hd
  have hrank : ∀ q : PrimeSpectrum C, Module.rankAtStalk (R := B) C (q.comap (algebraMap B C)) = d := by
    intro q
    have h1 := Module.rankAtStalk_tensorProduct_of_isScalarTower (R := B) (M := C) (S := C) C q
    have h2 := Module.rankAtStalk_tensorProduct_of_isScalarTower (R := κ) (M := D) (S := C) C q
    have h3 := congrFun (Module.rankAtStalk_eq_of_equiv e) q
    rw [h1, h2, Module.rankAtStalk_self, Pi.one_apply, one_mul, one_mul,
      Module.rankAtStalk_eq_finrank_of_free (R := κ) (M := D)] at h3
    exact h3
  have hrank' : ∀ p : PrimeSpectrum B, Module.rankAtStalk (R := B) C p = d := fun p => by
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := B) (B := C) p
    exact hrank q

  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  have hN : (⊥ : Ideal B) = nilradical B ^ (n + 1) := by
    rw [pow_succ, hn, zero_mul]; rfl
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let Bi : MaximalSpectrum B → Type u := fun i => B ⧸ i.asIdeal ^ (n + 1)
  let φ : B ≃ₐ[B] ((i : MaximalSpectrum B) → Bi i) :=
    (AlgEquiv.quotientBot B B).symm.trans
      ((Ideal.quotientEquivAlgOfEq B hN).trans (IsArtinianRing.quotNilradicalPowEquivPi B (n + 1)))

  have hBdim : Module.finrank κ B = ∑ i, Module.finrank κ (Bi i) := by
    rw [← Module.finrank_pi_fintype κ]
    exact (φ.toLinearEquiv.restrictScalars κ).finrank_eq

  let ψ : C ≃ₗ[B] ((i : MaximalSpectrum B) → Bi i ⊗[B] C) :=
    (TensorProduct.lid B C).symm ≪≫ₗ TensorProduct.congr φ.toLinearEquiv (LinearEquiv.refl B C) ≪≫ₗ
      TensorProduct.piLeft B C Bi
  have hfac : ∀ i : MaximalSpectrum B, Module.finrank κ (Bi i ⊗[B] C) = Module.finrank κ (Bi i) * d := by
    intro i
    haveI := i.isMaximal
    haveI : IsLocalRing (Bi i) := isLocalRing_quotient_maximal_pow i.asIdeal n.succ_ne_zero
    haveI : Nontrivial (Bi i) := Ideal.Quotient.nontrivial_iff.mpr
      (fun h => i.isMaximal.ne_top (by
        have := Ideal.pow_le_self (I := i.asIdeal) n.succ_ne_zero
        rw [h] at this
        exact top_le_iff.mp this))
    haveI : Module.Free (Bi i) (Bi i ⊗[B] C) := Module.free_of_flat_of_isLocalRing
    have hr : Module.finrank (Bi i) (Bi i ⊗[B] C) = d := by
      have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Bi i) (M := Bi i ⊗[B] C))
        ⟨IsLocalRing.maximalIdeal (Bi i), inferInstance⟩
      rw [Module.rankAtStalk_baseChange, hrank'] at h1
      exact_mod_cast h1.symm
    rw [← Module.finrank_mul_finrank κ (Bi i) (Bi i ⊗[B] C), hr]
  haveI : ∀ i : MaximalSpectrum B, Module.Finite κ (Bi i ⊗[B] C) := fun i =>
    Module.Finite.trans (Bi i) (Bi i ⊗[B] C)
  haveI : ∀ i : MaximalSpectrum B, Module.Free κ (Bi i ⊗[B] C) := fun i => Module.Free.of_divisionRing κ _
  have hCdim : Module.finrank κ C = ∑ i, Module.finrank κ (Bi i ⊗[B] C) := by
    rw [← Module.finrank_pi_fintype κ]
    exact (ψ.restrictScalars κ).finrank_eq
  rw [hCdim, hBdim, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfac i, mul_comm]

end S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
end P2MW
export P2MW.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange (solution)
