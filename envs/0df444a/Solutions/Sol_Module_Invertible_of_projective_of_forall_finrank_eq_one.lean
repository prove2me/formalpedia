-- Prove2me | solution 1 for Module.Invertible.of_projective_of_forall_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/66410366-40ac-5bd0-abdc-1d4f938985a4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Invertible_of_projective_of_forall_finrank_eq_one

set_option autoImplicit false

universe u v

open TensorProduct

namespace Module
p2m_export "Module" "finrank_zero_of_subsingleton Injective Finite.exists_fin' free_of_flat_of_isLocalRing finrank Free nonempty_linearEquiv_of_finrank_eq_one Dual ext' finrank_baseChange Dual.baseChange_apply_tmul Projective projective_lifting_property"
namespace Invertible
namespace RankOneAux
p2m_open "Module.Invertible Module"

variable {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]

lemma mul_comm_of_equiv {B : Type*} [CommRing B] {L : Type*} [AddCommGroup L] [Module B L]
    (e : B ≃ₗ[B] L) (f g : Module.Dual B L) (l l' : L) : f l * g l' = f l' * g l := by
  obtain ⟨a, rfl⟩ := e.surjective l
  obtain ⟨b, rfl⟩ := e.surjective l'
  have ha : e a = a • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hb : e b = b • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  rw [ha, hb]
  simp only [map_smul, smul_eq_mul]
  ring

variable [Module.Finite A P] [Module.Projective A P]
  (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1)

include h in

lemma finrank_localization_eq_one (m : Ideal A) [m.IsMaximal] :
    Module.finrank (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) = 1 := by
  haveI : Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) :=
    Module.free_of_flat_of_isLocalRing
  have h1 := h (IsLocalRing.ResidueField (Localization.AtPrime m))
  have h2 := Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime m))
    (S := Localization.AtPrime m) (M' := Localization.AtPrime m ⊗[A] P)
  rw [← h2, (AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime m)
    (IsLocalRing.ResidueField (Localization.AtPrime m)) (IsLocalRing.ResidueField (Localization.AtPrime m))
    P).finrank_eq]
  exact h1

include h in

lemma apply_mul_apply_comm (φ ψ : Module.Dual A P) (p q : P) : φ p * ψ q = φ q * ψ p := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro m hm
  haveI : m.IsMaximal := hm
  set B := Localization.AtPrime m
  haveI : Module.Free B (B ⊗[A] P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (finrank_localization_eq_one h m)
  have hΦ : ∀ x : P, φ.baseChange B (1 ⊗ₜ x) = algebraMap A B (φ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have hΨ : ∀ x : P, ψ.baseChange B (1 ⊗ₜ x) = algebraMap A B (ψ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have key := mul_comm_of_equiv e (φ.baseChange B) (ψ.baseChange B) (1 ⊗ₜ p) (1 ⊗ₜ q)
  rw [hΦ, hΦ, hΨ, hΨ] at key
  rw [map_sub, map_mul, map_mul, key, sub_self]

omit h in

lemma exists_dualBasis :
    ∃ (n : ℕ) (x : Fin n → P) (φ : Fin n → Module.Dual A P), ∀ p : P, ∑ i, φ i p • x i = p := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A P
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun i ↦ f (Pi.single i 1), fun i ↦ (LinearMap.proj i).comp g, fun p ↦ ?_⟩
  have hfg : f (g p) = p := congr($hg p)
  have hgp : ∑ i, (g p i) • (Pi.single i (1 : A) : Fin n → A) = g p := by
    simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
    exact Finset.univ_sum_single (g p)
  conv_rhs => rw [← hfg, ← hgp]
  simp [map_sum, map_smul]

include h in
lemma surjective_contractLeft : Function.Surjective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  rw [← LinearMap.range_eq_top]
  by_contra hT
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal _ hT
  letI := Ideal.Quotient.field m
  have hP : (⊤ : Submodule A P) ≤ m • ⊤ := by
    rintro p -
    rw [← hx p]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul (hTm ⟨φ i ⊗ₜ p, contractLeft_apply ..⟩) Submodule.mem_top
  have hs : Subsingleton ((A ⧸ m) ⊗[A] P) := by
    refine (quotTensorEquivQuotSMul P m).toEquiv.subsingleton_congr.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    exact hP
  have h1 := h (A ⧸ m)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

include h in
lemma injective_contractLeft : Function.Injective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  let u : Module.Dual A P ⊗[A] P := ∑ i, φ i ⊗ₜ x i
  have hu : (contractLeft A P).smulRight u = LinearMap.id := by
    refine TensorProduct.ext' fun ψ p ↦ ?_
    simp only [LinearMap.smulRight_apply, contractLeft_apply, LinearMap.id_apply]
    have hφ : ∀ i, ψ p • φ i = φ i p • ψ := fun i ↦ by
      ext q
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm (φ i p), apply_mul_apply_comm h ψ (φ i) p q, mul_comm]
    calc ψ p • u = ∑ i, (ψ p • φ i) ⊗ₜ[A] x i := by
            simp only [u, Finset.smul_sum, smul_tmul']
      _ = ∑ i, ψ ⊗ₜ[A] (φ i p • x i) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [hφ i, smul_tmul]
      _ = ψ ⊗ₜ[A] ∑ i, φ i p • x i := by rw [tmul_sum]
      _ = ψ ⊗ₜ[A] p := by rw [hx]
  intro t₁ t₂ ht
  have h₁ : contractLeft A P t₁ • u = t₁ := congr($hu t₁)
  have h₂ : contractLeft A P t₂ • u = t₂ := congr($hu t₂)
  rw [← h₁, ← h₂, ht]

end Module.Invertible.RankOneAux

theorem solution
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P :=
  ⟨Module.Invertible.RankOneAux.injective_contractLeft h, Module.Invertible.RankOneAux.surjective_contractLeft h⟩

end S_Module_Invertible_of_projective_of_forall_finrank_eq_one
end P2MW
export P2MW.S_Module_Invertible_of_projective_of_forall_finrank_eq_one (solution)
