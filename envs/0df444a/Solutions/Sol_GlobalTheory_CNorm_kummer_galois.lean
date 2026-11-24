-- Prove2me | solution 1 for GlobalTheory.CNorm.kummer_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:58.850878+00:00
-- url     : https://prove2.me/submissions/06eaa94f-ebb1-4db7-bd0e-079f2a0b4c94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_KummerGalois
import Theorems.Thm_GlobalTheory_CNorm_IsKum_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by
  intro p F E _ _ _ _ ζ δ θ σ h
  have hp := h.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero p := ⟨hp0⟩
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime hp h.nonpow
  have hζ : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := h.pow
    rw [h0, zero_pow hp0, eq_comm, map_eq_zero] at h1
    exact h.nonpow 0 (by rw [zero_pow hp0, h1])
  have hsplit : IsSplittingField F E (X ^ p - C δ) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow
    · rw [eq_top_iff, ← h.gen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]
      simp [h.pow]
  have hfin : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ p - C δ)
  have hrank : Module.finrank F E = p :=
    finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hgal : IsGalois F E := isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top h.gen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτ
  have hσp : σ ^ p = 1 :=
    hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hc := h.conj
    rw [h1, AlgEquiv.one_apply] at hc
    have hz : algebraMap F E ζ = 1 := mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])
    exact h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))
  have hord : orderOf σ = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hσp hσ1
  have hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have hτp : (τ θ) ^ p = algebraMap F E δ := by rw [← map_pow, h.pow, AlgEquiv.commutes]
    have hq : (τ θ / θ) ^ p = 1 := by
      rw [div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]
    obtain ⟨i, -, hi⟩ := (h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i, hext _ _ ?_⟩
    rw [zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]
  let e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E := adjoinRootXPowSubCEquiv hζ hirr h.pow
  refine ⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩
  intro L _ _ r hr
  refine ⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp
    e.symm.toAlgHom, ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root,
    AdjoinRoot.liftAlgHom_root]
end GlobalTheory.CNorm
