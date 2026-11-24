-- Prove2me | solution 1 for GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:59.551265+00:00
-- url     : https://prove2.me/submissions/096ef51e-e22e-4065-a4b6-afef13ea1669

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  set k := IsLocalRing.ResidueField Λ
  let V := k ⊗[Λ] A
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V

  have hsurj : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)

  have hspan : Submodule.span Λ (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b (fun i => hf i)

  let Φ : (V →ₗ[k] k) → (A →ₗ[Λ] k) := fun g =>
    (g.restrictScalars Λ).comp (TensorProduct.mk Λ k A 1)
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    have h' := LinearMap.congr_fun h y
    simp only [Φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply] at h'
    have e : x ⊗ₜ[Λ] y = x • ((1 : k) ⊗ₜ[Λ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul]
    exact congrArg (x • ·) h'

  have : Finite (A →ₗ[Λ] k) := by
    refine Finite.of_injective (fun g : A →ₗ[Λ] k => fun i => g (f i)) ?_
    intro g₁ g₂ h
    exact LinearMap.ext_on_range hspan (fun i => congr_fun h i)
  have hcard : Nat.card (V →ₗ[k] k) = Nat.card k ^ d := by
    rw [← Nat.card_congr (b.constr k).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
      Fintype.card_fin]
  have hle : Nat.card k ^ d ≤ Nat.card k ^ a := by
    rw [← hcard]; exact (Nat.card_le_card_of_injective Φ hΦ).trans h
  have hk : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hda : d ≤ a := (Nat.pow_le_pow_iff_right hk).mp hle

  refine ⟨fun i => if hi : (i : ℕ) < d then f ⟨i, hi⟩ else 0, ?_⟩
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hda⟩, by simp⟩
end GlobalTheory
