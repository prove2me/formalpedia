-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.tensor_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:06.554815+00:00
-- url     : https://prove2.me/submissions/8b1581ca-1b4e-4587-b2bf-73a6cb7bb32b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
import Theorems.Thm_GlobalTheory_CM_TenExp_mem_of_countable
import Theorems.Thm_GlobalTheory_CM_TenExp_exists_lift
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
variable {O M : Type} [CommRing O] [Algebra O ℂ] [AddCommGroup M] [Module O M]
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {X Y V : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [AddCommGroup V] [Module ℂ V] (eqv : M ⊗[O] X ≃ₗ[O] Y) (e₀ : ℂ →ₗ[O] X)
    (hs : Function.Surjective e₀) (hk : ∀ z, e₀ z = 0 ↔ z ∈ Set.range (algebraMap O ℂ)) (ex : V →+ Y)
    (hΛ : Set.Countable {v | ex v = 0}) (P : M →+ V) (hP : ∀ (o : O) a, P (o • a) = algebraMap O ℂ o • P a)
    (hi : Function.Injective P) (hex : ∀ (z : ℂ) a, ex (z • P a) = eqv (a ⊗ₜ e₀ z)) :
    Submodule.span ℂ (Set.range P) = ⊤ ∧ (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
      ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (f : M →+ V'), (∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) →
        ∃ F : V →ₗ[ℂ] V', ∀ a, F (P a) = f a := by
  obtain ⟨Φ, hΦ⟩ := exists_lift P hP
  have hc : ∀ t, ex (Φ t) = eqv (TensorProduct.comm O X M (e₀.rTensor M t)) := fun t => by
    induction t with
    | zero => simp
    | tmul z a => simp [hΦ, hex]
    | add x y hx hy => simp [hx, hy]
  have hker : ∀ t, ex (Φ t) = 0 → ∃ a, t = 1 ⊗ₜ a := fun t ht => by
    rw [hc, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at ht
    obtain ⟨s, rfl⟩ := (rTensor_exact M (f := Algebra.linearMap O ℂ) hk hs t).1 ht
    obtain ⟨a, rfl⟩ := (TensorProduct.lid O M).symm.surjective s
    exact ⟨a, by simp⟩
  have hsurj : Function.Surjective Φ := fun v => by
    refine mem_of_countable hΛ (LinearMap.range Φ) fun z => ?_
    obtain ⟨t, ht⟩ := (eqv.surjective.comp ((TensorProduct.comm O X M).surjective.comp
      (LinearMap.rTensor_surjective M hs))) (ex (z • v))
    refine ⟨z • v - Φ t, ?_, t, by simp⟩
    simp only [Set.mem_setOf_eq, map_sub, hc, ← ht]
    exact sub_self _
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun t ht => by
    obtain ⟨a, rfl⟩ := hker t (by rw [ht, map_zero])
    rw [hΦ, one_smul, map_eq_zero_iff _ hi] at ht
    simp [ht]
  refine ⟨eq_top_iff.2 fun v _ => ?_, fun v => ⟨fun hv => ?_, ?_⟩, fun V' _ _ f hf => ?_⟩
  · obtain ⟨t, rfl⟩ := hsurj v
    induction t with
    | zero => simp
    | tmul z a => rw [hΦ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  · obtain ⟨t, rfl⟩ := hsurj v
    obtain ⟨a, rfl⟩ := hker t hv
    exact ⟨a, by rw [hΦ, one_smul]⟩
  · rintro ⟨a, rfl⟩
    rw [← one_smul ℂ (P a), hex, (hk 1).2 ⟨1, map_one _⟩]
    simp
  · obtain ⟨F, hF⟩ := exists_lift f hf
    refine ⟨F ∘ₗ (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm.toLinearMap, fun a => ?_⟩
    have : P a = LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩ (1 ⊗ₜ a) :=
      ((hΦ 1 a).trans (one_smul _ _)).symm
    rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hF, one_smul]
end GlobalTheory.CM.TenExp
