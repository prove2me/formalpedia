-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.card_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:51.707085+00:00
-- url     : https://prove2.me/submissions/cd6a457f-ccaa-41fb-8cff-b0c000d9753b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
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
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : M →+ (Fin g → ℂ)} (hP : ∀ (s : 𝓞 E) a i, P (s • a) i = ty i (s : E) * P a i)
    (hs : Submodule.span ℂ (Set.range P) = ⊤) {w : 𝓞 E} {ω : ℂ} (hw : ∀ a, P (w • a) = ω • P a)
    (hu : ∀ f : M →+ ℂ, (∀ a, f (w • a) = ω • f a) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ a, F (P a) = f a)
    (τ : E →+* ℂ) : (τ w = ω → Nat.card {i // ty i = τ} = Module.finrank (𝓞 E) M) ∧
      (τ w ≠ ω → Nat.card {i // ty i = τ} = 0) := by
  classical
  have ext : ∀ F F' : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ a, F (P a) = F' (P a)) → F = F' := fun F F' h =>
    LinearMap.ext_on_range hs h
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · letI : Algebra (𝓞 E) ℂ := (τ.comp (algebraMap (𝓞 E) E)).toAlgebra
    have hsm : ∀ (s : 𝓞 E) (z : ℂ), s • z = τ s * z := fun _ _ => rfl
    haveI : FaithfulSMul (𝓞 E) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2
      (τ.injective.comp (IsFractionRing.injective (𝓞 E) E))
    let f : {i // ty i = τ} → (M →ₗ[𝓞 E] ℂ) := fun i =>
      { toFun := fun a => P a i, map_add' := fun a b => by simp, map_smul' := fun s a => by simp [hP, hsm, i.2] }
    have hli : LinearIndependent ℂ f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := ext (∑ j : {i // ty i = τ}, c j • LinearMap.proj j.1) 0 fun a => by
        simpa [f] using DFunLike.congr_fun hc a
      have := DFunLike.congr_fun this (Pi.single i.1 1)
      simpa [Pi.single_apply, Subtype.val_inj] using this
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := fun φ _ => by
      obtain ⟨F, hF⟩ := hu φ.toAddMonoidHom fun a => by simp [hsm, hτ]
      have h0 : ∀ i, ty i ≠ τ → F (Pi.single i 1) = 0 := fun i hi => by
        obtain ⟨s, hs⟩ : ∃ s : 𝓞 E, ty i s ≠ τ s := by
          by_contra hc
          push Not at hc
          exact hi (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
        have := ext (F ∘ₗ LinearMap.pi fun j => ty j (s : E) • LinearMap.proj j) (τ s • F) fun a => by
          have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j) (P a) =
              P (s • a) := funext fun j => by simp [hP]
          rw [LinearMap.comp_apply, e, hF, LinearMap.smul_apply, hF]
          simp [hsm]
        have := DFunLike.congr_fun this (Pi.single i 1)
        have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j)
            (Pi.single i 1) = ty i s • Pi.single i 1 := funext fun j => by
          by_cases h : j = i <;> simp [h]
        rw [LinearMap.comp_apply, e, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
        exact (mul_eq_mul_right_iff.1 this).resolve_left hs
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => F (Pi.single i.1 1), LinearMap.ext fun a => ?_⟩
      have e := hF a
      rw [LinearMap.pi_apply_eq_sum_univ, ← Fintype.sum_subtype_add_sum_subtype (fun i => ty i = τ),
        Finset.sum_eq_zero (s := Finset.univ (α := {i // ¬ ty i = τ})) fun i _ => by
          have := h0 i.1 i.2
          rw [show (fun j => if i.1 = j then (1 : ℂ) else 0) = Pi.single i.1 1 from by
            funext j; simp [Pi.single_apply, eq_comm], this, smul_zero], add_zero] at e
      refine Eq.trans ?_ e
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 2
      funext j; simp [Pi.single_apply, eq_comm]
    rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis (Module.Basis.mk hli hsp),
      (LinearMap.liftBaseChangeEquiv ℂ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) M ℂ).finrank_eq]
    exact Subspace.dual_finrank_eq
  · rw [Nat.card_eq_zero]
    refine Or.inl ⟨fun i => hτ ?_⟩
    have := ext (τ w • LinearMap.proj i.1) (ω • LinearMap.proj i.1) fun a => by
      have := congrFun (hw a) i.1
      rw [hP, i.2] at this
      simpa using this
    simpa using DFunLike.congr_fun this (Pi.single i.1 1)
end GlobalTheory.CM.TenExp
