-- Prove2me | solution 1 for GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:26.901064+00:00
-- url     : https://prove2.me/submissions/51dfbd20-a2e5-4d8c-94ce-1ce19d414094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyAlgHomAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdjoinAlgebraHomNonempty
namespace GlobalTheory.AdjoinAlgebraHomNonempty
theorem _root_.solution (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e, map_zero])
  have h0F : (h : F) ≠ 0 := fun e => h0 (Subtype.ext e)
  have hu : ∀ y : Submonoid.powers h, IsUnit (S.val y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ h0F).pow n
  have hv : ∀ y : Submonoid.powers h, IsUnit (ψ y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ hh).pow n
  let f : Localization.Away h →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu
  let g : Localization.Away h →ₐ[k] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers h) hv
  have hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F) := fun s => by
    simp [f, IsLocalization.liftAlgHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) z
    have h1 := congrArg f hab
    rw [map_mul, hz, zero_mul, hf] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at hab
    exact (IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab
  have hle : Algebra.adjoin k T ≤ f.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.Away h)
      (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
    refine ⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩
    apply mul_left_cancel₀ h0F
    have e : f u = (h : F) := by rw [hu']; exact hf h
    change (h : F) * f _ = _
    rw [map_mul, hf, ← mul_assoc]
    have e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1 := by
      rw [← e, ← map_mul, Units.mul_inv, map_one]
    rw [e2, one_mul]
  exact ⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩
end GlobalTheory.AdjoinAlgebraHomNonempty
