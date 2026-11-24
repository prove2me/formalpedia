-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TraceIsometry.exists_linearMap_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:31.124625+00:00
-- url     : https://prove2.me/submissions/19ebd6a7-1e48-46ca-ad1d-b476447cc84a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_trace_eq_of_apply_self_eq
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_exists_map_smul_eq
import Theorems.Thm_GlobalTheory_HermDiag_exists_apply_self_ne_zero
import Theorems.Thm_GlobalTheory_HermDiag_finrank_ker_flip_add_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}
universe u v
namespace GlobalTheory.LocalQuad.TraceIsometry
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) (d : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
      [FiniteDimensional E V] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
      (B : V →ₗ[E] V →ₛₗ[c] E) (B' : W →ₗ[E] W →ₛₗ[c] E),
      (∀ x y, c (B x y) = B y x) → (∀ x y, c (B' x y) = B' y x) → finrank E V = d →
      ∀ φ : V →ₗ[F] W, (∀ x, B' (φ x) (φ x) = B x x) →
      ∃ ψ : V →ₗ[E] W, ∀ x y, B' (ψ x) (ψ y) = B x y := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V W _ _ _ _ _ _ _ _ _ B B' hB hB' hd φ₀ hφ₀
  obtain rfl | hne := eq_or_ne B 0
  · exact ⟨0, fun x y => by simp⟩
  obtain ⟨e, he⟩ := GlobalTheory.HermDiag.exists_apply_self_ne_zero h2 hB hne
  have hk := GlobalTheory.HermDiag.finrank_ker_flip_add_one he
  obtain ⟨φ, hφ, hφe⟩ := exists_map_smul_eq h2 hc hF hB' φ₀ hφ₀ he
  have hf : B' (φ₀ e) (φ₀ e) = B e e := hφ₀ e
  generalize φ₀ e = f at hφe hf
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  have hker : ∀ x : LinearMap.ker (B.flip e), φ x ∈ LinearMap.ker (B'.flip f) := by
    intro x
    have hx : B x e = 0 := x.2
    have hx' : B e x = 0 := by rw [← hB, hx, map_zero]
    have h := hp x (B' (φ x) f • e)
    rw [hφe] at h
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, hx', smul_eq_mul,
      RingHom.id_apply, ← hB' (φ x) f] at h
    change B' (φ x) f = 0
    by_contra hne
    exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) hne) (by linear_combination h)
  obtain ⟨ψ, hψ⟩ := ih _ (by omega)
    (B.domRestrict₁₂ (LinearMap.ker (B.flip e)) (LinearMap.ker (B.flip e)))
    (B'.domRestrict₁₂ (LinearMap.ker (B'.flip f)) (LinearMap.ker (B'.flip f)))
    (fun y z => hB y z) (fun y z => hB' y z) rfl
    { toFun := fun x => ⟨φ x, hker x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun s x => Subtype.ext (by simp) }
    (fun x => hφ x)
  replace hψ : ∀ x y : LinearMap.ker (B.flip e), B' (ψ x) (ψ y) = B x y := hψ
  let p : V →ₗ[E] LinearMap.ker (B.flip e) :=
    (LinearMap.id - ((B e e)⁻¹ • B.flip e).smulRight e).codRestrict _ (fun x => by
      have h : (B e e)⁻¹ * B x e * B e e = B x e := by field_simp
      simp [h])
  have hpx : ∀ x, (p x : V) = x - ((B e e)⁻¹ * B x e) • e := fun x => rfl
  refine ⟨(LinearMap.ker (B'.flip f)).subtype ∘ₗ ψ ∘ₗ p + ((B e e)⁻¹ • B.flip e).smulRight f,
    fun x y => ?_⟩
  have h1 : ∀ z, B' (ψ z) f = 0 := fun z => (ψ z).2
  have h3 : ∀ z, B' f (ψ z) = 0 := fun z => by rw [← hB', h1, map_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.flip_apply, map_add,
    LinearMap.map_smulₛₗ, h1, h3, hψ, hpx, hf, map_sub, LinearMap.sub_apply, smul_eq_mul,
    RingHom.id_apply, map_mul, map_inv₀, hB]
  field_simp
  ring
end GlobalTheory.LocalQuad.TraceIsometry
