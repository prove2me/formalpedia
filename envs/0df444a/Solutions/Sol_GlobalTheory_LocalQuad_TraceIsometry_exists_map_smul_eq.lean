-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TraceIsometry.exists_map_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:24.575847+00:00
-- url     : https://prove2.me/submissions/10da3d18-dfe4-468e-a5b0-dbda1c447df2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_finiteDimensional_of_involution
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_exists_traceForm
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_trace_eq_of_apply_self_eq
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq_of_nondegenerate


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
namespace GlobalTheory.LocalQuad.TraceIsometry
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
    {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} (hB' : ∀ x y, c (B' x y) = B' y x)
    (φ : V →ₗ[F] W) (hφ : ∀ x, B' (φ x) (φ x) = B x x) {e : V} (he : B e e ≠ 0) :
    ∃ φ' : V →ₗ[F] W, (∀ x, B' (φ' x) (φ' x) = B x x) ∧ ∀ t : E, φ' (t • e) = t • φ e := by
  have := finiteDimensional_of_involution h2 hc hF
  obtain ⟨b, hb⟩ := exists_traceForm hF hB'
  have hi := (algebraMap F E).injective
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by
    rw [← map_ofNat (algebraMap F E) 2, h, map_zero])
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  obtain ⟨γ, hγ, hγe⟩ := GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
    (c := RingHom.id F) h2F (B := b)
    (fun x y => hi (by rw [RingHom.id_apply, hb, hb, add_comm]))
    (g := φ ∘ₗ (LinearMap.toSpanSingleton E V e).restrictScalars F)
    (f := (LinearMap.toSpanSingleton E W (φ e)).restrictScalars F)
    (fun s t => hi (by
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hp, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hφ]))
    (fun s hs => by
      have h := congrArg (algebraMap F E) (hs s)
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hφ, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        map_zero, smul_eq_mul, RingHom.id_apply] at h
      by_contra hne
      exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) (mul_ne_zero hne he))
        (by linear_combination h))
  refine ⟨γ.toLinearMap ∘ₗ φ, fun x => ?_, fun t => hγe t⟩
  have h := congrArg (algebraMap F E) (hγ (φ x) (φ x))
  rw [hb, hb, hφ] at h
  apply mul_left_cancel₀ h2
  change 2 * B' (γ (φ x)) (γ (φ x)) = _
  linear_combination h
end GlobalTheory.LocalQuad.TraceIsometry
