-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:11.521606+00:00
-- url     : https://prove2.me/submissions/55ccd57d-2b4e-44e9-b587-80af05c807e5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1) := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp hM
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hK' := ih K hxK hK
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    exact (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mpr hK'
end GroundTheory.Arith.SchemeCoh
