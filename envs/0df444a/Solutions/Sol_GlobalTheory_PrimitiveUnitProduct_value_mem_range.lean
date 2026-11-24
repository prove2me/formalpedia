-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.value_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:48.425186+00:00
-- url     : https://prove2.me/submissions/ce45a34f-8cee-4a09-b96f-3993219792a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_exists_unit_value

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution {K A Ω F : Type} [Field K] [CommRing A] [Algebra K A]
    [Field Ω] [IsAlgClosed Ω] [Field F] [Algebra K Ω] [Algebra K F] [Algebra Ω F]
    [IsScalarTower K Ω F]
    (H : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) (ι κ : A →ₐ[K] Ω)
    (u : F ⊗[K] A) (hu : IsUnit u)
    (h : Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K Ω F).comp κ)
        (fun _ _ => Commute.all _ _) u = 1) :
    ∃ c : Ω, algebraMap Ω F c =
      Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K Ω F).comp ι)
        (fun _ _ => Commute.all _ _) u := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  let R : Subring F := (algebraMap Ω F).range
  by_contra hn
  have : IsIntegrallyClosedIn R F := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    let e : Ω ≃+* R := RingEquiv.ofBijective (algebraMap Ω F).rangeRestrict
      ⟨fun a b h => (algebraMap Ω F).injective (congrArg Subtype.val h),
        (algebraMap Ω F).rangeRestrict_surjective⟩
    have hx' : IsIntegral Ω x :=
      (IsIntegral.map_of_comp_eq (e.symm : R →+* Ω) (RingHom.id F) (by
        ext y
        obtain ⟨y, rfl⟩ := e.surjective y
        simp
        rfl) hx)
    obtain ⟨y, hy⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω)
      (K := integralClosure Ω F) |>.2 ⟨x, hx'⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := R) hn
  let ω : Ω →+* V := (algebraMap Ω F).codRestrict V (fun y => hV ⟨y, rfl⟩)
  let _ : Algebra K V := (ω.comp (algebraMap K Ω)).toAlgebra
  have : IsScalarTower K V F := IsScalarTower.of_algebraMap_eq fun k =>
    IsScalarTower.algebraMap_apply K Ω F k
  have := H (IsLocalRing.ResidueField V)
  obtain ⟨c, hc⟩ := exists_unit_value (O := V) u v hv
  let φ : A →ₐ[K] V := { ω.comp ι.toRingHom with
    commutes' := fun k => congrArg ω (ι.commutes k) }
  let ψ : A →ₐ[K] V := { ω.comp κ.toRingHom with
    commutes' := fun k => congrArg ω (κ.commutes k) }
  obtain ⟨w, -, hw⟩ := hc φ
  obtain ⟨w', hw'u, hw'⟩ := hc ψ
  have e₁ : (IsScalarTower.toAlgHom K V F).comp φ = (IsScalarTower.toAlgHom K Ω F).comp ι :=
    AlgHom.ext fun _ => rfl
  have e₂ : (IsScalarTower.toAlgHom K V F).comp ψ = (IsScalarTower.toAlgHom K Ω F).comp κ :=
    AlgHom.ext fun _ => rfl
  simp only [e₁] at hw
  simp only [e₂, h] at hw'
  obtain ⟨z, hz⟩ := hw'u.exists_right_inv
  apply hxV
  have : c * algebraMap V F w = algebraMap V F (z * w) := by
    rw [map_mul, ← one_mul (algebraMap V F z), hw', mul_assoc c, ← map_mul _ w' z, hz, map_one,
      mul_one]
  rw [hw, this]
  exact (z * w).2
end GlobalTheory.PrimitiveUnitProduct
