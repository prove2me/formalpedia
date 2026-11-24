-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.exists_unit_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:53.424204+00:00
-- url     : https://prove2.me/submissions/5edb778c-9b41-4ae2-80cf-e54a148dd4b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_exists_primitive

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
variable {K A O F : Type} [Field K] [CommRing A] [Algebra K A] [CommRing O] [IsDomain O]
  [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K O] [Algebra K F]
  [IsScalarTower K O F]
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution [IsDomain (IsLocalRing.ResidueField O ⊗[K] A)]
    (u v : F ⊗[K] A) (huv : u * v = 1) :
    ∃ c : F, ∀ φ : A →ₐ[K] O, ∃ w : O, IsUnit w ∧
      Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K O F).comp φ)
        (fun _ _ => Commute.all _ _) u = c * algebraMap O F w := by
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (IsLocalRing.ResidueField O ⊗[K] A) inferInstance
  have : Nontrivial (F ⊗[K] A) := inferInstance
  obtain ⟨c, u', hu, hu'⟩ := exists_primitive (O := O) u (left_ne_zero_of_mul_eq_one huv)
  obtain ⟨d, v', hv, hv'⟩ := exists_primitive (O := O) v (right_ne_zero_of_mul_eq_one huv)
  set m := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O F) (AlgHom.id K A) with hm
  have minj : Function.Injective m :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A)
      (IsScalarTower.toAlgHom K O F).toLinearMap (IsFractionRing.injective O F)
  have key : ((c * d) ⊗ₜ[K] (1 : A)) * m (u' * v') = 1 := by
    rw [← huv, hu, hv, map_mul,
      show ((c * d) ⊗ₜ[K] (1 : A)) = (c ⊗ₜ[K] (1 : A)) * (d ⊗ₜ[K] (1 : A)) by simp]
    ring
  have hunit : IsUnit (u' * v') := by
    obtain ⟨a, ha | ha⟩ := ValuationRing.isInteger_or_isInteger O (c * d) |>.elim
      (fun ⟨a, ha⟩ => (⟨a, Or.inl ha⟩ : ∃ a : O, algebraMap O F a = c * d ∨
        algebraMap O F a = (c * d)⁻¹)) (fun ⟨a, ha⟩ => ⟨a, Or.inr ha⟩)
    · refine IsUnit.of_mul_eq_one_right (a ⊗ₜ[K] (1 : A)) (minj ?_)
      rw [map_mul, map_one, ← key]
      simp [m, ha]
    · have hcd : c * d ≠ 0 := by
        intro h
        rw [h] at key
        simp at key
      have h1 : u' * v' = a ⊗ₜ[K] (1 : A) := by
        apply minj
        have : m (a ⊗ₜ[K] (1 : A)) * ((c * d) ⊗ₜ[K] (1 : A)) = 1 := by
          simp only [m, Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', ha,
            AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hcd, mul_one]
          rfl
        rw [← one_mul (m (u' * v')), ← this, mul_assoc, key, mul_one]
      have h2 := mul_ne_zero hu' hv'
      rw [← map_mul, h1] at h2
      have ha' : IsUnit a := by
        by_contra hn
        apply h2
        have : algebraMap O (IsLocalRing.ResidueField O) a = 0 :=
          (IsLocalRing.residue_eq_zero_iff a).mpr hn
        simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', this, zero_tmul]
      rw [h1]
      exact ha'.map (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := O) (B := A))
  refine ⟨c, fun φ => ⟨Algebra.TensorProduct.lift (AlgHom.id K O) φ
    (fun _ _ => Commute.all _ _) u', (isUnit_of_mul_isUnit_left hunit).map _, ?_⟩⟩
  rw [hu, map_mul]
  congr 1
  · simp
  · clear hu hu' key hunit
    induction u' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [m]
    | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.PrimitiveUnitProduct
