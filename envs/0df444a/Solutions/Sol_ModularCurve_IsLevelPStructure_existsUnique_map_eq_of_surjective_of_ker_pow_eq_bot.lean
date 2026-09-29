-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9b591b7d-6ccd-5a9e-9236-99bba723ff17

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelP

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : IsUnit ((ℓ : ℕ) : T))
    (D' : ModularCurve.LevelPData T') (hD' : ModularCurve.IsLevelPStructure (W.map π) ℓ D') :
    ∃! D : ModularCurve.LevelPData T, D.map π = D' ∧ ModularCurve.IsLevelPStructure W ℓ D := by
  classical
  haveI : Algebra.Etale T (BasisRing W ℓ) :=
    ModularCurve.LevelP.BasisRing.etale W ((Fact.out : ℓ.Prime).odd_of_ne_two hℓ2) (hℓ.mul hΔ)
  letI : Algebra T T' := π.toAlgebra
  have hker : IsNilpotent (RingHom.ker ((Algebra.ofId T T' : T →ₐ[T] T') : T →+* T')) := by
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, by simp [Ideal.zero_eq_bot] at hn ⊢; exact hn⟩
  have hsurj : Function.Surjective (Algebra.ofId T T') := hπ

  obtain ⟨ψ', hψ'b, hψ'D⟩ := ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq W ℓ π D' hD'
  let ψ'ₐ : BasisRing W ℓ →ₐ[T] T' :=
    { toRingHom := ψ'
      commutes' := fun t ↦ by
        change ψ' (algebraMap T (BasisRing W ℓ) t) = π t
        rw [BasisRing.algebraMap_eq, ← hψ'b]; rfl }

  let ψ : BasisRing W ℓ →ₐ[T] T := Algebra.FormallySmooth.liftOfSurjective ψ'ₐ (Algebra.ofId T T') hsurj hker
  have hψ : (Algebra.ofId T T').comp ψ = ψ'ₐ := Algebra.FormallySmooth.comp_liftOfSurjective _ _ hsurj hker
  have hψπ : π.comp (ψ : BasisRing W ℓ →+* T) = ψ' := by
    ext b; exact AlgHom.congr_fun hψ b
  have hψb : (ψ : BasisRing W ℓ →+* T).comp (BasisRing.ofBase W ℓ) = RingHom.id T := by
    ext t; change ψ (algebraMap T (BasisRing W ℓ) t) = t; exact ψ.commutes t

  have hlev : ∀ (χ : BasisRing W ℓ →ₐ[T] T), IsLevelPStructure W ℓ ((basisData W ℓ).map (χ : BasisRing W ℓ →+* T)) := by
    intro χ
    have h := (isLevelPStructure_basisData W ℓ).map (χ : BasisRing W ℓ →+* T)
    have hc : (basisCurve W ℓ).map (χ : BasisRing W ℓ →+* T) = W := by
      rw [basisCurve, WeierstrassCurve.map_map]
      have : (χ : BasisRing W ℓ →+* T).comp (BasisRing.ofBase W ℓ) = RingHom.id T := by
        ext t; change χ (algebraMap T (BasisRing W ℓ) t) = t; exact χ.commutes t
      rw [this, WeierstrassCurve.map_id]
    rwa [hc] at h
  refine ⟨(basisData W ℓ).map (ψ : BasisRing W ℓ →+* T), ⟨?_, hlev ψ⟩, ?_⟩
  · rw [LevelPData.map_map, hψπ, hψ'D]
  ·
    rintro D ⟨hDπ, hD⟩
    have hD0 : IsLevelPStructure (W.map (RingHom.id T)) ℓ D := by rwa [WeierstrassCurve.map_id]
    obtain ⟨χ, hχb, hχD⟩ := ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq W ℓ (RingHom.id T) D hD0
    let χₐ : BasisRing W ℓ →ₐ[T] T :=
      { toRingHom := χ
        commutes' := fun t ↦ by
          change χ (algebraMap T (BasisRing W ℓ) t) = t
          rw [BasisRing.algebraMap_eq, ← RingHom.comp_apply, hχb]; rfl }
    have heq : χₐ = ψ := by
      apply Algebra.FormallyUnramified.lift_unique_of_ringHom π ?_ χₐ ψ
      · change π.comp χ = π.comp (ψ : BasisRing W ℓ →+* T)
        rw [hψπ]
        apply ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq W ℓ π
        · rw [RingHom.comp_assoc, hχb]; rfl
        · exact hψ'b
        · rw [← LevelPData.map_map, hχD, hDπ, hψ'D]
      · obtain ⟨n, hn⟩ := hnil
        exact ⟨n, by simpa [Ideal.zero_eq_bot] using hn⟩
    rw [← hχD]
    change (basisData W ℓ).map (χₐ : BasisRing W ℓ →+* T) = _
    rw [heq]

end S_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot (solution)
