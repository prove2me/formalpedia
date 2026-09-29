-- Prove2me | solution 1 for ModularCurve.XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/73203806-6b80-5025-96e8-68664e4c220f

import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation

set_option autoImplicit false

open ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (M : ℕ) (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M)
    (hmem : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
    (hsurj : ∀ z : LaurentSeries (IsLocalRing.ResidueField A),
      z ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z)
    (σ : ↥K ≃ₐ[L] ↥K) (hσA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a)

    (hA₁ : ∀ a : A, algebraMap A ↥K a ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) :
    ∃ θ : IsLocalRing.ResidueField ↥(W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ≃+*
        ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w),
      (∀ (f : ↥(W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((σ (f : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((θ (IsLocalRing.residue _ f) : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) :
            LaurentSeries (IsLocalRing.ResidueField A))
          = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      (∀ a : A, θ (IsLocalRing.residue _ ⟨algebraMap A ↥K a, hA₁ a⟩) =
        algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
          (IsLocalRing.residue A a)) := by
  classical

  obtain ⟨θ₀, hθ₀, hθ₀c⟩ :=
    ModularCurve.XOneP.exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation L K A W₀ hW₀ hnu hA M w hmem hsurj

  let τ : ↥K →+* ↥K := (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom
  have hτ : ∀ f : ↥K, τ f = σ f := fun f => rfl
  have hmemW : ∀ f : ↥K, f ∈ W₀.comap τ ↔ σ f ∈ W₀ := fun f => Iff.rfl
  let e : ↥(W₀.comap τ) ≃+* ↥W₀ :=
    { toFun := fun f => ⟨σ (f : ↥K), (hmemW f).mp f.2⟩
      invFun := fun g => ⟨σ.symm (g : ↥K), by rw [hmemW, AlgEquiv.apply_symm_apply]; exact g.2⟩
      left_inv := fun f => Subtype.ext (σ.symm_apply_apply (f : ↥K))
      right_inv := fun g => Subtype.ext (σ.apply_symm_apply (g : ↥K))
      map_mul' := fun f g => Subtype.ext (map_mul σ (f : ↥K) (g : ↥K))
      map_add' := fun f g => Subtype.ext (map_add σ (f : ↥K) (g : ↥K)) }
  have he : ∀ f : ↥(W₀.comap τ), ((e f : ↥W₀) : ↥K) = σ (f : ↥K) := fun f => rfl

  haveI : IsLocalRing ↥(W₀.comap τ) := inferInstance
  let θ : IsLocalRing.ResidueField ↥(W₀.comap τ) ≃+* ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) :=
    (IsLocalRing.ResidueField.mapEquiv e).trans θ₀
  have hθ : ∀ f : ↥(W₀.comap τ), θ (IsLocalRing.residue _ f) = θ₀ (IsLocalRing.residue ↥W₀ (e f)) := fun f => rfl
  refine ⟨θ, fun f x y hy hf => ?_, fun a => ?_⟩
  · rw [hθ]
    exact hθ₀ (e f) x y hy hf
  · rw [hθ]
    have hfix : e ⟨algebraMap A ↥K a, hA₁ a⟩ = ⟨algebraMap A ↥K a, hA a⟩ := Subtype.ext (hσA a)
    rw [hfix]
    exact hθ₀c a

#print axioms solution

end S_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation (solution)
