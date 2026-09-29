-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1c11c895-fa78-5797-b10d-de943af2cff8

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace InertFibreAux

theorem restrictAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.IsIntegral) (g : SemilinearAut K F') (g' : SemilinearAut K F)
    (hφeq : ∀ u, φ (g' • u) = g • φ u) (W : Place K F') :
    (g • W).restrictAlong φ hφ = g' • (W.restrictAlong φ hφ) := by
  have hφinv : ∀ u, φ (g'⁻¹ • u) = g⁻¹ • φ u := fun u => by
    rw [eq_inv_smul_iff, ← hφeq, smul_inv_smul]
  apply Place.ext
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  ext u
  show u ∈ ((g • W).restrict F).toValuationSubring ↔ u ∈ (g' • (W.restrict F)).toValuationSubring
  rw [Place.restrict_toValuationSubring, SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_comap,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
  show g⁻¹ • φ u ∈ W.toValuationSubring ↔ φ (g'⁻¹ • u) ∈ W.toValuationSubring
  rw [hφinv]

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

theorem alpha_smul
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    α (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • u) =
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • α u := by
  apply Subtype.ext
  rw [hα_coe, coe_arithmeticGalois_smul, coe_arithmeticGalois_smul, hα_coe]

theorem beta_smul
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    β (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • u) =
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • β u := by
  rw [hβθ, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, alpha_smul p M H hpM α hα_coe, hθgal]

end InertFibreAux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V) = Psp.reduceFst α hα V ∧
    Psp.reduceSnd β hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V) = Psp.reduceSnd β hβ δ V := by
  constructor
  · show Psp.sp (_root_.AlgebraicCurve.Place.restrictAlong α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V)) =
      Psp.sp (V.restrictAlong α hα)
    rw [InertFibreAux.restrictAlong_smul α hα _ _ (InertFibreAux.alpha_smul p M H hpM α hα_coe σ) V]
    exact Psp.d6_inertia σ hσ _
  · show δ (Psp.sp (_root_.AlgebraicCurve.Place.restrictAlong β hβ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V))) =
      δ (Psp.sp (V.restrictAlong β hβ))
    rw [InertFibreAux.restrictAlong_smul β hβ _ _ (InertFibreAux.beta_smul p M H hpM θ α β hα_coe hθgal hβθ σ) V,
      Psp.d6_inertia σ hσ _]

end S_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn (solution)
