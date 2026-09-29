-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bbc6ec54-b330-50dd-bfea-e3a6cb017706

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace P2M
namespace CrossUniv

universe u v

def val {C : Type v} (ξ η : C) : Fin 2 → C := ![ξ, η]

@[scoped simp] theorem val_zero {C : Type v} (ξ η : C) : val ξ η 0 = ξ := rfl
@[scoped simp] theorem val_one {C : Type v} (ξ η : C) : val ξ η 1 = η := rfl

variable {W : Type u} [CommRing W] (π : W) {C : Type v} [CommRing C] [Algebra W C]

theorem val_mem {I : Ideal C} {ξ η : C} (hξ : ξ ∈ I) (hη : η ∈ I) : ∀ i, val ξ η i ∈ I := by
  intro i
  fin_cases i
  · exact hξ
  · exact hη

theorem C_eq_algebraMap (w : W) :
    (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = algebraMap W (MvPowerSeries (Fin 2) W) w := rfl

theorem mkₐ_X_zero : Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 0) = U π := rfl

theorem mkₐ_X_one : Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 1) = V π := rfl

theorem exists_algHom (I : Ideal C) [IsAdicComplete I C] (ξ η : C) (hξ : ξ ∈ I) (hη : η ∈ I)
    (h : ξ * η = algebraMap W C π) :
    ∃ φ : UVCrossingModel W π →ₐ[W] C, φ (U π) = ξ ∧ φ (V π) = η := by
  obtain ⟨Φ, hΦ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin 2) (𝒪 := W) I (val ξ η) (val_mem hξ hη)
  have hΦ0 : Φ (MvPowerSeries.X 0) = ξ := by rw [hΦ 0]; rfl
  have hΦ1 : Φ (MvPowerSeries.X 1) = η := by rw [hΦ 1]; rfl
  have hker : ∀ f ∈ uvCrossingIdeal W π, Φ f = 0 := by
    intro f hf
    have hle : uvCrossingIdeal W π ≤ RingHom.ker Φ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hΦ0, hΦ1,
        C_eq_algebraMap, AlgHom.commutes, h, sub_self]
    exact hle hf
  refine ⟨Ideal.Quotient.liftₐ (uvCrossingIdeal W π) Φ hker, ?_, ?_⟩
  · show Ideal.Quotient.liftₐ (uvCrossingIdeal W π) Φ hker (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = ξ
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact hΦ0
  · show Ideal.Quotient.liftₐ (uvCrossingIdeal W π) Φ hker (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = η
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact hΦ1

theorem algHom_unique (I : Ideal C) [IsHausdorff I C] (ξ η : C) (hξ : ξ ∈ I) (hη : η ∈ I)
    (φ ψ : UVCrossingModel W π →ₐ[W] C) (hφ : φ (U π) = ξ ∧ φ (V π) = η) (hψ : ψ (U π) = ξ ∧ ψ (V π) = η) :
    φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPowerSeries.algHom_ext_of_apply_X_mem (σ := Fin 2) (𝒪 := W) I
  · intro i
    fin_cases i
    · show φ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 0)) ∈ I
      rw [mkₐ_X_zero, hφ.1]; exact hξ
    · show φ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 1)) ∈ I
      rw [mkₐ_X_one, hφ.2]; exact hη
  · intro i
    fin_cases i
    · show φ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 0)) =
        ψ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 0))
      rw [mkₐ_X_zero, hφ.1, hψ.1]
    · show φ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 1)) =
        ψ (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π) (MvPowerSeries.X 1))
      rw [mkₐ_X_one, hφ.2, hψ.2]

end P2M.CrossUniv
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete.P2M P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete.P2M.CrossUniv"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete.P2M"

theorem solution
    {W : Type*} [CommRing W] (π : W) {C : Type*} [CommRing C] [Algebra W C]
    (I : Ideal C) [IsAdicComplete I C] (ξ η : C) (hξ : ξ ∈ I) (hη : η ∈ I) (h : ξ * η = algebraMap W C π) :
    ∃! φ : UVCrossingModel W π →ₐ[W] C, φ (U π) = ξ ∧ φ (V π) = η := by
  obtain ⟨φ, hφ⟩ := P2M.CrossUniv.exists_algHom π I ξ η hξ hη h
  exact ⟨φ, hφ, fun ψ hψ => P2M.CrossUniv.algHom_unique π I ξ η hξ hη ψ φ hψ hφ⟩

end S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete (solution)
