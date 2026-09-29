-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3217aa67-9975-58e7-bcea-afe08ddc5d49

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair

set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair.ModularCurve ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.constHom UVCrossingModel.constHom_apply"
p2m_open "ModularCurve"
namespace Ws30MaxGen

theorem mem_span_X_of_constantCoeff_eq_zero {W : Type*} [CommRing W] (g : MvPowerSeries (Fin 2) W)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    g ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  classical

  let g' : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then g m else 0
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ g - g' := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    show g m - g' m = 0
    simp only [g', hm, if_true, sub_self]
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ g' := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    show (if m 0 = 0 then g m else 0) = 0
    split_ifs with hm0
    · have : m = 0 := by
        ext i; fin_cases i
        · exact hm0
        · exact hm
      subst this
      exact hg
    · rfl
  obtain ⟨A, hA⟩ := h0
  obtain ⟨B, hB⟩ := h1
  have : g = MvPowerSeries.X 0 * A + MvPowerSeries.X 1 * B := by rw [← hA, ← hB]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

variable {W : Type*} [CommRing W] [IsLocalRing W] (π : W)

theorem maximalIdeal_eq (hπu : ¬ IsUnit π) [IsLocalRing (UVCrossingModel W π)] :
    maximalIdeal (UVCrossingModel W π) =
      (maximalIdeal W).map (UVCrossingModel.constHom π) ⊔ Ideal.span {U π, V π} := by

  have hker : ∀ f ∈ uvCrossingIdeal W π, ((residue W).comp MvPowerSeries.constantCoeff) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hP : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π :
        MvPowerSeries (Fin 2) W) = -π := by
      rw [map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub]
    rw [RingHom.comp_apply, map_mul, hP, map_mul, map_neg, (residue_eq_zero_iff π).mpr
      ((mem_maximalIdeal π).mpr hπu), neg_zero, mul_zero]
  set ρ : UVCrossingModel W π →+* ResidueField W := Ideal.Quotient.lift _ _ hker with hρ
  have hρmk : ∀ f, ρ (UVCrossingModel.mk π f) = residue W (MvPowerSeries.constantCoeff f) := fun f => by
    rw [hρ]; exact Ideal.Quotient.lift_mk _ _ _
  have hsurj : Function.Surjective ρ := by
    intro r
    obtain ⟨w, rfl⟩ := residue_surjective r
    exact ⟨const π w, by rw [const, hρmk, MvPowerSeries.constantCoeff_C]⟩
  have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hsurj
  rw [← eq_maximalIdeal hmax]
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨f, rfl⟩ := mk_surjective π z
    rw [hρmk, residue_eq_zero_iff] at hz

    have hsplit : UVCrossingModel.mk π f =
        UVCrossingModel.constHom π (MvPowerSeries.constantCoeff f) +
          UVCrossingModel.mk π (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by
      rw [UVCrossingModel.constHom_apply, const, ← map_add]; congr 1; ring
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hz)) (Ideal.mem_sup_right ?_)
    have hmem := mem_span_X_of_constantCoeff_eq_zero (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f))
      (by rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self])
    have himg := Ideal.mem_map_of_mem (UVCrossingModel.mk π) hmem
    rw [Ideal.map_span, Set.image_pair] at himg
    exact himg
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro w hw
      rw [Ideal.mem_comap, RingHom.mem_ker, UVCrossingModel.constHom_apply, const, hρmk, MvPowerSeries.constantCoeff_C,
        residue_eq_zero_iff]
      exact hw
    · rw [Ideal.span_le, Set.pair_subset_iff]
      refine ⟨?_, ?_⟩
      · show ρ (U π) = 0
        rw [U, hρmk, MvPowerSeries.constantCoeff_X, map_zero]
      · show ρ (V π) = 0
        rw [V, hρmk, MvPowerSeries.constantCoeff_X, map_zero]

theorem maximalIdeal_eq_span (hπu : ¬ IsUnit π) [IsLocalRing (UVCrossingModel W π)] (π₀ : W)
    (hW : maximalIdeal W = Ideal.span {π₀}) :
    maximalIdeal (UVCrossingModel W π) = Ideal.span {const π π₀, U π, V π} := by
  rw [maximalIdeal_eq π hπu, hW, Ideal.map_span, Set.image_singleton, UVCrossingModel.constHom_apply,
    ← Ideal.span_union, Set.singleton_union]

end Ws30MaxGen
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair.ModularCurve ModularCurve.UVCrossingModel in
theorem solution
    {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπu : ¬IsUnit π) [IsLocalRing (UVCrossingModel W π)] :
    IsLocalRing.maximalIdeal (UVCrossingModel W π) =
      (IsLocalRing.maximalIdeal W).map (UVCrossingModel.constHom π) ⊔ Ideal.span {U π, V π} :=
  ModularCurve.Ws30MaxGen.maximalIdeal_eq π hπu

end S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair (solution)
