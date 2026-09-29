-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9012c10f-067f-57da-a3c0-eab06f24dd7c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange"
namespace BCEqProof
p2m_open "ModularCurve"

theorem ofPowerSeries_coeff_int {A : Type*} [CommRing A] (x : PowerSeries A) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ A x).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat x else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff]
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    rintro ⟨n, hn⟩
    apply h
    rw [← hn]
    exact Int.natCast_nonneg n

theorem coeffMap_intSeriesC {R S : Type*} [Field R] [Field S] (f : R →+* S) (x : PowerSeries ℤ) :
    coeffMap f (intSeriesC R x) = intSeriesC S x := by
  ext k
  show (coeffMap f (HahnSeries.ofPowerSeries ℤ R (x.map (Int.castRingHom R)))).coeff k =
    (HahnSeries.ofPowerSeries ℤ S (x.map (Int.castRingHom S))).coeff k
  rw [coeffMap_coeff, ofPowerSeries_coeff_int, ofPowerSeries_coeff_int]
  split_ifs
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · exact map_zero f

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

theorem coeffEmb_intSeriesC (x : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ x) = intSeriesC L x :=
  coeffMap_intSeriesC (algebraMap ℚ L) x

theorem image_intFormRatiosC : ⇑(coeffEmb L) '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  have hinj : Function.Injective (coeffEmb L) := (coeffEmb L).injective
  ext x
  constructor
  · rintro ⟨y, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← coeffEmb_intSeriesC L]
      exact (map_ne_zero_iff _ hinj).mpr hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨k, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · intro h0
      apply hg0
      rw [← coeffEmb_intSeriesC L, h0, map_zero]
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem coeffEmb_mem_adjoin (S : Set (LaurentSeries ℚ)) {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ S) :
    coeffEmb L x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' S) := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
  | algebraMap c =>
    rw [algebraMap_laurentSeries_eq_single, show coeffEmb L (HahnSeries.single 0 c) =
      HahnSeries.single 0 (algebraMap ℚ L c) from coeffMap_single _ _ _, ← algebraMap_laurentSeries_eq_single]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem main : laurentBaseChange L (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC L Γ := by
  apply le_antisymm
  ·
    show IntermediateField.adjoin L (⇑(coeffEmb L) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h := coeffEmb_mem_adjoin L (intFormRatiosC ℚ Γ) hx
    rw [image_intFormRatiosC] at h
    exact h
  ·
    show IntermediateField.adjoin L (intFormRatiosC L Γ) ≤ _
    rw [IntermediateField.adjoin_le_iff, ← image_intFormRatiosC L Γ]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ Γ hx)

end ModularCurve.BCEqProof

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) = ModularCurve.qExpFunctionFieldC L Γ :=
  ModularCurve.BCEqProof.main L Γ

end S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq (solution)
