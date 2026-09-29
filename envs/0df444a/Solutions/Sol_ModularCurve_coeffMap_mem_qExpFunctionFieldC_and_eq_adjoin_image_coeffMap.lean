-- Prove2me | solution 1 for ModularCurve.coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4fbfa94e-db00-5909-9a69-680da6ee27ef

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

namespace TBC

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R q) = HahnSeries.ofPowerSeries ℤ S (q.map f) := by
  ext n
  rw [coeffMap_coeff]
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]

theorem coeffMap_intSeriesC {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (q : PowerSeries ℤ) :
    coeffMap φ (intSeriesC K q) = intSeriesC K' q := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  rw [← RingHom.comp_apply (PowerSeries.map φ), ← PowerSeries.map_comp, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom K')]

theorem coeffMap_mem_adjoin {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (S : Set (LaurentSeries K))
    (T : IntermediateField K' (LaurentSeries K')) (hST : ∀ s ∈ S, coeffMap φ s ∈ T)
    {f : LaurentSeries K} (hf : f ∈ IntermediateField.adjoin K S) : coeffMap φ f ∈ T := by
  have hf' : f ∈ (IntermediateField.adjoin K S).toSubfield := hf
  rw [IntermediateField.adjoin_toSubfield] at hf'
  clear hf
  induction hf' using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | hx
    · rw [ModularCurve.algebraMap_laurentSeries_eq_single, coeffMap_single, ← ModularCurve.algebraMap_laurentSeries_eq_single]
      exact T.algebraMap_mem _
    · exact hST x hx
  | one => rw [map_one]; exact one_mem T
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem coeffMap_mem_qExpFunctionFieldC {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (Γ : Subgroup SL(2, ℤ))
    {f : LaurentSeries K} (hf : f ∈ qExpFunctionFieldC K Γ) : coeffMap φ f ∈ qExpFunctionFieldC K' Γ := by
  refine coeffMap_mem_adjoin φ (intFormRatiosC K Γ) (qExpFunctionFieldC K' Γ) ?_ hf
  rintro s ⟨w, fm, gm, pf, pg, hpf, hpg, hne, rfl⟩
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  by_cases h0 : intSeriesC K' pg = 0
  · rw [h0, div_zero]; exact zero_mem _
  · exact intFormRatiosC_subset K' Γ ⟨w, fm, gm, pf, pg, hpf, hpg, h0, rfl⟩

end TBC

open TBC in
theorem solution
    (K K' : Type*) [Field K] [Field K'] (ι : K →+* K') (Γ : Subgroup SL(2, ℤ)) :
    (∀ x ∈ qExpFunctionFieldC K Γ, coeffMap ι x ∈ qExpFunctionFieldC K' Γ) ∧
    qExpFunctionFieldC K' Γ =
      IntermediateField.adjoin K' (coeffMap ι '' (qExpFunctionFieldC K Γ : Set (LaurentSeries K))) := by
  classical
  refine ⟨fun x hx => coeffMap_mem_qExpFunctionFieldC ι Γ hx, le_antisymm ?_ ?_⟩
  ·
    rw [qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro s ⟨w, fm, gm, pf, pg, hpf, hpg, hne, rfl⟩
    have hne' : intSeriesC K pg ≠ 0 := by
      intro h0; apply hne
      rw [← coeffMap_intSeriesC ι pg, h0, map_zero]
    refine IntermediateField.subset_adjoin _ _ ⟨intSeriesC K pf / intSeriesC K pg, ?_, ?_⟩
    · exact intFormRatiosC_subset K Γ ⟨w, fm, gm, pf, pg, hpf, hpg, hne', rfl⟩
    · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  · rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨x, hx, rfl⟩
    exact coeffMap_mem_qExpFunctionFieldC ι Γ hx

end S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
end P2MW
export P2MW.S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap (solution)
