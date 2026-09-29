-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6df27ea3-727c-502a-9cd8-6a8bbce6028f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.qExpFunctionFieldC K Γ =
      IntermediateField.adjoin K
        (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (ModularCurve.qExpFunctionFieldC k Γ : Set (LaurentSeries k))) := by
  classical
  set f : LaurentSeries k →+* LaurentSeries K := ModularCurve.coeffMap (algebraMap k K) with hf

  have hfC : ∀ c : k, f (algebraMap k (LaurentSeries k) c) = algebraMap K (LaurentSeries K) (algebraMap k K c) := by
    intro c
    rw [hf, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single,
      ModularCurve.coeffMap_single]
  have hfinj : Function.Injective f := by
    intro x y hxy
    ext n
    have := congrArg (fun z : LaurentSeries K => z.coeff n) hxy
    simpa [hf, ModularCurve.coeffMap_coeff] using this

  have hS : ∀ p : PowerSeries ℤ, ModularCurve.intSeriesC K p = f (ModularCurve.intSeriesC k p) := by
    intro p
    ext n
    simp only [hf, ModularCurve.intSeriesC, ModularCurve.coeffMap_coeff]
    change ((PowerSeries.map (Int.castRingHom K) p : PowerSeries K) : LaurentSeries K).coeff n =
      algebraMap k K ((((PowerSeries.map (Int.castRingHom k) p : PowerSeries k)) : LaurentSeries k).coeff n)
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    split_ifs with h
    · simp
    · simp [PowerSeries.coeff_map, map_intCast]

  have hR : ModularCurve.intFormRatiosC K Γ = f '' ModularCurve.intFormRatiosC k Γ := by
    ext x
    constructor
    · rintro ⟨w, F₁, G₁, pf, pg, hF₁, hG₁, hg0, rfl⟩
      refine ⟨ModularCurve.intSeriesC k pf / ModularCurve.intSeriesC k pg, ⟨w, F₁, G₁, pf, pg, hF₁, hG₁, ?_, rfl⟩, ?_⟩
      · intro h
        apply hg0
        rw [hS, h, map_zero]
      · rw [map_div₀, ← hS, ← hS]
    · rintro ⟨y, ⟨w, F₁, G₁, pf, pg, hF₁, hG₁, hg0, rfl⟩, rfl⟩
      refine ⟨w, F₁, G₁, pf, pg, hF₁, hG₁, ?_, ?_⟩
      · intro h
        apply hg0
        apply hfinj
        rw [← hS, h, map_zero]
      · rw [map_div₀, ← hS, ← hS]

  apply le_antisymm
  ·
    change IntermediateField.adjoin K (ModularCurve.intFormRatiosC K Γ) ≤ _
    rw [hR]
    exact IntermediateField.adjoin.mono K _ _ (Set.image_mono (ModularCurve.intFormRatiosC_subset k Γ))
  ·
    rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨y, hy, rfl⟩
    change y ∈ IntermediateField.adjoin k (ModularCurve.intFormRatiosC k Γ) at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz =>
        apply ModularCurve.intFormRatiosC_subset K Γ
        rw [hR]
        exact ⟨z, hz, rfl⟩
    | algebraMap c =>
        rw [hfC]
        exact IntermediateField.algebraMap_mem _ _
    | add z w _ _ hz hw =>
        rw [map_add]
        exact add_mem hz hw
    | inv z _ hz =>
        rw [map_inv₀]
        exact inv_mem hz
    | mul z w _ _ hz hw =>
        rw [map_mul]
        exact mul_mem hz hw

end S_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC (solution)
