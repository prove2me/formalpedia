-- Prove2me | solution 1 for ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f5165eb9-65a4-587d-a98a-29945dc95ed9

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Theorems.Thm_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (D' : ModularCurve.LevelPData K) (hD' : ModularCurve.IsGamma1Point (W₀.map (algebraMap R₀ K)) ℓ D') :
    ∃ D₀ : ModularCurve.LevelPData R₀, D₀.map (algebraMap R₀ K) = D' ∧ ModularCurve.IsGamma1Point W₀ ℓ D₀ := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ :=
    WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero W₀ ℓ hℓ D'.xP D'.yP hD'.equation_P hD'.preΨ_P
  refine ⟨⟨x₀, y₀, x₀, y₀⟩, ?_, ?_⟩
  · ext
    · simp [LevelPData.map, hx₀]
    · simp [LevelPData.map, hy₀]
    · simp [LevelPData.map, hx₀, hD'.xQ_eq]
    · simp [LevelPData.map, hy₀, hD'.yQ_eq]
  · refine ⟨?_, ?_, rfl, rfl⟩
    ·
      have h := hD'.equation_P
      rw [← hx₀, ← hy₀] at h
      rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
      apply hinj
      simp only [map_add, map_mul, map_pow]
      simpa [WeierstrassCurve.map] using h
    · have h := hD'.preΨ_P
      rw [← hx₀, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      exact hinj (by rw [h, map_zero])

end S_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
end P2MW
export P2MW.S_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map (solution)
