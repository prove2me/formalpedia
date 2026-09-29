-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/667ef316-94a3-51d8-ba82-4d4b95088ca3

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace Ws31
namespace JT

open LanglandsTunnell.CubicInduction

theorem charExt_mul {K : Type*} [Field K] (χ μ : Kˣ →* ℂˣ) (x : K) :
    charExt (χ * μ) x = charExt χ x * charExt μ x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx, MonoidHom.mul_apply,
      Units.val_mul]

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem units_prod_eq_det (g : LocalGL3 v) (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    Units.mk0 (gl3Det v g / lowerMinor v g) (div_ne_zero (gl3Det_ne_zero v g) hl) *
        Units.mk0 (lowerMinor v g / cornerEntry v g) (div_ne_zero hl hc) * Units.mk0 (cornerEntry v g) hc =
      Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_mk0, Matrix.GeneralLinearGroup.val_det_apply]
  rw [show (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det = gl3Det v g from rfl]
  field_simp

theorem cellValue_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (g : LocalGL3 v) (hg : g ∈ bigCell3 v) :
    cellValue v (fun i => χ i * μ) g = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * cellValue v χ g := by
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v g).1 hg
  have h1 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
  have h2 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
  have key : ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      charExt μ (gl3Det v g / lowerMinor v g) * charExt μ (lowerMinor v g / cornerEntry v g) *
        charExt μ (cornerEntry v g) := by
    rw [charExt_of_ne_zero μ h1, charExt_of_ne_zero μ h2, charExt_of_ne_zero μ hc, ← Units.val_mul, ← Units.val_mul,
      ← map_mul, ← map_mul, units_prod_eq_det v g hc hl]
  simp only [cellValue, charExt_mul]
  rw [key]
  ring

theorem cellSectionOf_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    cellSectionOf v (fun i => χ i * μ) Φ g =
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * cellSectionOf v χ Φ g := by
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v _ Φ hg, cellSectionOf_apply_of_mem v _ Φ hg, cellValue_mul v χ μ g hg,
      mul_assoc]
  · rw [cellSectionOf_apply_of_notMem v _ Φ hg, cellSectionOf_apply_of_notMem v _ Φ hg, mul_zero]

theorem det_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 v) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one]
  simp [Matrix.det_fin_three]

theorem det_antidiagonal3_coe :
    ((Matrix.GeneralLinearGroup.det (antidiagonal3 v) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, antidiagonal3_coe]
  simp [Matrix.det_fin_three]

theorem jacquetTruncated3_twist (c : ℤ) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v (fun i => χ i * μ) Φ)) =
      (((μ (Matrix.GeneralLinearGroup.det (antidiagonal3 v)) : ℂˣ) : ℂ) *
          ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) *
        jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ)) := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3, gl3AmbientRightTranslate_apply]
  rw [← integral_const_mul]
  congr 1
  funext q
  rw [cellSectionOf_mul]
  simp only [map_mul, det_upperUnipotent3, mul_one, Units.val_mul, Units.val_one]
  ring

theorem jacquetValue_eq_mul_of_forall (u₁ u₂ : LocalGL3 v → ℂ) (a : ℂ)
    (h : ∀ c : ℤ, jacquetTruncated3 v c u₁ = a * jacquetTruncated3 v c u₂) :
    jacquetValue v u₁ = a * jacquetValue v u₂ := by
  by_cases ha : a = 0
  · simp only [jacquetValue, h, ha, zero_mul]
  · have hset : {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u₁ = jacquetTruncated3 v c₀ u₁} =
        {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u₂ = jacquetTruncated3 v c₀ u₂} := by
      ext c₀
      simp only [Set.mem_setOf_eq, h]
      exact forall_congr' fun c => imp_congr_right fun _ => (mul_right_injective₀ ha).eq_iff
    have hlev : jacquetLevel v u₁ = jacquetLevel v u₂ := by
      unfold jacquetLevel
      rw [hset]
    simp only [jacquetValue, hlev, h]

theorem jacquetWhittaker3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hμ1 : μ (Matrix.GeneralLinearGroup.det (antidiagonal3 v)) = 1) (g : LocalGL3 v) :
    jacquetWhittaker3 v (fun i => χ i * μ) Φ g =
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * jacquetWhittaker3 v χ Φ g := by
  simp only [jacquetWhittaker3_apply]
  refine jacquetValue_eq_mul_of_forall v _ _ _ fun c => ?_
  rw [jacquetTruncated3_twist, hμ1, Units.val_one, one_mul]

theorem modulus_neg_one {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] :
    modulus (-1 : K) = 1 := by
  have h : modulus (-1 : K) * modulus (-1 : K) = 1 := by
    rw [← modulus_mul, neg_one_mul, neg_neg, modulus_one]
  have h' : (modulus (-1 : K) : ℝ) * (modulus (-1 : K) : ℝ) = 1 := by exact_mod_cast h
  have hnn : (0 : ℝ) ≤ (modulus (-1 : K) : ℝ) := NNReal.coe_nonneg _
  rcases mul_self_eq_one_iff.1 h' with h1 | h1
  · exact_mod_cast h1
  · exfalso; linarith

theorem jacquetWhittaker3_mul_eq_modulus_det_cpow_mul
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℝ)
    (hμ : ∀ u : (v.adicCompletion ℚ)ˣ,
      ((μ u : ℂˣ) : ℂ) = ((modulus (u : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ)) (g : LocalGL3 v) :
    jacquetWhittaker3 v (fun i => χ i * μ) Φ g =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ) *
        jacquetWhittaker3 v χ Φ g := by
  have hμ1 : μ (Matrix.GeneralLinearGroup.det (antidiagonal3 v)) = 1 := by
    apply Units.ext
    rw [hμ, det_antidiagonal3_coe, modulus_neg_one, Units.val_one]
    simp
  rw [jacquetWhittaker3_mul v χ μ Φ hμ1 g, hμ]

end Ws31.JT

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℝ)
    (hμ : ∀ u : (v.adicCompletion ℚ)ˣ,
      ((μ u : ℂˣ) : ℂ) = ((modulus (u : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ))
    (g : LocalGL3 v) :
    jacquetWhittaker3 v (fun i => χ i * μ) Φ g =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ) *
        jacquetWhittaker3 v χ Φ g :=
  Ws31.JT.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul v χ Φ μ a hμ g

end S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3 (solution)
