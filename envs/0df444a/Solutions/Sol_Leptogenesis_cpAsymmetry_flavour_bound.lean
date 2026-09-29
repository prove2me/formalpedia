-- Prove2me | solution 1 for Leptogenesis.cpAsymmetry_flavour_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:49:05.186928+00:00
-- url     : https://prove2.me/submissions/f1df56ac-7d10-4643-be14-0beacfc891e3

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

set_option autoImplicit false

open Leptogenesis Matrix in
/-- Pasted from the proved sibling `lightMassMatrix_mulVec_conj_le` (871435d3):
`‖m x̄‖² ≤ m_max² ‖x‖²`. -/
theorem lepto_mulVec_conj_le_fb (v : ℝ) (M : Fin 3 → ℝ)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (x : Fin 3 → ℂ) :
    ∑ α, ‖(lightMassMatrix v M lam *ᵥ star x) α‖ ^ 2 ≤
      (⨆ i, masses i) ^ 2 * ∑ α, ‖x α‖ ^ 2 := by
  obtain ⟨hU, h0, hmU⟩ := hdiag
  have hnsq : ∀ w : Fin 3 → ℂ, ((∑ α, ‖w α‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Complex.star_def, Complex.conj_mul']
  have hiso : ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), Aᴴ * A = 1 → ∀ w : Fin 3 → ℂ,
      ∑ α, ‖(A *ᵥ w) α‖ ^ 2 = ∑ α, ‖w α‖ ^ 2 := by
    intro A hA w
    apply Complex.ofReal_injective
    rw [hnsq, hnsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]
  have hU1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU3 : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : Uᵀ * U.map (starRingEnd ℂ) = 1 := by
    have h := congrArg Matrix.transpose hU1
    rw [transpose_mul, transpose_one] at h
    have hc : (Uᴴ)ᵀ = U.map (starRingEnd ℂ) := by
      ext i j
      simp
    rw [hc] at h
    exact h
  have hcU : (U.map (starRingEnd ℂ))ᴴ * U.map (starRingEnd ℂ) = 1 := by
    have hc : (U.map (starRingEnd ℂ))ᴴ = Uᵀ := by
      ext i j
      simp
    rw [hc, hU2]
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [conjTranspose_conjTranspose, hU3]
  set S : ℝ := ⨆ i, masses i with hS
  have hle : ∀ i, masses i ^ 2 ≤ S ^ 2 := by
    intro i
    exact pow_le_pow_left₀ (h0 i) (le_ciSup (Set.finite_range masses).bddAbove i) 2
  rw [hmU, ← mulVec_mulVec, ← mulVec_mulVec, hiso _ hcU]
  set z : Fin 3 → ℂ := Uᴴ *ᵥ star x with hz
  have hzx : ∑ α, ‖z α‖ ^ 2 = ∑ α, ‖x α‖ ^ 2 := by
    rw [hz, hiso _ hUH]
    simp [Pi.star_apply]
  rw [← hzx, Finset.mul_sum]
  refine Finset.sum_le_sum (fun α _ => ?_)
  rw [mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 α),
    mul_pow]
  exact mul_le_mul_of_nonneg_right (hle α) (by positivity)

open Leptogenesis Matrix in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses) (α : Fin 3) :
    |cpAsymmetry v M lam α| ≤
      3 * M 0 * (⨆ i, masses i) / (16 * Real.pi * v ^ 2) *
        Real.sqrt (partialDecayRate M lam α / totalDecayRate M lam) := by
  set ℓ : Fin 3 → ℂ := fun j => lam j 0 with hℓ
  set S : ℝ := ∑ β, ‖lam β 0‖ ^ 2 with hSdef
  set hi : ℝ := ⨆ i, masses i with hhi
  set X : ℂ := ((lightMassMatrix v M lam).map (starRingEnd ℂ) * lam) α 0 with hX
  have h0 : ∀ i, 0 ≤ masses i := hdiag.2.1
  have hhi0 : 0 ≤ hi := le_trans (h0 0) (le_ciSup (Set.finite_range masses).bddAbove 0)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun β _ => by positivity)
  -- X is the conjugate of (m *ᵥ star ℓ) α
  have hXeq : X = star ((lightMassMatrix v M lam *ᵥ star ℓ) α) := by
    rw [hX]
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, Pi.star_apply,
      star_sum, star_mul', hℓ, Complex.star_def, Complex.conj_conj]
  have hXle : ‖X‖ ^ 2 ≤ hi ^ 2 * S := by
    have h1 := lepto_mulVec_conj_le_fb v M lam U masses hdiag ℓ
    have h2 : ‖(lightMassMatrix v M lam *ᵥ star ℓ) α‖ ^ 2 ≤
        ∑ β, ‖(lightMassMatrix v M lam *ᵥ star ℓ) β‖ ^ 2 :=
      Finset.single_le_sum (f := fun β => ‖(lightMassMatrix v M lam *ᵥ star ℓ) β‖ ^ 2)
        (fun β _ => by positivity) (Finset.mem_univ α)
    rw [hXeq, norm_star]
    simpa [hℓ, hSdef] using h2.trans h1
  have hXle' : ‖X‖ ≤ hi * Real.sqrt S := by
    rw [← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_sq hhi0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hXle
  have hratio : partialDecayRate M lam α / totalDecayRate M lam = ‖lam α 0‖ ^ 2 / S := by
    have hK : M 0 / (8 * Real.pi) ≠ 0 := by
      have := hM 0
      positivity
    have ht : totalDecayRate M lam = S * (M 0 / (8 * Real.pi)) := by
      simp only [totalDecayRate, partialDecayRate, hSdef, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      ring
    have hp : partialDecayRate M lam α = ‖lam α 0‖ ^ 2 * (M 0 / (8 * Real.pi)) := by
      simp only [partialDecayRate]
      ring
    rw [ht, hp, mul_div_mul_right _ _ hK]
  have hc0 : 0 < 3 * M 0 / (16 * Real.pi * v ^ 2) := by
    have := hM 0
    positivity
  have hcp : cpAsymmetry v M lam α =
      3 * M 0 / (16 * Real.pi * v ^ 2) * ((lam α 0 * X).im / S) := by
    simp only [cpAsymmetry, hX, hSdef]
  rw [hcp, hratio, abs_mul, abs_of_pos hc0]
  have hrw : 3 * M 0 * hi / (16 * Real.pi * v ^ 2) * Real.sqrt (‖lam α 0‖ ^ 2 / S) =
      3 * M 0 / (16 * Real.pi * v ^ 2) * (hi * Real.sqrt (‖lam α 0‖ ^ 2 / S)) := by
    ring
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ hc0.le
  rcases hS0.eq_or_lt with hSz | hSp
  · rw [← hSz, div_zero, div_zero, abs_zero, Real.sqrt_zero, mul_zero]
  · have hsq : Real.sqrt (‖lam α 0‖ ^ 2 / S) = ‖lam α 0‖ / Real.sqrt S := by
      rw [Real.sqrt_div' _ hSp.le, Real.sqrt_sq (norm_nonneg _)]
    have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSp
    have hSS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSp.le
    rw [hsq, abs_div, abs_of_pos hSp]
    have him : |(lam α 0 * X).im| ≤ ‖lam α 0‖ * (hi * Real.sqrt S) := by
      calc |(lam α 0 * X).im| ≤ ‖lam α 0 * X‖ := Complex.abs_im_le_norm _
        _ = ‖lam α 0‖ * ‖X‖ := norm_mul _ _
        _ ≤ ‖lam α 0‖ * (hi * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left hXle' (norm_nonneg _)
    rw [div_le_iff₀ hSp]
    calc |(lam α 0 * X).im| ≤ ‖lam α 0‖ * (hi * Real.sqrt S) := him
      _ = hi * (‖lam α 0‖ / Real.sqrt S) * S := by
        rw [show hi * (‖lam α 0‖ / Real.sqrt S) * S =
          ‖lam α 0‖ * (hi * (S / Real.sqrt S)) by ring, Real.div_sqrt]
