-- Prove2me | solution 1 for Maldacena2003.gammaZetaZeta_squeezed_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:07:19.905757+00:00
-- url     : https://prove2.me/submissions/37f9e349-5471-49b3-9a92-32c590d7f23b

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (ρd φd : ℝ) (n k₂ : EuclideanSpace ℝ (Fin 3))
    (hn : ‖n‖ = 1) (hk₂ : k₂ ≠ 0) (ε : Matrix (Fin 3) (Fin 3) ℝ)
    (hεsymm : ∀ i j, ε i j = ε j i) (hεtr : Matrix.trace ε = 0)
    (hεtv : ∀ i, ∑ j, ε i j * n j = 0) :
    Tendsto (fun t : ℝ => 2 * t ^ 3 * gammaZetaZetaBispectrum ρd φd ε (t • n) k₂ (-(t • n) - k₂))
      (𝓝[>] 0)
      (𝓝 (1 / (2 * ‖k₂‖ ^ 5) * (ρd ^ 4 / φd ^ 2) * (2 * ρd ^ 2) * (3 / 2)
        * ∑ i, ∑ j, ε i j * k₂ i * k₂ j)) := by
  set S := ∑ i, ∑ j, ε i j * k₂ i * k₂ j with hS
  set K := ‖k₂‖ with hK
  have hK0 : 0 < K := norm_pos_iff.2 hk₂
  set h : ℝ → ℝ := fun t => 1 / ((2 * K ^ 3) * (2 * ‖-(t • n) - k₂‖ ^ 3)) * ρd ^ 4 * (ρd ^ 2 / φd ^ 2)
      * (-S) * (4 * integralI ‖t • n‖ K ‖-(t • n) - k₂‖) with hh
  have hcont3 : ContinuousAt (fun t : ℝ => ‖-(t • n) - k₂‖) 0 := by fun_prop
  have hcont1 : ContinuousAt (fun t : ℝ => ‖t • n‖) 0 := by fun_prop
  have hv3 : ‖-((0:ℝ) • n) - k₂‖ = K := by simp [hK]
  have hc : ContinuousAt h 0 := by
    simp only [hh, integralI]
    fun_prop (disch := (simp [← hK]; first | positivity | (constructor <;> positivity)))
  have hv : h 0 = 1 / (2 * K ^ 5) * (ρd ^ 4 / φd ^ 2) * (2 * ρd ^ 2) * (3 / 2) * S := by
    have hv3' : ‖-(0:EuclideanSpace ℝ (Fin 3)) - k₂‖ = K := by simp [hK]
    simp only [hh, integralI, zero_smul, norm_zero, hv3']
    field_simp
    ring
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rw [hv] at h1
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hnt : ‖t • n‖ = t := by rw [norm_smul, hn, Real.norm_of_nonneg ht.le, mul_one]
  have hsum : ∑ i, ∑ j, ε i j * k₂ i * (-(t • n) - k₂) j = -S := by
    have e0 := hεtv 0; have e1 := hεtv 1; have e2 := hεtv 2
    simp only [Fin.sum_univ_three] at e0 e1 e2
    simp only [hS, Fin.sum_univ_three, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (-(t * k₂ 0)) * e0 + (-(t * k₂ 1)) * e1 + (-(t * k₂ 2)) * e2
  simp only [hh, gammaZetaZetaBispectrum, hsum, hnt, ← hK]
  have h3 : 0 < ‖-(t • n) - k₂‖ ^ 3 ∨ ‖-(t • n) - k₂‖ = 0 := by
    rcases (norm_nonneg (-(t • n) - k₂)).lt_or_eq with h | h
    · left; positivity
    · right; exact h.symm
  rcases h3 with h3 | h3
  · field_simp
  · simp [h3]
