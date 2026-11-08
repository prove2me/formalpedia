-- Prove2me | solution 1 for KallMayerSLP.CondExp.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:02:00.378795+00:00
-- url     : https://prove2.me/submissions/d60ce359-9806-4ff2-b6ad-982c00f35bd1

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_wC

open MeasureTheory

open KallMayerSLP.CondExp in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : Ω → Fin n → ℝ) (h : Ω → ℝ)
    (ht : ∀ i, Integrable (fun ω => t ω i) μ) (hh : Integrable h μ) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) :
    ConvexOn ℝ Set.univ (fun p : (Fin n → ℝ) × ℝ => wC μ t h α p.1 p.2) := by
  have hint : ∀ (x : Fin n → ℝ) (z : ℝ),
      Integrable (fun ω => max (t ω ⬝ᵥ x - h ω - z) 0) μ := by
    intro x z
    have h1 : Integrable (fun ω => t ω ⬝ᵥ x) μ := by
      simp only [dotProduct]
      exact integrable_finsetSum _ (fun i _ => (ht i).mul_const (x i))
    exact ((h1.sub hh).sub (integrable_const z)).pos_part
  refine ⟨convex_univ, ?_⟩
  rintro ⟨x, z⟩ - ⟨y, w⟩ - a b ha hb hab
  simp only [wC, cvarObjective, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have hc : 0 ≤ 1 / (1 - α) := by
    apply div_nonneg zero_le_one; linarith
  have hmono : ∫ ω, max (t ω ⬝ᵥ (a • x + b • y) - h ω - (a * z + b * w)) 0 ∂μ ≤
      ∫ ω, (a * max (t ω ⬝ᵥ x - h ω - z) 0 + b * max (t ω ⬝ᵥ y - h ω - w) 0) ∂μ := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => le_max_right _ _)
    · exact ((hint x z).const_mul a).add ((hint y w).const_mul b)
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have e : t ω ⬝ᵥ (a • x + b • y) - h ω - (a * z + b * w)
          = a * (t ω ⬝ᵥ x - h ω - z) + b * (t ω ⬝ᵥ y - h ω - w) := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have : h ω = a * h ω + b * h ω := by rw [← add_mul, hab, one_mul]
        linarith
      simp only
      rw [e]
      apply max_le
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
      · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  rw [integral_add ((hint x z).const_mul a) ((hint y w).const_mul b), integral_const_mul,
    integral_const_mul] at hmono
  have := mul_le_mul_of_nonneg_left hmono hc
  nlinarith
