-- Prove2me | solution 1 for IntuitiveDPI.Smooth.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:14:36.17145+00:00
-- url     : https://prove2.me/submissions/9ffe60be-df52-4baf-9191-ebb5888e2440

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology Matrix

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

theorem solution {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    Tendsto (fun α : ℝ => renyiEntropy α ρ) (𝓝[≠] 1) (𝓝 (vnEntropy ρ)) := by
  have hH : ρ.IsHermitian := hρ.1.isHermitian
  obtain ⟨lam, hlam⟩ : ∃ l, l = hH.eigenvalues := ⟨_, rfl⟩
  have hnn : ∀ i, 0 ≤ lam i := fun i => hlam ▸ hρ.1.eigenvalues_nonneg i
  have hsumC : (∑ i, ((lam i : ℝ) : ℂ)) = 1 := by
    have := hH.trace_eq_sum_eigenvalues; rw [← hlam, hρ.2] at this; exact this.symm
  have hsum : ∑ i, lam i = 1 := by
    have := congrArg Complex.re hsumC
    simpa [Complex.re_sum] using this
  -- the scalar power sum
  let φ : ℝ → ℝ := fun α => ∑ i, (if lam i = 0 then 0 else lam i ^ α)
  set S : ℝ := ∑ i, lam i * Real.log (lam i) with hS
  have hφ1 : φ 1 = 1 := by
    simp only [φ, Real.rpow_one]
    rw [← hsum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h <;> simp [h]
  have hφd : HasDerivAt φ S 1 := by
    have : ∀ i ∈ (Finset.univ : Finset A),
        HasDerivAt (fun α : ℝ => if lam i = 0 then (0 : ℝ) else lam i ^ α)
          (lam i * Real.log (lam i)) 1 := by
      intro i _
      by_cases h : lam i = 0
      · simp only [h, if_true, zero_mul]; exact hasDerivAt_const _ _
      · have hp : 0 < lam i := lt_of_le_of_ne (hnn i) (Ne.symm h)
        simp only [h, if_false]
        have := (Real.hasStrictDerivAt_const_rpow hp 1).hasDerivAt
        simpa using this
    exact HasDerivAt.fun_sum this
  have hLd : HasDerivAt (fun α => Real.log (φ α) / Real.log 2) (S / φ 1 / Real.log 2) 1 :=
    (hφd.log (by rw [hφ1]; norm_num)).div_const _
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hLd).neg
  have hvn : vnEntropy ρ = -(S / φ 1 / Real.log 2) := by
    rw [hφ1, div_one, vnEntropy, trace_cfc_herm hH, Complex.re_sum, ← hlam]
    simp only [Complex.ofReal_re, hS, Finset.sum_div, ← Finset.sum_neg_distrib]
    congr 1; funext i
    rw [Real.logb]; ring
  rw [hvn]
  refine Tendsto.congr' ?_ hslope
  have hne0 : ∀ᶠ α in 𝓝[≠] (1 : ℝ), α ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne0, self_mem_nhdsWithin] with α h0 h1
  have h1' : α ≠ 1 := h1
  simp only [slope_def_field, hφ1, Real.log_one, zero_div, sub_zero]
  rw [renyiEntropy, if_neg h1']
  have htr1 : QAlgorithms.Papers.Independent.Dependency50.P35.tr ρ = 1 := by
    simp [QAlgorithms.Papers.Independent.Dependency50.P35.tr, hρ.2]
  have htrp : QAlgorithms.Papers.Independent.Dependency50.P35.tr
      (QAlgorithms.Papers.Independent.Dependency50.P35.spectralPower ρ α) = φ α := by
    simp only [QAlgorithms.Papers.Independent.Dependency50.P35.tr,
      QAlgorithms.Papers.Independent.Dependency50.P35.spectralPower, if_neg h0,
      trace_cfc_herm hH, Complex.re_sum, Complex.ofReal_re, φ, ← hlam]
  rw [htr1, htrp, div_one, Real.logb]
  have : (1 - α) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1')
  have : (α - 1) ≠ 0 := sub_ne_zero.mpr h1'
  field_simp
  ring
