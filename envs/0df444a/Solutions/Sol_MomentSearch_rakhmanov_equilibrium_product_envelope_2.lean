-- Prove2me | solution 2 for MomentSearch.rakhmanov_equilibrium_product_envelope
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:52:53.072405+00:00
-- url     : https://prove2.me/submissions/11bca3f1-ffe3-4180-998b-bd92ceaa997d

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_product_representation
import Theorems.Thm_MomentSearch_rakhmanov_equilibrium_potential_comparison

open Filter Set
open scoped Topology

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
    ∃ S : Polynomial ℝ, ∃ a : ℝ → ℝ,
      S.natDegree ≤ N-k ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < a z ∧ |S.eval z| * w z = a z * |f z|) ∧
      (∀ x ∈ Set.Ioo (-r) r, ∀ z ∈ Set.Icc (-1 : ℝ) 1, a z ≤ 12 * a x) ∧
      (∀ y ∈ Set.Ioo (-r) r, f y = 0 →
        |S.derivative.eval y| * w y = a y * (Real.pi * ρ y)) := by 
  intro r ρ f w
  let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
  obtain ⟨S,C,hdeg,hcont,hrep,hC⟩ :=
    MomentSearch.rakhmanov_quantile_product_representation N k hk hkN
  change ∀ z ∈ Icc (-1 : ℝ) 1, 0 < C z ∧ S.eval z = C z * Real.exp (-V z) * f z at hrep
  obtain ⟨d,heq,hge⟩ := MomentSearch.rakhmanov_equilibrium_potential_comparison N k hk hkN
  change ∀ x ∈ Ioo (-r) r, V x - Real.log (w x) = d at heq
  change ∀ z ∈ Icc (-1 : ℝ) 1, d ≤ V z - Real.log (w z) at hge
  let E := fun z => Real.exp (-(V z - Real.log (w z)))
  have hw (z : ℝ) : 0 < w z := Real.exp_pos _
  have hE (z : ℝ) : E z = Real.exp (-V z) * w z := by
    dsimp [E]
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log (hw z), mul_comm]
  have eint (z : ℝ) (hz : z ∈ Ioo (-r) r) : E z = Real.exp (-d) := by dsimp [E]; rw [heq _ hz]
  have hr : r ≤ 1 := by
    dsimp [r]
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k : ℝ)) (sq_nonneg (N : ℝ))]⟩
  have inside : Ioo (-r) r ⊆ Icc (-1 : ℝ) 1 := fun z hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
  refine ⟨S,fun z => C z * E z,hdeg,?_,?_,?_⟩
  · intro z hz
    have h := hrep z hz
    constructor
    · exact mul_pos h.1 (Real.exp_pos _)
    · dsimp only
      rw [h.2, abs_mul, abs_mul, abs_of_pos h.1, abs_of_pos (Real.exp_pos _), hE]
      ring
  · intro x hx z hz
    have hle : E z ≤ E x := by
      rw [eint _ hx]
      exact Real.exp_le_exp.mpr (neg_le_neg (hge _ hz))
    calc
      _ ≤ (12 * C x) * E x := mul_le_mul (hC z hz x (inside hx)) hle (Real.exp_pos _).le
        (by have := (hrep x (inside hx)).1; positivity)
      _ = _ := by ring
  · intro y hy hfzero
    let θ := fun z => Real.pi * ∫ t in z..1, ρ t
    have hρ : Continuous ρ := by dsimp [ρ]; fun_prop
    have hi := intervalIntegral.integral_hasDerivAt_left (hρ.intervalIntegrable y 1)
      hρ.stronglyMeasurable.stronglyMeasurableAtFilter hρ.continuousAt
    have hf : HasDerivAt f (-Real.sin (θ y) * (Real.pi * (-ρ y))) y := (hi.const_mul Real.pi).cos
    have hs : |Real.sin (θ y)| = 1 := by
      change Real.cos (θ y) = 0 at hfzero
      rcases Real.cos_eq_zero_iff_sin_eq.mp hfzero with h | h <;> simp [h]
    let g := fun z => C z * Real.exp (-d) / w z
    have cw : Continuous w := by
      dsimp [w]
      apply Real.continuous_exp.comp
      apply Continuous.mul continuous_const
      exact (Real.continuous_mul_log.comp (continuous_const.add continuous_id)).add
        (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))
    have cg : ContinuousAt g y := by
      have hc := (hcont y (inside hy)).continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy) inside)
      exact (hc.mul continuousAt_const).div cw.continuousAt (hw _).ne'
    have loc (z : ℝ) (hz : z ∈ Ioo (-r) r) : S.eval z = g z * f z := by
      have he := (hE z).symm.trans (eint _ hz)
      rw [(hrep z (inside hz)).2]
      dsimp [g]
      field_simp [ne_of_gt (hw z)]
      linear_combination C z * f z * he
    have hroot : S.eval y = 0 := by rw [loc _ hy,hfzero,mul_zero]
    have hprod := (cg.tendsto.mono_left (nhdsWithin_le_nhds (s := {y}ᶜ))).mul hf.tendsto_slope
    have hder : HasDerivAt (fun z => S.eval z) (g y * (-Real.sin (θ y) * (Real.pi * (-ρ y)))) y := by
      apply hasDerivAt_iff_tendsto_slope.mpr
      apply hprod.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hy)] with z hz
      simp only [slope_def_field, hroot, hfzero, sub_zero, loc z hz]
      ring
    have hy' := (S.hasDerivAt y).unique hder
    have hnn : 0 ≤ ρ y := by
      dsimp [ρ]
      exact mul_nonneg (by positivity) (Real.arctan_nonneg.mpr (by positivity))
    have hg : 0 < g y := div_pos (mul_pos (hrep _ (inside hy)).1 (Real.exp_pos _)) (hw y)
    dsimp only
    rw [hy',abs_mul,abs_of_pos hg,abs_mul,abs_neg,hs,one_mul,abs_mul,
      abs_of_pos Real.pi_pos,abs_neg,abs_of_nonneg hnn,eint _ hy]
    dsimp [g]
    field_simp [(hw y).ne']
