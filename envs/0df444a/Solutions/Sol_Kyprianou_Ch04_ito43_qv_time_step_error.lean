-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_time_step_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:32:18.823984+00:00
-- url     : https://prove2.me/submissions/4703be22-f987-4bf0-958a-9dc4819d1fe2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_finite_step_integral_identity
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_threshold_integral
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Use finite-step integral linearity and threshold interval masses; integrate the uniform error against the finite interval volume. -/
theorem solution
    (Y : ℝ → ℝ) (t : NNReal) (hY : IntegrableOn Y (Icc (0:ℝ) (t:ℝ)) volume)
    (δ : ℝ) (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ∈ Icc (0:ℝ) (t:ℝ),
      |Y s - ∑ i ∈ Finset.range m, c i * (if (b i:ℝ) ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∫ s in Icc (0:ℝ) (t:ℝ), Y s ∂volume) -
      ∑ i ∈ Finset.range m, c i *
        ((∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
          ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume)| ≤
      δ * (t:ℝ) := by
  let S : Set ℝ := Icc (0:ℝ) (t:ℝ)
  let W : ℝ → ℝ := fun s =>
    ∑ i ∈ Finset.range m, c i * (if (b i:ℝ) ≤ s then (1:ℝ) else 0)
  let D : ℕ → Set ℝ := fun i => Ici (b i:ℝ)
  have h1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) S volume :=
    integrableOn_const (by
      change volume (Icc (0:ℝ) (t:ℝ)) ≠ ⊤
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  obtain ⟨hi,he⟩ := Kyprianou.Ch04.ito43_finite_step_integral_identity
    volume S (fun _ => (1:ℝ)) h1 m D (fun _ => measurableSet_Ici) c
  dsimp only at hi he
  have hfun : (fun s : ℝ => (∑ i ∈ Finset.range m,
      c i * (D i).indicator (fun _ => (1:ℝ)) s) * 1) = W := by
    funext s
    simp [D,W,Set.indicator]
  rw [hfun] at hi he
  have hstep : (∫ s in S, W s ∂volume) =
      ∑ i ∈ Finset.range m, c i *
        ((∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
          ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume) :=
    he.trans (Finset.sum_congr rfl (fun i _ =>
      congrArg (fun x => c i*x) (Kyprianou.Ch04.ito43_qv_time_threshold_integral t (b i))))
  rw [← hstep]
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    dsimp [S]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hbound : ∀ᵐ s ∂volume.restrict S, ‖Y s-W s‖ ≤ δ := by
    filter_upwards [ae_restrict_mem (μ:=volume) (show MeasurableSet S from measurableSet_Icc)]
      with s hs
    simpa [W,Real.norm_eq_abs] using hW s hs
  have hn := norm_integral_le_of_norm_le_const (μ:=volume.restrict S) hbound
  rw [integral_sub hY hi] at hn
  simpa [S,Real.norm_eq_abs,measureReal_def,Measure.restrict_apply_univ,
    Real.volume_Icc,ENNReal.toReal_ofReal t.coe_nonneg] using hn
