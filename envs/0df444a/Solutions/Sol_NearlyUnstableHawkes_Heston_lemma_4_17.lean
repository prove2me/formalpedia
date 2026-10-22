-- Prove2me | solution 1 for NearlyUnstableHawkes.Heston.lemma_4_17
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:05:00.86141+00:00
-- url     : https://prove2.me/submissions/bf695579-e7cf-4efb-a116-ae92d9ebc4f2

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open NearlyUnstableHawkes.Heston

theorem X_tail_lt_top (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hle : ∀ s, 0 ≤ s → φ s ≤ ψ s)
    (hψ : IntegrableOn (fun s => s * ψ s) (Set.Ici 0)) :
    (∫⁻ x in Set.Ici (0 : ℝ), ∫⁻ s in Set.Ici x, ENNReal.ofReal (φ s)) < ∞ := by
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (φ s) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp hφ
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 ≤ p.2 then f p.2 else 0
  have hHm : Measurable H := by
    refine Measurable.ite (measurableSet_le measurable_fst measurable_snd) (hfm.comp measurable_snd)
      measurable_const
  have h1 : ∀ x : ℝ, ∫⁻ s in Set.Ici x, f s = ∫⁻ s, H (x, s) := by
    intro x
    rw [← lintegral_indicator measurableSet_Ici]
    congr 1
  simp_rw [h1]
  rw [lintegral_lintegral_swap hHm.aemeasurable]
  have h2 : ∀ s : ℝ, ∫⁻ x in Set.Ici (0 : ℝ), H (x, s) = f s * ENNReal.ofReal s := by
    intro s
    have : (fun x : ℝ => H (x, s)) = (Set.Iic s).indicator (fun _ => f s) := by
      funext x
      simp only [H, Set.indicator, Set.mem_Iic]
    rw [this, lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    congr 1
    rw [Set.inter_comm]
    have : Set.Ici (0 : ℝ) ∩ Set.Iic s = Set.Icc 0 s := rfl
    rw [this, Real.volume_Icc, sub_zero]
  simp_rw [h2]
  have hbound : ∀ s : ℝ, f s * ENNReal.ofReal s ≤
      (Set.Ici (0 : ℝ)).indicator (fun s => ENNReal.ofReal (s * ψ s)) s := by
    intro s
    by_cases hs : 0 ≤ s
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hs), hf]
      simp only
      rw [mul_comm, ← ENNReal.ofReal_mul hs]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hle s hs) hs)
    · have : ENNReal.ofReal s = 0 := ENNReal.ofReal_eq_zero.2 (by linarith [not_le.1 hs])
      rw [this]; simp
  calc ∫⁻ s, f s * ENNReal.ofReal s
      ≤ ∫⁻ s, (Set.Ici (0 : ℝ)).indicator (fun s => ENNReal.ofReal (s * ψ s)) s :=
        lintegral_mono hbound
    _ = ∫⁻ s in Set.Ici (0 : ℝ), ENNReal.ofReal (s * ψ s) := lintegral_indicator measurableSet_Ici _
    _ < ∞ := hψ.lintegral_lt_top

theorem solution (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hK : KernelAssumption3 φ₁ φ₂ m) :
    (∫⁻ x in Set.Ici (0 : ℝ), ∫⁻ s in Set.Ici x, ENNReal.ofReal (φ₁ s)) < ∞ ∧
      (∫⁻ x in Set.Ici (0 : ℝ), ∫⁻ s in Set.Ici x, ENNReal.ofReal (φ₂ s)) < ∞ := by
  have hmean := hK.integrable_mean
  refine ⟨X_tail_lt_top φ₁ (fun s => φ₁ s + φ₂ s) hK.meas₁ ?_ hmean,
    X_tail_lt_top φ₂ (fun s => φ₁ s + φ₂ s) hK.meas₂ ?_ hmean⟩
  · intro s hs; linarith [hK.nonneg₂ s hs]
  · intro s hs; linarith [hK.nonneg₁ s hs]
