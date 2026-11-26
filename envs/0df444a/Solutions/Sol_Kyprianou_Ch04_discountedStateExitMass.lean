-- Prove2me | solution 1 for Kyprianou.Ch04.discountedStateExitMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:48:43.798803+00:00
-- url     : https://prove2.me/submissions/b0b0cf0a-0132-4b0e-a68f-da3ecea0b923

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_generatorAbsoluteJumpContinuityOnCompact
import Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
import Theorems.Thm_Kyprianou_Ch04_stoppedAbsoluteMassFromBound
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Spatial exit bounds the discounted stopped absolute jump mass. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : Measure ℝ) (X L : NNReal → Ω → ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (l : ℝ) (hl : 0 ≤ l)
    (hi : ∀ y, Integrable (fun x => f (y+x)-f y) nu)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (n : ℕ) (t : NNReal) :
    let tau : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    let k := fun s x w => Real.exp (-l*s)*(f (L (Real.toNNReal s) w+x)-f (L s.toNNReal w))
    (∫⁻ w, ∫⁻ s in Icc (0:ℝ) (t:ℝ), ∫⁻ x,
      ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
      ∂nu ∂volume ∂P) < ⊤ := by
  let tau : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
    ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
  let k := fun (s x : ℝ) w => Real.exp (-l*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
  let A := fun y => ∫ x, ‖f (y+x)-f y‖ ∂nu
  have hA : Continuous A := generatorAbsoluteJumpContinuityOnCompact nu f hf hdom
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := -(n:ℝ)) (b := (n:ℝ))).bddAbove_image hA.continuousOn
  apply stoppedAbsoluteMassFromBound P nu k tau (ENNReal.ofReal B) (by simp) _ t
  filter_upwards [hLeft] with w hw
  intro s hs hstop
  have hL := (stateExitPreLimitBound (fun u => X u w) (fun u => L u w) (n:ℝ) hw).2
    s.toNNReal (Real.toNNReal_pos.mpr hs) hstop
  have hB' : A (L s.toNNReal w) ≤ B := hB (mem_image_of_mem A (abs_le.mp hL))
  have hExp : Real.exp (-l*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖f (L s.toNNReal w+x)-f (L s.toNNReal w)‖ ∂nu := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      dsimp only [k]
      rw [abs_mul,abs_of_pos (Real.exp_pos _),Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) hExp
    _ = ENNReal.ofReal (A (L s.toNNReal w)) :=
      (ofReal_integral_eq_lintegral_ofReal (hi _).norm
        (Eventually.of_forall fun _ => norm_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hB'
