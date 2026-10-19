-- Prove2me | solution 1 for OAI.KervaireScalarPhase.phase_eq_arg_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:06:17.616139+00:00
-- url     : https://prove2.me/submissions/a5d75ea9-f5e3-4170-8d21-9946ca743533

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase

open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
theorem solution {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    phase z = 1 / 2 + (1 - z).arg / Real.pi := by
  set θ := z.arg with hθdef
  have hθ := Complex.arg_mem_Ioc z
  rw [← hθdef] at hθ
  have hz_eq : z = Complex.cos θ + Complex.sin θ * Complex.I := by
    have := Complex.norm_mul_cos_add_sin_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have hθ0 : θ ≠ 0 := by
    intro h; apply hz'; rw [hz_eq, h]; simp
  have hpi := Real.pi_pos
  set h := θ / 2
  have hc : Real.cos θ = 1 - 2 * Real.sin h ^ 2 := by
    rw [show θ = 2 * h by simp [h]; ring, Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq h]
  have hs : Real.sin θ = 2 * Real.sin h * Real.cos h := by
    rw [show θ = 2 * h by simp [h]; ring, Real.sin_two_mul]
  have hrep : ∀ (ρ φ : ℝ), ρ * Real.cos φ = 1 - Real.cos θ → ρ * Real.sin φ = - Real.sin θ →
      1 - z = (ρ : ℂ) * (Complex.cos φ + Complex.sin φ * Complex.I) := by
    intro ρ φ h1 h2
    rw [hz_eq]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.add_im, Complex.mul_im]
      linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.add_im, Complex.mul_im]
      linarith
  unfold phase
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- θ < 0
    have hsh : Real.sin h < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by simp [h]; linarith)
      (by simp [h]; linarith [hθ.1])
    have harg : (1 - z).arg = h + Real.pi / 2 := by
      rw [hrep (-2 * Real.sin h) (h + Real.pi / 2)
        (by rw [Real.cos_add_pi_div_two, hc]; ring) (by rw [Real.sin_add_pi_div_two, hs]; ring)]
      exact Complex.arg_mul_cos_add_sin_mul_I (by linarith)
        ⟨by simp [h]; linarith [hθ.1], by simp [h]; linarith⟩
    rw [harg, Int.fract_eq_iff]
    have hb1 : -Real.pi / 2 < h := by simp only [h]; linarith [hθ.1]
    have he : 1 / 2 + (h + Real.pi / 2) / Real.pi = 1 + h / Real.pi := by field_simp; ring
    have hq1 : -1/2 < h / Real.pi := by rw [lt_div_iff₀ hpi]; linarith
    have hq2 : h / Real.pi < 0 := div_neg_of_neg_of_pos (by simp only [h]; linarith) hpi
    rw [he]
    refine ⟨by linarith, by linarith, ⟨-1, ?_⟩⟩
    simp only [h]; push_cast; field_simp; ring
  · -- θ > 0
    have hsh : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi (by simp [h]; linarith)
      (by simp [h]; linarith [hθ.2])
    have harg : (1 - z).arg = h - Real.pi / 2 := by
      rw [hrep (2 * Real.sin h) (h - Real.pi / 2)
        (by rw [Real.cos_sub_pi_div_two, hc]; ring) (by rw [Real.sin_sub_pi_div_two, hs]; ring)]
      exact Complex.arg_mul_cos_add_sin_mul_I (by linarith)
        ⟨by simp [h]; linarith, by simp [h]; linarith [hθ.2]⟩
    rw [harg, Int.fract_eq_iff]
    have hb2 : h ≤ Real.pi / 2 := by simp only [h]; linarith [hθ.2]
    have he : 1 / 2 + (h - Real.pi / 2) / Real.pi = h / Real.pi := by field_simp; ring
    have hq1 : 0 < h / Real.pi := div_pos (by simp only [h]; linarith) hpi
    have hq2 : h / Real.pi ≤ 1/2 := by rw [div_le_iff₀ hpi]; linarith
    rw [he]
    refine ⟨by linarith, by linarith, ⟨0, ?_⟩⟩
    simp only [h]; push_cast; field_simp; ring

