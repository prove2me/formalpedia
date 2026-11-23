-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_4_complex_extension_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:41:55.49275+00:00
-- url     : https://prove2.me/submissions/4db998c0-aab5-4706-a1e8-f53b68a089d2

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_3_v2
set_option autoImplicit false
open MeasureTheory
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [hP : IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P)
      (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
      (hψ : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
      (hW : HasSourceScaleFamily ψ W)
      (c : ℝ)
      (hc : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P),
      ∃ (F G : ℂ → ℝ → ℂ),
        (∀ x : ℝ, 0 ≤ x →
          Differentiable ℂ (fun q : ℂ => F q x) ∧
          Differentiable ℂ (fun q : ℂ => G q x)) ∧
        (∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
          F (q : ℂ) x = (W q x : ℂ)) ∧
        (∀ (p x : ℝ), 0 ≤ p → 0 ≤ x →
          0 ≤ p + ψ c →
          G (p : ℂ) x =
            ((tiltedScale c (W (p + ψ c)) x) : ℂ)) ∧
        (∀ (q : ℂ) (x : ℝ), 0 ≤ x →
          F q x =
            Complex.exp (((c * x : ℝ) : ℂ)) *
              G (q - ((ψ c : ℝ) : ℂ)) x) := by
  intro Ω mΩ P hP D ψ W hψ hW c hc
  classical
  let hExt := source_result8_3_v2 ψ W hW
  let F : ℂ → ℝ → ℂ := fun z x =>
    if hx : 0 ≤ x then Classical.choose (hExt x hx) z else 0
  have hF : ∀ x : ℝ, 0 ≤ x →
      Differentiable ℂ (fun z : ℂ => F z x) ∧
        ∀ q : ℝ, 0 ≤ q → F (q : ℂ) x = (W q x : ℂ) := by
    intro x hx
    simpa [F, hx] using (Classical.choose_spec (hExt x hx))
  let G : ℂ → ℝ → ℂ := fun z x =>
    Complex.exp (((-c * x : ℝ) : ℂ)) *
      F (z + ((ψ c : ℝ) : ℂ)) x
  have hGdiff : ∀ x : ℝ, 0 ≤ x →
      Differentiable ℂ (fun z : ℂ => G z x) := by
    intro x hx
    dsimp [G]
    have hArg : Differentiable ℂ
        (fun z : ℂ => z + ((ψ c : ℝ) : ℂ)) := by fun_prop
    have hComp : Differentiable ℂ
        (fun z : ℂ => F (z + ((ψ c : ℝ) : ℂ)) x) :=
      (hF x hx).1.comp hArg
    exact hComp.const_mul _
  have hGreal : ∀ (p x : ℝ), 0 ≤ p → 0 ≤ x → 0 ≤ p + ψ c →
      G (p : ℂ) x =
        ((tiltedScale c (W (p + ψ c)) x) : ℂ) := by
    intro p x hp hx hpq
    dsimp [G, tiltedScale]
    rw [show (p : ℂ) + ((ψ c : ℝ) : ℂ) = ((p + ψ c : ℝ) : ℂ) by
      push_cast
      ring]
    rw [(hF x hx).2 (p + ψ c) hpq]
    simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  have hComplex : ∀ (q : ℂ) (x : ℝ), 0 ≤ x →
      F q x =
        Complex.exp (((c * x : ℝ) : ℂ)) *
          G (q - ((ψ c : ℝ) : ℂ)) x := by
    intro q x hx
    dsimp [G]
    rw [sub_add_cancel, ← mul_assoc, ← Complex.exp_add]
    rw [show ((c * x : ℝ) : ℂ) + ((-c * x : ℝ) : ℂ) = 0 by
      push_cast
      ring]
    simp
  exact ⟨F, G,
    (fun x hx => ⟨(hF x hx).1, hGdiff x hx⟩),
    (fun q x hq hx => (hF x hx).2 q hq),
    hGreal,
    hComplex⟩
