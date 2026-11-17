-- Prove2me | solution 1 for N25.cusp_complex_order_zero_of_nonzero_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:11.470531+00:00
-- url     : https://prove2.me/submissions/088c41bc-6963-402d-812a-9765f379fbc9

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_finite_limit_iff_nonnegative_of_normalized_leading
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false

open Filter Topology ModularCurve AlgebraicCurve UpperHalfPlane

open scoped MatrixGroups

namespace N25

private theorem exponent_zero (f : UpperHalfPlane → ℂ) (a : ℝ)
    (L c : ℂ) (hL : L ≠ 0) (hc : c ≠ 0)
    (hl : Tendsto (fun τ : UpperHalfPlane => f τ /
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L))
    (hf : Tendsto f UpperHalfPlane.atImInfty (nhds c)) : a = 0 := by
  have hp : 0 ≤ a :=
    (N25.finite_limit_iff_nonnegative_of_normalized_leading f a L hL hl).mp ⟨c, hf⟩
  have he (τ : UpperHalfPlane) :
      (f τ / Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))⁻¹ =
      (f τ)⁻¹ / Complex.exp (2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ)) := by
    have hn : 2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ) =
        -(2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)) := by push_cast; ring
    rw [hn, Complex.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  have hi : Tendsto (fun τ : UpperHalfPlane => (f τ)⁻¹ /
      Complex.exp (2 * Real.pi * Complex.I * ((-a : ℝ) : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L⁻¹) := by
    simpa only [he] using hl.inv₀ hL
  have hn : 0 ≤ -a :=
    (N25.finite_limit_iff_nonnegative_of_normalized_leading
      (fun τ => (f τ)⁻¹) (-a) L⁻¹ (inv_ne_zero hL) hi).mp ⟨c⁻¹, hf.inv₀ hc⟩
  linarith

/-- A finite nonzero endpoint limit forces both a nonzero field element and normalized order zero. -/
theorem _root_.solution
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (B : SL(2, ℤ)) (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ (xHFunctionField 25 N25.H25), y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto
        (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
          (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (P.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L))
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tendsto (fun τ : UpperHalfPlane =>
      realizeOf (CohCarrier.GammaH 25 N25.H25) (x : LaurentSeries ℂ) (B • τ))
      UpperHalfPlane.atImInfty (nhds c)) : x ≠ 0 ∧ P.ord x = 0 := by
  have hzero (τ : UpperHalfPlane) : realizeOf (CohCarrier.GammaH 25 N25.H25) 0 τ = 0 := by
    have hh := realizeOf_eq_div (CohCarrier.GammaH 25 N25.H25)
      (translation_mem_GammaH 25 N25.H25)
      (0 : ModularForm (CohCarrier.GammaH 25 N25.H25) 0) 1 0
      (by simp [qExpansion_zero]) τ (by simp)
    simpa using hh
  have hx0 : x ≠ 0 := by
    intro hx
    have ht : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ)) atImInfty (nhds c) := by
      simpa [hx, hzero] using hf
    exact hc (tendsto_nhds_unique ht tendsto_const_nhds)
  obtain ⟨L, hL, hl⟩ := hlead x hx0
  let a : ℝ := (P.ord x : ℝ) / (w : ℝ)
  let f : UpperHalfPlane → ℂ := fun τ =>
    realizeOf (CohCarrier.GammaH 25 N25.H25) (x : LaurentSeries ℂ) (B • τ)
  have he (τ : UpperHalfPlane) :
      f τ / Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)) =
      f τ * Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (w : ℂ))) := by
    rw [div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    dsimp only [a]
    push_cast
    ring
  have hl' : Tendsto (fun τ : UpperHalfPlane =>
      f τ / Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L) := by simpa only [he] using hl
  have ha := exponent_zero f a L c hL hc hl' hf
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hz : (P.ord x : ℝ) = 0 := (div_eq_zero_iff.mp ha).resolve_right hwR
  exact ⟨hx0, by exact_mod_cast hz⟩

end N25
