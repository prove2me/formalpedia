-- Prove2me | solution 1 for Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:08:04.657187+00:00
-- url     : https://prove2.me/submissions/f3bca384-65bf-48e7-a9f0-e89f5b7bb81b

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) (hm : mu (Set.Iic (0 : Real)) = 0)
    (hi : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu)
    (t : Real) (ht : 0 < t) :
    let w := mu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2))
    let L := ∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂w
    L < ⊤ ∧ L =
      ENNReal.ofReal (2 * (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-(t+1)*x)) ∂mu)
        - (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂mu)
        - (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-(t+2)*x)) ∂mu)) := by
  dsimp only
  have hpos : ∀ᵐ x ∂mu, x ∈ Set.Ioi (0 : Real) := by
    rw [ae_iff]
    convert hm using 2
    ext x
    simp
  have hr := Measure.restrict_eq_self_of_ae_mem hpos
  let D (s x : Real) := 1 - Real.exp (-s*x)
  have hI (s : Real) (hs : 0 < s) : Integrable (D s) mu := by
    simpa only [IntegrableOn, hr, D] using hi s hs
  have h1 := hI (t+1) (by linarith)
  have h0 := hI t ht
  have h2 := hI (t+2) (by linarith)
  have hE (x : Real) : (1 - Real.exp (-x))^2 * Real.exp (-t*x) =
      2 * D (t+1) x - D t x - D (t+2) x := by
    dsimp [D]
    rw [show -(t+1)*x = -t*x + -x by ring,
      show -(t+2)*x = -t*x + -x + -x by ring]
    simp only [Real.exp_add]
    ring
  have hInt : Integrable (fun x => (1 - Real.exp (-x))^2 * Real.exp (-t*x)) mu :=
    (((h1.const_mul 2).sub h0).sub h2).congr
      (Filter.Eventually.of_forall fun x => (hE x).symm)
  have hnn : 0 ≤ᵐ[mu] (fun x => (1 - Real.exp (-x))^2 * Real.exp (-t*x)) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp_rw [Pi.mul_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  refine ⟨ENNReal.ofReal_lt_top, ?_⟩
  rw [hr]
  simp_rw [hE]
  have h10 : Integrable (fun x => 2 * D (t+1) x - D t x) mu :=
    (h1.const_mul 2).sub h0
  rw [integral_sub h10 h2, integral_sub (h1.const_mul 2) h0, integral_const_mul]
