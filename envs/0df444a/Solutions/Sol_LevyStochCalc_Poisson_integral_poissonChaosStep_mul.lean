-- Prove2me | solution 1 for LevyStochCalc.Poisson.integral_poissonChaosStep_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:31:36.151574+00:00
-- url     : https://prove2.me/submissions/ff7a4c48-7120-4be0-9ebf-7e813b7990ba

import Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Poisson chaos element of one strip at the mark-constant level

For a Poisson random measure `N` with reference intensity `ν̂ = volume.restrict [0, ∞) ⊗ ν` and a
region `B` of finite intensity, `poissonChaosStep N n B` is the Charlier polynomial of degree `n`
and rate `λ = ν̂(B)` evaluated at the count `N(B)`. On the strip `B = (a, b] ×ˢ A` the rate is
`(b - a) ν(A)`, the degree-one element is the compensated count `Ñ(B)` and the degree-two element
is `Ñ(B) ^ 2 - N(B)`. Under `P` the elements of positive degree are centred and the family is
orthogonal, with `E[C_n C_m] = δ_(n m) n! λ ^ n`; both come from the Charlier orthogonality under
a Poisson law, transferred along the law of the count.

Only a single mark set is covered: these are polynomials of the one count `N(B)`, with no mark
profile beyond the indicator of `A`, so the rate enters only through `ν̂(B)`.

## Main statements

* `LevyStochCalc.Poisson.poissonChaosStep_one` — the degree-one element is `Ñ(B)`.
* `LevyStochCalc.Poisson.poissonChaosStep_two` — the degree-two element is `Ñ(B) ^ 2 - N(B)`.
* `LevyStochCalc.Poisson.integrable_poissonChaosStep_mul` — a product of two elements of a region
  of finite intensity is integrable.
* `LevyStochCalc.Poisson.memLp_two_poissonChaosStep` — an element of a region of finite intensity
  lies in `L²`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_mul` — `E[C_n C_m] = δ_(n m) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_eq_zero` — `E[C_n] = 0` for `n ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_strip_mul` — the same on a strip `(a, b] ×ˢ A`,
  with rate `(b - a) ν(A)`.
* `LevyStochCalc.Poisson.referenceIntensity_strip_ne_top`,
  `LevyStochCalc.Poisson.referenceIntensity_strip_toReal` — the intensity of such a strip is
  finite and equals `(b - a) ν(A)`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_mul` — the same orthogonality at a complex
  scalar: `E[(c^n C_n) (c'^m C_m)] = δ_(n m) c^n c'^n n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_norm_sq_poissonChaosStepC` —
  `E[‖c^n C_n‖ ^ 2] = ‖c‖ ^ (2n) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_sq` —
  `E[(c^n C_n) ^ 2] = c ^ (2n) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_strip_mul` — the complex-scaled bilinear
  moment on a strip `(a, b] ×ˢ A`, with rate `(b - a) ν(A)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

lemma AuxP_comp (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (N.N ω B).toReal ∂P
      = ∫ k : ℕ, g (k : ℝ) ∂poissonMeasure (referenceIntensity ν B).toNNReal := by
  have hmeas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have hcomp : Measurable (fun x : ℝ≥0∞ => g x.toReal) := hg.comp ENNReal.measurable_toReal
  rw [show (∫ ω, g (N.N ω B).toReal ∂P) = ∫ x, g x.toReal ∂(P.map (fun ω => N.N ω B)) from
    (integral_map hmeas.aemeasurable hcomp.aestronglyMeasurable).symm, N.poisson_law hB hfin]
  change ∫ x, g x.toReal
      ∂((poissonMeasure (referenceIntensity ν B).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞))) = _
  rw [integral_map measurable_from_nat.aemeasurable hcomp.aestronglyMeasurable]
  simp

theorem _root_.solution (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n m : ℕ) :
    ∫ ω, poissonChaosStep N n B ω * poissonChaosStep N m B ω ∂P
      = if n = m then (n.factorial : ℝ) * (referenceIntensity ν B).toReal ^ n else 0 := by
  have hr : (((referenceIntensity ν B).toNNReal : ℝ≥0) : ℝ) = (referenceIntensity ν B).toReal :=
    ENNReal.coe_toNNReal_eq_toReal _
  have hg : Measurable (fun x : ℝ =>
      Probability.charlierScaled n (referenceIntensity ν B).toReal x *
        Probability.charlierScaled m (referenceIntensity ν B).toReal x) :=
    ((Probability.continuous_charlierScaled n _).mul
      (Probability.continuous_charlierScaled m _)).measurable
  have h := AuxP_comp N hB hfin hg
  simp only [poissonChaosStep]
  rw [h]
  have hs := _root_.Prove2MeSourceProof.h_5e9757a88ef83b24bbaf0d97
    (referenceIntensity ν B).toNNReal n m
  rw [hr] at hs
  exact hs

end LevyStochCalc.Poisson
