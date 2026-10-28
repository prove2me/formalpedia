-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_mul_cross_increment_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:12.929282+00:00
-- url     : https://prove2.me/submissions/b30730a1-96b8-43c2-8eff-87c8b91dbb73

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariation
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_cross_increment_eq_zero_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariation.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section Cross
open LevyStochCalc.Brownian.Multidim
variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
/-- **The cross-variation is conditionally centred at the left endpoint.** The product of the
increments of the Itô integrals against two distinct coordinates has vanishing conditional
expectation at the left endpoint of the cell. -/
theorem solution {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω) | ℱ a]
      =ᵐ[P] 0 := by
  classical
  have hLi : ∀ u : ℝ,
      MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W i) ℱ (hcoord i) H hHm hHp hHs u).symm
  have hLj : ∀ u : ℝ,
      MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W j) ℱ (hcoord j) K hKm hKp hKs u).symm
  have hint : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) P :=
    MemLp.integrable_mul ((hLi b).sub (hLi a)) ((hLj b).sub (hLj a))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hint
    (fun s _ _ => (integrable_zero Ω ℝ P).integrableOn) (fun s hs _ => ?_)
    (aestronglyMeasurable_const (b := (0 : ℝ)))).symm
  simp only [Pi.zero_apply, MeasureTheory.integral_zero]
  have hind : StronglyMeasurable[ℱ a] (s.indicator fun _ : Ω => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hs
  have hbd : ∀ ω : Ω, |s.indicator (fun _ : Ω => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hkey := LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero_readable W hcoord hHm hHp hHs hKm hKp hKs hij
    ha hab (Z := s.indicator fun _ => (1 : ℝ))
    ((measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator (ℱ.le a s hs)) hbd hind
  refine (Eq.trans ?_ hkey).symm
  rw [← MeasureTheory.integral_indicator (ℱ.le a s hs)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
