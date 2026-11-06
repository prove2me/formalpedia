-- Prove2me | solution 1 for OAI.SharpPlanar.interval_integral_tsum_uniform_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:09:44.450473+00:00
-- url     : https://prove2.me/submissions/50a32208-f655-4817-87f0-73b1c3d729c7

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

lemma interval_integral_tsum_uniform_e_oai {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, ContinuousOn (f i) (Icc a b))
    (g : ι → ℝ) (hg : Summable g)
    (hbound : ∀ i t, t ∈ Icc a b → ‖f i t‖ ≤ g i) :
    (∫ t in a..b, ∑' i, f i t) = ∑' i, ∫ t in a..b, f i t := by
  have hi (i : ι) : IntegrableOn (f i) (Icc a b) volume := (hf i).integrableOn_Icc
  have hb (i : ι) : ‖∫ t in Icc a b, ‖f i t‖‖ ≤ |b-a| *g i := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ g i * |b-a| := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t ht => by simpa using hbound i t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht))
      _ = _ := mul_comm _ _
  have hs : Summable (fun i => ∫ t in Icc a b, ‖f i t‖) :=
    (hg.mul_left |b-a|).of_norm_bounded hb
  simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (integral_tsum_of_summable_integral_norm hi hs).symm

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.interval_integral_tsum_uniform_e_oai.{u_1} := @OAI.SharpPlanar.interval_integral_tsum_uniform_e_oai.{u_1}
