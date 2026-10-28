-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:27.643899+00:00
-- url     : https://prove2.me/submissions/1f98db29-8d30-48e5-97b4-663c6573ee00

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section RemainderMeasurable
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- The second-order Taylor remainder along a measurable sequence of a function with continuous
first and second derivatives is measurable. -/
theorem solution {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
    (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
    Measurable fun ω => LevyStochCalc.taylorRemainderNormed f f' f'' (fun i => x i ω) m := by
  have hfirst : ∀ i : ℕ, Measurable fun ω => f' (x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f' p.1 (p.2 - p.1) :=
      (hf'c.comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  have hsecond : ∀ i : ℕ,
      Measurable fun ω => f'' (x i ω) (x (i + 1) ω - x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f'' p.1 (p.2 - p.1) (p.2 - p.1) :=
      ((hf''c.comp continuous_fst).clm_apply
        (continuous_snd.sub continuous_fst)).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  unfold LevyStochCalc.taylorRemainderNormed
  exact ((hfc.measurable.comp (hx m)).sub (hfc.measurable.comp (hx 0))).sub
    ((Finset.measurable_sum _ fun i _ => hfirst i).add
      (Finset.measurable_sum _ fun i _ => (hsecond i).div_const 2))
