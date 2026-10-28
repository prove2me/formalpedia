-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_sq_increment_of_martingale_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:17:46.988481+00:00
-- url     : https://prove2.me/submissions/e38752d0-1769-48fa-8a84-7d45d5ef2325

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Conditional Pythagoras for L² martingales.** `𝔼[(M t − M s)² | ℱ s] =ᵐ
𝔼[(M t)² | ℱ s] − (M s)²`. Conditional version of the orthogonal-increment identity;
the cross term `𝔼[M s · M t | ℱ s] =ᵐ (M s)²` by pull-out + the martingale identity. -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P := hMs.integrable_mul hMt
  have hMsm : StronglyMeasurable[ℱ s] (M s) := hmart.stronglyAdapted s
  have hMs2m : StronglyMeasurable[ℱ s] (fun ω => (M s ω) ^ 2) := by
    have heq : (fun ω => (M s ω) ^ 2) = (fun ω => M s ω * M s ω) := by funext ω; ring
    rw [heq]; exact hMsm.mul hMsm
  have hf_int : MeasureTheory.Integrable (fun ω => (M t ω - M s ω) ^ 2) P := by
    have heq : (fun ω => (M t ω - M s ω) ^ 2)
        = (fun ω => (M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) := by funext ω; ring
    rw [heq]; exact (hMt2.sub (hcr.const_mul 2)).add hMs2
  have hcross_ae : P[(fun ω => M s ω * M t ω) | ℱ s] =ᵐ[P] fun ω => (M s ω) ^ 2 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ s) hMsm
      (show MeasureTheory.Integrable ((M s) * (M t)) P from hcr)
      (hmart.integrable t)
    filter_upwards [hpull, hmart.condExp_ae_eq hst] with ω hp hmeq
    have hp' : P[(fun ω => M s ω * M t ω) | ℱ s] ω = M s ω * (P[M t | ℱ s]) ω := by
      have : (fun ω => M s ω * M t ω) = (M s) * (M t) := rfl
      rw [this]; simpa [Pi.mul_apply] using hp
    rw [hp', hmeq, ← pow_two]
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf_int
    (fun B _ _ => (MeasureTheory.integrable_condExp.sub hMs2).integrableOn)
    (fun B hB _ => ?_)
    ((MeasureTheory.stronglyMeasurable_condExp.sub hMs2m).aestronglyMeasurable)
  have hcross : ∫ ω in B, M s ω * M t ω ∂P = ∫ ω in B, (M s ω) ^ 2 ∂P :=
    calc ∫ ω in B, M s ω * M t ω ∂P
        = ∫ ω in B, (P[(fun ω => M s ω * M t ω) | ℱ s]) ω ∂P :=
          (MeasureTheory.setIntegral_condExp hm hcr hB).symm
      _ = ∫ ω in B, (M s ω) ^ 2 ∂P :=
          MeasureTheory.setIntegral_congr_ae (hm B hB) (hcross_ae.mono (fun ω hω _ => hω))
  -- LHS `∫_B (condExp(M t²|ℱ s) − M s²)`
  have e1 : ∫ ω in B, ((P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2) ∂P
      = (∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P) - ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn hMs2.integrableOn
  have e1' : ∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P = ∫ ω in B, (M t ω) ^ 2 ∂P :=
    MeasureTheory.setIntegral_condExp hm hMt2 hB
  -- RHS `∫_B (M t − M s)²`
  have hexp : ∫ ω in B, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P :=
    MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => by ring)
  have e2a : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
      = (∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_add ((hMt2.sub (hcr.const_mul 2)).integrableOn) hMs2.integrableOn
  have e2b : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
      = (∫ ω in B, (M t ω) ^ 2 ∂P) - ∫ ω in B, 2 * (M s ω * M t ω) ∂P :=
    MeasureTheory.integral_sub hMt2.integrableOn (hcr.const_mul 2).integrableOn
  have e2c : ∫ ω in B, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω in B, M s ω * M t ω ∂P :=
    MeasureTheory.integral_const_mul 2 _
  rw [e1, e1', hexp, e2a, e2b, e2c, hcross]; ring
