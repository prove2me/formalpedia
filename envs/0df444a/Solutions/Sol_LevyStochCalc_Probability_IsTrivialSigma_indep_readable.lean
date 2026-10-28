-- Prove2me | solution 1 for LevyStochCalc.Probability.IsTrivialSigma.indep_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:53.091341+00:00
-- url     : https://prove2.me/submissions/cd0411a1-d415-4e5b-a630-d8b1ab974751

import Definitions.Def_KLSModular_LevyStochCalc_Probability_TrivialSigma

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/TrivialSigma.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}
/-- **A trivial σ-algebra is independent of every other one.** -/
theorem solution [IsProbabilityMeasure P] {m m' : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (h : LevyStochCalc.Probability.IsTrivialSigma P m) : Indep m m' P := by
  rw [Indep_iff]
  intro A B hA hB
  rcases h A hA with h0 | h1
  · rw [measure_mono_null Set.inter_subset_left h0, h0, zero_mul]
  · have hAc : P Aᶜ = 0 := by
      rw [prob_compl_eq_one_sub (hm A hA), h1, tsub_self]
    have hsub : B \ Aᶜ ⊆ A ∩ B := fun x hx => ⟨not_not.1 hx.2, hx.1⟩
    have : P (A ∩ B) = P B :=
      le_antisymm (measure_mono Set.inter_subset_right)
        ((measure_sdiff_null hAc).symm.trans_le (measure_mono hsub))
    rw [this, h1, one_mul]
