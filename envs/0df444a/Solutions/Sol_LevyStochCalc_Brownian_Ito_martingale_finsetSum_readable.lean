-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_finsetSum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:31.230788+00:00
-- url     : https://prove2.me/submissions/5aedd947-d89c-4e95-9d43-6a91721b35de

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Helpers
variable {Ω : Type u}
variable [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
/-- A finite sum of martingales is a martingale. -/
theorem solution {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (f : ι → ℝ → Ω → ℝ)
    (hf : ∀ i ∈ s, MeasureTheory.Martingale (f i) ℱ P) :
    MeasureTheory.Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun (t : ℝ) (ω : Ω) => ∑ i ∈ (∅ : Finset ι), f i t ω) = (0 : ℝ → Ω → ℝ) := by
        funext t ω
        simp
      rw [h0]
      exact MeasureTheory.martingale_zero ℝ ℱ P
  | insert i s hi ih =>
      have hsum : (fun t ω => ∑ j ∈ insert i s, f j t ω)
          = fun t ω => f i t ω + ∑ j ∈ s, f j t ω := by
        funext t ω
        rw [Finset.sum_insert hi]
      rw [hsum]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
