-- Prove2me | solution 1 for MaxCutSample2027.Coreset.equation_2_14
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:37:18.789292+00:00
-- url     : https://prove2.me/submissions/f01b0da0-9f2f-4c7c-abf1-a4b56d87c846

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_7
import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_8
import Definitions.Def_MaxCutSample2027_Coreset_signed
import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => DeltaK (K A p) p (empirical x)) ≤
      12 * H A p / Real.sqrt (k : ℝ) := by
  have h₁ := lemma_2_7 A p hA hp k hk
  have h₂ := lemma_2_8 A p hA hp k hk
  calc
    _ ≤ 4 * jointAverage p k (signedMaximum (K A p) p) := h₁
    _ ≤ 4 * (3 * H A p / Real.sqrt (k : ℝ)) := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = _ := by ring
