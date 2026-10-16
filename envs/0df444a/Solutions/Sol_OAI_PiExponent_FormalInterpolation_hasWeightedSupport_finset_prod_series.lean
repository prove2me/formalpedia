-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_finset_prod_series
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:21:56.551749+00:00
-- url     : https://prove2.me/submissions/47937619-d5f0-491b-90a5-aa719c2bc7eb

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_zero_one
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul_series

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) {ι : Type}
    [DecidableEq ι] (t : Finset ι)
    (f : ι → MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : ∀ i ∈ t, hasWeightedSupport v R (f i)) :
    hasWeightedSupport v ((t.card : ℝ) * R) (t.prod f) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using hasWeightedSupport_zero_one (v := v)
  | @insert a s ha ih =>
      have hhead : hasWeightedSupport v R (f a) :=
        hf a (Finset.mem_insert_self a s)
      have htail : ∀ i ∈ s, hasWeightedSupport v R (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hprod := hasWeightedSupport_mul_series v R ((s.card : ℝ) * R)
        (f a) (s.prod f) hhead (ih htail)
      simpa [Finset.prod_insert, ha, Finset.card_insert_of_notMem, Nat.cast_add,
        add_mul, add_comm, add_left_comm, add_assoc] using hprod