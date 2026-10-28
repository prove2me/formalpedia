-- Prove2me | solution 2 for NagaevLD.LowerBound.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:47:49.98266+00:00
-- url     : https://prove2.me/submissions/5136d881-e32e-4697-b653-bf25f0e76d18

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting
import Theorems.Thm_NagaevLD_LowerBound_eq_1_57
import Theorems.Thm_NagaevLD_LowerBound_eq_1_58

-- carved verbatim out of submission c292144c-12f1-4203-9004-35fafc266350, lines 220-227

section
open MeasureTheory ProbabilityTheory
open NagaevLD
open NagaevLD.LowerBound

theorem lower_bound_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) :
    (1 / 2) * ∑ j, P.real {ω | 2 * x ≤ X j ω} ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum fun j _ => NagaevLD.LowerBound.eq_1_58 P n X hXm hindep hL2 hmean x hx hxB j).trans
    (NagaevLD.LowerBound.eq_1_57 P n X hXm x)

end

section
open MeasureTheory ProbabilityTheory
open NagaevLD.LowerBound

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) :
    (1 / 2) * ∑ j, P.real {ω | 2 * x ≤ X j ω} ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by
  exact lower_bound_core P n X hXm hindep hL2 hmean x hx hxB

end
