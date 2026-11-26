-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_grid_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:53:10.742833+00:00
-- url     : https://prove2.me/submissions/440261d9-8660-4ed8-af69-3680573979a2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite deterministic left-point Esscher grid gain is measurable. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real)
    (u : Nat → NNReal) (n : Nat) :
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha*L.X t w-L.ψ alpha*(t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha*runningSup L t w+L.ψ alpha*(t:Real))
    Measurable (fun w => ∑ i ∈ Finset.range n,
      H (u i) w * (E (u (i+1)) w-E (u i) w)) := by
  dsimp only
  let E : NNReal → Ω → Real := fun t w =>
    Real.exp (alpha*L.X t w-L.ψ alpha*(t:Real))
  let H : NNReal → Ω → Real := fun t w =>
    Real.exp (-alpha*runningSup L t w+L.ψ alpha*(t:Real))
  have hU : Adapted F (runningSup L) := (runningSup_isDividendStrategy L).2.2.2
  have hE (r : NNReal) : Measurable (E r) :=
    ((measurable_const.mul ((L.adapted r).mono (F.le r) le_rfl)).sub
      measurable_const).exp
  have hH (r : NNReal) : Measurable (H r) :=
    ((measurable_const.mul ((hU r).mono (F.le r) le_rfl)).add
      measurable_const).exp
  change Measurable (fun w => ∑ i ∈ Finset.range n,
    H (u i) w * (E (u (i+1)) w-E (u i) w))
  apply Finset.measurable_sum
  intro i hi
  exact (hH _).mul ((hE _).sub (hE _))
