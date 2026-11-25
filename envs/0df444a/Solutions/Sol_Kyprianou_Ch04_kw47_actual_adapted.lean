-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_actual_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:48:16.155116+00:00
-- url     : https://prove2.me/submissions/b4720321-8865-4980-b55d-a2ba7b7ce436

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Adaptedness of the actual reflected Kella--Whitt process follows
from right-endpoint quadrature within each observation horizon. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha) :
    let Z : NNReal → Ω → Real := fun r w =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Ω → Real := fun t w =>
      ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal w ∂volume
    StronglyAdapted F (fun t w => L.ψ alpha * J t w + 1 -
      Z t w - alpha * runningSup L t w) := by
  dsimp only
  let Z : NNReal → Ω → Real := fun r w =>
    Real.exp (-alpha * (runningSup L r w - L.X r w))
  let J : NNReal → Ω → Real := fun t w =>
    ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal w ∂volume
  have hU : Adapted F (runningSup L) := (runningSup_isDividendStrategy L).2.2.2
  have hZ (r : NNReal) : Measurable[F r] (Z r) :=
    (measurable_const.mul ((hU r).sub (L.adapted r))).exp
  intro t
  let u : Nat → Nat → NNReal := fun n i =>
    0 + (t-0) * ((min i (n+1) : Nat) : NNReal) / ((n+1 : Nat) : NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid 0 t (show 0 ≤ t from zero_le)
  let Q : Nat → Ω → Real := fun n w => ∑ i ∈ Finset.range (n+1),
    ((u n (i+1):Real)-(u n i:Real))*Z (u n (i+1)) w
  have hQ (n : Nat) : Measurable[F t] (Q n) := by
    dsimp only [Q]
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul ((hZ (u n (i+1))).mono
      (F.mono (hT n (i+1))) le_rfl)
  have hJ0 (w : Ω) : J 0 w = 0 := by
    simp [J, Set.Icc_self]
  have hLim (w : Ω) : Tendsto (fun n => Q n w) atTop (nhds (J t w)) := by
    have h := Kyprianou.Ch04.kw47_reflected_time_quadrature L alpha hAlpha
      w 0 t (show 0 ≤ t from zero_le) u (fun n => n+1) hu h0 hN
      (fun n => ((t:Real)-(0:NNReal):Real) / ((n+1:Nat):Real)) hDelta
      (fun n i hi => le_of_eq (hMesh n i hi))
    change Tendsto (fun n => Q n w) atTop (nhds (J t w-J 0 w)) at h
    simpa only [hJ0 w, sub_zero] using h
  have hJ : Measurable[F t] (J t) :=
    @measurable_of_tendsto_metrizable Ω Real (F t) _ _ _ _ Q (J t) hQ (tendsto_pi_nhds.mpr hLim)
  change StronglyMeasurable[F t] (fun w => L.ψ alpha * J t w + 1 -
    Z t w - alpha * runningSup L t w)
  exact ((((measurable_const.mul hJ).add measurable_const).sub (hZ t)).sub
    (measurable_const.mul (hU t))).stronglyMeasurable
