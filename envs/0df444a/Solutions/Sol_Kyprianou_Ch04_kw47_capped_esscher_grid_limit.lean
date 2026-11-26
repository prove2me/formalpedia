-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_capped_esscher_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:00:34.914801+00:00
-- url     : https://prove2.me/submissions/08114696-bddc-490b-a31c-a09c342be08c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_product_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The capped uniform grids have the actual signed Kella--Whitt
increment as their pointwise limit, including zero-length intervals. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (a b : NNReal) (hab : a ≤ b) (w : Ω) :
    let U := runningSup L
    let Z : NNReal → Ω → Real := fun t w => Real.exp (-alpha * (U t w-L.X t w))
    let J : NNReal → Ω → Real := fun t w =>
      ∫ s in Icc (0:Real) (t:Real), Z s.toNNReal w ∂volume
    let M : NNReal → Ω → Real := fun t w =>
      L.ψ alpha * J t w + 1 - Z t w - alpha * U t w
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha * U t w + L.ψ alpha * (t:Real))
    let u : Nat → Nat → NNReal := fun n i =>
      a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      H (u n i) w * (E (u n (i+1)) w - E (u n i) w)) atTop
      (nhds (M a w - M b w)) := by
  dsimp only
  let U := runningSup L
  let Z : NNReal → Ω → Real := fun t w => Real.exp (-alpha * (U t w-L.X t w))
  let J : NNReal → Ω → Real := fun t w =>
    ∫ s in Icc (0:Real) (t:Real), Z s.toNNReal w ∂volume
  let M : NNReal → Ω → Real := fun t w =>
    L.ψ alpha * J t w + 1 - Z t w - alpha * U t w
  let E : NNReal → Ω → Real := fun t w =>
    Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
  let H : NNReal → Ω → Real := fun t w =>
    Real.exp (-alpha * U t w + L.ψ alpha * (t:Real))
  let u : Nat → Nat → NNReal := fun n i =>
    a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
  have h := Kyprianou.Ch04.kw47_actual_product_grid_pathwise_limit
    L alpha hAlpha w a b hab u (fun n => n+1) hu h0 hN
    (fun n => ((b:Real)-(a:Real))/((n+1:Nat):Real)) hDelta
    (fun n i hi => le_of_eq (hMesh n i hi))
  change Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
    H (u n i) w * (E (u n (i+1)) w - E (u n i) w)) atTop
    (nhds ((Z b w - Z a w) - L.ψ alpha * (J b w - J a w) +
      alpha * (U b w - U a w))) at h
  have hEnd : (Z b w - Z a w) - L.ψ alpha * (J b w - J a w) +
      alpha * (U b w - U a w) = M a w - M b w := by
    dsimp only [M]
    ring
  rw [hEnd] at h
  exact h
