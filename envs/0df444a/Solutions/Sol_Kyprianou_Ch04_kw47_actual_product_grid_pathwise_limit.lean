-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_actual_product_grid_pathwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:52:47.012739+00:00
-- url     : https://prove2.me/submissions/05096924-5896-496a-9426-f2176824c201

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_grid_correction
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_record_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual Esscher product grids converge pathwise to the signed
increment of the Kella--Whitt process, on any vanishing-mesh grid. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let E : NNReal → Real := fun r =>
      Real.exp (alpha * L.X r w - L.ψ alpha * (r:Real))
    let H : NNReal → Real := fun r =>
      Real.exp (-alpha * runningSup L r w + L.ψ alpha * (r:Real))
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Real := fun t =>
      ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal ∂volume
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      H (u n i) * (E (u n (i+1))-E (u n i))) atTop
      (nhds ((Z b-Z a) - L.ψ alpha * (J b-J a) +
        alpha * (runningSup L b w-runningSup L a w))) := by
  dsimp only
  let U : NNReal → Real := fun r => runningSup L r w
  let G : NNReal → Real := fun r => -alpha * U r + L.ψ alpha * (r:Real)
  let E : NNReal → Real := fun r =>
    Real.exp (alpha * L.X r w - L.ψ alpha * (r:Real))
  let H : NNReal → Real := fun r => Real.exp (G r)
  let Z : NNReal → Real := fun r => Real.exp (-alpha * (U r - L.X r w))
  let J : NNReal → Real := fun t =>
    ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal ∂volume
  have hCorr' := Kyprianou.Ch04.kw47_actual_grid_correction
    L alpha hAlpha w a b hab u N hu h0 hN delta hDelta hMesh
  have hEH (r : NNReal) : E r * H r = Z r := by
    dsimp only [E,H,G,Z]
    rw [← Real.exp_add]
    congr 1
    ring
  change Tendsto (fun n => ∑ i ∈ Finset.range (N n),
    H (u n i) * (E (u n (i+1))-E (u n i))) atTop
    (nhds ((Z b-Z a)-L.ψ alpha*(J b-J a)+alpha*(U b-U a)))
  have hGrid (n : Nat) : (∑ i ∈ Finset.range (N n),
      H (u n i) * (E (u n (i+1))-E (u n i))) =
      Z b-Z a - (∑ i ∈ Finset.range (N n),
        E (u n (i+1)) * (H (u n (i+1))-H (u n i))) := by
    rw [Kyprianou.Ch04.kw47_discrete_product_summation
      (fun i => E (u n i)) (fun i => H (u n i)), h0 n,hN n,hEH,hEH]
  change Tendsto (fun n => ∑ i ∈ Finset.range (N n),
    E (u n (i+1)) * (H (u n (i+1))-H (u n i))) atTop
    (nhds (L.ψ alpha * (J b-J a)-alpha*(U b-U a))) at hCorr'
  have hEnd : (Z b-Z a) - (L.ψ alpha*(J b-J a)-alpha*(U b-U a)) =
      (Z b-Z a)-L.ψ alpha*(J b-J a)+alpha*(U b-U a) := by ring
  simp only [hGrid, ← hEnd]
  exact tendsto_const_nhds.sub hCorr'
