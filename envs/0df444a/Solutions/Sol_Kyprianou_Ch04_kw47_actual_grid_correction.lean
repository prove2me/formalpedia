-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_actual_grid_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:53:18.54534+00:00
-- url     : https://prove2.me/submissions/00e0ff6a-3d32-42a5-9e82-60e9a6567a45

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_record_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false


/-- The right-point exponential correction converges to the time and record terms. -/
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
      E (u n (i+1)) * (H (u n (i+1))-H (u n i))) atTop
      (nhds (L.ψ alpha * (J b-J a)-alpha*(runningSup L b w-runningSup L a w))) := by
  dsimp only
  let U : NNReal → Real := fun r => runningSup L r w
  let G : NNReal → Real := fun r => -alpha * U r + L.ψ alpha * (r:Real)
  let E : NNReal → Real := fun r =>
    Real.exp (alpha * L.X r w - L.ψ alpha * (r:Real))
  let H : NNReal → Real := fun r => Real.exp (G r)
  let Z : NNReal → Real := fun r => Real.exp (-alpha * (U r - L.X r w))
  let J : NNReal → Real := fun t =>
    ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal ∂volume
  have hTime := Kyprianou.Ch04.kw47_reflected_time_quadrature
    L alpha hAlpha w a b hab u N hu h0 hN delta hDelta hMesh
  have hRecord := Kyprianou.Ch04.kw47_reflected_record_quadrature
    L alpha hAlpha w a b hab u N hu h0 hN delta hDelta hMesh
  have hErr := Kyprianou.Ch04.kw47_actual_exp_grid_linearization_limit
    L alpha hAlpha w a b hab u N hu h0 hN delta hDelta hMesh
  change Tendsto (fun n => ∑ i ∈ Finset.range (N n),
    ((u n (i+1):Real)-(u n i:Real))*Z (u n (i+1))) atTop
      (nhds (J b-J a)) at hTime
  change Tendsto (fun n => ∑ i ∈ Finset.range (N n),
    (U (u n (i+1))-U (u n i))*Z (u n (i+1))) atTop
      (nhds (U b-U a)) at hRecord
  change Tendsto (fun n =>
    (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
      (1-Real.exp (-(G (u n (i+1))-G (u n i))))) -
    (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
      (G (u n (i+1))-G (u n i)))) atTop (nhds 0) at hErr
  let S : Nat → Real := fun n => ∑ i ∈ Finset.range (N n),
    Z (u n (i+1)) * (G (u n (i+1))-G (u n i))
  have hS (n : Nat) : S n =
      L.ψ alpha * (∑ i ∈ Finset.range (N n),
        ((u n (i+1):Real)-(u n i:Real))*Z (u n (i+1))) -
      alpha * (∑ i ∈ Finset.range (N n),
        (U (u n (i+1))-U (u n i))*Z (u n (i+1))) := by
    dsimp only [S]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    ring
  have hSL : Tendsto S atTop
      (nhds (L.ψ alpha * (J b-J a)-alpha*(U b-U a))) := by
    simpa only [← hS] using (hTime.const_mul (L.ψ alpha)).sub
      (hRecord.const_mul alpha)
  have hEH (r : NNReal) : E r * H r = Z r := by
    dsimp only [E,H,G,Z]
    rw [← Real.exp_add]
    congr 1
    ring
  have hCell (r s : NNReal) :
      E s * (H s-H r) = Z s * (1-Real.exp (-(G s-G r))) := by
    have hh : H r = H s * Real.exp (-(G s-G r)) := by
      dsimp only [H]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hh, ← hEH s]
    ring
  have hCorr := hErr.add hSL
  have hCorr' : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      E (u n (i+1)) * (H (u n (i+1))-H (u n i))) atTop
      (nhds (L.ψ alpha * (J b-J a)-alpha*(U b-U a))) := by
    simpa only [S, sub_add_cancel, zero_add, hCell] using hCorr
  exact hCorr'
