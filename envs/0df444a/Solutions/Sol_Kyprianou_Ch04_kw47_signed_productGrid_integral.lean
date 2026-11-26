-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_signed_productGrid_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:57:22.989015+00:00
-- url     : https://prove2.me/submissions/87e9e247-4b4d-4339-9baf-c41309289689

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_product_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_Kyprianou_Ch04_kw47_ae_abs_tail_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual left-point Esscher grids converge in probability to
the signed Kella--Whitt increment. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha) :
    let supX : NNReal → Ω → Real := fun t w =>
      sSup ((fun s : NNReal => L.X s w) '' Set.Iic t)
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha * L.X t w - L.ψ alpha * (t : Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha * supX t w + L.ψ alpha * (t : Real))
    let M : NNReal → Ω → Real := fun t w =>
      L.ψ alpha * (∫ s in Icc (0:Real) (t:Real),
        Real.exp (-alpha*(supX s.toNNReal w-L.X s.toNNReal w)) ∂volume) +
      1-Real.exp (-alpha*(supX t w-L.X t w))-alpha*supX t w
    Kyprianou.Ch04.IsStochasticIntegralInProbability P E H
      (fun t w => M 0 w - M t w) := by
  dsimp only
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L]
  letI : IsProbabilityMeasure P := L.isProbability
  let U := runningSup L
  let E : NNReal → Ω → Real := fun t w =>
    Real.exp (alpha*L.X t w-L.ψ alpha*(t:Real))
  let H : NNReal → Ω → Real := fun t w =>
    Real.exp (-alpha*U t w+L.ψ alpha*(t:Real))
  let Z : NNReal → Ω → Real := fun t w => Real.exp (-alpha*(U t w-L.X t w))
  let J : NNReal → Ω → Real := fun t w => ∫ s in Icc (0:Real) (t:Real),
    Z s.toNNReal w ∂volume
  let M : NNReal → Ω → Real := fun t w =>
    L.ψ alpha * J t w + 1 - Z t w - alpha*U t w
  change Kyprianou.Ch04.IsStochasticIntegralInProbability P E H
    (fun t w => M 0 w - M t w)
  intro t epsilon heps
  let Q : Nat → Ω → Real := fun n w =>
    ∑ i ∈ Finset.range n, H (t*(i:NNReal)/(n:NNReal)) w *
      (E (t*((i+1:Nat):NNReal)/(n:NNReal)) w-E (t*(i:NNReal)/(n:NNReal)) w)
  change Tendsto (fun n => (P {w | epsilon ≤ |Q n w-(M 0 w-M t w)|}).toReal)
    atTop (nhds 0)
  refine Kyprianou.Ch04.kw47_ae_abs_tail_zero P Q
    (fun w => M 0 w - M t w) ?_ ?_ epsilon heps
  · intro n
    exact (Kyprianou.Ch04.kw47_esscher_grid_measurable
      L alpha (fun i => t * (i:NNReal) / (n:NNReal)) n).aestronglyMeasurable
  · filter_upwards [] with w
    let u : Nat → Nat → NNReal := fun n i =>
      0+(t-0)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
    obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
      Kyprianou.Ch04.kw47_capped_uniform_grid 0 t (show 0 ≤ t from zero_le)
    have h := Kyprianou.Ch04.kw47_actual_product_grid_pathwise_limit
      L alpha hAlpha w 0 t (show 0 ≤ t from zero_le) u (fun n => n+1)
      hu h0 hN (fun n => ((t:Real)-(0:NNReal):Real)/((n+1:Nat):Real))
      hDelta (fun n i hi => le_of_eq (hMesh n i hi))
    have heq (n : Nat) : (∑ i ∈ Finset.range (n+1),
        H (u n i) w * (E (u n (i+1)) w-E (u n i) w)) = Q (n+1) w := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n+1 := Finset.mem_range.mp hi
      simp only [u,Q,zero_add,tsub_zero,min_eq_left (le_of_lt hi'),
        min_eq_left (Nat.succ_le_of_lt hi')]
    change Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      H (u n i) w * (E (u n (i+1)) w-E (u n i) w)) atTop
      (nhds ((Z t w - Z 0 w) - L.ψ alpha * (J t w - J 0 w) +
        alpha * (U t w - U 0 w))) at h
    have hEnd : (Z t w - Z 0 w) - L.ψ alpha * (J t w - J 0 w) +
        alpha * (U t w - U 0 w) = M 0 w - M t w := by
      dsimp only [M]
      ring
    simp only [heq, hEnd] at h
    exact (tendsto_add_atTop_iff_nat 1).mp h
