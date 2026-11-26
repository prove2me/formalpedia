-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_J_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:46.034818+00:00
-- url     : https://prove2.me/submissions/07fbafc1-86d5-460b-8399-394e9a6d9c8b

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual time primitive is adapted by right-endpoint grid approximation. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) :
    Measurable[F t] (J L alpha beta t) := by
  let u : Nat → Nat → NNReal := fun n i =>
    0+(t-0)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid 0 t (show 0 ≤ t from zero_le)
  let q : Nat → Ω → Complex := fun n w => ∑ i ∈ Finset.range (n+1),
    ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w
  have hQ (n : Nat) : Measurable[F t] (q n) := by
    unfold q
    apply Finset.measurable_sum
    intro i hi
    have hZ := (Kyprianou.Ch04.kw48_Z_adapted L Psi alpha beta (u n (i+1))).1
    have hK : Measurable[F t] (fun _ : Ω => ((u n (i+1):Real)-(u n i:Real))) := measurable_const
    exact hK.smul (hZ.mono (F.mono (hT n (i+1))) le_rfl)
  have hLim (w : Ω) : Tendsto (fun n => q n w) atTop
      (nhds (J L alpha beta t w)) := by
    have h := Kyprianou.Ch04.kw48_time_quadrature L alpha beta w
      0 t (show 0 ≤ t from zero_le) u (fun n => n+1) hu h0 hN
      (fun n => ((t:Real)-(0:NNReal):Real)/((n+1:Nat):Real))
      hDelta (fun n i hi => le_of_eq (hMesh n i hi))
    have hJ0 : J L alpha beta 0 w = 0 := by simp [J,Set.Icc_self]
    simpa only [q,hJ0,sub_zero] using h
  exact @measurable_of_tendsto_metrizable Ω Complex (F t) _ _ _ _
    q (J L alpha beta t) hQ (tendsto_pi_nhds.mpr hLim)
