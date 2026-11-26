-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_extended_perpetual_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:48:14.809135+00:00
-- url     : https://prove2.me/submissions/8fddb585-8e0f-4272-8775-78ea9ed25026

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
import Theorems.Thm_Kyprianou_Ch04_cor412_perpetual_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_frequency_limit
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_path
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0)
    (β : ℝ) (hβ : 0 < β) :
    let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Omega → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    (∫ w, Real.exp (β * (-D w)) ∂P) =
      derivWithin L.ψ (Ici 0) 0 * β / L.ψ β := by
  classical
  intro B D
  let : IsProbabilityMeasure P := L.isProbability
  obtain ⟨ha,hb⟩ := Kyprianou.Ch04.cor412_lower_bounded P F L hm
  obtain ⟨_,hp⟩ := Kyprianou.Ch04.cor412_positive_exponent P F L hm
  obtain ⟨h0,_,hc,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hs := Kyprianou.Ch04.cor412_secant_deriv L.ψ h0 hc hm
  have H := Kyprianou.Ch04.cor412_perpetual_transform P F L hb ha β hβ (hp β hβ).ne'
  rw [hs] at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards [hb] with w hw
  have hwB : w ∈ B := hw
  simp [D,hwB]
