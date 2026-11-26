-- Prove2me | solution 1 for Kyprianou.Ch04.downwardPassageFiniteProbabilityBV
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:56:16.789774+00:00
-- url     : https://prove2.me/submissions/255a4396-ac21-4469-8379-8f10800ae3fd

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_probability
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_atom_complement
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hm : 0 < derivWithin L.ψ (Ici (0 : ℝ)) 0) :
    let tau : Omega → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
    let rho : ℝ := (L.drift - derivWithin L.ψ (Ici (0 : ℝ)) 0) / L.drift
    (P {w : Omega | tau w ≠ ⊤}).toReal = rho := by
  classical
  intro tau rho
  have h := Kyprianou.Ch04.cor412_zero_atom_complement P F L hm
  have hz := Kyprianou.Ch04.cor412_zero_atom_probability P F L hBV hd hm
  dsimp only at h hz
  rw [hz] at h
  change (P {w : Omega | tau w ≠ ⊤}).toReal = _
    at h
  rw [h]
  change 1 - derivWithin L.ψ (Ici 0) 0 / L.drift =
    (L.drift - derivWithin L.ψ (Ici 0) 0) / L.drift
  field_simp [hd.ne']
