-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FiniteRestartLawUnrestrictV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:39:18.713453+00:00
-- url     : https://prove2.me/submissions/a3cc0406-87eb-40d0-b873-297c913029fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (A : Omega → WithTop NNReal)
    (hFin : ∀ᵐ w ∂P, A w ≠ ⊤)
    (Z Y : Omega → E)
    (hZ : AEMeasurable Z (P.restrict {w | A w ≠ ⊤}))
    (B : Set Omega)
    (hLaw : (P.restrict (B ∩ {w | A w ≠ ⊤})).map Z =
      P (B ∩ {w | A w ≠ ⊤}) • P.map Y) :
    AEMeasurable Z P ∧ (P.restrict B).map Z = P B • P.map Y := by
  have hD : ({w | A w ≠ ⊤} : Set Omega) =ᵐ[P] univ := by
    filter_upwards [hFin] with w hw
    exact propext (show (A w ≠ ⊤) ↔ True from iff_true_intro hw)
  have hE : (B ∩ {w | A w ≠ ⊤} : Set Omega) =ᵐ[P] B := by
    filter_upwards [hFin] with w hw
    exact propext (show (w ∈ B ∧ A w ≠ ⊤) ↔ w ∈ B from
      ⟨And.left, fun hb => ⟨hb, hw⟩⟩)
  rw [Measure.restrict_congr_set hD, Measure.restrict_univ] at hZ
  rw [Measure.restrict_congr_set hE, measure_congr hE] at hLaw
  exact ⟨hZ,hLaw⟩
