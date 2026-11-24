-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_expTailFormula_atZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:22:03.99806+00:00
-- url     : https://prove2.me/submissions/80d847ca-cbf1-49b2-8c5f-a4fc036b31b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03
open scoped Topology

theorem solution
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    ∀ (phi : ℝ), (0 < phi ∧ L.ψ phi = q) →
    ((P.prod Q) {pair : Omega × OmegaE |
          0 < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal = 1 := by
  intro phi hphi
  let E : Set (Omega × OmegaE) :=
    {pair | 0 < LevyExtrema.SBA.runSup
      (fun s => L.X s pair.1) (e pair.2)}
  change (P.prod Q).real E = 1
  have hLower : ∀ x : ℝ, 0 < x →
      Real.exp (-phi * x) ≤ (P.prod Q).real E := by
    intro x hx
    have hsub : {pair : Omega × OmegaE |
        x < LevyExtrema.SBA.runSup
          (fun s => L.X s pair.1) (e pair.2)} ⊆ E := by
      intro pair hp
      exact lt_trans hx hp
    have hBound : (P.prod Q) E ≤ (P.prod Q) Set.univ :=
      measure_mono (Set.subset_univ E)
    have hTop : (P.prod Q) Set.univ ≠ ⊤ := by simp
    have hFinite : (P.prod Q) E ≠ ⊤ :=
      ne_top_of_le_ne_top hTop hBound
    have hMeasured :
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal ≤
        ((P.prod Q) E).toReal := by
      exact MeasureTheory.measureReal_mono hsub hFinite
    have hTail :=
      Kyprianou.Ch03.exercise36_expTailFormula_positive
        P Q F L hNotDecreasing q hq e hExponential phi hphi x hx
    rw [hTail] at hMeasured
    exact hMeasured
  have hLimit : Tendsto (fun x : ℝ => Real.exp (-phi * x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ => Real.exp (-phi * x)) (0 : ℝ) := by
      fun_prop
    have hAt : Tendsto (fun x : ℝ => Real.exp (-phi * x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Real.exp (-phi * (0 : ℝ)))) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hAt
  have hEventual :
      Filter.Eventually (fun x : ℝ => Real.exp (-phi * x) ≤ (P.prod Q).real E)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hLower x hx
  have hLow : (1 : ℝ) ≤ (P.prod Q).real E :=
    le_of_tendsto hLimit hEventual
  have hUp : (P.prod Q).real E ≤ (1 : ℝ) :=
    MeasureTheory.measureReal_le_one
  exact le_antisymm hUp hLow

