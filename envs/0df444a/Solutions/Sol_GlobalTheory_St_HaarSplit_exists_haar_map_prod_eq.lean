-- Prove2me | solution 1 for GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:14.524207+00:00
-- url     : https://prove2.me/submissions/e76d5b32-a8c6-4aa4-8ee0-d62c5241679d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHaarMapProdEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure
open scoped NNReal ENNReal
open GlobalTheory GlobalTheory.St GlobalTheory.St.HaarSplit
namespace GlobalTheory.St.HaarSplit
theorem _root_.solution {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  rw [← Measure.map_smul]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]
end GlobalTheory.St.HaarSplit
