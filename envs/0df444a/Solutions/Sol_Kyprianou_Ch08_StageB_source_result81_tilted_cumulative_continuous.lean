-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:04:31.688231+00:00
-- url     : https://prove2.me/submissions/08154310-d87e-4612-9c65-383e13e44b3e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Iic_of_finite_noAtoms
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Defs.Filter

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hf : ∀ x : ℝ, ν (Iic x) < ⊤) (hatom : ∀ x : ℝ, 0 < x → ν {x} = 0) :
    ContinuousOn (fun x => (ν (Iic x)).toReal) (Ici (0 : ℝ)) := by
  classical
  let ν' := ν.restrict (Ioi (0 : ℝ))
  letI : NullSingletonClass ν' := ⟨fun x => by
    change ν.restrict (Ioi (0 : ℝ)) {x} = 0
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : 0 < x
    · have hxset : ({x} : Set ℝ) ∩ Ioi (0 : ℝ) = {x} := by
        ext y
        simp [hx]
      rw [hxset, hatom x hx]
    · have h : ({x} : Set ℝ) ∩ Ioi 0 = ∅ := by ext y; simp [hx]
      rw [h, measure_empty]⟩
  have hf' (x : ℝ) : ν' (Iic x) ≠ ⊤ :=
    ((Measure.restrict_le_self (s := Ioi 0) (μ := ν) (Iic x)).trans_lt (hf x)).ne
  have hc := AvramDividend.Classical.continuous_measureReal_Iic_of_finite_noAtoms ν' hf'
  have h0 : ν (Iic (0 : ℝ)) = ν {0} := by
    have h : Iic (0 : ℝ) = Iio 0 ∪ {(0 : ℝ)} := by
      ext y
      simp [le_iff_lt_or_eq]
    rw [h, measure_union (disjoint_singleton_right.mpr (by simp)) (measurableSet_singleton _),
      hsupp, zero_add]
  have hz : Continuous (fun _ : ℝ => (ν {0}).toReal) := continuous_const
  refine (hc.add hz).continuousOn.congr (fun x hx => ?_)
  have he : Iic x ∩ (Ioi (0 : ℝ))ᶜ = Iic 0 := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_compl_iff, mem_Ioi]
    exact ⟨fun h => le_of_not_gt h.2, fun h => ⟨h.trans hx, not_lt_of_ge h⟩⟩
  have hcpart : (ν.restrict ((Ioi (0 : ℝ))ᶜ)) (Iic x) = ν {0} := by
    rw [Measure.restrict_apply measurableSet_Iic, he, h0]
  have hsplit : ν' (Iic x) + ν {0} = ν (Iic x) := by
    have h := congrArg (fun μ : Measure ℝ => μ (Iic x))
      (Measure.restrict_add_restrict_compl (μ := ν) (s := Ioi (0 : ℝ)) measurableSet_Ioi)
    simpa only [ν', Measure.add_apply, hcpart] using h
  have hfiniteZero : ν {0} ≠ ⊤ := by simpa only [h0] using (hf 0).ne
  change (ν (Iic x)).toReal = (ν' (Iic x)).toReal + (ν {0}).toReal
  calc
    (ν (Iic x)).toReal = (ν' (Iic x) + ν {0}).toReal :=
      congrArg ENNReal.toReal hsplit.symm
    _ = _ := ENNReal.toReal_add (hf' x) hfiniteZero
