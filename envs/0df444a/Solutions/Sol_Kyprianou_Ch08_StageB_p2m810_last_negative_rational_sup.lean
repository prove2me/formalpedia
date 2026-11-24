-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_last_negative_rational_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:39.151865+00:00
-- url     : https://prove2.me/submissions/977665f3-04e0-4d72-9152-fffed94e3a16

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.LeftRightNhds
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    lastNegativeVisit (fun t (_ : Unit) => f t) () =
      ⨆ r : ℚ, if 0 < (r : ℝ) ∧ f (Real.toNNReal (r : ℝ)) < 0
        then (Real.toNNReal (r : ℝ) : WithTop ℝ≥0) else 0 := by
  classical
  let k : ℚ → ℝ≥0 := fun r => Real.toNNReal (r : ℝ)
  let C : ℚ → WithTop ℝ≥0 := fun r =>
    if 0 < (r : ℝ) ∧ f (k r) < 0 then (k r : WithTop ℝ≥0) else 0
  let S : Set (WithTop ℝ≥0) :=
    {s | ∃ u : ℝ≥0, 0 < u ∧ (u : WithTop ℝ≥0) = s ∧ f u < 0}
  change sSup S = ⨆ r, C r
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨u, hu, rfl, hfu⟩
    obtain ⟨b, hub, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.mp (hr u (Iio_mem_nhds hfu))
    obtain ⟨r, hur, hrb⟩ := exists_rat_btwn
      (show (u : ℝ) < (b : ℝ) by exact_mod_cast hub)
    have hp : 0 < (r : ℝ) := lt_trans (NNReal.coe_pos.mpr hu) hur
    have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ hp.le
    have huk : u < k r := by
      exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkb : k r < b := by
      exact_mod_cast (show (k r : ℝ) < (b : ℝ) by rwa [hcoe])
    have hneg : f (k r) < 0 := hsub ⟨huk.le,hkb⟩
    have hle : (u : WithTop ℝ≥0) ≤ C r := by
      rw [show C r = (k r : WithTop ℝ≥0) from if_pos ⟨hp,hneg⟩]
      exact WithTop.coe_le_coe.mpr huk.le
    exact hle.trans (le_iSup C r)
  · apply iSup_le
    intro r
    by_cases h : 0 < (r : ℝ) ∧ f (k r) < 0
    · have hk : 0 < k r := by
        have hc : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ h.1.le
        exact NNReal.coe_pos.mp (hc.symm ▸ h.1)
      rw [show C r = (k r : WithTop ℝ≥0) from if_pos h]
      exact le_sSup ⟨k r,hk,rfl,h.2⟩
    · rw [show C r = 0 from if_neg h]
      exact zero_le
