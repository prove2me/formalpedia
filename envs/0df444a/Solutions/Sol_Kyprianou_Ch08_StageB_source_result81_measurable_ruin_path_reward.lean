-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_measurable_ruin_path_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T01:09:23.041429+00:00
-- url     : https://prove2.me/submissions/324889dd-e7d1-42e5-8dd8-52257e434ede

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem lower_clock_eq_rational_iInf (f : ℝ≥0 → ℝ) (hright : ∀ t, ContinuousWithinAt f (Ici t) t) : tauMinus (fun s (_ : Unit) => f s) 0 () = ⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ f (r : ℝ).toNNReal < 0 then ((r : ℝ).toNNReal : ℝ≥0∞) else ⊤ := by
  let k : ℚ → ℝ≥0 := fun r => (r : ℝ).toNNReal
  let C : ℚ → ℝ≥0∞ := fun r => if 0 < k r ∧ f (k r) < 0 then k r else ⊤
  let S : Set ℝ≥0∞ := {y | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = y ∧ f u < 0}
  change sInf S = ⨅ r, C r
  apply le_antisymm
  · apply le_iInf; intro r; by_cases h : 0 < k r ∧ f (k r) < 0
    · rw [show C r = (k r : ℝ≥0∞) from if_pos h]; exact sInf_le ⟨k r, h.1, rfl, h.2⟩
    · simp [C, h]
  · apply le_sInf; rintro _ ⟨u, hu, rfl, hfu⟩; by_contra! hlt
    obtain ⟨w, huw, hw⟩ := exists_between hlt
    obtain ⟨v, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hw.trans_le le_top))
    obtain ⟨b, hub, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp ((hright u) (Iio_mem_nhds hfu))
    obtain ⟨r, hur, hrm⟩ := exists_rat_btwn (show (u : ℝ) < (min v b : ℝ≥0) by exact_mod_cast lt_min (WithTop.coe_lt_coe.mp huw) hub)
    have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ (by linarith [u.coe_nonneg])
    have huk : u < k r := by exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkm : k r < min v b := by exact_mod_cast (show (k r : ℝ) < (min v b : ℝ≥0) by rwa [hcoe])
    have hneg : f (k r) < 0 := hsub ⟨huk.le, hkm.trans_le (min_le_right _ _)⟩
    have hkv : C r < (v : ℝ≥0∞) := by rw [show C r = (k r : ℝ≥0∞) from if_pos ⟨hu.trans huk, hneg⟩]; exact WithTop.coe_lt_coe.mpr (hkm.trans_le (min_le_left _ _))
    exact (not_le_of_gt (hkv.trans hw)) (iInf_le C r)

private theorem discountedAt_meas (q : ℝ) : Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  classical
  have hIf : Measurable (fun t : ℝ≥0∞ => if t = ⊤ then (0 : ℝ) else Real.exp (-q * t.toReal)) := Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))
  have hEq : (fun t : ℝ≥0∞ => discountedAt q t) = (fun t : ℝ≥0∞ => if t = ⊤ then (0 : ℝ) else Real.exp (-q * t.toReal)) := by funext t; exact ENNReal.recTopCoe (by rw [if_pos rfl]; rfl) (fun r => by simp [(show discountedAt q (↑r : ℝ≥0∞) = Real.exp (-q * (r : ℝ)) from rfl), ENNReal.coe_toReal, ENNReal.coe_ne_top]) t
  rw [hEq]; exact hIf

private theorem discountedAt_bounds (q : ℝ) (hq : 0 ≤ q) : ∀ t : ℝ≥0∞, 0 ≤ discountedAt q t ∧ discountedAt q t ≤ 1 := fun t => WithTop.recTopCoe ⟨le_refl 0, zero_le_one⟩ (fun r => ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (by positivity))⟩) t

theorem solution (q a : ℝ) (hq : 0 ≤ q) :
    Measurable (fun t : ℝ≥0∞ => discountedAt q t) ∧
    (∀ t : ℝ≥0∞, 0 ≤ discountedAt q t ∧ discountedAt q t ≤ 1) ∧
    ∃ reward : (ℝ≥0 → ℝ) → ℝ,
      Measurable reward ∧
      ∀ f : ℝ≥0 → ℝ, (∀ t, ContinuousWithinAt f (Ici t) t) →
        reward f = discountedAt q (tauMinus (fun s (_ : Unit) => a + f s) 0 ()) := by
  classical
  refine ⟨discountedAt_meas q, discountedAt_bounds q hq, ?_⟩
  have hTau : Measurable (fun f : ℝ≥0 → ℝ => ⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ a + f ((r : ℝ).toNNReal) < 0 then (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤) := by
    have hparts : ∀ r : ℚ, Measurable (fun f : ℝ≥0 → ℝ => if 0 < (r : ℝ).toNNReal ∧ a + f ((r : ℝ).toNNReal) < 0 then (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤) := fun r => if h : 0 < (r : ℝ).toNNReal then (by simp only [h, true_and]; exact (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const).comp (measurable_const.add (measurable_pi_apply _))) else (by simpa only [h, false_and, if_false] using measurable_const)
    exact Measurable.iInf hparts
  refine ⟨fun f => discountedAt q (⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ a + f ((r : ℝ).toNNReal) < 0 then (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤), (discountedAt_meas q).comp hTau, ?_⟩
  intro f hf
  have hRightG : ∀ t, ContinuousWithinAt (fun s => a + f s) (Ici t) t := fun t => continuous_const.continuousWithinAt.add (hf t)
  have hTauEq : (⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ a + f ((r : ℝ).toNNReal) < 0 then (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤) = tauMinus (fun s (_ : Unit) => a + f s) 0 () := (lower_clock_eq_rational_iInf (fun s => a + f s) hRightG).symm
  exact congrArg (discountedAt q) hTauEq
