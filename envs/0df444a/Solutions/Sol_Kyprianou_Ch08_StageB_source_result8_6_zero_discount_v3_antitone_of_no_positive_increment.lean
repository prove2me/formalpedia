-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_antitone_of_no_positive_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:26:04.900803+00:00
-- url     : https://prove2.me/submissions/be8d9337-e7d6-4cd8-9b3a-19596338ff7f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem antitone_of_no_positive_increment_impl :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      (∀ t : ℝ≥0, P {ω | 0 < D.X t ω} = 0) →
      ∀ (ω : Ω) (u v : ℝ≥0), u ≤ v → D.X v ω ≤ D.X u ω := by
  intro Ω mΩ P hP D hzeroAll
  have hinc : ∀ u v : ℝ≥0, u ≤ v → ∀ᵐ ω ∂P, D.X v ω ≤ D.X u ω := by
    intro u v huv
    have hstat := (D.levy.stationary_increments u (v - u)).measure_mem_eq
      (s := Ioi (0 : ℝ)) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))
    have huvadd : u + (v - u) = v := add_tsub_cancel_of_le huv
    have hleft : ProbabilityTheory.increment D.X u (u + (v - u)) =
        (fun ω => D.X v ω - D.X u ω) := by
      funext ω
      change D.X (u + (v - u)) ω - D.X u ω = D.X v ω - D.X u ω
      rw [huvadd]
    have hright : ProbabilityTheory.increment D.X 0 (v - u) = D.X (v - u) := by
      funext ω
      change D.X (v - u) ω - D.X 0 ω = D.X (v - u) ω
      rw [D.levy.start_zero]
      simp
    have hmap : P ((fun ω => D.X v ω - D.X u ω) ⁻¹' Ioi (0 : ℝ)) =
        P ((fun ω => D.X (v - u) ω) ⁻¹' Ioi (0 : ℝ)) := by
      rw [← hleft, ← hright]
      exact hstat
    have hzero : P ((fun ω => D.X v ω - D.X u ω) ⁻¹' Ioi (0 : ℝ)) = 0 := by
      rw [hmap]
      exact hzeroAll (v - u)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hzero
    have hω' : D.X u ω < D.X v ω := by
      simpa only [mem_setOf_eq, not_le] using hω
    change 0 < D.X v ω - D.X u ω
    linarith [hω']
  have hrat : ∀ᵐ ω ∂P, ∀ q r : ℚ, Real.toNNReal q ≤ Real.toNNReal r →
      D.X (Real.toNNReal r) ω ≤ D.X (Real.toNNReal q) ω := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro r
    by_cases hqr : Real.toNNReal q ≤ Real.toNNReal r
    · filter_upwards [hinc _ _ hqr] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall (fun ω h => absurd h hqr)
  have hae : ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => D.X t ω) := by
    filter_upwards [hrat, D.levy.cadlag_ae] with ω hω hcad
    intro u v huv
    have hrc : ∀ w : ℝ≥0, ContinuousWithinAt (fun z : ℝ≥0 => D.X z ω) (Ici w) w :=
      fun w => (hcad w).1
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    obtain ⟨δv, hδv_pos, hδv'⟩ := Metric.continuousWithinAt_iff.mp (hrc v) (ε / 2) (by linarith)
    obtain ⟨δu, hδu_pos, hδu'⟩ := Metric.continuousWithinAt_iff.mp (hrc u) (ε / 2) (by linarith)
    obtain ⟨r, hvr, hrv⟩ := exists_rat_btwn (show (v : ℝ) < (v : ℝ) + δv by linarith)
    have hur : (u : ℝ) < min ((u : ℝ) + δu) (r : ℝ) := by
      apply lt_min (by linarith)
      have : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
      linarith [hvr]
    obtain ⟨q, huq_lower, huq_upper⟩ := exists_rat_btwn hur
    have hr0 : (0 : ℝ) ≤ r := by
      have hv0 : (0 : ℝ) ≤ (v : ℝ) := by positivity
      linarith
    have hq0 : (0 : ℝ) ≤ q := by
      have hu0 : (0 : ℝ) ≤ (u : ℝ) := by positivity
      linarith
    have hrr : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
    have hqq : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hqr : Real.toNNReal q ≤ Real.toNNReal r := by
      rw [← NNReal.coe_le_coe, hrr, hqq]
      exact le_trans (le_of_lt (lt_of_lt_of_le huq_upper (min_le_right _ _))) le_rfl
    have hX := hω q r hqr
    have hmemr : (Real.toNNReal r : ℝ≥0) ∈ Ici v := by
      change v ≤ Real.toNNReal r
      rw [← NNReal.coe_le_coe, hrr]
      exact le_of_lt hvr
    have hdistv : dist (Real.toNNReal r) v < δv := by
      rw [NNReal.dist_eq, hrr, abs_of_pos (sub_pos.mpr hvr)]
      linarith
    have hdv := hδv' (x := Real.toNNReal r) hmemr hdistv
    have hmemq : (Real.toNNReal q : ℝ≥0) ∈ Ici u := by
      change u ≤ Real.toNNReal q
      rw [← NNReal.coe_le_coe, hqq]
      exact le_of_lt huq_lower
    have hq_uδ : (q : ℝ) < (u : ℝ) + δu :=
      lt_of_lt_of_le huq_upper (min_le_left _ _)
    have hdistq : dist (Real.toNNReal q) u < δu := by
      rw [NNReal.dist_eq, hqq, abs_of_pos (sub_pos.mpr huq_lower)]
      linarith
    have hdu := hδu' (x := Real.toNNReal q) hmemq hdistq
    rw [Real.dist_eq, abs_lt] at hdv hdu
    linarith [hX, hdv.1, hdu.2]
  exact (D.excludesNegativeSubordinator hae).elim

theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      (∀ t : ℝ≥0, P {ω | 0 < D.X t ω} = 0) →
      ∀ (ω : Ω) (u v : ℝ≥0), u ≤ v → D.X v ω ≤ D.X u ω := by
  exact antitone_of_no_positive_increment_impl
