-- Prove2me | solution 1 for ManyServerQED.Scheduling.arctangent_fdd_limit_is_interior_on_compact_rational_times
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:37:17.567358+00:00
-- url     : https://prove2.me/submissions/cc036f95-09d3-4b4f-a4e9-c2319d9e9384

import Mathlib

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 1800000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (y : Ω' → ℝ → Fin k → ℝ)
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j i => Real.arctan (X n ω (τ j) i)) atTop
        (fun ω j => y ω (τ j)) (fun _ => P) P')
    (hB : ∀ (T : ℕ) (η : ℝ), 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖X n ω t‖} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P', ∀ (T : ℕ) (i : Fin k), ∃ b : ℕ, ∀ q : ℚ,
      (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) → |y ω (q:ℝ) i| ≤ Real.pi/2-1/((b:ℝ)+1) := by
  classical
  apply ae_all_iff.2
  intro T
  apply ae_all_iff.2
  intro i
  apply ae_iff.2
  apply le_antisymm _ zero_le
  apply le_of_forall_gt
  intro η hη
  obtain ⟨e,_,he,heη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  obtain ⟨A,hA,hN⟩ := hB T e (ENNReal.ofReal_pos.1 he)
  let Q := {q : ℚ // (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ)}
  have : Nonempty Q := ⟨⟨0,by simpa using Nat.cast_nonneg (α:=ℝ) T⟩⟩
  obtain ⟨s,hs⟩ := exists_surjective_nat Q
  let τ (j : ℕ) : ℝ := (s j).val
  let a : ℝ := Real.arctan A
  let U (m : ℕ) := {ω | ∃ j < m, a < |y ω (τ j) i|}
  have hMono : Monotone U := by
    intro m n hmn ω hω
    obtain ⟨j,hj,hb⟩ := hω
    exact ⟨j,hj.trans_le hmn,hb⟩
  have hU (m : ℕ) : P' (U m) ≤ ENNReal.ofReal e := by
    let B : Set (Fin m → Fin k → ℝ) := {z | ∃ j, a < |z j i|}
    have hB : IsOpen B := by
      have he : B = ⋃ j : Fin m, {z : Fin m → Fin k → ℝ | a < |z j i|} := by
        ext z
        simp [B]
      rw [he]
      apply isOpen_iUnion
      intro j
      exact isOpen_lt continuous_const (((continuous_apply i).comp (continuous_apply j)).abs)
    let Z (n : ℕ) (ω : Ω) (j : Fin m) (i : Fin k) := Real.arctan (X n ω (τ j) i)
    let v (ω : Ω') (j : Fin m) := y ω (τ j)
    have hF' : TendstoInDistribution Z atTop v (fun _ => P) P' :=
      hF m (fun j => τ j) (fun j => (s j).2.1)
    have hPort := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hF'.tendsto hB
    have h' : P' (U m) = (P'.map v) B := by
      rw [Measure.map_apply_of_aemeasurable hF'.aemeasurable_limit hB.measurableSet]
      congr 1
      ext ω
      exact ⟨fun ⟨j,hj,h⟩ => ⟨⟨j,hj⟩,h⟩,fun ⟨j,h⟩ => ⟨j,j.2,h⟩⟩
    rw [h']
    refine hPort.trans (Filter.liminf_le_of_frequently_le' ?_)
    apply Eventually.frequently
    filter_upwards [hN] with n hn
    change (P.map (Z n)) B ≤ _
    rw [Measure.map_apply_of_aemeasurable (hF'.forall_aemeasurable n) hB.measurableSet]
    refine (measure_mono ?_).trans hn
    rintro ω ⟨j,hj⟩
    refine ⟨τ j,(s j).2,?_⟩
    by_contra! hn
    have hCoord : |X n ω (τ j) i| ≤ ‖X n ω (τ j)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (X n ω (τ j)) i
    have hXi : |X n ω (τ j) i| ≤ A := hCoord.trans hn
    have h1 := Real.arctan_mono (abs_le.1 hXi).1
    have h2 := Real.arctan_mono (abs_le.1 hXi).2
    rw [Real.arctan_neg] at h1
    exact (not_lt_of_ge (abs_le.2 ⟨h1,h2⟩)) hj
  have hAll : P' (⋃ m, U m) ≤ ENNReal.ofReal e :=
    le_of_tendsto_of_tendsto' (tendsto_measure_iUnion_atTop hMono) tendsto_const_nhds hU
  have hMargin : ∃ b : ℕ, a ≤ Real.pi/2-1/((b:ℝ)+1) := by
    have hPos : 0 < Real.pi/2-a := sub_pos.2 (Real.arctan_lt_pi_div_two A)
    obtain ⟨b,hb⟩ := exists_nat_gt (1/(Real.pi/2-a))
    refine ⟨b,?_⟩
    have hB : 1/((b:ℝ)+1) < Real.pi/2-a := by
      apply (div_lt_iff₀ (by positivity : 0 < (b:ℝ)+1)).2
      have h := (div_lt_iff₀ hPos).1 hb
      nlinarith
    linarith
  obtain ⟨b,hb⟩ := hMargin
  refine (measure_mono ?_).trans_lt (hAll.trans_lt heη)
  intro ω hω
  by_contra hnot
  apply hω
  refine ⟨b,fun q hq => ?_⟩
  obtain ⟨j,hj⟩ := hs ⟨q,hq⟩
  have hr : τ j = q := congrArg (fun z : Q => (z.val:ℝ)) hj
  refine (le_of_not_gt (fun h => hnot (mem_iUnion.2 ⟨j+1,j,Nat.lt_succ_self j,?_⟩))).trans hb
  simpa only [hr] using h
