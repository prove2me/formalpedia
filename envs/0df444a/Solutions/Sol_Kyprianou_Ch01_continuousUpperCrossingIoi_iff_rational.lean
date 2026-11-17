-- Prove2me | solution 1 for Kyprianou.Ch01.continuousUpperCrossingIoi_iff_rational
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:01:24.549466+00:00
-- url     : https://prove2.me/submissions/afa4c666-0ba7-4d08-89cc-7ca65ed6cfc2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (u : ℝ≥0) :
    (∃ t : ℝ≥0, 0 < t ∧ t < u ∧ s < X t ω) ↔
    (∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < (u : ℝ) ∧
      s < X (Real.toNNReal (q : ℝ)) ω) := by
  constructor
  · rintro ⟨t, ht0, htu, htX⟩
    let S : Set ℝ := {r | 0 < r ∧ r < (u : ℝ) ∧
      s < X (Real.toNNReal r) ω}
    have hcont : Continuous (fun r : ℝ => X (Real.toNNReal r) ω) :=
      hc.comp continuous_real_toNNReal
    have hopen : IsOpen S := by
      change IsOpen (Set.Ioi (0 : ℝ) ∩
        (Set.Iio (u : ℝ) ∩
          (fun r : ℝ => X (Real.toNNReal r) ω) ⁻¹' Set.Ioi s))
      exact isOpen_Ioi.inter
        (isOpen_Iio.inter (hcont.isOpen_preimage (Set.Ioi s) isOpen_Ioi))
    have hmem : (t : ℝ) ∈ S := by
      change 0 < (t : ℝ) ∧ (t : ℝ) < (u : ℝ) ∧
        s < X (Real.toNNReal (t : ℝ)) ω
      exact ⟨by exact_mod_cast ht0, by exact_mod_cast htu,
        by simpa only [Real.toNNReal_coe] using htX⟩
    obtain ⟨q, hq⟩ :=
      (show DenseRange (fun q : ℚ => (q : ℝ)) from
        Rat.denseRange_cast).exists_mem_open hopen ⟨(t : ℝ), hmem⟩
    change 0 < (q : ℝ) ∧ (q : ℝ) < (u : ℝ) ∧
      s < X (Real.toNNReal (q : ℝ)) ω at hq
    exact ⟨q, hq.1, hq.2.1, hq.2.2⟩
  · rintro ⟨q, hq0, hqu, hqX⟩
    refine ⟨Real.toNNReal (q : ℝ), ?_, ?_, hqX⟩
    · exact Real.toNNReal_pos.mpr hq0
    · exact (Real.toNNReal_lt_iff_lt_coe (le_of_lt hq0)).mpr hqu
