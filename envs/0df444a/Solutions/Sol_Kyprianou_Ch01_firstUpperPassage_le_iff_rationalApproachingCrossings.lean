-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_le_iff_rationalApproachingCrossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:06:17.413752+00:00
-- url     : https://prove2.me/submissions/406374c0-194c-4efb-92ab-baf7a3e3be81

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_continuousUpperCrossingIoi_iff_rational

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
    (s : ℝ) (t : ℝ≥0) :
    Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ q : ℚ, 0 < (q : ℝ) ∧
          (q : ℝ) < ((t + ε : ℝ≥0) : ℝ) ∧
          s < X (Real.toNNReal (q : ℝ)) ω := by
  let A : Set ℝ≥0 := {v | 0 < v ∧ s < X v ω}
  have hstep (u : ℝ≥0) :
      (∃ v : ℝ≥0, 0 < v ∧ v < u ∧ s < X v ω) ↔
        ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < (u : ℝ) ∧
          s < X (Real.toNNReal (q : ℝ)) ω :=
    Kyprianou.Ch01.continuousUpperCrossingIoi_iff_rational X ω hc s u
  constructor
  · intro h
    by_cases hA : ∃ v : ℝ≥0, 0 < v ∧ s < X v ω
    · have hne : A.Nonempty := by
        rcases hA with ⟨v, hv0, hvX⟩
        exact ⟨v, hv0, hvX⟩
      have hle : sInf A ≤ t := by
        simpa only [Kyprianou.Ch01.firstUpperPassage,
          if_pos hA, WithTop.coe_le_coe, A] using h
      intro ε hε
      have heps : sInf A < t + ε :=
        lt_of_le_of_lt hle (lt_add_of_pos_right t hε)
      obtain ⟨v, hvA, hvlt⟩ := exists_lt_of_csInf_lt hne heps
      exact (hstep (t + ε)).mp ⟨v, hvA.1, hvlt, hvA.2⟩
    · have htop : Kyprianou.Ch01.firstUpperPassage X s ω = ⊤ := by
        simp [Kyprianou.Ch01.firstUpperPassage, hA]
      have hleTop : (⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
        simpa only [htop] using h
      have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique hleTop
      exact (WithTop.coe_ne_top heq).elim
  · intro h
    have hA : ∃ v : ℝ≥0, 0 < v ∧ s < X v ω := by
      obtain ⟨q, hq0, hqt, hqX⟩ := h 1 (by norm_num)
      obtain ⟨v, hv0, _, hvX⟩ :=
        (hstep (t + 1)).mpr ⟨q, hq0, hqt, hqX⟩
      exact ⟨v, hv0, hvX⟩
    have hle : sInf A ≤ t := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨q, hq0, hqt, hqX⟩ := h ε hε
      obtain ⟨v, hv0, hvlt, hvX⟩ :=
        (hstep (t + ε)).mpr ⟨q, hq0, hqt, hqX⟩
      exact (csInf_le' (show v ∈ A from ⟨hv0, hvX⟩)).trans hvlt.le
    simpa only [Kyprianou.Ch01.firstUpperPassage,
      if_pos hA, WithTop.coe_le_coe, A] using hle
