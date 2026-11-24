-- Prove2me | solution 1 for Kyprianou.Ch01.rightContinuous_of_joint
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-24T22:39:15.70741+00:00
-- url     : https://prove2.me/submissions/e6d4c317-42e8-4146-91f4-1a0ca9133c01

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Disproof: jointly measurable integer paths need not be right-continuous (√2 spike). -/
theorem solution
    (h : ∀ {Ω : Type} [MeasurableSpace Ω]
        (X : ℝ≥0 → Ω → ℤ)
        (_hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)),
        ∀ ω : Ω, ∀ t : ℝ≥0,
          ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    False := by
  let t0 : ℝ≥0 := ⟨√(2 : ℝ), by positivity⟩
  let X : ℝ≥0 → Unit → ℤ := fun t _ => if t = t0 then (-1 : ℤ) else 1
  have hX : Measurable (fun p : Unit × ℝ≥0 => X p.2 p.1) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_singleton t0).preimage measurable_snd
  have ht0pos : (0 : ℝ≥0) < t0 := by
    change (0 : ℝ) < √(2 : ℝ)
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hnot :
      ¬ ContinuousWithinAt (fun s : ℝ≥0 => X s ()) (Set.Ici t0) t0 := by
    intro hcont
    unfold ContinuousWithinAt at hcont
    have hval : (fun s : ℝ≥0 => X s ()) t0 = (-1 : ℤ) := by simp [X]
    rw [hval, nhds_discrete (α := ℤ)] at hcont
    have hev : ∀ᶠ u in 𝓝[Set.Ici t0] t0, X u () = (-1 : ℤ) := tendsto_pure.mp hcont
    obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    obtain ⟨u, htu, hub⟩ := exists_between (mem_Ioi.mp hb)
    have hune : u ≠ t0 := ne_of_gt htu
    have : X u () = (-1 : ℤ) := hsub ⟨htu.le, hub⟩
    simp [X, hune] at this
  exact hnot (h (Ω := Unit) X hX () t0)
