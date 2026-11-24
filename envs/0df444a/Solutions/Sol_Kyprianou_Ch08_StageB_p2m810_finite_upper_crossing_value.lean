-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_finite_upper_crossing_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:44:54.2988+00:00
-- url     : https://prove2.me/submissions/2c9e8f91-f307-4226-9a65-05d04e4d8629


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0),
      ContinuousWithinAt (fun t => X t ω) (Ici u) u →
      tauPlus X l ω = (u : WithTop ℝ≥0) → l ≤ X u ω := by
  intro Ω X ω l u hc ht
  by_contra! hn
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hc (Iio_mem_nhds hn))
  let S : Set (WithTop ℝ≥0) := {s | ∃ v : ℝ≥0,
      0 < v ∧ (v:WithTop ℝ≥0)=s ∧ l < X v ω}
  have hS : sInf S = (u:WithTop ℝ≥0) := ht
  have hu : sInf S < (b:WithTop ℝ≥0) := by rw [hS]; exact_mod_cast hb
  obtain ⟨s,hs,hlt⟩ := sInf_lt_iff.mp hu
  have hle := sInf_le hs
  rcases hs with ⟨v,hv,rfl,hcross⟩
  rw [hS] at hle
  have hvI : v ∈ Ico u b := ⟨WithTop.coe_le_coe.mp hle, WithTop.coe_lt_coe.mp hlt⟩
  exact (not_lt_of_ge hcross.le) (hsub hvI)
