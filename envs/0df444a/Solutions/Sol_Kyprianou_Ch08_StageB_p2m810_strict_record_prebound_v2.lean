-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_strict_record_prebound_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:52:10.12763+00:00
-- url     : https://prove2.me/submissions/ebfa57cb-1a67-4aa2-be28-fa3be9e7ea0e


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (f : ℝ≥0 → ℝ) (a : ℝ) (u : ℝ≥0),
      f 0 ≤ a → f u < a → ContinuousWithinAt f (Ici u) u →
      (((u : WithTop ℝ≥0) < tauPlus (fun t (_ : Unit) => f t) a ()) ↔
      (∀ t : ℝ≥0, t < u → f t ≤ a)) := by
  intro f a u h0 hu hc
  constructor
  · intro h t ht
    by_contra! hbad
    have hp : 0 < t := by
      by_contra! hn
      have he : t=0 := le_antisymm hn bot_le
      rw [he] at hbad
      exact (not_lt_of_ge h0) hbad
    have hτ : tauPlus (fun t (_ : Unit) => f t) a () ≤ (t:WithTop ℝ≥0) :=
      sInf_le ⟨t,hp,rfl,hbad⟩
    exact (not_lt_of_ge (hτ.trans (WithTop.coe_le_coe.mpr ht.le))) h
  · intro h
    obtain ⟨b,hb,hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hc (Iio_mem_nhds hu))
    have hB : (b:WithTop ℝ≥0) ≤ tauPlus (fun t (_ : Unit) => f t) a () := by
      unfold tauPlus
      apply le_sInf
      rintro _ ⟨t,ht,rfl,hbad⟩
      apply WithTop.coe_le_coe.mpr
      by_contra! hlt
      by_cases htu : t < u
      · exact (not_le_of_gt hbad) (h t htu)
      · exact (not_lt_of_ge hbad.le) (hsub ⟨le_of_not_gt htu,hlt⟩)
    exact (WithTop.coe_lt_coe.mpr hb).trans_le hB
