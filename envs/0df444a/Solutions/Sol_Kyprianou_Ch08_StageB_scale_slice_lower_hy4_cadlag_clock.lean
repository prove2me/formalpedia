-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_slice_lower_hy4_cadlag_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:28:25.88182+00:00
-- url     : https://prove2.me/submissions/28efcff3-74fe-471c-953c-5d52c6073a42

import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_finite_endpoint
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.WithBot
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private theorem withTop_eq_of_ennreal_eq {u : ℝ≥0} {t : WithTop ℝ≥0}
    (h : (u : ℝ≥0∞) = t) : (u : WithTop ℝ≥0) = t := by
  cases t with
  | top =>
      exact False.elim (ENNReal.coe_ne_top h)
  | coe v =>
      have huv : u = v := by simpa using h
      exact congrArg (fun x : ℝ≥0 => (x : WithTop ℝ≥0)) huv
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    {l d : ℝ} (hl : 0 < l) (hd : 0 < d) {ω : Ω}
    (hcad : IsCadlag (fun t : ℝ≥0 => D.X t ω))
    (hND : NoDrawdownBeforeUpcrossing D.X d l ω) :
    tauPlus D.X d ω ≠ ⊤ → tauPlus D.X d ω < tauMinus D.X (-l) ω := by
  intro hUtop
  obtain ⟨u, hu, hXu⟩ :=
    Kyprianou.Ch08.StageB.scale_slice_lower_hy4_finite_endpoint D hd hcad hUtop
  have hTu : (u : WithTop ℝ≥0) = tauPlus D.X d ω := withTop_eq_of_ennreal_eq hu
  have hEv : {v : ℝ≥0 | -l < D.X v ω} ∈ 𝓝[Ici u] u :=
    (hcad u).1 (Ioi_mem_nhds (lt_of_lt_of_le (by linarith) hXu))
  obtain ⟨b, hub, hbsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hEv
  have hLge : (b : WithTop ℝ≥0) ≤ tauMinus D.X (-l) ω := by
    unfold tauMinus
    apply le_sInf
    intro t ht
    rcases ht with ⟨v, hv0, rfl, hvl⟩
    by_contra hnot
    have hvtE : (v : WithTop ℝ≥0) < (b : WithTop ℝ≥0) := lt_of_not_ge hnot
    have hvt : v < b := by exact_mod_cast hvtE
    by_cases hvu : v < u
    · have hvuE : (v : WithTop ℝ≥0) < tauPlus D.X d ω := by
        rw [← hTu]
        exact WithTop.coe_lt_coe.mpr hvu
      have href := hND v hvuE
      unfold reflectAtSup at href
      have hmax : 0 ≤ max 0 (runningSup D.X v ω) := le_max_left _ _
      have hxgt : -l < D.X v ω := by linarith
      linarith
    · have huv : u ≤ v := le_of_not_gt hvu
      have hxgt : -l < D.X v ω := hbsub ⟨huv, hvt⟩
      linarith
  have hUb : tauPlus D.X d ω < (b : WithTop ℝ≥0) := by
    rw [← hTu]
    exact WithTop.coe_lt_coe.mpr hub
  exact lt_of_lt_of_le hUb hLge
