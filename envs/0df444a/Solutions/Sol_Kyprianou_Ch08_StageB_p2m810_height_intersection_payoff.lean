-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_height_intersection_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:56:39.083691+00:00
-- url     : https://prove2.me/submissions/184eccd8-8d34-49e9-b115-ef1d2677e529

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_upper_crossing_value
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_record_drawdown_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_record_prebound_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedPathRegularityAE
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      (fun ω => (⋂ k : ℕ, {ω | NoDrawdownBeforeUpcrossing D.X l
          (a+1/((k:ℝ)+1)) ω}).indicator (fun ω => discountedAt q (tauPlus D.X l ω)) ω)
        =ᵐ[P] (fun ω => if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
          then discountedAt q (tauPlus D.X l ω) else 0) := by
  intro Ω mΩ P hP D ψ W hψ hW q a l hq ha hl
  filter_upwards [D.levy.cadlag_ae,sourceReflectedPathRegularityAE P D] with ω hc hr
  let f := fun t : ℝ≥0 => reflectAtSup D.X 0 t ω
  have hX0 : D.X 0 ω = 0 := congrFun D.levy.start_zero ω
  have hf0 : f 0 = 0 := by
    have he : {z : ℝ | ∃ t : ℝ≥0,t≤0 ∧ z=D.X t ω} = {0} := by
      ext z
      simp only [mem_setOf_eq,mem_singleton_iff]
      constructor
      · rintro ⟨t,ht,rfl⟩
        simpa [show t=0 from le_antisymm ht bot_le] using hX0
      · intro hz
        exact ⟨0,le_rfl,hz.trans hX0.symm⟩
    simp [f,reflectAtSup,runningSup,he,hX0]
  cases hτ : tauPlus D.X l ω with
  | top => simp [hτ,discountedAt,Set.indicator_apply]
  | coe u =>
    have hu := p2m810_finite_upper_crossing_value Ω D.X ω l u (hc u).1 hτ
    have hfu : f u = 0 := p2m810_finite_record_drawdown_zero Ω D.X ω l u hl hX0
      (Kyprianou.Ch01.cadlag_runningSup_bddAbove (fun t=>D.X t ω) hc u) hu hτ
    have hsurv := p2m810_strict_record_prebound_v2 f a u (by rw [hf0]; exact ha.le)
      (by rw [hfu]; exact ha) (hr.1 u)
    have he : ω ∈ ⋂ k : ℕ, {ω | NoDrawdownBeforeUpcrossing D.X l (a+1/((k:ℝ)+1)) ω}
        ↔ tauPlus D.X l ω < reflectedSupExit D.X 0 a ω := by
      rw [hτ]
      change _ ↔ (u:WithTop ℝ≥0) < tauPlus (fun t (_:Unit)=>f t) a ()
      rw [hsurv]
      simp only [mem_iInter,mem_setOf_eq,NoDrawdownBeforeUpcrossing,hτ,WithTop.coe_lt_coe]
      constructor
      · intro h t ht
        have htend : Tendsto (fun n : ℕ => a + 1 / ((n:ℝ)+1)) atTop (nhds a) := by
          have hh := (tendsto_const_nhds (x := a)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          simpa using hh
        exact ge_of_tendsto htend (Filter.Eventually.of_forall (fun n => (h n t ht).le))
      · intro h n t ht
        exact lt_of_le_of_lt (h t ht) (lt_add_of_pos_right a (by positivity))
    change (⋂ k : ℕ, {ω | NoDrawdownBeforeUpcrossing D.X l
      (a+1/((k:ℝ)+1)) ω}).indicator _ ω = _
    by_cases hh : tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
    · rw [Set.indicator_of_mem (he.mpr hh)]
      simp [hτ] at hh
      simp [hh,hτ]
    · rw [Set.indicator_of_notMem (fun hm => hh (he.mp hm))]
      simp [hτ] at hh
      simp [hh,hτ]
