-- Prove2me | solution 1 for Kyprianou.Ch01.levyIncrement_indep_naturalSigmaRight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:22:40.011896+00:00
-- url     : https://prove2.me/submissions/4b1ea4bc-3205-48e2-bbca-0361d0515b9d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
import Theorems.Thm_AvramDividend_Classical_independence_of_ambient_pointwise_limit_real

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Continuity upgrades Lévy independent increments to the shifted right-natural germ. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x : ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => X t ω - X s ω) inferInstance)
      (naturalSigmaRight (fun u ω => x + X u ω) s) P := by
  let Y : ℝ≥0 → Ω → ℝ := fun u ω => x + X u ω
  have hm : naturalSigmaRight Y s ≤ (inferInstance : MeasurableSpace Ω) :=
    Kyprianou.Ch01.naturalSigmaRight_le_ambient
      Y (fun u => measurable_const.add (hmeas u)) s
  have hSigma (u : ℝ≥0) (hsu : s < u) :
      naturalSigmaRight Y s ≤ naturalSigma X u := by
    have hRight : naturalSigmaRight Y s ≤ naturalSigma Y u := by
      unfold naturalSigmaRight
      exact iInf_le_of_le u (iInf_le_of_le hsu le_rfl)
    have hShift : naturalSigma Y u ≤ naturalSigma X u := by
      unfold naturalSigma
      refine iSup_le fun v => iSup_le fun hv => ?_
      have hy : @Measurable Ω ℝ (naturalSigma X u)
          inferInstance (Y v) :=
        measurable_const.add
          (Kyprianou.Ch01.naturalSigma_measurable_past X v u hv)
      exact hy.comap_le
    exact le_trans hRight hShift
  by_cases heq : s = t
  · subst t
    simpa only [sub_self, MeasurableSpace.comap_const] using
      (ProbabilityTheory.indep_bot_left (naturalSigmaRight Y s) :
        Indep (⊥ : MeasurableSpace Ω) (naturalSigmaRight Y s) P)
  · have hlt : s < t := lt_of_le_of_ne hst heq
    haveI : NeBot (𝓝[>] s) :=
      nhdsGT_neBot_of_exists_gt ⟨t, hlt⟩
    obtain ⟨v, hv⟩ := Filter.exists_seq_tendsto (𝓝[>] s)
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 (hv.eventually (Ioc_mem_nhdsGT hlt))
    let u (n : ℕ) : ℝ≥0 := v (n + N)
    have hsu (n : ℕ) : s < u n := (hN (n + N) (by omega)).1
    have hut (n : ℕ) : u n ≤ t := (hN (n + N) (by omega)).2
    have hu : Tendsto u atTop (𝓝[>] s) :=
      hv.comp (Filter.tendsto_add_atTop_nat N)
    have hu0 : Tendsto u atTop (nhds s) :=
      hu.mono_right nhdsWithin_le_nhds
    have hZ (n : ℕ) :
        Measurable (fun ω : Ω => X t ω - X (u n) ω) :=
      (hmeas t).sub (hmeas (u n))
    have hz : Measurable (fun ω : Ω => X t ω - X s ω) :=
      (hmeas t).sub (hmeas s)
    have hi (n : ℕ) :
        Indep
          (MeasurableSpace.comap (fun ω => X t ω - X (u n) ω)
            inferInstance) (naturalSigmaRight Y s) P :=
      ProbabilityTheory.indep_of_indep_of_le_right
        (Kyprianou.Ch01.levyIncrement_indep_naturalSigma
          P X hX hmeas (u n) t (hut n))
        (hSigma (u n) (hsu n))
    have htend (ω : Ω) :
        Tendsto (fun n => X t ω - X (u n) ω) atTop
          (nhds (X t ω - X s ω)) :=
      tendsto_const_nhds.sub ((hcont ω).tendsto s |>.comp hu0)
    exact AvramDividend.Classical.independence_of_ambient_pointwise_limit_real
      hm (fun n ω => X t ω - X (u n) ω)
      (fun ω => X t ω - X s ω) hZ hz hi htend
