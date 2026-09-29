-- Prove2me | solution 1 for KServer.level_step_full
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T21:40:46.207761+00:00
-- url     : https://prove2.me/submissions/22dce6fa-b2c1-4b1c-b3b7-1392ccf523e1

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_assemble
import Definitions.Def_KServer_race_fix
import Definitions.Def_KServer_race_fix2
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_race_pad
import Definitions.Def_KServer_race_bad
import Definitions.Def_KServer_race_nbad
import Definitions.Def_KServer_race_step3
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold
import Definitions.Def_KServer_race_geo
import Theorems.Thm_KServer_chunk_regrid2
import Theorems.Thm_KServer_chunk_pad2
import Theorems.Thm_KServer_race_gain_bound2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

open KServer KServer.Race ThetaChain

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    (hst : s ≠ t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    {c T p V : ℝ} {M : ℕ}
    (C : KServer.ChunkSystemB X s t 0 c T p M) (hm : C.m = M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    {δ ε cLo' p' p'' V1 G T3 V3 : ℝ} {M' κ : ℕ}
    (hδ : 0 < δ) (hc0 : 0 ≤ c) (hc2δ : c ≤ 2 * δ)
    (hM'0 : 0 < M') (hM'M : M' ≤ M) (hκM' : κ ≤ M')
    (hTmax : (M : ℝ) * c ≤ 2 * δ * (M' : ℝ))
    (hε : 0 < ε) (hεLo : ε ≤ cLo') (hLo2δ : cLo' < 2 * δ + c)
    (hp0 : 0 ≤ p) (hpp' : p + (2 * δ + c) ≤ p')
    (hp'D : p' ≤ dist s t) (hp'p'' : p' ≤ p'')
    (hV0 : 0 ≤ V)
    (hV1 : 5 / 4 * V + 20 * ((2 * δ + c) * ((M : ℝ) * c)) ≤ V1)
    (hG : G ≤ Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (2 * δ + c + ε) ^ 2) ^ 2
          + 3 * (2 * δ + c + ε) ^ 2 * ((κ : ℝ) * (2 * δ + c + ε) ^ 2)))
      - (κ : ℝ) * ε
      - (2 * δ + c + ε + cLo')
        * (4 * ((M' : ℝ) * (2 * δ + c) - T) / (2 * δ + c - cLo')))
    (hT3 : T3 ≤ 3 * T + G / 2 - 2 * (2 * δ + c) - (κ : ℝ) * ε / 2
      - 2 * Real.sqrt V1)
    (hV3 : V1 + (2 * V1 + 2 * (((κ : ℝ) + 1) * (2 * δ + c))
          * Real.sqrt (2 * V1)
        + (((κ : ℝ) + 1) * (2 * δ + c)) ^ 2)
      + (2 * V1 + 2 * (2 * δ + c) ^ 2) ≤ V3) :
    letI := stepMetric s t hst
    ∃ C' : KServer.ChunkSystemB (Step s t hst) (stepS s t hst)
        (stepT s t hst) 0 (2 * δ + c) T3 p'' (3 * M' + κ),
      C'.m = 3 * M' + κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V3) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  have hcB0 : (0 : ℝ) ≤ 2 * δ + c := by linarith
  -- Step 1: grid regrouping into exactly M' windows
  have hMm : M' ≤ C.m := by
    rw [hm]
    exact hM'M
  have hmcast : ((C.m : ℕ) : ℝ) = (M : ℝ) := by rw [hm]
  have htot_ub : ∀ ω, (∑ i, C.size ω i) ≤ (M : ℝ) * c := by
    intro ω
    calc (∑ i, C.size ω i) ≤ ((C.m : ℕ) : ℝ) * c := total_le_m_mul C hc0 ω
      _ = (M : ℝ) * c := by rw [hmcast]
  have hTmax' : ∀ ω, (∑ i, C.size ω i) ≤ 2 * δ * (M' : ℕ) := by
    intro ω
    exact le_trans (htot_ub ω) hTmax
  have hEtot_ub : ∑ ω, C.P ω * ∑ i, C.size ω i ≤ (M : ℝ) * c := by
    have h1 : ∀ ω, C.P ω * ∑ i, C.size ω i ≤ C.P ω * ((M : ℝ) * c) := by
      intro ω
      exact mul_le_mul_of_nonneg_left (htot_ub ω) (C.hP ω).le
    refine le_trans (Finset.sum_le_sum fun ω _ => h1 ω) ?_
    rw [← Finset.sum_mul, C.hPsum, one_mul]
  have hV1' : 5 / 4 * V
      + 20 * ((2 * δ + c) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V1 := by
    have h20 : (2 * δ + c) * (∑ ω, C.P ω * ∑ i, C.size ω i)
        ≤ (2 * δ + c) * ((M : ℝ) * c) :=
      mul_le_mul_of_nonneg_left hEtot_ub hcB0
    linarith
  obtain ⟨C1, hm1, h0triv1, hVar1⟩ :=
    KServer.chunk_regrid2 C hMm hM'0 hδ (le_refl 0) hc0 hc2δ hp0 hpp'
      hTmax' h0triv hVar hV1'
  -- Step 2: pad empty chunks
  have hp'0 : (0 : ℝ) ≤ p' := by linarith
  obtain ⟨C2, hm2, h0triv2, hVar2, hch2⟩ :=
    KServer.chunk_pad2 C1 hp'0 h0triv1 hVar1
  have hm2' : C2.m = M' := by
    rw [hm2, hm1]
  -- Step 3: the anti-concentration gain
  have hκL : κ ≤ C2.m := by
    rw [hm2']
    exact hκM'
  have hgap : (0 : ℝ) < (2 * δ + c) - cLo' := by linarith
  have hLoB : cLo' ≤ 2 * δ + c := le_of_lt hLo2δ
  have hNbadmul := race_Nbad_bound C2 C2 C2 C2 κ ε cLo' hε hεLo hcB0
    hLoB hκL hκL
  have hEtot2 : T ≤ ∑ ω, C2.P ω * ∑ i, C2.size ω i := C2.htotal
  have hNb : ∑ ω : RΩ C2 C2 C2 C2 κ, RP C2 C2 C2 C2 κ ε ω
      * Nbad C2 C2 C2 C2 κ cLo' ω
      ≤ 4 * ((M' : ℝ) * (2 * δ + c) - T) / (2 * δ + c - cLo') := by
    rw [le_div_iff₀ hgap]
    refine le_trans hNbadmul ?_
    have hcast2 : ((C2.m : ℕ) : ℝ) = (M' : ℝ) := by rw [hm2']
    have hProd : ((C2.m : ℕ) : ℝ) * (2 * δ + c)
        = (M' : ℝ) * (2 * δ + c) := by rw [hcast2]
    linarith
  have hLocB : cLo' ≤ (2 * δ + c) + ε := by linarith
  have hGain := KServer.race_gain_bound2 C2 C2 C2 C2 κ ε hε hcB0 hεLo
    hLocB hNb
  have hG' : G ≤ ∑ ω : RΩ C2 C2 C2 C2 κ, RP C2 C2 C2 C2 κ ε ω
      * |sumL C2 C2 C2 C2 κ ω - sumR C2 C2 C2 C2 κ ω| := by
    refine le_trans hG ?_
    exact hGain
  -- Step 4: the race on the theta step
  have hV10 : (0 : ℝ) ≤ V1 := by
    have h1 : (0 : ℝ) ≤ 20 * ((2 * δ + c) * ((M : ℝ) * c)) := by
      have h2 : (0 : ℝ) ≤ (M : ℝ) * c :=
        mul_nonneg (Nat.cast_nonneg M) hc0
      positivity
    linarith
  have hpeD : dist s t + p' ≤ 2 * dist s t := by linarith
  have hmrace : mrace C2 C2 C2 C2 κ = 3 * M' + κ := by
    unfold mrace
    rw [hm2', max_self]
    omega
  have hmLo : 3 * M' + κ ≤ mrace C2 C2 C2 C2 κ := le_of_eq hmrace.symm
  have hmean : (∑ l : C2.Ω, C2.P l * ∑ i, C2.size l i)
      = ∑ r : C2.Ω, C2.P r * ∑ i, C2.size r i := rfl
  obtain ⟨C3, hm3, h0triv3, hVar3, hch3⟩ :=
    race_step3 hst C2 C2 C2 C2 κ ε hε hκL hκL hcB0 hp'0 hp'p'' hpeD
      htaut hmean h0triv2 h0triv2 h0triv2 hch2 hch2 hch2 hch2 hV10
      hVar2 hVar2 hVar2 hVar2 hG' hmLo
  -- Step 5: lower the total to T3
  refine ⟨C3.adjust (le_refl 0) (le_refl (2 * δ + c)) hT3
    (le_refl p'') (le_refl (3 * M' + κ)), ?_, ?_, ?_⟩
  · rw [ChunkSystemB.adjust_m, hm3, hmrace]
  · intro ω₁ ω₂
    exact h0triv3 ω₁ ω₂
  · exact le_trans hVar3 hV3
