-- Prove2me | solution 1 for ManyServerQED.Scheduling.coupled_lipschitz_observable_compact_suprema_converge
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:24:14.507705+00:00
-- url     : https://prove2.me/submissions/5f37a458-cf9d-415e-ac39-1e7c0e8ff43d

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1350000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (T : ℝ≥0)
    (v : (Fin (k+k+k+2) → ℝ) → ℝ) (hv : Continuous v)
    (hn : ∀ z, 0 ≤ v z)
    (h : ∀ x y, |v x-v y| ≤ ∑ i, |x i-y i|) :
    let S (ω : d.Ω') := ⨆ t : Icc (0:ℝ) T, ENNReal.ofReal (v (d.limit ω t.1))
    let R (n : ℕ) (ω : d.Ω') := ⨆ t : Icc (0:ℝ) T, ENNReal.ofReal (v (d.row n ω t.1))
    (∀ ω, S ω ≠ ⊤) ∧
    ∀ᵐ ω ∂d.Q, Tendsto (fun n => R n ω) atTop (𝓝 (S ω)) := by
  intro S R
  have hSF (ω : d.Ω') : S ω ≠ ⊤ := by
    have hc : ContinuousOn (fun t => v (d.limit ω t)) (Icc 0 (T:ℝ)) :=
      hv.comp_continuousOn ((d.limit_cont ω).mono fun t ht => ht.1)
    obtain ⟨C,hC⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
    have hS : S ω ≤ ENNReal.ofReal C := iSup_le fun t => ENNReal.ofReal_le_ofReal
      (hC ⟨t.1,t.2,rfl⟩)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  refine ⟨hSF,?_⟩
  filter_upwards [d.convergence] with ω hw
  have hB (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j in atTop, R j ω ≤ S ω+ENNReal.ofReal ε ∧ S ω ≤ R j ω+ENNReal.ofReal ε := by
    filter_upwards [(tendsto_order.1 (hw T T.2)).2 _ (ENNReal.ofReal_pos.2 hε)] with j hj
    have hVal (t : Icc (0:ℝ) T) :
        |v (d.row j ω t.1)-v (d.limit ω t.1)| ≤ ε := by
      apply le_of_lt
      apply (ENNReal.ofReal_lt_ofReal_iff hε).1
      exact ((ENNReal.ofReal_le_ofReal (h _ _)).trans (le_iSup₂_of_le (t:ℝ) t.2 le_rfl)).trans_lt hj
    constructor
    · apply iSup_le
      intro t
      have hv' := (abs_le.1 (hVal t)).2
      have h' : v (d.row j ω t.1) ≤ v (d.limit ω t.1)+ε := by linarith
      refine (ENNReal.ofReal_le_ofReal h').trans ?_
      rw [ENNReal.ofReal_add (hn _) hε.le]
      exact add_le_add (le_iSup (fun t : Icc (0:ℝ) T => ENNReal.ofReal (v (d.limit ω t.1))) t) le_rfl
    · apply iSup_le
      intro t
      have hv' := (abs_le.1 (hVal t)).1
      have h' : v (d.limit ω t.1) ≤ v (d.row j ω t.1)+ε := by linarith
      refine (ENNReal.ofReal_le_ofReal h').trans ?_
      rw [ENNReal.ofReal_add (hn _) hε.le]
      exact add_le_add (le_iSup (fun t : Icc (0:ℝ) T => ENNReal.ofReal (v (d.row j ω t.1))) t) le_rfl
  have hR : ∀ᶠ j in atTop, R j ω ≠ ⊤ := (hB 1 zero_lt_one).mono fun j hj =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hSF ω,ENNReal.ofReal_ne_top⟩) hj.1
  have hT : Tendsto (fun j => (R j ω).toReal) atTop (𝓝 (S ω).toReal) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hR,hB (ε/2) (half_pos hε)] with j hFin hBound
    rw [Real.dist_eq]
    have h₁ := (ENNReal.toReal_add (hSF ω) ENNReal.ofReal_ne_top) ▸
      (ENNReal.toReal_le_toReal hFin (ENNReal.add_ne_top.2 ⟨hSF ω,ENNReal.ofReal_ne_top⟩)).2 hBound.1
    have h₂ := (ENNReal.toReal_add hFin ENNReal.ofReal_ne_top) ▸
      (ENNReal.toReal_le_toReal (hSF ω) (ENNReal.add_ne_top.2 ⟨hFin,ENNReal.ofReal_ne_top⟩)).2 hBound.2
    rw [ENNReal.toReal_ofReal (half_pos hε).le] at h₁ h₂
    exact abs_lt.2 ⟨by linarith,by linarith⟩
  have hA := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hT
  rw [ENNReal.ofReal_toReal (hSF ω)] at hA
  exact hA.congr' (hR.mono fun _ h => ENNReal.ofReal_toReal h)
