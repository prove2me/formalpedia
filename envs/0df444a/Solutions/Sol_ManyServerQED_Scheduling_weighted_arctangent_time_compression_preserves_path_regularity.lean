-- Prove2me | solution 1 for ManyServerQED.Scheduling.weighted_arctangent_time_compression_preserves_path_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:00:37.966648+00:00
-- url     : https://prove2.me/submissions/af44e9ef-f5d4-47b1-975f-e592d1066ec6

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

private noncomputable def compressedTime (s : ℝ) : ℝ := s/(1-s)
private noncomputable def timeLeft (s : ℝ) : ℝ := max 0 (1-s)
private noncomputable def unitEmbed (t : ℝ) : ℝ := max t 0/(1+max t 0)
private noncomputable def unweight (t : ℝ) : ℝ := 1+max t 0

private noncomputable def arctanVector {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => Real.arctan (x i)

private noncomputable def compactify {k : ℕ} (x : ℝ → Fin k → ℝ) (s : ℝ) :
    Fin k → ℝ := timeLeft s • arctanVector (x (compressedTime s))

private theorem continuous_arctanVector {k : ℕ} : Continuous (arctanVector (k := k)) :=
  continuous_pi (fun i => Real.continuous_arctan.comp (continuous_apply i))

private theorem norm_arctanVector {k : ℕ} (x : Fin k → ℝ) :
    ‖arctanVector x‖ ≤ Real.pi/2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Real.pi/2)).2
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_lt.2 (Real.arctan_mem_Ioo (x i))).le

private theorem arctanVector_lip {k : ℕ} (x y : Fin k → ℝ) :
    ‖arctanVector x-arctanVector y‖ ≤ ‖x-y‖ := by
  have h : LipschitzWith 1 Real.arctan := by
    apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
    intro x
    change ((‖deriv Real.arctan x‖₊ : ℝ) ≤ 1)
    rw [coe_nnnorm,Real.deriv_arctan,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (div_le_one (show (0:ℝ) < 1+x^2 by positivity)).2
      (le_add_of_nonneg_right (sq_nonneg x))
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).2
  intro i
  have hh := h.dist_le_mul (x i) (y i)
  simpa only [arctanVector,Real.norm_eq_abs,Real.dist_eq,NNReal.coe_one,one_mul,Pi.sub_apply] using
    hh.trans (by simpa only [Real.dist_eq,Real.norm_eq_abs,NNReal.coe_one,one_mul,Pi.sub_apply] using
      norm_le_pi_norm (x-y) i)

private theorem continuousAt_compressedTime {s : ℝ} (hs : s < 1) :
    ContinuousAt compressedTime s :=
  continuous_id.continuousAt.div (continuous_const.sub continuous_id).continuousAt (by linarith)

private theorem continuous_timeLeft : Continuous timeLeft :=
  continuous_const.max (continuous_const.sub continuous_id)

private theorem timeLeft_eq {s : ℝ} (hs : s ≤ 1) : timeLeft s = 1-s :=
  max_eq_right (sub_nonneg.2 hs)

private theorem compressedTime_nonneg {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    0 ≤ compressedTime s := div_nonneg hs.1 (sub_nonneg.2 hs.2)

private theorem compressedTime_mono : StrictMonoOn compressedTime (Ico (0:ℝ) 1) := by
  intro s hs t ht hst
  apply (div_lt_div_iff₀ (sub_pos.2 hs.2) (sub_pos.2 ht.2)).2
  nlinarith only [hst]

private theorem continuous_unitEmbed : Continuous unitEmbed := by
  have hM : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  exact hM.div (continuous_const.add hM) (fun t => by positivity)

private theorem unitEmbed_bounds {t : ℝ} (ht : 0 ≤ t) : unitEmbed t ∈ Ico (0:ℝ) 1 := by
  dsimp [unitEmbed]
  rw [max_eq_left ht]
  exact ⟨div_nonneg ht (by positivity),(div_lt_one (by positivity)).2 (by linarith)⟩

private theorem unitEmbed_mono : StrictMonoOn unitEmbed (Ici 0) := by
  intro s hs t ht hst
  unfold unitEmbed
  rw [max_eq_left hs,max_eq_left ht]
  apply (div_lt_div_iff₀ (by linarith [show 0 ≤ s from hs] : 0 < 1+s) (by linarith [show 0 ≤ t from ht] : 0 < 1+t)).2
  nlinarith only [hst]

private theorem compactify_inverse {k : ℕ} (f : ℝ → Fin k → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    unweight t • compactify f (unitEmbed t) = arctanVector (f t) := by
  have h := unitEmbed_bounds ht
  have hl : 1-unitEmbed t = (1+t)⁻¹ := by
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
    ring
  have hC : compressedTime (unitEmbed t) = t := by
    unfold compressedTime
    rw [hl]
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
  simp only [compactify, hC,timeLeft_eq h.2.le,hl,smul_smul,unweight,max_eq_left ht]
  rw [mul_inv_cancel₀ (by positivity : 1+t ≠ 0),one_smul]

private theorem norm_compactify {k : ℕ} (f : ℝ → Fin k → ℝ) {s : ℝ}
    (hs : s ≤ 1) : ‖compactify f s‖ ≤ (1-s)*(Real.pi/2) := by
  rw [compactify,norm_smul,timeLeft_eq hs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.2 hs)]
  exact mul_le_mul_of_nonneg_left (norm_arctanVector _) (sub_nonneg.2 hs)

private theorem compactify_one {k : ℕ} (f : ℝ → Fin k → ℝ) : compactify f 1 = 0 := by
  simp [compactify,timeLeft]

private theorem compactify_tendsto_one {k : ℕ} (f : ℝ → Fin k → ℝ) {S : Set ℝ}
    (hS : S ⊆ Iic (1:ℝ)) : Tendsto (compactify f) (𝓝[S] 1) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hW : Tendsto (fun s : ℝ => (1-s)*(Real.pi/2)) (𝓝[S] 1) (𝓝 0) := by
    have hV : Continuous (fun s : ℝ => (1-s)*(Real.pi/2)) := by fun_prop
    have hc : Tendsto (fun s : ℝ => (1-s)*(Real.pi/2)) (𝓝[S] 1) (𝓝 ((1-1)*(Real.pi/2))) :=
      hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self,zero_mul] using hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hW
    (Eventually.of_forall fun _ => norm_nonneg _) (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact norm_compactify f (hS hs))

private theorem compactify_cadlag_path {k : ℕ} {f : ℝ → Fin k → ℝ}
    (hf : ∀ i, IsCadlag (fun t => f t i)) : IsCadlag01 (compactify f) := by
  constructor
  · intro s hs
    have hS : Tendsto compressedTime (𝓝[Icc s 1] s) (𝓝[Ici (compressedTime s)] (compressedTime s)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuousAt_compressedTime hs.2).tendsto.mono_left nhdsWithin_le_nhds
      · have hLt : Iio (1:ℝ) ∈ 𝓝[Icc s 1] s :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2)
        filter_upwards [self_mem_nhdsWithin,hLt] with t ht ht'
        change compressedTime s ≤ compressedTime t
        rcases ht.1.eq_or_lt with h | h
        · rw [h]
        · exact (compressedTime_mono hs ⟨hs.1.trans ht.1,ht'⟩ h).le
    have hU : Tendsto f (𝓝[Ici (compressedTime s)] (compressedTime s)) (𝓝 (f (compressedTime s))) := by
      apply tendsto_pi_nhds.2
      intro i
      exact (hf i).1 _ (compressedTime_nonneg ⟨hs.1,hs.2.le⟩)
    exact (continuous_timeLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).smul
      (continuous_arctanVector.continuousAt.tendsto.comp (hU.comp hS))
  · intro s hs
    rcases hs.2.lt_or_eq with hb | rfl
    · have hC : 0 < compressedTime s := div_pos hs.1 (sub_pos.2 hb)
      have hS : Tendsto compressedTime (𝓝[Ico 0 s] s) (𝓝[<] (compressedTime s)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (continuousAt_compressedTime hb).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact compressedTime_mono ⟨ht.1,ht.2.trans hb⟩ ⟨hs.1.le,hb⟩ ht.2
      choose l hl using fun i => (hf i).2 _ hC
      have hF : Tendsto f (𝓝[<] (compressedTime s)) (𝓝 l) := tendsto_pi_nhds.2 hl
      exact ⟨timeLeft s • arctanVector l,
        (continuous_timeLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).smul
          (continuous_arctanVector.continuousAt.tendsto.comp (hF.comp hS))⟩
    · exact ⟨0,compactify_tendsto_one _ (fun _ h => h.2.le)⟩

set_option maxHeartbeats 1000000 in
theorem solution {k : ℕ} (f : ℝ → Fin k → ℝ) :
    let z (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (f (s/(1-s)) i))
    ((∀ i, IsCadlag (fun t => f t i)) → IsCadlag01 z) ∧
    (ContinuousOn f (Set.Ici 0) → ContinuousOn z (Set.Icc (0:ℝ) 1)) := by
  intro z
  change ((∀ i, IsCadlag (fun t => f t i)) → IsCadlag01 (compactify f)) ∧
    (ContinuousOn f (Set.Ici 0) → ContinuousOn (compactify f) (Set.Icc (0:ℝ) 1))
  refine ⟨compactify_cadlag_path,?_⟩
  intro hF s hs
  rcases hs.2.lt_or_eq with hb | rfl
  · have hS : ContinuousWithinAt compressedTime (Icc (0:ℝ) 1) s :=
      (continuousAt_compressedTime hb).continuousWithinAt
    have hf := (hF _ (compressedTime_nonneg hs)).comp hS
      (fun t ht => compressedTime_nonneg ht)
    exact continuous_timeLeft.continuousWithinAt.smul
      (continuous_arctanVector.continuousAt.comp_continuousWithinAt hf)
  · rw [ContinuousWithinAt,compactify_one]
    exact compactify_tendsto_one _ (fun _ h => h.2)
