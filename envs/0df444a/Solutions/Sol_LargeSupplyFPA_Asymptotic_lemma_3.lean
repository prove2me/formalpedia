-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T13:53:11.818459+00:00
-- url     : https://prove2.me/submissions/610c6d40-21b1-49ea-9aa9-f67c31b53584

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

private theorem marginalBid_Ioi_eq_zero {n : ℕ} (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (i : Fin n) [IsProbabilityMeasure (V i)]
    [IsMarkovKernel (E i)] {H ω b : ℝ} (hValue : V i (Set.Icc 0 H) = 1)
    (hBid : OverbidAtMost ω V E) (hb : H + ω ≤ b) :
    marginalBid V E i (Set.Ioi b) = 0 := by
  have hValues : ∀ᵐ v ∂V i, v ∈ Set.Icc (0 : ℝ) H :=
    (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).2
      (hValue.trans (measure_univ (μ := V i)).symm)
  have hzero : (fun v => E i v (Set.Ioi b)) =ᵐ[V i] 0 := by
    filter_upwards [hValues, Measure.support_mem_ae (μ := V i)] with v hv hs
    have hmass := hBid i v hs
    have hcompl : E i v (Set.Iic (v + ω))ᶜ = 0 := by
      rw [measure_compl measurableSet_Iic (by finiteness), hmass, measure_univ, tsub_self]
    refine measure_mono_null (s := Set.Ioi b) ?_ hcompl
    intro x hx hle
    exact not_lt_of_ge (le_trans (show x ≤ v + ω from hle)
      (le_trans (add_le_add_left hv.2 ω) hb)) hx
  rw [marginalBid, Measure.bind_apply measurableSet_Ioi (E i).aemeasurable,
    lintegral_congr_ae hzero]
  simp

private theorem eventually_nonneg_cutoff (δ : ℝ) (hδ : δ < (0.5 : ℝ)) :
    ∀ᶠ k : ℕ in atTop, 0 ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
  have hExponent : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith
  have hPower := (tendsto_rpow_neg_atTop hExponent).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hPower.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop (2 : ℕ)] with k hSmall hk
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : 0 < (k : ℝ) := by linarith
  have hRewrite : (k : ℝ) ^ ((0.5 : ℝ) + δ) =
      (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) * (k : ℝ) := by
    conv_rhs => rw [← Real.rpow_add_one hkPos.ne']
    congr 1
    ring
  change (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) < 1 / 2 at hSmall
  have hBound := mul_lt_mul_of_pos_right hSmall hkPos
  rw [hRewrite]
  linarith

theorem solution (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ)
    (hH : 0 < H) (_hκ : 0 < κ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (_hA4 : ∀ k, IsAtomless (V k) (E k)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, highThreshold δ k (V k) (E k) ≤ H + η := by
  intro η hη
  obtain ⟨ω, hωpos, hωsmall, hωbid⟩ := hA3
  filter_upwards [hωsmall.bound hη, eventually_nonneg_cutoff δ hδ.2] with k hSmall hCutoff
  have hnk : (k : ℝ) < n k := by exact_mod_cast hseq.1 k
  have hnPos : 0 < (n k : ℝ) := lt_of_le_of_lt (by positivity) hnk
  have hRatio : (k : ℝ) / (n k : ℝ) ≤ 1 := (div_le_one hnPos).2 hnk.le
  have hRatio0 : 0 ≤ (k : ℝ) / (n k : ℝ) := by positivity
  have hωle : ω k ≤ η := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hωpos k), abs_of_nonneg hRatio0] at hSmall
    exact hSmall.trans (mul_le_of_le_one_right hη.le hRatio)
  have hExpected : expNumAbove (V k) (E k) (H + η) = 0 := by
    unfold expNumAbove
    apply Finset.sum_eq_zero
    intro i _
    let hv := hseq.2.1 k i
    let he := (hseq.2.2 k i).1
    rw [Measure.real, marginalBid_Ioi_eq_zero (V k) (E k) i (hA1 k i).1 (hωbid k)
      (add_le_add_right hωle H), ENNReal.toReal_zero]
  unfold highThreshold
  apply csInf_le
  · exact ⟨0, fun _ hb => hb.1⟩
  · exact ⟨by linarith, hExpected ▸ hCutoff⟩

#print axioms solution
