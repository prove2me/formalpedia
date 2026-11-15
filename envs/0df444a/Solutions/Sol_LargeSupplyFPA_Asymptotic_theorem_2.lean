-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T14:13:15.185193+00:00
-- url     : https://prove2.me/submissions/a587a1f3-e17f-44ec-8ca4-50cb2bb5f43d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_3
import Theorems.Thm_LargeSupplyFPA_Asymptotic_corollary_1
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_6

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

private theorem smoothing_budget (n : ℕ → ℕ) (hn : ∀ k, k < n k) :
    ∃ ω : ℕ → ℝ, (∀ k, 0 < ω k) ∧ Tendsto ω atTop (𝓝 0) ∧
      (ω =o[atTop] fun k => (k : ℝ) / (n k : ℝ)) := by
  let ω : ℕ → ℝ := fun k => 1 / ((n k : ℝ) + 1)
  have hn0 (k : ℕ) : 0 ≤ (n k : ℝ) := by positivity
  have hw (k : ℕ) : 0 < ω k := by
    dsimp [ω]
    positivity
  have hnTop : Tendsto (fun k : ℕ => n k) atTop atTop :=
    tendsto_atTop_mono (fun k => (hn k).le) tendsto_id
  have hwTop : Tendsto ω atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hnTop
  refine ⟨ω, hw, hwTop, ?_⟩
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    intro h
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hnR : (0 : ℝ) < n k := by exact_mod_cast (Nat.zero_lt_of_lt (hn k))
    exact ((div_pos hkR hnR).ne' h).elim
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · exact Filter.Eventually.of_forall fun k => by
        dsimp [ω]
        positivity
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hnR : (0 : ℝ) < n k := by exact_mod_cast (Nat.zero_lt_of_lt (hn k))
      dsimp [ω]
      rw [div_div_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hkR.le
      rw [div_mul_eq_mul_div, one_mul]
      exact (div_le_one (show 0 < (n k : ℝ) + 1 by positivity)).2 (by linarith)

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (ε : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        (∀ k, NoOverbidding (V k) (E k)) →
        Tendsto εs atTop (𝓝 ε) →
        (ε = 0 → Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop = 1) ∧
        (ε ∈ Set.Ioo 0 H →
          1 - ζ * ε * (1 + Real.log (H / ε)) ≤
            Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop) := by
  classical
  obtain ⟨ζ, hζ, hApprox⟩ := lemma_6 H κ hH hκ
  refine ⟨ζ, hζ, ?_⟩
  intro n V E εs ε hseq hA1 hBNE hNoOver hε
  obtain ⟨ω, hω, hωlim, hωsmall⟩ := smoothing_budget n hseq.1
  have hsmooth (k : ℕ) := theorem_3 k (V k) (E k) (εs k)
    (hseq.2.1 k) (hseq.2.2 k) (hBNE k) (ω k) (hω k)
  choose Et hStrategy hBNEt hA4t hWelfare hShift using hsmooth
  have hseqt : IsAuctionSequence n V Et := ⟨hseq.1, hseq.2.1, hStrategy⟩
  have hA3t : Assumption3 n V Et := by
    refine ⟨ω, hω, hωsmall, ?_⟩
    intro k i v hv
    exact hShift k i v v (hNoOver k i v hv)
  have hεt : Tendsto (fun k => εs k + ω k) atTop (𝓝 ε) := by
    simpa only [add_zero] using hε.add hωlim
  have hRatio : Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop =
      Filter.liminf (fun k => welfareRatio k (V k) (Et k)) atTop := by
    apply liminf_congr
    exact Filter.Eventually.of_forall fun k => by
      unfold welfareRatio
      rw [hWelfare k]
  rw [hRatio]
  refine ⟨?_, ?_⟩
  · intro he
    exact corollary_1 H κ hH hκ n V Et _ hseqt hA1 hBNEt hA3t hA4t (he ▸ hεt)
  · intro he
    exact hApprox n V Et _ ε hseqt hA1 hBNEt hA3t hA4t hεt he

#print axioms solution
