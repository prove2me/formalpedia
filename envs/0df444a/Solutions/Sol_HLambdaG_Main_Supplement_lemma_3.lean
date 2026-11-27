-- Prove2me | solution 1 for HLambdaG.Main.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:39.86245+00:00
-- url     : https://prove2.me/submissions/5e2fd4d5-c879-43b6-9562-3b2754994946

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Lemma 3, p. 640: for the epochs of §1.1 and a nonnegative finite sequence `S`,
`S_n / T_n → 0` implies `U_n / T_n → 0`, where `U_n = max {S_k : 1 ≤ k ≤ n}`. -/
theorem solution (T : ℕ → ℝ≥0) (hT0 : T 0 = 0) (hmono : Monotone T)
    (htend : Tendsto T atTop atTop) (S : ℕ → ℝ≥0)
    (hS : Tendsto (fun n : ℕ => (S n : ℝ) / (T n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (U S n : ℝ) / (T n : ℝ)) atTop (𝓝 0) := by
      have hTr : Tendsto (fun n => (T n : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 htend
      have hpos : ∀ᶠ n in atTop, (0 : ℝ) < T n := hTr.eventually_gt_atTop 0
      rw [tendsto_order]
      refine ⟨fun a ha => Eventually.of_forall (fun n => lt_of_lt_of_le ha (by positivity)), ?_⟩
      intro b hb
      have hε : (0 : ℝ) < b / 2 := by linarith
      have h1 : ∀ᶠ n in atTop, (S n : ℝ) / T n < b / 2 := (tendsto_order.1 hS).2 _ hε
      obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and hpos)
      have hSk : ∀ k, N ≤ k → (S k : ℝ) ≤ b / 2 * T k := by
        intro k hk
        obtain ⟨h1, h2⟩ := hN k hk
        rw [div_lt_iff₀ h2] at h1
        linarith
      have hU : ∀ n, N ≤ n → (U S n : ℝ) ≤ U S N + b / 2 * T n := by
        intro n hn
        have hB : U S n ≤ U S N + (b/2).toNNReal * T n := by
          apply Finset.sup_le
          intro k hk
          rcases le_or_gt k N with hkN | hkN
          · have : S k ≤ U S N := Finset.le_sup (f := S) (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hk).1, hkN⟩)
            exact le_trans this le_self_add
          · rw [← NNReal.coe_le_coe]
            push_cast
            rw [Real.coe_toNNReal _ hε.le]
            have := hSk k hkN.le
            have hTk : (T k : ℝ) ≤ T n := NNReal.coe_le_coe.2 (hmono (Finset.mem_Icc.1 hk).2)
            have : (0:ℝ) ≤ U S N := (U S N).2
            nlinarith
        have := NNReal.coe_le_coe.2 hB
        push_cast at this
        rwa [Real.coe_toNNReal _ hε.le] at this
      have h2 : Tendsto (fun n => (U S N : ℝ) / T n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hTr
      have h3 : ∀ᶠ n in atTop, (U S N : ℝ) / T n < b / 2 := (tendsto_order.1 h2).2 _ hε
      filter_upwards [h3, hpos, eventually_ge_atTop N] with n h3 hp hn
      have := hU n hn
      rw [div_lt_iff₀ hp] at h3 ⊢
      nlinarith
