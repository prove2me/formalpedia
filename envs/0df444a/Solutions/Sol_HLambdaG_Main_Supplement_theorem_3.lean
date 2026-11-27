-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:50.676185+00:00
-- url     : https://prove2.me/submissions/dc6d4db0-05c2-477c-86a2-ec769c4f5459

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 3, p. 640: in the setting of §1.1, (18) implies (15) for the time change
`T₂(s) = T_{[s]} + U_{[s]}` of (19), and `lim s⁻¹T₂(s) = lim n⁻¹T_n` whenever the latter
limit exists (finite or `+∞`). -/
theorem solution (D : DiscreteSetting) (S : ℕ → ℝ≥0) (h18 : D.Cond18 S) :
    Cond15 D.input (D.T2 S) ∧
      (∀ c : ℝ, Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 c) →
        Tendsto (fun s : ℝ≥0 => ((D.T2 S).T s : ℝ) / (s : ℝ)) atTop (𝓝 c)) ∧
      (Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop atTop →
        Tendsto (fun s : ℝ≥0 => ((D.T2 S).T s : ℝ) / (s : ℝ)) atTop atTop) := by
          have hT2 : ∀ s, (D.T2 S).T s = D.T ⌊s⌋₊ + U S ⌊s⌋₊ := fun s => rfl
          have hfl : Tendsto (fun s : ℝ≥0 => (⌊s⌋₊ : ℝ) / (s : ℝ)) atTop (𝓝 1) := by
            have := (tendsto_nat_floor_div_atTop (R := ℝ)).comp
              (NNReal.tendsto_coe_atTop.2 (tendsto_id (x := (atTop : Filter ℝ≥0))))
            refine this.congr (fun s => ?_)
            simp only [Function.comp_apply, id]
            rfl
          have hfloorTop : Tendsto (fun s : ℝ≥0 => ⌊s⌋₊) atTop atTop := tendsto_nat_floor_atTop
          have hs1 : ∀ᶠ s : ℝ≥0 in atTop, 1 ≤ ⌊s⌋₊ := hfloorTop.eventually_ge_atTop 1
          have hnle : ∀ s : ℝ≥0, (⌊s⌋₊ : ℝ) ≤ (s : ℝ) := fun s => by
            have := Nat.floor_le s.2
            exact_mod_cast this
          -- U_n / T_n → 0
          have hUT : Tendsto (fun n : ℕ => (U S n : ℝ) / (D.T n : ℝ)) atTop (𝓝 0) := by
            rw [Metric.tendsto_atTop]
            intro ε hε
            have hA := (Metric.tendsto_atTop.1 h18.1) (ε / 2) (by positivity)
            obtain ⟨N₁, hN₁⟩ := hA
            obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 (D.T_tendsto.eventually_ge_atTop 1))
            set N := max N₁ N₂
            have hTr : Tendsto (fun n => (D.T n : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 D.T_tendsto
            obtain ⟨M, hM⟩ := eventually_atTop.1 (hTr.eventually_ge_atTop (2 * (U S N : ℝ) / ε))
            refine ⟨max N M, fun n hn => ?_⟩
            have hnN : N ≤ n := le_trans (le_max_left _ _) hn
            have hnM : M ≤ n := le_trans (le_max_right _ _) hn
            have hTn1 : (1 : ℝ≥0) ≤ D.T n := hN₂ n (le_trans (le_max_right _ _) hnN)
            have hTnpos : (0 : ℝ) < D.T n := by
              have : (1:ℝ) ≤ D.T n := by exact_mod_cast hTn1
              linarith
            have hUN : (U S N : ℝ) ≤ ε / 2 * D.T n := by
              have h1 := hM n hnM
              rw [div_le_iff₀ hε] at h1
              linarith
            have hUn : (U S n : ℝ) ≤ ε / 2 * D.T n := by
              have key : ∀ k ∈ Finset.Icc 1 n, (S k : ℝ) ≤ ε / 2 * D.T n := by
                intro k hk
                rcases le_or_gt k N with hkN | hkN
                · have : S k ≤ U S N := Finset.le_sup (f := S) (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hk).1, hkN⟩)
                  have : (S k : ℝ) ≤ U S N := by exact_mod_cast this
                  linarith
                · have hk1 : N₁ ≤ k := le_trans (le_max_left _ _) hkN.le
                  have hk2 : N₂ ≤ k := le_trans (le_max_right _ _) hkN.le
                  have hTk1 : (1 : ℝ≥0) ≤ D.T k := hN₂ k hk2
                  have hTkpos : (0 : ℝ) < D.T k := by
                    have : (1:ℝ) ≤ D.T k := by exact_mod_cast hTk1
                    linarith
                  have h1 := hN₁ k hk1
                  rw [Real.dist_eq, sub_zero] at h1
                  have h2 : (S k : ℝ) / D.T k < ε / 2 := lt_of_le_of_lt (le_abs_self _) h1
                  rw [div_lt_iff₀ hTkpos] at h2
                  have hTkn : (D.T k : ℝ) ≤ D.T n := by
                    have := D.T_mono (Finset.mem_Icc.1 hk).2
                    exact_mod_cast this
                  nlinarith
              have hsup : U S n ≤ (ε / 2 * D.T n).toNNReal := by
                apply Finset.sup_le
                intro k hk
                rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
                exact key k hk
              have := (NNReal.coe_le_coe.2 hsup)
              rwa [Real.coe_toNNReal _ (by positivity)] at this
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hTnpos]
            nlinarith
          have hTpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < D.T n := by
            filter_upwards [D.T_tendsto.eventually_ge_atTop 1] with n hn
            have : (1:ℝ) ≤ D.T n := by exact_mod_cast hn
            linarith
          have hrewrite : ∀ (a : ℕ → ℝ), (∀ n, a n = ((D.T n + U S n : ℝ≥0) : ℝ) / (n : ℝ)) →
              ∀ᶠ s : ℝ≥0 in atTop, a ⌊s⌋₊ * ((⌊s⌋₊ : ℝ) / (s : ℝ)) = ((D.T2 S).T s : ℝ) / (s : ℝ) := by
            intro a ha
            filter_upwards [hs1] with s hs
            rw [ha, hT2]
            have hn : (0:ℝ) < (⌊s⌋₊ : ℝ) := by exact_mod_cast hs
            have hs' : (0:ℝ) < (s : ℝ) := lt_of_lt_of_le hn (hnle s)
            field_simp
          refine ⟨?_, ?_, ?_⟩
          · -- Cond15
            set A : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 n, (D.Finf k - D.F k (D.T k + S k)) with hA
            have hAnn : ∀ n, 0 ≤ A n := fun n => Finset.sum_nonneg (fun k _ => by
              have := le_ciSup (D.F_bdd k) (D.T k + S k)
              simp only [DiscreteSetting.Finf]; linarith)
            have hup : Tendsto (fun s : ℝ≥0 => ((⌊s⌋₊ : ℕ) : ℝ)⁻¹ * A ⌊s⌋₊) atTop (𝓝 0) :=
              h18.2.comp hfloorTop
            unfold Cond15
            apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
            · filter_upwards with s
              apply mul_nonneg (inv_nonneg.2 (NNReal.coe_nonneg s))
              have := le_ciSup (D.input.bdd_t s) ((D.T2 S).T s)
              unfold FsInf
              linarith
            · filter_upwards [hs1] with s hs
              have hn : (0:ℝ) < (⌊s⌋₊ : ℝ) := by exact_mod_cast hs
              have hinv : (s : ℝ)⁻¹ ≤ ((⌊s⌋₊ : ℕ) : ℝ)⁻¹ := inv_anti₀ hn (hnle s)
              have hX0 : 0 ≤ FsInf D.input s - D.input.F s ((D.T2 S).T s) := by
                have := le_ciSup (D.input.bdd_t s) ((D.T2 S).T s)
                unfold FsInf
                linarith
              have hXA : FsInf D.input s - D.input.F s ((D.T2 S).T s) ≤ A ⌊s⌋₊ := by
                have h1 : FsInf D.input s ≤ ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.Finf k := by
                  unfold FsInf
                  apply ciSup_le
                  intro t
                  show ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t ≤ _
                  exact Finset.sum_le_sum (fun k _ => le_ciSup (D.F_bdd k) t)
                have h2 : ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T k + S k) ≤ D.input.F s ((D.T2 S).T s) := by
                  show _ ≤ ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k ((D.T2 S).T s)
                  apply Finset.sum_le_sum
                  intro k hk
                  apply D.F_mono
                  rw [hT2]
                  exact add_le_add (D.T_mono (Finset.mem_Icc.1 hk).2) (Finset.le_sup (f := S) hk)
                have h3 : A ⌊s⌋₊ = ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.Finf k -
                    ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T k + S k) := by
                  rw [hA]; simp only; rw [Finset.sum_sub_distrib]
                linarith
              calc (s : ℝ)⁻¹ * (FsInf D.input s - D.input.F s ((D.T2 S).T s))
                  ≤ ((⌊s⌋₊ : ℕ) : ℝ)⁻¹ * (FsInf D.input s - D.input.F s ((D.T2 S).T s)) :=
                    mul_le_mul_of_nonneg_right hinv hX0
                _ ≤ ((⌊s⌋₊ : ℕ) : ℝ)⁻¹ * A ⌊s⌋₊ :=
                    mul_le_mul_of_nonneg_left hXA (inv_nonneg.2 hn.le)
          · intro c hc
            have ha : Tendsto (fun n : ℕ => ((D.T n + U S n : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 c) := by
              have := hc.add (hUT.mul hc)
              rw [zero_mul, add_zero] at this
              refine this.congr' ?_
              filter_upwards [hTpos] with n hn
              push_cast
              field_simp
            have := (ha.comp hfloorTop).mul hfl
            rw [mul_one] at this
            exact this.congr' (hrewrite _ (fun n => rfl))
          · intro hc
            have := (hc.comp hfloorTop).atTop_mul_pos one_pos hfl
            refine tendsto_atTop_mono' _ ?_ this
            filter_upwards [hrewrite _ (fun n => rfl)] with s hs
            rw [← hs]
            simp only [Function.comp_apply]
            apply mul_le_mul_of_nonneg_right _ (div_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg s))
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            push_cast
            linarith [NNReal.coe_nonneg (U S ⌊s⌋₊)]
