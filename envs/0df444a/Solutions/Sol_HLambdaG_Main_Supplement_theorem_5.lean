-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:18.329269+00:00
-- url     : https://prove2.me/submissions/ac0dad89-5840-4c43-add2-c29caeb3f516

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_LittleLaw

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 5, p. 641: in the `L = λW` framework of §1.2, if `t⁻¹S₁(t) → λ ∈ (0, ∞)` and
`H(t) → L`, then (a) `lim inf n⁻¹ Σ_{k ≤ n} W_k ≥ λ⁻¹L`; (b) if moreover `Q(t_k) = 0` along an
increasing sequence `t_k → ∞`, the lim inf equals `λ⁻¹L`; (c) if moreover `n⁻¹W_n → 0`,
then `n⁻¹ Σ_{k ≤ n} W_k → λ⁻¹L`. -/
theorem solution (L : LWSetting) (lam Lval : ℝ) (hlam : 0 < lam)
    (hS₁ : Tendsto (fun t : ℝ≥0 => (inv L.toDiscrete.T1 t : ℝ) / (t : ℝ)) atTop (𝓝 lam))
    (hH : Tendsto (H L.toDiscrete.input) atTop (𝓝 Lval)) :
    ((lam⁻¹ * Lval : ℝ) : EReal) ≤ Filter.liminf (fun n : ℕ =>
        ((((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k : ℝ) : EReal)) atTop ∧
    (∀ t : ℕ → ℝ≥0, StrictMono t → Tendsto t atTop atTop → (∀ k, L.Q (t k) = 0) →
      Filter.liminf (fun n : ℕ =>
        ((((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k : ℝ) : EReal)) atTop =
          ((lam⁻¹ * Lval : ℝ) : EReal)) ∧
    (Tendsto (fun n : ℕ => L.W n / (n : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k) atTop
        (𝓝 (lam⁻¹ * Lval))) := by
          have hT1 : ∀ s, L.toDiscrete.T1.T s = L.T ⌊s⌋₊ := fun s => rfl
          have hinv : ∀ t : ℝ≥0, ∃ p : ℕ, inv L.toDiscrete.T1 t = p ∧ (∀ j < p, L.T j ≤ t) ∧
              (∀ j, p ≤ j → t < L.T j) := by
            intro t
            have hex : ∃ k, t < L.T k := (L.T_tendsto.eventually_gt_atTop t).exists
            classical
            refine ⟨Nat.find hex, ?_, fun j hj => not_lt.1 (Nat.find_min hex hj),
              fun j hj => lt_of_lt_of_le (Nat.find_spec hex) (L.T_mono hj)⟩
            have hmem : ((Nat.find hex : ℕ) : ℝ≥0) ∈ {s : ℝ≥0 | t < L.toDiscrete.T1.T s} := by
              show t < L.toDiscrete.T1.T _
              rw [hT1, Nat.floor_natCast]; exact Nat.find_spec hex
            apply le_antisymm
            · exact csInf_le (OrderBot.bddBelow _) hmem
            · apply le_csInf ⟨_, hmem⟩
              intro s hs
              have hs' : t < L.T ⌊s⌋₊ := by rw [← hT1]; exact hs
              have : Nat.find hex ≤ ⌊s⌋₊ := Nat.find_min' hex hs'
              exact le_trans (by exact_mod_cast this) (Nat.floor_le s.2)
          have hFz : ∀ k t, t ≤ L.T k → L.F k t = 0 := fun k t h => L.F_eq_zero_of_le k t h
          have hsum : ∀ (t : ℝ≥0) (m : ℕ), (∀ j, m < j → t ≤ L.T j) →
              FInfT L.toDiscrete.input t = ∑ k ∈ Finset.Icc 1 m, L.F k t := by
            intro t m hm
            have key : ∀ a : ℕ, ∑ k ∈ Finset.Icc 1 a, L.F k t ≤ ∑ k ∈ Finset.Icc 1 m, L.F k t := by
              intro a
              calc ∑ k ∈ Finset.Icc 1 a, L.F k t ≤ ∑ k ∈ Finset.Icc 1 (max a m), L.F k t :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.Icc_subset_Icc le_rfl (le_max_left _ _)) (fun k _ _ => L.F_nonneg k t)
                _ = ∑ k ∈ Finset.Icc 1 m, L.F k t := by
                    symm
                    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (le_max_right _ _))
                    intro k hk hk'
                    apply hFz
                    apply hm
                    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
                    exact hk' hk.1
            apply le_antisymm
            · apply ciSup_le
              intro s
              exact key _
            · calc ∑ k ∈ Finset.Icc 1 m, L.F k t = L.toDiscrete.input.F (m : ℝ≥0) t := by
                    show _ = ∑ k ∈ Finset.Icc 1 ⌊(m:ℝ≥0)⌋₊, L.F k t
                    rw [Nat.floor_natCast]
                _ ≤ _ := le_ciSup (L.toDiscrete.input.bdd_s t) (m : ℝ≥0)
          have hsum_le : ∀ (t : ℝ≥0) (m : ℕ), ∑ k ∈ Finset.Icc 1 m, L.F k t ≤ FInfT L.toDiscrete.input t := by
            intro t m
            calc ∑ k ∈ Finset.Icc 1 m, L.F k t = L.toDiscrete.input.F (m : ℝ≥0) t := by
                  show _ = ∑ k ∈ Finset.Icc 1 ⌊(m:ℝ≥0)⌋₊, L.F k t
                  rw [Nat.floor_natCast]
              _ ≤ _ := le_ciSup (L.toDiscrete.input.bdd_s t) (m : ℝ≥0)
          have hW0 : ∀ k, 0 ≤ L.W k := by
            intro k
            unfold LWSetting.W
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp [L.T_zero]
            · have := L.T_le_D k hk
              have : (L.T k : ℝ) ≤ L.D k := by exact_mod_cast this
              linarith
          have hFW : ∀ k t, 1 ≤ k → L.F k t ≤ L.W k := by
            intro k t hk
            unfold LWSetting.F LWSetting.W
            rw [if_neg (by omega)]
            exact max_le (by have := hW0 k; unfold LWSetting.W at this; linarith)
              (by linarith [min_le_right (t : ℝ) (L.D k)])
          have hFeqW : ∀ k t, 1 ≤ k → L.D k ≤ t → L.F k t = L.W k := by
            intro k t hk hD
            unfold LWSetting.F LWSetting.W
            rw [if_neg (by omega)]
            have : (L.D k : ℝ) ≤ t := by exact_mod_cast hD
            rw [min_eq_right this]
            have := hW0 k; unfold LWSetting.W at this
            exact max_eq_right this
          have hHt : ∀ t : ℝ≥0, t ≠ 0 → FInfT L.toDiscrete.input t = (t : ℝ) * H L.toDiscrete.input t := by
            intro t ht
            have : (t : ℝ) ≠ 0 := by exact_mod_cast ht
            simp only [H]; field_simp
          set I : ℝ≥0 → ℝ := fun t => (inv L.toDiscrete.T1 t : ℝ) with hI
          have hIge : ∀ t : ℝ≥0, 1 ≤ I t := by
            intro t
            obtain ⟨p, hp, h1, h2⟩ := hinv t
            simp only [hI, hp, NNReal.coe_natCast]
            rcases Nat.eq_zero_or_pos p with h0 | h0
            · have := h2 0 (by omega); rw [L.T_zero] at this; exact absurd this (not_lt.2 t.2)
            · exact_mod_cast h0
          have hIn : ∀ n : ℕ, (n : ℝ) + 1 ≤ I (L.T n) := by
            intro n
            obtain ⟨p, hp, h1, h2⟩ := hinv (L.T n)
            simp only [hI, hp, NNReal.coe_natCast]
            have : n < p := by
              by_contra hc
              exact lt_irrefl _ (h2 n (not_lt.1 hc))
            exact_mod_cast this
          have hIlt : ∀ (n : ℕ) (t : ℝ≥0), t < L.T n → I t ≤ n := by
            intro n t ht
            obtain ⟨p, hp, h1, h2⟩ := hinv t
            simp only [hI, hp, NNReal.coe_natCast]
            have : p ≤ n := by
              by_contra hc
              exact absurd (h1 n (not_le.1 hc)) (not_le.2 ht)
            exact_mod_cast this
          have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
          have hφ : Tendsto (fun t : ℝ≥0 => (t : ℝ) / I t) atTop (𝓝 lam⁻¹) := by
            have := hS₁.inv₀ hlam.ne'
            refine this.congr (fun t => ?_)
            simp only [hI, inv_div]
          have hψ : Tendsto (fun t : ℝ≥0 => 1 / I t) atTop (𝓝 0) := by
            have h := (tendsto_inv_atTop_zero.comp hcoe).mul hφ
            rw [zero_mul] at h
            refine h.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
            have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
            have := hIge t
            simp only [Function.comp]
            field_simp
          have hTr : Tendsto (fun n => (L.T n : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 L.T_tendsto
          have hsub : Tendsto (fun n => L.T n - 1) atTop atTop := by
            rw [tendsto_atTop_atTop]
            intro b
            obtain ⟨N, hN⟩ := (L.T_tendsto.eventually_ge_atTop (b + 1)).exists_forall_of_atTop
            exact ⟨N, fun n hn => le_tsub_of_add_le_right (hN n hn)⟩
          have hTn : Tendsto (fun n : ℕ => (L.T n : ℝ) / n) atTop (𝓝 lam⁻¹) := by
            have hlow := hφ.comp L.T_tendsto
            have hup := (hφ.add hψ).comp hsub
            rw [add_zero] at hup
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
            · filter_upwards [eventually_ge_atTop 1] with n hn
              simp only [Function.comp]
              have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
              exact div_le_div_of_nonneg_left (L.T n).2 (by linarith) (by linarith [hIn n])
            · filter_upwards [L.T_tendsto.eventually_ge_atTop 1] with n hn
              simp only [Function.comp]
              have e : ((L.T n - 1 : ℝ≥0) : ℝ) + 1 = L.T n := by
                rw [NNReal.coe_sub hn]; simp
              rw [← add_div, e]
              have hlt : L.T n - 1 < L.T n := tsub_lt_self (lt_of_lt_of_le one_pos hn) one_pos
              have := hIlt n _ hlt
              have := hIge (L.T n - 1)
              exact div_le_div_of_nonneg_left (L.T n).2 (by linarith) (by linarith)
          set avg : ℕ → ℝ := fun n => ((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k with havg
          have ha : Tendsto (fun n => (L.T n : ℝ) / n * H L.toDiscrete.input (L.T n)) atTop
              (𝓝 (lam⁻¹ * Lval)) := hTn.mul (hH.comp L.T_tendsto)
          have hlow : ∀ᶠ n in atTop, (L.T n : ℝ) / n * H L.toDiscrete.input (L.T n) ≤ avg n := by
            filter_upwards [L.T_tendsto.eventually_gt_atTop 0] with n hn
            have e := hHt (L.T n) hn.ne'
            have e2 := hsum (L.T n) n (fun j hj => L.T_mono hj.le)
            have h3 : (L.T n : ℝ) / n * H L.toDiscrete.input (L.T n)
                = ((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.F k (L.T n) := by
              rw [← e2, e]; ring
            rw [h3, havg]
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg n))
            exact Finset.sum_le_sum (fun k hk => hFW k _ (Finset.mem_Icc.1 hk).1)
          have hA : ((lam⁻¹ * Lval : ℝ) : EReal) ≤
              Filter.liminf (fun n : ℕ => ((avg n : ℝ) : EReal)) atTop := by
            calc ((lam⁻¹ * Lval : ℝ) : EReal)
                = Filter.liminf (fun n => (((L.T n : ℝ) / n * H L.toDiscrete.input (L.T n) : ℝ) : EReal))
                    atTop := ((EReal.tendsto_coe.2 ha).liminf_eq).symm
              _ ≤ _ := liminf_le_liminf (hlow.mono fun n h => EReal.coe_le_coe_iff.2 h)
          refine ⟨hA, ?_, ?_⟩
          · intro t _ ht hQ
            apply le_antisymm _ hA
            choose p hp h1 h2 using fun k => hinv (t k)
            have hp1 : ∀ k, 1 ≤ p k := by
              intro k
              have := hIge (t k)
              simp only [hI, hp k, NNReal.coe_natCast] at this
              exact_mod_cast this
            set m : ℕ → ℕ := fun k => p k - 1 with hm
            have hmr : ∀ k, (m k : ℝ) = I (t k) - 1 := by
              intro k
              simp only [hm, hI, hp k, NNReal.coe_natCast]
              rw [Nat.cast_sub (hp1 k)]; simp
            have hmt : Tendsto (fun k => (m k : ℝ) / t k) atTop (𝓝 lam) := by
              have h := (hS₁.comp ht).sub (tendsto_inv_atTop_zero.comp (hcoe.comp ht))
              rw [sub_zero] at h
              refine h.congr (fun k => ?_)
              simp only [Function.comp]
              rw [hmr k, sub_div, one_div]
            have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop := by
              have h := hmt.pos_mul_atTop hlam (hcoe.comp ht)
              refine h.congr' ?_
              filter_upwards [ht.eventually_gt_atTop 0] with k hk
              have : (t k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
              simp only [Function.comp]
              field_simp
            have hmT : Tendsto m atTop atTop := tendsto_natCast_atTop_iff.1 hmR
            have hval : ∀ k, avg (m k) = ((m k : ℝ))⁻¹ * FInfT L.toDiscrete.input (t k) := by
              intro k
              have hempty : {j : ℕ | 1 ≤ j ∧ L.T j ≤ t k ∧ t k ≤ L.D j} = ∅ := by
                have hfin : {j : ℕ | 1 ≤ j ∧ L.T j ≤ t k ∧ t k ≤ L.D j}.Finite := by
                  apply (Finset.range (p k)).finite_toSet.subset
                  intro j hj
                  simp only [Set.mem_ofPred_eq] at hj
                  simp only [Finset.coe_range, Set.mem_Iio]
                  by_contra hc
                  exact absurd hj.2.1 (not_le.2 (h2 k j (not_lt.1 hc)))
                have := hQ k
                unfold LWSetting.Q at this
                exact (Set.ncard_eq_zero hfin).1 this
              simp only [havg]
              rw [hsum (t k) (m k) (fun j hj => (h2 k j (by simp only [hm] at hj; omega)).le)]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
              have hTj : L.T j ≤ t k := h1 k j (by simp only [hm] at hj2; omega)
              have hD : L.D j ≤ t k := by
                by_contra hc
                have : j ∈ {j : ℕ | 1 ≤ j ∧ L.T j ≤ t k ∧ t k ≤ L.D j} := ⟨hj1, hTj, (not_le.1 hc).le⟩
                rw [hempty] at this
                exact this
              exact (hFeqW j (t k) hj1 hD).symm
            have hcomp : Tendsto (fun k => avg (m k)) atTop (𝓝 (lam⁻¹ * Lval)) := by
              have h := (hmt.inv₀ hlam.ne').mul (hH.comp ht)
              refine h.congr' ?_
              filter_upwards [ht.eventually_gt_atTop 0] with k hk
              rw [hval k, hHt (t k) hk.ne']
              have : (t k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
              simp only [Function.comp]
              rw [inv_div]
              ring
            have hcompE : Tendsto (fun k => ((avg (m k) : ℝ) : EReal)) atTop
                (𝓝 ((lam⁻¹ * Lval : ℝ) : EReal)) := EReal.tendsto_coe.2 hcomp
            apply le_of_forall_gt_imp_ge_of_dense
            intro c hc
            have hev : ∀ᶠ k in atTop, ((avg (m k) : ℝ) : EReal) < c := hcompE.eventually (gt_mem_nhds hc)
            have hfr : ∃ᶠ n in atTop, ((avg n : ℝ) : EReal) ≤ c :=
              hmT.frequently ((hev.mono fun _ h => h.le).frequently)
            exact liminf_le_of_frequently_le' hfr
          · intro hWn
            set U : ℕ → ℝ := fun n => (Finset.range (n+1)).sup' Finset.nonempty_range_add_one L.W with hU
            have hWU : ∀ k n, k ≤ n → L.W k ≤ U n := fun k n hk =>
              Finset.le_sup' L.W (Finset.mem_range.2 (by omega))
            have hU0 : ∀ n, 0 ≤ U n := fun n => le_trans (hW0 0) (hWU 0 n (Nat.zero_le _))
            have hUn : Tendsto (fun n : ℕ => U n / n) atTop (𝓝 0) := by
              rw [Metric.tendsto_atTop]
              intro ε hε
              obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hWn (ε/2) (by linarith)
              set N := max N0 1 with hN
              set M := ∑ k ∈ Finset.range N, L.W k with hM
              have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => hW0 k)
              have hbound : ∀ n, N ≤ n → U n ≤ M + ε/2 * n := by
                intro n hn
                apply Finset.sup'_le
                intro k hk
                have hkn : k ≤ n := by have := Finset.mem_range.1 hk; omega
                rcases lt_or_ge k N with hkN | hkN
                · have : L.W k ≤ M := Finset.single_le_sum (fun j _ => hW0 j) (Finset.mem_range.2 hkN)
                  have : (0:ℝ) ≤ ε/2 * n := by positivity
                  linarith
                · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (le_trans (le_max_right _ _) hkN)
                  have h := hN0 k (le_trans (le_max_left _ _) hkN)
                  rw [Real.dist_eq, sub_zero, abs_lt, lt_div_iff₀ (by linarith), div_lt_iff₀ (by linarith)] at h
                  have : (k:ℝ) ≤ n := by exact_mod_cast hkn
                  nlinarith [h.2]
              obtain ⟨N2, hN2⟩ := exists_nat_gt (2 * M / ε)
              refine ⟨max N N2 + 1, fun n hn => ?_⟩
              have hnN : N ≤ n := by omega
              have hn2 : (N2 : ℝ) < n := by exact_mod_cast (show N2 < n by omega)
              have hnpos : (0:ℝ) < n := by linarith [(Nat.cast_nonneg N2 : (0:ℝ) ≤ N2)]
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hU0 n) hnpos.le), div_lt_iff₀ hnpos]
              have := hbound n hnN
              have h2M : 2 * M < ε * n := by
                rw [div_lt_iff₀ hε] at hN2; nlinarith
              nlinarith
            set s : ℕ → ℝ≥0 := fun n => ⟨(L.T n : ℝ) + U n, by have := hU0 n; positivity⟩ with hs
            have hsr : ∀ n, (s n : ℝ) = L.T n + U n := fun n => rfl
            have hsT : ∀ n, L.T n ≤ s n := by
              intro n; rw [← NNReal.coe_le_coe, hsr]; linarith [hU0 n]
            have hstend : Tendsto s atTop atTop := tendsto_atTop_mono hsT L.T_tendsto
            have hb : Tendsto (fun n => (s n : ℝ) / n * H L.toDiscrete.input (s n)) atTop
                (𝓝 (lam⁻¹ * Lval)) := by
              have h1 : Tendsto (fun n : ℕ => (s n : ℝ) / n) atTop (𝓝 lam⁻¹) := by
                have := hTn.add hUn
                rw [add_zero] at this
                refine this.congr (fun n => ?_)
                rw [hsr, add_div]
              exact h1.mul (hH.comp hstend)
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ha hb hlow ?_
            filter_upwards [L.T_tendsto.eventually_gt_atTop 0] with n hn
            have hsn : s n ≠ 0 := (lt_of_lt_of_le hn (hsT n)).ne'
            have e : (s n : ℝ) / n * H L.toDiscrete.input (s n)
                = ((n : ℝ))⁻¹ * FInfT L.toDiscrete.input (s n) := by
              rw [hHt (s n) hsn]; ring
            rw [e]
            simp only [havg]
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg n))
            refine le_trans (le_of_eq ?_) (hsum_le (s n) n)
            apply Finset.sum_congr rfl
            intro k hk
            obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
            symm
            apply hFeqW k (s n) hk1
            rw [← NNReal.coe_le_coe, hsr]
            have h1 := hWU k n hk2
            have h2 : (L.T k : ℝ) ≤ L.T n := by exact_mod_cast L.T_mono hk2
            unfold LWSetting.W at h1
            linarith
