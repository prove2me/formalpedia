-- Prove2me | solution 1 for MultiPriceOnline.Balance.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:30:55.454141+00:00
-- url     : https://prove2.me/submissions/41c7f902-ede7-4e8d-b8ec-88462795bc2f

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_LP
import Definitions.Def_MultiPriceOnline_Balance_Procedure
import Definitions.Def_MultiPriceOnline_Balance_Algorithm

open MultiPriceOnline.Balance Finset

private lemma r_pos_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [← h]; exact hr.1
    · have hk_pos : 0 < r k := ih (by omega) (by omega)
      have hlt : r k < r (k + 1) := hr.2 k (by omega) (by omega)
      linarith

private lemma valueFn_mono {k : ℕ} {φ : ℕ → ℝ} (hφ : IsValueFn k φ) :
    (∀ N, N ≤ k → 0 ≤ φ N) ∧ (∀ N₁ N₂, N₁ ≤ N₂ → N₂ ≤ k → φ N₁ ≤ φ N₂) := by
  have hmono : ∀ N₁ N₂, N₁ ≤ N₂ → N₂ ≤ k → φ N₁ ≤ φ N₂ := by
    intro N₁ N₂ h12 h2k
    induction N₂ with
    | zero =>
      have : N₁ = 0 := by omega
      subst this; exact le_rfl
    | succ n ih =>
      rcases eq_or_lt_of_le h12 with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega) (by omega)) (hφ.2 n (by omega))
  refine ⟨fun N hNk => ?_, hmono⟩
  rw [← hφ.1]
  exact hmono 0 N (Nat.zero_le N) hNk

private lemma cv_le_k {k m : ℕ} (c : Config k m) (j : ℕ) : cv c j ≤ k := by
  unfold cv
  split_ifs with h
  · exact Nat.le_of_lt_succ (c ⟨j, h⟩).isLt
  · exact le_rfl

private lemma runValue_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ι → ℕ)
    (r : ι → ℕ → ℝ) (hr : ∀ i, IsPriceSet (m i) (r i))
    (P : ∀ i, Procedure (k i) (m i)) (cfg : ∀ i, Config (k i) (m i))
    (sel : Selector m) {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1) :
    ∀ s t N, 0 ≤ runValue k m r P cfg sel p s t N := by
  intro s
  induction s with
  | zero => intro t N; simp [runValue]
  | succ s ih =>
    intro t N
    unfold runValue
    split_ifs with ht hsc
    · set a := sel t N (score k m P cfg (p ⟨t, ht⟩) N)
      have hj1 : 1 ≤ a.2.val + 1 := by omega
      have hjm : a.2.val + 1 ≤ m a.1 := Nat.succ_le_of_lt a.2.isLt
      have hp_bds := hp ⟨t, ht⟩ a.1 (a.2.val + 1) hj1 hjm
      have hr_pos := r_pos_of_priceSet (hr a.1) (a.2.val + 1) hj1 hjm
      have h1 := ih (t + 1) (Function.update N a.1 (N a.1 + 1))
      have h2 := ih (t + 1) N
      nlinarith
    · exact ih (t + 1) N
    · exact le_rfl

private lemma marginal_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ι → ℕ)
    (P : ∀ i, Procedure (k i) (m i)) (hP : ∀ i, IsProcedure (P i)) (i₀ : ι) (j : ℕ) :
    (∑ cfg : (∀ i, Config (k i) (m i)),
      (∏ i, (P i).ρ (cfg i)) * (P i₀).Φ (cfg i₀) (cv (cfg i₀) j)) =
      ∑ c₀ : Config (k i₀) (m i₀), (P i₀).ρ c₀ * (P i₀).Φ c₀ (cv c₀ j) := by
  let f : ∀ i, Config (k i) (m i) → ℝ := fun i c =>
    (P i).ρ c * if i = i₀ then (P i).Φ c (cv c j) else 1
  have hterm : ∀ cfg : (∀ i, Config (k i) (m i)),
      (∏ i, (P i).ρ (cfg i)) * (P i₀).Φ (cfg i₀) (cv (cfg i₀) j) = ∏ i, f i (cfg i) := by
    intro cfg
    dsimp [f]
    rw [prod_mul_distrib, prod_ite_eq' univ i₀ (fun i => (P i).Φ (cfg i) (cv (cfg i) j)),
        if_pos (mem_univ i₀)]
  rw [sum_congr rfl (fun cfg _ => hterm cfg), ← Fintype.prod_sum]
  have hfactor : ∀ i : ι,
      (∑ c : Config (k i) (m i), f i c) =
        if i = i₀ then ∑ c : Config (k i) (m i), (P i).ρ c * (P i).Φ c (cv c j) else 1 := by
    intro i
    dsimp [f]
    split_ifs with h
    · rfl
    · simp only [mul_one]
      exact (hP i).2.1
  rw [prod_congr rfl (fun i _ => hfactor i),
      prod_ite_eq' univ i₀ (fun i => ∑ c : Config (k i) (m i), (P i).ρ c * (P i).Φ c (cv c j)),
      if_pos (mem_univ i₀)]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ι → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hm : ∀ i, 1 ≤ m i) (r : ι → ℕ → ℝ) (hr : ∀ i, IsPriceSet (m i) (r i))
    (P : ∀ i, Procedure (k i) (m i)) (hP : ∀ i, IsProcedure (P i)) (c : ℝ)
    (h17 : ∀ i, Cond17 (r i) (P i) c) (h18 : ∀ i, Cond18 (r i) (P i))
    {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1)
    (sel : Selector m) (hsel : IsArgmaxSelector sel)
    (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x) :
    c * lpObj m r p x ≤ expRevenue k m r P sel p := by
  have hexp_nonneg : 0 ≤ expRevenue k m r P sel p := by
    unfold expRevenue
    apply sum_nonneg
    intro cfg _
    apply mul_nonneg
    · exact prod_nonneg (fun i _ => (hP i).1 (cfg i))
    · exact runValue_nonneg k m r hr P cfg sel p hp T 0 (fun _ => 0)
  have hlp_nonneg : 0 ≤ lpObj m r p x := by
    unfold lpObj
    apply sum_nonneg; intro t _
    apply sum_nonneg; intro i _
    apply sum_nonneg; intro j hj
    rw [mem_Icc] at hj
    have hp0 := (hp t i j hj.1 hj.2).1
    have hr0 := le_of_lt (r_pos_of_priceSet (hr i) j hj.1 hj.2)
    have hx0 := hx.2.2 t i j hj.1 hj.2
    exact mul_nonneg (mul_nonneg hp0 hr0) hx0
  rcases le_or_gt c 0 with hc | hc
  · have : c * lpObj m r p x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hlp_nonneg
    linarith
  -- Now 0 < c
  have h_cfg_bound : ∀ cfg : (∀ i, Config (k i) (m i)),
      (∀ i, (P i).ρ (cfg i) ≠ 0) →
      c * (∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
          p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j) ≤
        runValue k m r P cfg sel p T 0 (fun _ => 0) := by
    intro cfg hcfg
    have hcfg_prop : ∀ i, IsConfig (cfg i) ∧ IsValueFn (k i) ((P i).Φ (cfg i)) :=
      fun i => (hP i).2.2 (cfg i) (hcfg i)
    let remLP (t : ℕ) (i : ι) : ℝ :=
      ∑ τ ∈ univ.filter (fun τ : Fin T => t ≤ τ.val), ∑ j ∈ Icc 1 (m i), p τ i j * x τ i j
    let remObj (t : ℕ) : ℝ :=
      ∑ τ ∈ univ.filter (fun τ : Fin T => t ≤ τ.val),
        ∑ i : ι, ∑ j ∈ Icc 1 (m i), p τ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ i j
    let pot (t : ℕ) (N : ι → ℕ) : ℝ :=
      ∑ i : ι, ((k i : ℝ) - remLP 0 i + remLP t i) * (P i).Φ (cfg i) (N i)
    have hfilt0 : univ.filter (fun τ : Fin T => 0 ≤ τ.val) = univ := by
      ext τ; simp
    have hremLP0_le_k : ∀ i, remLP 0 i ≤ (k i : ℝ) := by
      intro i
      dsimp [remLP]
      rw [hfilt0]
      exact hx.1 i
    have hremLP_le0 : ∀ t i, remLP t i ≤ remLP 0 i := by
      intro t i
      dsimp [remLP]
      apply sum_le_sum_of_subset_of_nonneg
      · intro τ _
        simp only [mem_filter, mem_univ, true_and]
        exact Nat.zero_le τ.val
      · intro τ _ _
        apply sum_nonneg; intro j hj
        rw [mem_Icc] at hj
        exact mul_nonneg (hp τ i j hj.1 hj.2).1 (hx.2.2 τ i j hj.1 hj.2)
    have hind : ∀ s t (N : ι → ℕ), t + s = T → (∀ i, N i ≤ k i) →
        c * remObj t ≤ runValue k m r P cfg sel p s t N + c * pot t N := by
      intro s
      induction s with
      | zero =>
        intro t N ht hN
        have htT : t = T := by omega
        rw [htT]
        have hempty : univ.filter (fun τ : Fin T => T ≤ τ.val) = ∅ := by
          rw [filter_eq_empty_iff]
          intro τ _; exact not_le.mpr τ.isLt
        have hremObj0 : remObj T = 0 := by dsimp [remObj]; rw [hempty, sum_empty]
        have hpot_nonneg : 0 ≤ pot T N := by
          dsimp [pot]
          apply sum_nonneg; intro i _
          have hrem0 : remLP T i = 0 := by dsimp [remLP]; rw [hempty, sum_empty]
          rw [hrem0, add_zero]
          have hsub_nonneg : 0 ≤ (k i : ℝ) - remLP 0 i := sub_nonneg.mpr (hremLP0_le_k i)
          exact mul_nonneg hsub_nonneg
            ((valueFn_mono (hcfg_prop i).2).1 (N i) (hN i))
        rw [hremObj0, mul_zero]
        dsimp [runValue]
        nlinarith
      | succ s ih =>
        intro t N ht hN
        have ht_lt : t < T := by omega
        let τ₀ : Fin T := ⟨t, ht_lt⟩
        have hfilt : univ.filter (fun τ : Fin T => t ≤ τ.val) =
            insert τ₀ (univ.filter (fun τ : Fin T => t + 1 ≤ τ.val)) := by
          ext τ
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          change t ≤ τ.val ↔ τ.val = t ∨ t + 1 ≤ τ.val
          omega
        have hnotmem : τ₀ ∉ univ.filter (fun τ : Fin T => t + 1 ≤ τ.val) := by
          simp only [mem_filter, mem_univ, true_and]
          change ¬ (t + 1 ≤ t)
          omega
        have hremObj_step : remObj t =
            (∑ i : ι, ∑ j ∈ Icc 1 (m i), p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j) +
              remObj (t + 1) := by
          dsimp [remObj]
          rw [hfilt, sum_insert hnotmem]
        have hremLP_step : ∀ i, remLP t i =
            (∑ j ∈ Icc 1 (m i), p τ₀ i j * x τ₀ i j) + remLP (t + 1) i := by
          intro i
          dsimp [remLP]
          rw [hfilt, sum_insert hnotmem]
        have hpot_diff : pot t N - pot (t + 1) N =
            ∑ i : ι, ∑ j ∈ Icc 1 (m i), p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j := by
          dsimp [pot]
          rw [← sum_sub_distrib]
          apply sum_congr rfl
          intro i _
          rw [hremLP_step i]
          have : (((k i : ℝ) - remLP 0 i + ((∑ j ∈ Icc 1 (m i), p τ₀ i j * x τ₀ i j) + remLP (t + 1) i)) *
              (P i).Φ (cfg i) (N i) -
              ((k i : ℝ) - remLP 0 i + remLP (t + 1) i) *
                (P i).Φ (cfg i) (N i)) =
              (∑ j ∈ Icc 1 (m i), p τ₀ i j * x τ₀ i j) * (P i).Φ (cfg i) (N i) := by ring
          rw [this, sum_mul]
          apply sum_congr rfl
          intro j _
          ring
        set a := sel t N (score k m P cfg (p τ₀) N)
        have hscore_le : ∀ i : ι, ∀ j ∈ Icc 1 (m i),
            p τ₀ i j * ((P i).Φ (cfg i) (cv (cfg i) j) - (P i).Φ (cfg i) (N i)) ≤
              score k m P cfg (p τ₀) N a := by
          intro i j hj
          rw [mem_Icc] at hj
          let a_ij : Cand m := ⟨i, ⟨j - 1, by omega⟩⟩
          have h := hsel t N (score k m P cfg (p τ₀) N) a_ij
          dsimp [score, a_ij] at h
          have hj_eq : j - 1 + 1 = j := by omega
          rw [hj_eq, min_eq_left (hN i)] at h
          exact h
        unfold runValue
        rw [dif_pos ht_lt]
        split_ifs with hsc
        · -- Branch: 0 < score a
          have h_sum_score : (∑ i : ι, ∑ j ∈ Icc 1 (m i),
              (p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j -
                p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j)) ≤ score k m P cfg (p τ₀) N a := by
            calc
              (∑ i : ι, ∑ j ∈ Icc 1 (m i),
                  (p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j -
                    p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j))
                = ∑ i : ι, ∑ j ∈ Icc 1 (m i),
                    p τ₀ i j * ((P i).Φ (cfg i) (cv (cfg i) j) - (P i).Φ (cfg i) (N i)) * x τ₀ i j := by
                  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
              _ ≤ ∑ i : ι, ∑ j ∈ Icc 1 (m i), score k m P cfg (p τ₀) N a * x τ₀ i j := by
                  apply sum_le_sum; intro i _; apply sum_le_sum; intro j hj
                  have hxj := hx.2.2 τ₀ i j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
                  exact mul_le_mul_of_nonneg_right (hscore_le i j hj) hxj
              _ = score k m P cfg (p τ₀) N a * (∑ i : ι, ∑ j ∈ Icc 1 (m i), x τ₀ i j) := by
                  simp only [← mul_sum]
              _ ≤ score k m P cfg (p τ₀) N a * 1 :=
                  mul_le_mul_of_nonneg_left (hx.2.1 τ₀) (le_of_lt hsc)
              _ = score k m P cfg (p τ₀) N a := mul_one _
          let i_star := a.1
          let j_star := a.2.val + 1
          have hj_star1 : 1 ≤ j_star := by omega
          have hj_starm : j_star ≤ m i_star := Nat.succ_le_of_lt a.2.isLt
          have hp_star := hp τ₀ i_star j_star hj_star1 hj_starm
          have hN_lt_cv : N i_star < cv (cfg i_star) j_star := by
            by_contra hge
            push_neg at hge
            have hle_phi : (P i_star).Φ (cfg i_star) (cv (cfg i_star) j_star) ≤
                (P i_star).Φ (cfg i_star) (N i_star) :=
              (valueFn_mono (hcfg_prop i_star).2).2 _ _ hge (hN i_star)
            have hsc_le0 : score k m P cfg (p τ₀) N a ≤ 0 := by
              dsimp [score]
              rw [min_eq_left (hN i_star)]
              exact mul_nonpos_of_nonneg_of_nonpos hp_star.1 (by linarith)
            linarith
          have hN_lt_k : N i_star < k i_star :=
            lt_of_lt_of_le hN_lt_cv (cv_le_k (cfg i_star) j_star)
          let N' := Function.update N i_star (N i_star + 1)
          have hN' : ∀ i, N' i ≤ k i := by
            intro i
            dsimp [N']
            by_cases hi : i = i_star
            · subst hi; rw [Function.update_self]; omega
            · rw [Function.update_of_ne hi]; exact hN i
          have ih1 := ih (t + 1) N' (by omega) hN'
          have ih2 := ih (t + 1) N (by omega) hN
          have hpot_N' : pot (t + 1) N' - pot (t + 1) N ≤
              (k i_star : ℝ) * ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star)) := by
            have heq : pot (t + 1) N' - pot (t + 1) N =
                ((k i_star : ℝ) - remLP 0 i_star + remLP (t + 1) i_star) *
                  ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star)) := by
              dsimp [pot, N']
              rw [← sum_sub_distrib]
              have hterm : ∀ i : ι,
                  ((k i : ℝ) - remLP 0 i + remLP (t + 1) i) * (P i).Φ (cfg i) (Function.update N i_star (N i_star + 1) i) -
                    ((k i : ℝ) - remLP 0 i + remLP (t + 1) i) * (P i).Φ (cfg i) (N i) =
                  if i = i_star then
                    ((k i_star : ℝ) - remLP 0 i_star + remLP (t + 1) i_star) *
                      ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star))
                  else 0 := by
                intro i
                by_cases hi : i = i_star
                · subst hi; rw [Function.update_self, if_pos rfl]; ring
                · rw [Function.update_of_ne hi, if_neg hi]; ring
              rw [sum_congr rfl (fun i _ => hterm i), sum_ite_eq' univ i_star _, if_pos (mem_univ _)]
            rw [heq]
            have hphi_diff_nonneg : 0 ≤ (P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star) := by
              have := (hcfg_prop i_star).2.2 (N i_star) hN_lt_k
              linarith
            have hrem_le0 := hremLP_le0 (t + 1) i_star
            nlinarith
          have h17_inst := h17 i_star (cfg i_star) (hcfg i_star) j_star hj_star1 hj_starm (N i_star) hN_lt_cv
          have h17_mul : c * ((k i_star : ℝ) * ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star)) +
              (P i_star).Φ (cfg i_star) (cv (cfg i_star) j_star) - (P i_star).Φ (cfg i_star) (N i_star)) ≤ r i_star j_star := by
            have := mul_le_mul_of_nonneg_left h17_inst (le_of_lt hc)
            rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at this
          have hsc_def : score k m P cfg (p τ₀) N a =
              p τ₀ i_star j_star * ((P i_star).Φ (cfg i_star) (cv (cfg i_star) j_star) - (P i_star).Φ (cfg i_star) (N i_star)) := by
            dsimp [score, i_star, j_star]
            rw [min_eq_left (hN a.1)]
          have h_sum_diff : (∑ i : ι, ∑ j ∈ Icc 1 (m i),
              (p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j -
                p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j)) =
              (remObj t - remObj (t + 1)) - (pot t N - pot (t + 1) N) := by
            simp only [sum_sub_distrib]
            rw [hremObj_step, hpot_diff]
            ring
          rw [h_sum_diff] at h_sum_score
          have hp0 := hp_star.1
          have hp1 : 0 ≤ 1 - p τ₀ i_star j_star := by linarith [hp_star.2]
          change c * remObj t ≤
            (p τ₀ i_star j_star * (r i_star j_star + runValue k m r P cfg sel p s (t + 1) N') +
              (1 - p τ₀ i_star j_star) * runValue k m r P cfg sel p s (t + 1) N) + c * pot t N
          have h_c_score := mul_le_mul_of_nonneg_left h_sum_score (le_of_lt hc)
          rw [hsc_def] at h_c_score
          have h_cp_pot := mul_le_mul_of_nonneg_left hpot_N' (mul_nonneg (le_of_lt hc) hp0)
          have h_p_17 := mul_le_mul_of_nonneg_left h17_mul hp0
          have h_p_ih1 := mul_le_mul_of_nonneg_left ih1 hp0
          have h_p1_ih2 := mul_le_mul_of_nonneg_left ih2 hp1
          have h_id : ((p τ₀ i_star j_star * (r i_star j_star + runValue k m r P cfg sel p s (t + 1) N') +
              (1 - p τ₀ i_star j_star) * runValue k m r P cfg sel p s (t + 1) N) + c * pot t N) - c * remObj t =
            (c * (p τ₀ i_star j_star * ((P i_star).Φ (cfg i_star) (cv (cfg i_star) j_star) - (P i_star).Φ (cfg i_star) (N i_star))) +
              c * p τ₀ i_star j_star * ((k i_star : ℝ) * ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star))) +
              p τ₀ i_star j_star * r i_star j_star +
              p τ₀ i_star j_star * (runValue k m r P cfg sel p s (t + 1) N' + c * pot (t + 1) N') +
              (1 - p τ₀ i_star j_star) * (runValue k m r P cfg sel p s (t + 1) N + c * pot (t + 1) N)) -
            (c * (remObj t - remObj (t + 1) - (pot t N - pot (t + 1) N)) +
              c * p τ₀ i_star j_star * (pot (t + 1) N' - pot (t + 1) N) +
              p τ₀ i_star j_star * (c * ((k i_star : ℝ) * ((P i_star).Φ (cfg i_star) (N i_star + 1) - (P i_star).Φ (cfg i_star) (N i_star)) +
                (P i_star).Φ (cfg i_star) (cv (cfg i_star) j_star) - (P i_star).Φ (cfg i_star) (N i_star))) +
              p τ₀ i_star j_star * (c * remObj (t + 1)) +
              (1 - p τ₀ i_star j_star) * (c * remObj (t + 1))) := by ring
          linarith
        · -- Branch: score a ≤ 0
          have ih2 := ih (t + 1) N (by omega) hN
          have h_sum_score : (∑ i : ι, ∑ j ∈ Icc 1 (m i),
              (p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j -
                p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j)) ≤ 0 := by
            apply sum_nonpos; intro i _
            apply sum_nonpos; intro j hj
            have hxj := hx.2.2 τ₀ i j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
            have hsc_ij := hscore_le i j hj
            nlinarith
          have h_sum_diff : (∑ i : ι, ∑ j ∈ Icc 1 (m i),
              (p τ₀ i j * (P i).Φ (cfg i) (cv (cfg i) j) * x τ₀ i j -
                p τ₀ i j * (P i).Φ (cfg i) (N i) * x τ₀ i j)) =
              (remObj t - remObj (t + 1)) - (pot t N - pot (t + 1) N) := by
            simp only [sum_sub_distrib]
            rw [hremObj_step, hpot_diff]
            ring
          rw [h_sum_diff] at h_sum_score
          have h_c_score := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) h_sum_score
          have h_id : (runValue k m r P cfg sel p s (t + 1) N + c * pot t N) - c * remObj t =
            (runValue k m r P cfg sel p s (t + 1) N + c * pot (t + 1) N - c * remObj (t + 1)) -
              c * (remObj t - remObj (t + 1) - (pot t N - pot (t + 1) N)) := by ring
          linarith
    have h0 := hind T 0 (fun _ => 0) (Nat.zero_add T) (fun i => Nat.zero_le (k i))
    have hpot0 : pot 0 (fun _ => 0) = 0 := by
      dsimp [pot]
      apply sum_eq_zero; intro i _
      rw [(hcfg_prop i).2.1, mul_zero]
    have hremObj0 : remObj 0 = ∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
        p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j := by
      dsimp [remObj]
      have hfilt0 : univ.filter (fun τ : Fin T => 0 ≤ τ.val) = univ := by
        ext τ; simp
      rw [hfilt0]
    rw [hpot0, hremObj0, mul_zero, add_zero] at h0
    exact h0
  -- Now take expectation over cfg
  have h_exp : c * (∑ cfg : (∀ i, Config (k i) (m i)),
      (∏ i, (P i).ρ (cfg i)) *
        (∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
          p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j)) ≤
      expRevenue k m r P sel p := by
    unfold expRevenue
    rw [mul_sum]
    apply sum_le_sum
    intro cfg _
    by_cases hpos : ∀ i, (P i).ρ (cfg i) ≠ 0
    · have hprod_nonneg : 0 ≤ ∏ i, (P i).ρ (cfg i) :=
        prod_nonneg (fun i _ => (hP i).1 (cfg i))
      have hb := h_cfg_bound cfg hpos
      calc
        c * ((∏ i, (P i).ρ (cfg i)) *
            ∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
              p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j)
          = (∏ i, (P i).ρ (cfg i)) *
              (c * ∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
                p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j) := by ring
        _ ≤ (∏ i, (P i).ρ (cfg i)) * runValue k m r P cfg sel p T 0 (fun _ => 0) :=
            mul_le_mul_of_nonneg_left hb hprod_nonneg
    · push_neg at hpos
      obtain ⟨i₀, hi₀⟩ := hpos
      have hprod0 : (∏ i, (P i).ρ (cfg i)) = 0 :=
        prod_eq_zero (mem_univ i₀) hi₀
      rw [hprod0]
      linarith
  -- Finally, swap sums and apply Cond18
  have h_18_bound : lpObj m r p x ≤
      ∑ cfg : (∀ i, Config (k i) (m i)),
        (∏ i, (P i).ρ (cfg i)) *
          (∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
            p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j) := by
    have h_swap : (∑ cfg : (∀ i, Config (k i) (m i)),
        (∏ i, (P i).ρ (cfg i)) *
          (∑ t : Fin T, ∑ i : ι, ∑ j ∈ Icc 1 (m i),
            p t i j * (P i).Φ (cfg i) (cv (cfg i) j) * x t i j)) =
        ∑ t : Fin T, ∑ i₀ : ι, ∑ j ∈ Icc 1 (m i₀),
          p t i₀ j * (∑ c₀ : Config (k i₀) (m i₀), (P i₀).ρ c₀ * (P i₀).Φ c₀ (cv c₀ j)) * x t i₀ j := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro t _
      rw [sum_comm]
      apply sum_congr rfl; intro i₀ _
      rw [sum_comm]
      apply sum_congr rfl; intro j _
      have hpull : (∑ cfg : (∀ i, Config (k i) (m i)),
          (∏ i, (P i).ρ (cfg i)) * (p t i₀ j * (P i₀).Φ (cfg i₀) (cv (cfg i₀) j) * x t i₀ j)) =
          p t i₀ j * (∑ cfg : (∀ i, Config (k i) (m i)),
            (∏ i, (P i).ρ (cfg i)) * (P i₀).Φ (cfg i₀) (cv (cfg i₀) j)) * x t i₀ j := by
        rw [mul_sum, sum_mul]
        apply sum_congr rfl; intro cfg _; ring
      rw [hpull, marginal_sum k m P hP i₀ j, mul_sum]
    rw [h_swap]
    unfold lpObj
    apply sum_le_sum; intro t _
    apply sum_le_sum; intro i₀ _
    apply sum_le_sum; intro j hj
    rw [mem_Icc] at hj
    have hp0 := (hp t i₀ j hj.1 hj.2).1
    have hx0 := hx.2.2 t i₀ j hj.1 hj.2
    have h18_ij := h18 i₀ j hj.1 hj.2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h18_ij hp0) hx0
  exact le_trans (mul_le_mul_of_nonneg_left h_18_bound (le_of_lt hc)) h_exp
