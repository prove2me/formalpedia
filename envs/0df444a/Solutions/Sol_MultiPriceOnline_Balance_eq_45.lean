-- Prove2me | solution 1 for MultiPriceOnline.Balance.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:58:47.946688+00:00
-- url     : https://prove2.me/submissions/c80b0d44-e6c4-417f-a755-e04d47d87f92

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure


namespace Aux_MPO45
open MultiPriceOnline.Balance

lemma cfg_inj {m d d' : ℕ} (hd : d ≤ m) (hd' : d' ≤ m) (h : cfg45 m d = cfg45 m d') :
    d = d' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := congrFun h ⟨d, by omega⟩
    simp [cfg45, hlt] at this
  · have := congrFun h ⟨d', by omega⟩
    simp [cfg45, hlt] at this

lemma sum_single {m d : ℕ} (hd : d ∈ Finset.Icc 1 m) (x : ℕ → ℝ) :
    (∑ d' ∈ Finset.Icc 1 m, if cfg45 m d = cfg45 m d' then x d' else 0) = x d := by
  rw [Finset.sum_eq_single_of_mem d hd]
  · simp
  · intro b hb hne
    rw [if_neg]
    intro h
    exact hne (cfg_inj (Finset.mem_Icc.1 hb).2 (Finset.mem_Icc.1 hd).2 h.symm)

lemma phi_cfg {m : ℕ} (r σ : ℕ → ℝ) {d : ℕ} (hd : d ∈ Finset.Icc 1 m) (N : ℕ) :
    (proc45 m r σ).Φ (cfg45 m d) N = if N = 0 then 0 else r d / σ 1 := by
  show (if N = 0 then (0:ℝ) else ∑ d' ∈ Finset.Icc 1 m,
      if cfg45 m d = cfg45 m d' then r d' / σ 1 else 0) = _
  split_ifs with hN
  · rfl
  · exact sum_single hd (fun d' => r d' / σ 1)

lemma rho_ne {m : ℕ} (r σ : ℕ → ℝ) (c : Config 1 m) (h : (proc45 m r σ).ρ c ≠ 0) :
    ∃ d ∈ Finset.Icc 1 m, c = cfg45 m d := by
  by_contra hc
  push_neg at hc
  apply h
  show (∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then σ d else 0) = 0
  apply Finset.sum_eq_zero
  intro d hd
  rw [if_neg (hc d hd)]

lemma cv_cfg {m d j : ℕ} (hj : j ≤ m) : cv (cfg45 m d) j = if j < d then 0 else 1 := by
  unfold cv cfg45
  rw [dif_pos (by omega)]
  split_ifs <;> simp_all

lemma r_pos {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) : ∀ d, 1 ≤ d → d ≤ m → 0 < r d := by
  intro d h1 h2
  induction d with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hr.1
    · exact (ih hn (by omega)).trans (hr.2 n hn (by omega))

lemma r_mono {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) {d j : ℕ} (hd : 1 ≤ d) (hdj : d ≤ j)
    (hj : j ≤ m) : r d ≤ r j := by
  induction j, hdj using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (hr.2 n (by omega) (by omega)).le

end Aux_MPO45

open MultiPriceOnline.Balance Aux_MPO45 in
theorem solution (m : ℕ) (hm : 1 ≤ m) (r σ : ℕ → ℝ) (hr : IsPriceSet m r)
    (hσ : IsBQLimits m r σ) :
    IsProcedure (proc45 m r σ) ∧ Cond17 r (proc45 m r σ) (Gval σ / 2) ∧
    Cond18 r (proc45 m r σ) := by
  obtain ⟨hσpos, hσsum, hσrel⟩ := hσ
  have hσ1 : 0 < σ 1 := hσpos 1 le_rfl hm
  have hrpos := r_pos hr
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro c
    show 0 ≤ ∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then σ d else 0
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact (hσpos d (Finset.mem_Icc.1 hd).1 (Finset.mem_Icc.1 hd).2).le
    · exact le_rfl
  · show (∑ c : Config 1 m, ∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then σ d else 0) = 1
    rw [Finset.sum_comm, ← hσsum]
    apply Finset.sum_congr rfl
    intro d _
    simp
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := rho_ne r σ c hc
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.1 hd
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · show ((if (0:ℕ) < d then (0 : Fin 2) else 1 : Fin 2) : ℕ) = 0
      rw [if_pos (by omega)]; rfl
    · show ((if m < d then (0 : Fin 2) else 1 : Fin 2) : ℕ) = 1
      rw [if_neg (by omega)]; rfl
    · intro a b hab
      have hab' : (a : ℕ) ≤ b := hab
      simp only [cfg45]
      split_ifs with h1 h2 h2
      all_goals first | exact le_rfl | (exfalso; omega) | decide
    · simp [phi_cfg r σ hd]
    · intro N hN
      have : N = 0 := by omega
      subst this
      rw [phi_cfg r σ hd, phi_cfg r σ hd]
      simp only [if_true, one_ne_zero, if_false, zero_add]
      exact div_nonneg (hrpos d hd1 hd2).le hσ1.le
  · intro c₀ hc j hj1 hjm N hN
    obtain ⟨d, hd, rfl⟩ := rho_ne r σ c₀ hc
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.1 hd
    rw [cv_cfg hjm] at hN ⊢
    split_ifs at hN ⊢ with hjd
    · omega
    · have hN0 : N = 0 := by omega
      subst hN0
      rw [phi_cfg r σ hd, phi_cfg r σ hd]
      simp only [Gval, if_true, one_ne_zero, if_false, zero_add, Nat.cast_one, one_mul, sub_zero]
      have hrd : r d ≤ r j := r_mono hr hd1 (by omega) hjm
      have h2 : r d / σ 1 ≤ r j / σ 1 := div_le_div_of_nonneg_right hrd hσ1.le
      have h3 : r j / (σ 1 / 2) = 2 * (r j / σ 1) := by field_simp
      rw [h3]; linarith
  · intro j hj1 hjm
    have hexp : ∀ c : Config 1 m, (proc45 m r σ).ρ c * (proc45 m r σ).Φ c (cv c j) =
        ∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then
          σ d * (proc45 m r σ).Φ (cfg45 m d) (cv (cfg45 m d) j) else 0 := by
      intro c
      show (∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then σ d else 0) * _ = _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs with h
      · subst h; rfl
      · simp
    rw [Finset.sum_congr rfl (fun c _ => hexp c), Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hterm : ∀ d ∈ Finset.Icc 1 m,
        σ d * (proc45 m r σ).Φ (cfg45 m d) (cv (cfg45 m d) j) =
          if d ≤ j then σ d * (r d / σ 1) else 0 := by
      intro d hd
      rw [phi_cfg r σ hd, cv_cfg hjm]
      by_cases h : j < d
      · simp [h, show ¬ d ≤ j by omega]
      · simp [h, show d ≤ j by omega]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hfil : (Finset.Icc 1 m).filter (fun d => d ≤ j) = Finset.Icc 1 j := by
      ext d; simp; omega
    have tele : ∀ j, 1 ≤ j → j ≤ m → ∑ d ∈ Finset.Icc 1 j, σ d * (r d / σ 1) = r j := by
      intro j hj1 hjm
      induction j, hj1 using Nat.le_induction with
      | base => rw [Finset.Icc_self, Finset.sum_singleton]; field_simp
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
        have hrel := hσrel (n+1) (by omega) hjm
        simp only [Nat.add_sub_cancel] at hrel
        have hp := hrpos (n+1) (by omega) hjm
        have hlt := hr.2 n hn (by omega)
        have hne : 1 - r n / r (n+1) ≠ 0 := by
          have : r n / r (n+1) < 1 := (div_lt_one hp).2 hlt
          linarith
        have hs : σ (n+1) = σ 1 * (1 - r n / r (n+1)) := ((eq_div_iff hne).1 hrel).symm
        rw [hs]
        field_simp <;> ring
    rw [hfil, tele j hj1 hjm]
