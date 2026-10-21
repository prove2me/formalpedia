-- Prove2me | solution 1 for MNLBandit.LowerBound.lemma_E_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:51:26.884957+00:00
-- url     : https://prove2.me/submissions/00e13abf-736c-4bd6-8215-83aeed34e114

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_MNLBandit_LowerBound_Setting

set_option autoImplicit false
open MNLBandit.LowerBound

lemma step_E4 (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 ≤ ε) (S : Finset (Fin N)) :
    (∀ y, 0 ≤ choiceProb 1 (instHat N ε false).v S y) ∧
    ∑ y, choiceProb 1 (instHat N ε false).v S y = 1 ∧
    (∀ y, choiceProb 1 (instHat N ε false).v S y ≠ 0 → 0 < choiceProb 1 (instHat N ε true).v S y) ∧
    ∑ y, choiceProb 1 (instHat N ε false).v S y *
      Real.log (choiceProb 1 (instHat N ε false).v S y / choiceProb 1 (instHat N ε true).v S y)
      ≤ 4 * ε ^ 2 := by
  set i0 : Fin N := ⟨0, by omega⟩ with hi0
  have hv0 : ∀ i, (instHat N ε false).v i = 1 / 2 := by
    intro i; simp [instHat]
  have hv1 : ∀ i, (instHat N ε true).v i = 1 / 2 + if i = i0 then ε else 0 := by
    intro i
    simp only [instHat, hi0, Fin.ext_iff]
    split_ifs <;> simp_all
  set k : ℝ := (S.card : ℝ) with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hs0 : ∑ j ∈ S, (instHat N ε false).v j = k / 2 := by
    simp only [hv0, Finset.sum_const, nsmul_eq_mul]; rw [hk]; ring
  have hD0 : 0 < 1 + k / 2 := by linarith
  set P := choiceProb 1 (instHat N ε false).v S with hP
  have hPn : P none = 1 / (1 + k / 2) := by simp [hP, choiceProb, hs0]
  have hPs : ∀ i, P (some i) = if i ∈ S then (1 / 2) / (1 + k / 2) else 0 := by
    intro i; simp only [hP, choiceProb]; rw [hs0, hv0]
  have hP0 : ∀ y, 0 ≤ P y := by
    intro y
    cases y with
    | none => rw [hPn]; positivity
    | some i => rw [hPs]; split_ifs <;> positivity
  have hPsum : ∑ y, P y = 1 := by
    rw [Fintype.sum_option, hPn]
    simp only [hPs]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, ← hk]
    field_simp
  have main : (∀ y, P y ≠ 0 → 0 < choiceProb 1 (instHat N ε true).v S y) ∧
      ∑ y, P y * Real.log (P y / choiceProb 1 (instHat N ε true).v S y) ≤ 4 * ε ^ 2 := by
    by_cases h0 : i0 ∈ S
    · have hcard1 : 1 ≤ S.card := Finset.card_pos.2 ⟨i0, h0⟩
      have hk1 : 1 ≤ k := by
        rw [hk]; exact_mod_cast hcard1
      have hs1 : ∑ j ∈ S, (instHat N ε true).v j = k / 2 + ε := by
        simp only [hv1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_ite_eq', if_pos h0]
        rw [hk]; ring
      set Q := choiceProb 1 (instHat N ε true).v S with hQ
      have hD1 : 0 < 1 + (k / 2 + ε) := by linarith
      have hQn : Q none = 1 / (1 + (k / 2 + ε)) := by simp [hQ, choiceProb, hs1]
      have hQs : ∀ i, Q (some i) =
          if i ∈ S then (1 / 2 + if i = i0 then ε else 0) / (1 + (k / 2 + ε)) else 0 := by
        intro i; simp only [hQ, choiceProb]; rw [hs1, hv1]
      have hQpos : ∀ y, P y ≠ 0 → 0 < Q y := by
        intro y hy
        cases y with
        | none => rw [hQn]; positivity
        | some i =>
          rw [hPs] at hy
          by_cases hi : i ∈ S
          · rw [hQs, if_pos hi]
            have : 0 ≤ (if i = i0 then ε else 0) := by split_ifs <;> linarith
            apply div_pos <;> linarith
          · simp [hi] at hy
      refine ⟨hQpos, ?_⟩
      have hterm : ∀ y, P y * Real.log (P y / Q y) ≤ P y * (P y / Q y - 1) := by
        intro y
        by_cases hy : P y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne (hP0 y) (Ne.symm hy)) (hQpos y hy)))
            (hP0 y)
      refine (Finset.sum_le_sum (fun y _ => hterm y)).trans ?_
      rw [Fintype.sum_option]
      have hsome : ∀ f : Fin N → ℝ, ∑ i, (if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
        intro f; simp [Finset.sum_ite_mem]
      have hrest : ∑ i : Fin N, P (some i) * (P (some i) / Q (some i) - 1) =
          ∑ i ∈ S, ((1 / 2) / (1 + k / 2) *
            (((1 / 2) / (1 + k / 2)) /
              ((1 / 2 + if i = i0 then ε else 0) / (1 + (k / 2 + ε))) - 1)) := by
        rw [← hsome]
        apply Finset.sum_congr rfl
        intro i _
        rw [hPs, hQs]
        split_ifs <;> simp
      rw [hrest, ← Finset.add_sum_erase S _ h0, hPn, hQn]
      rw [Finset.sum_congr rfl (g := fun _ => ((1 / 2) / (1 + k / 2) *
            (((1 / 2) / (1 + k / 2)) / ((1 / 2) / (1 + (k / 2 + ε))) - 1)))
        (by
          intro i hi
          have : i ≠ i0 := (Finset.mem_erase.1 hi).1
          simp [this])]
      rw [Finset.sum_const, Finset.card_erase_of_mem h0, nsmul_eq_mul]
      have hc : ((S.card - 1 : ℕ) : ℝ) = k - 1 := by
        rw [Nat.cast_sub hcard1]; simp [hk]
      rw [hc]
      simp only [if_true]
      have hk2 : 0 < k + 2 := by linarith
      have e : 1 / (1 + k / 2) * (1 / (1 + k / 2) / (1 / (1 + (k / 2 + ε))) - 1) +
          (1 / 2 / (1 + k / 2) * (1 / 2 / (1 + k / 2) / ((1 / 2 + ε) / (1 + (k / 2 + ε))) - 1) +
          (k - 1) * (1 / 2 / (1 + k / 2) * (1 / 2 / (1 + k / 2) / (1 / 2 / (1 + (k / 2 + ε))) - 1)))
          = 4 * ε ^ 2 * (k + 1) / ((1 + 2 * ε) * (k + 2) ^ 2) := by
        have : (1 + 2 * ε) ≠ 0 := by positivity
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) hε, mul_nonneg (sq_nonneg ε) (by linarith : (0:ℝ) ≤ k),
        mul_nonneg (mul_nonneg (sq_nonneg ε) hε) (by linarith : (0:ℝ) ≤ k),
        mul_nonneg (sq_nonneg ε) (mul_nonneg (by linarith : (0:ℝ) ≤ k) (by linarith : (0:ℝ) ≤ k))]
    · have hsum : ∑ j ∈ S, (instHat N ε true).v j = ∑ j ∈ S, (instHat N ε false).v j := by
        apply Finset.sum_congr rfl
        intro j hj
        have : j ≠ i0 := fun h => h0 (h ▸ hj)
        rw [hv1, hv0]; simp [this]
      have hPQ : choiceProb 1 (instHat N ε true).v S = P := by
        funext y
        cases y with
        | none => simp [hP, choiceProb, hsum]
        | some i =>
          simp only [hP, choiceProb]
          split_ifs with hi
          · have : i ≠ i0 := fun h => h0 (h ▸ hi)
            rw [hv1, hv0, hsum]; simp [this]
          · rfl
      rw [hPQ]
      refine ⟨fun y hy => lt_of_le_of_ne (hP0 y) (Ne.symm hy), ?_⟩
      have : ∀ y, P y * Real.log (P y / P y) = 0 := by
        intro y
        by_cases hy : P y = 0
        · simp [hy]
        · simp [div_self hy]
      simp only [this, Finset.sum_const_zero]
      positivity
  exact ⟨hP0, hPsum, main.1, main.2⟩

lemma logsplit (a b c d : ℝ) (hac : a ≠ 0 → 0 < c) (hbd : b ≠ 0 → 0 < d) :
    (a * b) * Real.log ((a * b) / (c * d)) =
      b * (a * Real.log (a / c)) + a * (b * Real.log (b / d)) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hc := hac ha
  have hd := hbd hb
  rw [mul_div_mul_comm, Real.log_mul (div_ne_zero ha hc.ne') (div_ne_zero hb hd.ne')]
  ring

lemma prod_snoc {N : ℕ} (r : Finset (Fin N) → Option (Fin N) → ℝ) (π : MNLBandit.UCB.Policy N)
    (T : ℕ) (h : Fin T → Option (Fin N)) (y : Option (Fin N)) :
    ∏ t : Fin (T + 1), r (π t (prefixOf (Fin.snoc (α := fun _ => Option (Fin N)) h y) t))
        ((Fin.snoc (α := fun _ => Option (Fin N)) h y : Fin (T + 1) → Option (Fin N)) t) =
      (∏ t : Fin T, r (π t (prefixOf h t)) (h t)) * r (π T h) y := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    have e1 : prefixOf (Fin.snoc (α := fun _ => Option (Fin N)) h y : Fin (T + 1) → Option (Fin N))
        (Fin.castSucc t) = prefixOf h t := by
      funext s
      simp only [prefixOf]
      exact Fin.snoc_castSucc (α := fun _ => Option (Fin N)) y h (Fin.castLE t.isLt.le s)
    rw [Fin.snoc_castSucc]
    exact congrArg₂ (fun a b => r (π t a) b) e1 rfl
  · have e2 : prefixOf (Fin.snoc (α := fun _ => Option (Fin N)) h y : Fin (T + 1) → Option (Fin N))
        (Fin.last T) = h := by
      funext s
      simp only [prefixOf]
      exact Fin.snoc_castSucc (α := fun _ => Option (Fin N)) y h s
    rw [Fin.snoc_last]
    exact congrArg₂ (fun a b => r (π T a) b) e2 rfl

lemma chain {N : ℕ} (p q : Finset (Fin N) → Option (Fin N) → ℝ) (B : ℝ)
    (hp0 : ∀ S y, 0 ≤ p S y) (hp1 : ∀ S, ∑ y, p S y = 1)
    (hq : ∀ S y, p S y ≠ 0 → 0 < q S y)
    (hB : ∀ S, ∑ y, p S y * Real.log (p S y / q S y) ≤ B) (π : MNLBandit.UCB.Policy N) :
    ∀ T : ℕ,
      (∀ c : Fin T → Option (Fin N), 0 ≤ ∏ t : Fin T, p (π t (prefixOf c t)) (c t)) ∧
      ∑ c : Fin T → Option (Fin N), ∏ t : Fin T, p (π t (prefixOf c t)) (c t) = 1 ∧
      (∀ c : Fin T → Option (Fin N), ∏ t : Fin T, p (π t (prefixOf c t)) (c t) ≠ 0 →
        0 < ∏ t : Fin T, q (π t (prefixOf c t)) (c t)) ∧
      ∑ c : Fin T → Option (Fin N),
        (∏ t : Fin T, p (π t (prefixOf c t)) (c t)) *
          Real.log ((∏ t : Fin T, p (π t (prefixOf c t)) (c t)) /
            ∏ t : Fin T, q (π t (prefixOf c t)) (c t)) ≤ T * B := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
    set P : (Fin T → Option (Fin N)) → ℝ := fun c => ∏ t : Fin T, p (π t (prefixOf c t)) (c t)
      with hPdef
    set Q : (Fin T → Option (Fin N)) → ℝ := fun c => ∏ t : Fin T, q (π t (prefixOf c t)) (c t)
      with hQdef
    let e := Fin.snocEquiv (fun _ : Fin (T + 1) => Option (Fin N))
    have hsum : ∀ F : (Fin (T + 1) → Option (Fin N)) → ℝ,
        ∑ c, F c = ∑ h : Fin T → Option (Fin N), ∑ y : Option (Fin N),
          F (Fin.snoc (α := fun _ => Option (Fin N)) h y) := by
      intro F
      rw [← Equiv.sum_comp e F, Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    have hPs : ∀ h y, ∏ t : Fin (T + 1), p (π t (prefixOf (Fin.snoc (α := fun _ => Option (Fin N)) h y) t))
        ((Fin.snoc (α := fun _ => Option (Fin N)) h y : Fin (T + 1) → Option (Fin N)) t) =
        P h * p (π T h) y := fun h y => prod_snoc p π T h y
    have hQs : ∀ h y, ∏ t : Fin (T + 1), q (π t (prefixOf (Fin.snoc (α := fun _ => Option (Fin N)) h y) t))
        ((Fin.snoc (α := fun _ => Option (Fin N)) h y : Fin (T + 1) → Option (Fin N)) t) =
        Q h * q (π T h) y := fun h y => prod_snoc q π T h y
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c
      have : c = Fin.snoc (α := fun _ => Option (Fin N)) (Fin.init c) (c (Fin.last T)) := by simp
      rw [this, hPs]
      exact mul_nonneg (ih0 _) (hp0 _ _)
    · rw [hsum]
      simp only [hPs]
      simp_rw [← Finset.mul_sum, hp1, mul_one]
      exact ih1
    · intro c hc
      have : c = Fin.snoc (α := fun _ => Option (Fin N)) (Fin.init c) (c (Fin.last T)) := by simp
      rw [this, hPs] at hc
      rw [this, hQs]
      have h1 := left_ne_zero_of_mul hc
      have h2 := right_ne_zero_of_mul hc
      exact mul_pos (ih2 _ h1) (hq _ _ h2)
    · rw [hsum]
      simp only [hPs, hQs]
      have hpt : ∀ h y, (P h * p (π T h) y) * Real.log ((P h * p (π T h) y) / (Q h * q (π T h) y)) =
          p (π T h) y * (P h * Real.log (P h / Q h)) +
            P h * (p (π T h) y * Real.log (p (π T h) y / q (π T h) y)) := by
        intro h y
        have := logsplit (P h) (p (π T h) y) (Q h) (q (π T h) y) (ih2 h) (hq _ _)
        linarith
      simp only [hpt, Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul, hp1, one_mul, ← Finset.mul_sum]
      have h5 : ∑ h : Fin T → Option (Fin N), P h * ∑ y, p (π T h) y * Real.log (p (π T h) y / q (π T h) y)
          ≤ ∑ h : Fin T → Option (Fin N), P h * B :=
        Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hB _) (ih0 h))
      rw [← Finset.sum_mul, ih1, one_mul] at h5
      push_cast
      linarith

theorem solution (N T : ℕ) (hN : 2 ≤ N) (hT : 1 ≤ T) (π : MNLBandit.UCB.Policy N) :
    FoundationsRL.GeneralDM.klDivDiscrete
        (histProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v π T)
        (histProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v π T) ≤
      ENNReal.ofReal (4 * T * (Real.sqrt (1 / (32 * (T : ℝ)))) ^ 2) := by
  set ε := Real.sqrt (1 / (32 * (T : ℝ))) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have := chain (fun S y => choiceProb 1 (instHat N ε false).v S y)
    (fun S y => choiceProb 1 (instHat N ε true).v S y) (4 * ε ^ 2)
    (fun S => (step_E4 N hN ε hε0 S).1) (fun S => (step_E4 N hN ε hε0 S).2.1)
    (fun S => (step_E4 N hN ε hε0 S).2.2.1) (fun S => (step_E4 N hN ε hε0 S).2.2.2) π T
  obtain ⟨_, _, h2, h3⟩ := this
  unfold FoundationsRL.GeneralDM.klDivDiscrete histProb
  rw [if_pos (by
    intro c hc
    by_contra hne
    exact absurd hc (h2 c hne).ne')]
  apply ENNReal.ofReal_le_ofReal
  have : (4 : ℝ) * T * ε ^ 2 = T * (4 * ε ^ 2) := by ring
  rw [this]
  exact h3
