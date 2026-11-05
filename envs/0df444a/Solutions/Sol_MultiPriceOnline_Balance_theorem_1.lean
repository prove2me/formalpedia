-- Prove2me | solution 1 for MultiPriceOnline.Balance.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:07:10.08278+00:00
-- url     : https://prove2.me/submissions/f3216ee8-d7b3-4e63-ab23-7b8ff078cea3

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_LP
import Definitions.Def_MultiPriceOnline_Balance_Procedure
import Definitions.Def_MultiPriceOnline_Balance_Algorithm
import Theorems.Thm_MultiPriceOnline_Balance_theorem_4
import Theorems.Thm_MultiPriceOnline_Balance_theorem_5
import Theorems.Thm_MultiPriceOnline_Balance_eq_45

open MultiPriceOnline.Balance

namespace MPBalanceT1Aux

lemma price_pos {m : ℕ} {r : ℕ → ℝ} (hr : IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj hjm
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact hr.1
    · have := hr.2 n h (by omega)
      linarith [ih h (by omega)]

lemma cond17_mono {k m : ℕ} {r : ℕ → ℝ} {P : Procedure k m} {b c : ℝ}
    (h : Cond17 r P b) (hc : 0 < c) (hcb : c ≤ b) (hr : ∀ j, 1 ≤ j → j ≤ m → 0 < r j) :
    Cond17 r P c := by
  intro c₀ hc₀ j hj hjm N hN
  refine (h c₀ hc₀ j hj hjm N hN).trans ?_
  exact div_le_div_of_nonneg_left (hr j hj hjm).le hc hcb

lemma mode_facts (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (r α σ : ℕ → ℝ)
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) (hσ : IsBQLimits m r σ) (b : Bool) :
    IsProcedure (modeProc k m r α σ b) ∧ Cond17 r (modeProc k m r α σ b) (modeBound k m α σ b) ∧
      Cond18 r (modeProc k m r α σ b) ∧ 0 < modeBound k m α σ b := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h1k : (0 : ℝ) < 1 / k := by positivity
  have hden1 : 0 < (1 + (k : ℝ)) * (Real.exp (1 / k) - 1) := by
    have : 1 < Real.exp (1 / k) := Real.one_lt_exp_iff.mpr h1k
    nlinarith
  have hden2 : 0 < (1 + (k : ℝ)) * (1 - Real.exp (-1 / k)) := by
    have : Real.exp (-1 / k) < 1 := by
      rw [Real.exp_lt_one_iff]; rw [neg_div]; linarith
    nlinarith
  have hF : 0 < Fval α := by
    unfold Fval
    have : Real.exp (-α 1) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith [hα.1 1 le_rfl hm]
    linarith
  cases b with
  | true =>
    obtain ⟨h1, h2, h3⟩ := eq_45 m hm r σ hr hσ
    refine ⟨h1, h2, h3, ?_⟩
    show 0 < Gval σ / 2
    have := hσ.1 1 le_rfl hm
    unfold Gval; linarith
  | false =>
    obtain ⟨h1, h2, h3, h4⟩ := theorem_5 k m hk hm r α hr hα
    refine ⟨h1, ?_, h3, ?_⟩
    · show Cond17 r (def3Proc k m r α) (if m = 1 then (1 - 1 / Real.exp 1) / ((1 + k) * (1 - Real.exp (-1 / k)))
        else Fval α / ((1 + k) * (Real.exp (1 / k) - 1)))
      split_ifs with hm1
      · have hF1 : Fval α = 1 - 1 / Real.exp 1 := by
          have hs := hα.2.1
          subst hm1
          simp at hs
          unfold Fval; rw [hs, Real.exp_neg, one_div]
        rw [← hF1]; exact h4 hm1
      · exact h2
    · show 0 < (if m = 1 then (1 - 1 / Real.exp 1) / ((1 + k) * (1 - Real.exp (-1 / k)))
        else Fval α / ((1 + k) * (Real.exp (1 / k) - 1)))
      split_ifs
      · have : 1 / Real.exp 1 < 1 := by
          rw [div_lt_one (Real.exp_pos 1)]; exact Real.one_lt_exp_iff.mpr one_pos
        apply div_pos (by linarith) hden2
      · exact div_pos hF hden1

end MPBalanceT1Aux

open MPBalanceT1Aux in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (k m : ι → ℕ)
    (hk : ∀ i, 1 ≤ k i) (hm : ∀ i, 1 ≤ m i) (r α σ : ι → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, IsBookingLimits (m i) (r i) (α i))
    (hσ : ∀ i, IsBQLimits (m i) (r i) (σ i)) (split : ι → Bool)
    {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1)
    (sel : Selector (fun x : SplitItem k split => m x.1)) (hsel : IsArgmaxSelector sel)
    (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x) :
    (Finset.univ.inf' Finset.univ_nonempty
        (fun i => modeBound (k i) (m i) (α i) (σ i) (split i))) * lpObj m r p x ≤
      balanceRevenue k m r α σ split sel p := by
  set c := Finset.univ.inf' Finset.univ_nonempty
        (fun i => modeBound (k i) (m i) (α i) (σ i) (split i)) with hc_def
  have hMF := fun i => mode_facts (k i) (m i) (hk i) (hm i) (r i) (α i) (σ i) (hr i) (hα i) (hσ i)
    (split i)
  have hcpos : 0 < c := by
    rw [hc_def, Finset.lt_inf'_iff]
    intro i _; exact (hMF i).2.2.2
  have hcle : ∀ i, c ≤ modeBound (k i) (m i) (α i) (σ i) (split i) := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hcop : ∀ i, (0 : ℝ) < (copies k split i : ℝ) := by
    intro i; unfold copies; cases split i <;> simp; exact_mod_cast hk i
  -- the derived LP solution
  let x' : Fin T → SplitItem k split → ℕ → ℝ := fun t y j => x t y.1 j / (copies k split y.1 : ℝ)
  have hobj : lpObj m r p x = lpObj (fun y : SplitItem k split => m y.1) (fun y => r y.1)
      (fun t y j => p t y.1 j) x' := by
    unfold lpObj
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [x', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    field_simp [(hcop i).ne']
  have hx' : LPFeasible (splitK k split) (fun y : SplitItem k split => m y.1)
      (fun t y j => p t y.1 j) x' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨i, u⟩
      have h := hx.1 i
      simp only [x']
      have : ∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * (x t i j / (copies k split i : ℝ))
          = (∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j) / (copies k split i : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [this, div_le_iff₀ (hcop i)]
      unfold copies splitK
      cases split i <;> simpa using h
    · intro t
      have h := hx.2.1 t
      rw [Fintype.sum_sigma]
      simp only [x', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc _ = ∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              field_simp [(hcop i).ne']
        _ ≤ 1 := h
    · intro t y j hj hjm
      exact div_nonneg (hx.2.2 t y.1 j hj hjm) (hcop y.1).le
  rw [hobj]
  exact theorem_4 (splitK k split) (fun y => m y.1)
    (fun y => by unfold splitK; cases split y.1 <;> simp [hk y.1])
    (fun y => hm y.1) (fun y => r y.1) (fun y => hr y.1)
    (fun y => modeProc (k y.1) (m y.1) (r y.1) (α y.1) (σ y.1) (split y.1))
    (fun y => (hMF y.1).1) c
    (fun y => cond17_mono (hMF y.1).2.1 hcpos (hcle y.1) (price_pos (hr y.1)))
    (fun y => (hMF y.1).2.2.1)
    (fun t y j => p t y.1 j) (fun t y j hj hjm => hp t y.1 j hj hjm)
    sel hsel x' hx'
