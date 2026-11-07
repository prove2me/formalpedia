-- Prove2me | solution 1 for MNLBandit.UCB.lemma_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:19:41.206194+00:00
-- url     : https://prove2.me/submissions/6cf7a82a-7675-4c34-a9d2-c43d17a1a049
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Theorems.Thm_MNLBandit_UCB_lemma_A_2

open ChoiceCDLP.MNL MNLBandit.UCB

namespace MNLLemma41Aux

lemma histProb_nonneg {N T : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N)
    (h : History N T) : 0 ≤ histProb v π h := by
  unfold histProb
  apply Finset.prod_nonneg
  intro t _
  have hden : 0 < 1 + ∑ j ∈ offered π h t, v j :=
    by have := Finset.sum_nonneg (fun j (_ : j ∈ offered π h t) => hv0 j); linarith
  cases h t with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv0 i) hden.le
    · exact le_refl 0

lemma probT_mono {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) (hEF : ∀ h, E h → F h) :
    probT v π T E ≤ probT v π T F := by
  unfold probT
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos hE, if_pos (hEF h hE)]
  · rw [if_neg hE]; split_ifs <;> linarith

lemma probT_or {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) :
    probT v π T (fun h => E h ∨ F h) ≤ probT v π T E + probT v π T F := by
  unfold probT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos (Or.inl hE), if_pos hE]; split_ifs <;> linarith
  · by_cases hF : F h
    · rw [if_pos (Or.inr hF), if_neg hE, if_pos hF]; linarith
    · rw [if_neg (by tauto), if_neg hE, if_neg hF]; simp

lemma sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

end MNLLemma41Aux

open MNLLemma41Aux in
theorem solution {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i) ≤ 6 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        vUCB r sel h i ℓ - v i >
          (Real.sqrt 72 + Real.sqrt 24)
              * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 7 / (N * ℓ) := by
  obtain ⟨hA1, hA2, hA3⟩ := lemma_A_2 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ i
  -- unfolding the UCB along a history with at least `ℓ` completed epochs
  have hUCB : ∀ h : History N T, ℓ ≤ epochsDone r sel h →
      vUCB r sel h i ℓ = if Tcount r sel h i ℓ = 0 then 1 else
        vbar r sel h i ℓ
          + Real.sqrt (vbar r sel h i ℓ * (48 * Real.log (Real.sqrt N * (ℓ : ℝ) + 1))
              / (Tcount r sel h i ℓ : ℝ))
          + 48 * Real.log (Real.sqrt N * (ℓ : ℝ) + 1) / (Tcount r sel h i ℓ : ℝ) := by
    intro h hl
    have hlen : (pastUpTo r sel h ℓ).length = ℓ := by
      unfold pastUpTo; rw [List.length_take]; exact min_eq_left hl
    simp only [vUCB, vUCBL, Tcount, vbar, hlen]
    by_cases h0 : TcountL (pastUpTo r sel h ℓ) i = 0 <;> simp [h0]
  have hlg : ∀ h : History N T, 0 ≤ Real.log (Real.sqrt N * (ℓ : ℝ) + 1) := fun _ =>
    Real.log_nonneg (by have := Real.sqrt_nonneg (N : ℝ); nlinarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ ℓ)])
  constructor
  · refine le_trans (probT_mono v hv0 _ T _ _ ?_) hA1
    intro h ⟨hl, hlt⟩
    refine ⟨hl, ?_, ?_⟩
    · by_contra h0
      have h0' : Tcount r sel h i ℓ = 0 := by omega
      rw [hUCB h hl, if_pos h0'] at hlt
      linarith [hv1 i]
    · have h0 : Tcount r sel h i ℓ ≠ 0 := by
        intro h0'; rw [hUCB h hl, if_pos h0'] at hlt; linarith [hv1 i]
      rw [hUCB h hl, if_neg h0] at hlt
      have heq : vbar r sel h i ℓ * (48 * Real.log (Real.sqrt N * (ℓ : ℝ) + 1))
              / (Tcount r sel h i ℓ : ℝ) =
          48 * vbar r sel h i ℓ * Real.log (Real.sqrt N * (ℓ : ℝ) + 1)
              / (Tcount r sel h i ℓ : ℝ) := by ring
      rw [heq] at hlt
      have := neg_abs_le (vbar r sel h i ℓ - v i)
      linarith
  · have h47 : (4 : ℝ) / (N * ℓ) + 3 / (N * ℓ) = 7 / (N * ℓ) := by ring
    rw [← h47]
    refine le_trans (probT_mono v hv0 _ T _ _ ?_)
      (le_trans (probT_or v hv0 _ T _ _) (add_le_add hA2 hA3))
    intro h ⟨hl, hT, hgt⟩
    by_contra hcon
    simp only [not_or, not_and, not_lt] at hcon
    obtain ⟨hc2, hc3⟩ := hcon
    have hb2 := hc2 hl hT
    have hb3 := hc3 hl hT
    have h0 : Tcount r sel h i ℓ ≠ 0 := by omega
    rw [hUCB h hl, if_neg h0] at hgt
    set lam : ℝ := Real.log (Real.sqrt N * (ℓ : ℝ) + 1) with hlam
    set Tc : ℝ := (Tcount r sel h i ℓ : ℝ) with hTc
    set vb : ℝ := vbar r sel h i ℓ with hvb
    have hTc1 : (1 : ℝ) ≤ Tc := by rw [hTc]; exact_mod_cast hT
    have hTcp : 0 < Tc := by linarith
    have hlam0 : 0 ≤ lam := hlg h
    set a : ℝ := lam / Tc with ha
    have ha0 : 0 ≤ a := div_nonneg hlam0 hTcp.le
    set b : ℝ := v i * lam / Tc with hb
    have hb0 : 0 ≤ b := div_nonneg (mul_nonneg (hv0 i) hlam0) hTcp.le
    -- rewrite every square root in terms of `a` and `b`
    have e1 : 24 * v i * lam / Tc = 24 * b := by rw [hb]; ring
    have e2 : vb * (48 * lam) / Tc = 48 * a * vb := by rw [ha]; ring
    have e3 : 48 * lam / Tc = 48 * a := by rw [ha]; ring
    have e4 : 144 * lam / Tc = 144 * a := by rw [ha]; ring
    rw [e1, e3] at hb2
    rw [e3] at hb3
    rw [e2, e3, e4] at hgt
    have hsb : Real.sqrt (24 * b) = Real.sqrt 24 * Real.sqrt b := Real.sqrt_mul (by norm_num) b
    rw [hsb] at hb2
    -- the bound on the square-root term
    have hs1 : Real.sqrt (48 * a * vb) ≤ Real.sqrt (72 * b + (48 * a) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : 48 * a * vb ≤ 48 * a * (3 * v i / 2 + 48 * a) :=
        mul_le_mul_of_nonneg_left hb3 (by positivity)
      have hb' : b = v i * a := by rw [hb, ha]; ring
      rw [hb']; nlinarith
    have hs2 : Real.sqrt (72 * b + (48 * a) ^ 2) ≤ Real.sqrt 72 * Real.sqrt b + 48 * a := by
      calc Real.sqrt (72 * b + (48 * a) ^ 2)
          ≤ Real.sqrt (72 * b) + Real.sqrt ((48 * a) ^ 2) :=
            sqrt_add_le' _ _ (by positivity) (by positivity)
        _ = Real.sqrt 72 * Real.sqrt b + 48 * a := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    have habs := le_abs_self (vb - v i)
    nlinarith
