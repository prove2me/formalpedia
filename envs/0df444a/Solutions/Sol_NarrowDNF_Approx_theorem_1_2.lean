-- Prove2me | solution 1 for NarrowDNF.Approx.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:27.503112+00:00
-- url     : https://prove2.me/submissions/68e8f7bb-41b4-492d-9e76-345d50267cfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Certificates
import Theorems.Thm_NarrowDNF_Approx_lemma_2_1
import Theorems.Thm_NarrowDNF_Approx_theorem_3_5
import Theorems.Thm_NarrowDNF_Approx_lemma_4_1

section
set_option autoImplicit false
namespace NarrowDNF.Dev.T12
open NarrowDNF.Approx
open Classical

noncomputable def wt {n : ℕ} (p : ℝ) (x : Cube n) : ℝ := ∏ i : Fin n, FriedgutCoalition.bern p (x i)

lemma prob_eq {n : ℕ} (p : ℝ) (E : Cube n → Prop) [DecidablePred E] :
    prob p E = ∑ x : Cube n, if E x then wt p x else 0 := by
  unfold prob FriedgutCoalition.wProb wt
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : E x <;> simp [h]

lemma wt_nonneg {n : ℕ} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Cube n) : 0 ≤ wt p x :=
  Finset.prod_nonneg (fun j _ => by
    simp only [FriedgutCoalition.bern]; split_ifs <;> linarith)

lemma error_triangle {n : ℕ} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (f u g : Cube n → Bool) :
    error p f g ≤ error p f u + error p u g := by
  unfold error
  rw [prob_eq, prob_eq, prob_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hw := wt_nonneg p h0 h1 x
  by_cases h : f x = g x
  · simp only [h, ne_eq, not_true_eq_false, if_false]
    split_ifs <;> linarith
  · by_cases h2 : f x = u x
    · have : u x ≠ g x := by rw [← h2]; exact h
      simp [h, h2, this]
    · simp [h, h2]
      split_ifs <;> linarith

lemma force_inc {n : ℕ} (J : ActivationFamily n) (D : Finset (Fin n))
    (hJ : IncreasingActivations J) : IncreasingActivations (force J D) := by
  intro S z1 z2 h
  unfold force
  apply hJ S
  intro i
  by_cases hi : (i : Fin n) ∈ D
  · simp [hi]
  · simp only [hi, if_false]; exact h i

lemma arityLE_of {n : ℕ} (J : ActivationFamily n) (d : ℕ) (h : arity J ≤ d) : ArityLE J d := by
  intro S hS z
  by_contra hz
  have hz' : J S z = true := by simpa using hz
  have : S.card ≤ arity J := by
    unfold arity
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, z, hz'⟩)
  omega

lemma two_pow_le (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp d := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  calc (2 : ℝ) ^ d ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) h2 d
    _ = Real.exp d := by rw [← Real.exp_nat_mul]; simp

lemma est (ε M Cf : ℝ) (d : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) (hM : 1 ≤ M) (hCf0 : 0 ≤ Cf)
    (hCf : Cf ≤ M) (hd : (d : ℝ) ≤ 1000 * Cf / (ε / 4) + 1) :
    ((⌈4 * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) / ε⌉₊ : ℕ) : ℝ)
      ≤ Real.exp (10 ^ 12 * M ^ 2 / ε ^ 2) := by
  set t : ℝ := M ^ 2 / ε ^ 2 with ht
  have hε2 : 0 < ε ^ 2 := by positivity
  have hinv : 1 ≤ ε⁻¹ := by
    rw [one_le_inv_iff₀]; exact ⟨hε0, hε1.le⟩
  have hMe : 1 ≤ M / ε := by
    rw [le_div_iff₀ hε0]; linarith
  have ht1 : M / ε ≤ t := by
    rw [ht, ← div_pow] at *
    nlinarith
  have ht1' : 1 ≤ t := le_trans hMe ht1
  have hεt : ε⁻¹ ≤ t := by
    have : ε⁻¹ ≤ M / ε := by rw [div_eq_mul_inv]; nlinarith
    linarith
  -- 2^d
  have hd1 : (d : ℝ) ≤ 4001 * t := by
    have : 1000 * Cf / (ε / 4) = 4000 * (Cf / ε) := by field_simp; ring
    have h3 : Cf / ε ≤ M / ε := div_le_div_of_nonneg_right hCf hε0.le
    nlinarith
  have h2d : (2 : ℝ) ^ d ≤ Real.exp (4001 * t) :=
    (two_pow_le d).trans (Real.exp_le_exp.2 hd1)
  -- L
  have hL : Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) ≤ Real.exp (16 * 10 ^ 10 * t) := by
    apply Real.exp_le_exp.2
    have : ((ε / 4)⁻¹) ^ 2 = 16 / ε ^ 2 := by field_simp; ring
    rw [this]
    have h4 : Cf ^ 2 / ε ^ 2 ≤ t := by
      rw [ht]; exact div_le_div_of_nonneg_right (by nlinarith) hε2.le
    have : (10 : ℝ) ^ 10 * (16 / ε ^ 2) * Cf ^ 2 = 16 * 10 ^ 10 * (Cf ^ 2 / ε ^ 2) := by ring
    rw [this]; nlinarith
  -- 4/ε
  have he1 : (1 : ℝ) ≤ Real.exp t := by
    have := Real.add_one_le_exp t; linarith
  have h4e : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h4t : 4 / ε ≤ Real.exp (3 * t) := by
    have h1 : t ≤ Real.exp t := by have := Real.add_one_le_exp t; linarith
    calc 4 / ε = 4 * ε⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.exp 2 * Real.exp t := by
          apply mul_le_mul h4e (by linarith) (by positivity) (by positivity)
      _ = Real.exp (2 + t) := by rw [Real.exp_add]
      _ ≤ Real.exp (3 * t) := Real.exp_le_exp.2 (by linarith)
  -- combine
  have hX : 4 * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) / ε
      ≤ Real.exp ((3 + 4001 + 16 * 10 ^ 10) * t) := by
    calc 4 * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) / ε
        = (4 / ε) * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) := by ring
      _ ≤ Real.exp (3 * t) * Real.exp (4001 * t) * Real.exp (16 * 10 ^ 10 * t) := by
          apply mul_le_mul (mul_le_mul h4t h2d (by positivity) (by positivity)) hL
            (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hX1 : 1 ≤ 4 * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) / ε := by
    have h1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) :=
      Real.one_le_exp (by positivity)
    rw [le_div_iff₀ hε0]
    nlinarith
  set X := 4 * 2 ^ d * Real.exp ((10 : ℝ) ^ 10 * ((ε / 4)⁻¹) ^ 2 * Cf ^ 2) / ε with hXdef
  have hw : ((⌈X⌉₊ : ℕ) : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  calc ((⌈X⌉₊ : ℕ) : ℝ) ≤ X + 1 := hw
    _ ≤ Real.exp t * X := by
        have : (2 : ℝ) ≤ Real.exp t := by
          have := Real.add_one_le_exp t; linarith
        nlinarith
    _ ≤ Real.exp t * Real.exp ((3 + 4001 + 16 * 10 ^ 10) * t) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = Real.exp ((1 + (3 + 4001 + 16 * 10 ^ 10)) * t) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (10 ^ 12 * M ^ 2 / ε ^ 2) := by
        apply Real.exp_le_exp.2
        have : (10 : ℝ) ^ 12 * M ^ 2 / ε ^ 2 = 10 ^ 12 * t := by rw [ht]; ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        norm_num

end NarrowDNF.Dev.T12

namespace NarrowDNF.Approx
open NarrowDNF.Dev.T12 in
theorem chk_theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ K : ℝ, 0 < K →
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : Cube n → Bool, Monotone f → FriedgutCoalition.totalPInfl p f ≤ K →
      ∃ g : DNF n, (width g : ℝ) ≤ Real.exp (C * (K + 1) ^ 2 / ε ^ 2) ∧
        error p f (evalDNF g) ≤ ε := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro n _ K hK p hp hp_half ε hε hε1 f hf hinfl
  have hp1 : p < 1 := by linarith
  have ha : 0 < ε / 4 := by positivity
  have ha1 : ε / 4 ≤ 1 := by linarith
  have h21 := lemma_2_1 (n := n) p (ε / 4) f hp hp_half ha ha1
  dsimp only at h21
  obtain ⟨J, h, hJ, herr, hmeas, har, hload⟩ := h21
  set Cf : ℕ := ⌈FriedgutCoalition.totalPInfl p f⌉₊ with hCfdef
  set d : ℕ := ⌈(10 : ℝ) ^ 3 * (Cf : ℝ) / (ε / 4)⌉₊ with hddef
  set L : ℝ := Real.exp ((10 : ℝ) ^ 10 * (ε / 4)⁻¹ ^ 2 * (Cf : ℝ) ^ 2) with hLdef
  have hL0 : 0 < L := Real.exp_pos _
  have hCfK : (Cf : ℝ) ≤ K + 1 := by
    have h1 : Cf ≤ ⌈K⌉₊ := Nat.ceil_mono hinfl
    have h2 : (⌈K⌉₊ : ℝ) < K + 1 := Nat.ceil_lt_add_one hK.le
    have h3 : (Cf : ℝ) ≤ (⌈K⌉₊ : ℝ) := by exact_mod_cast h1
    linarith
  have hd_le : (d : ℝ) ≤ 1000 * (Cf : ℝ) / (ε / 4) + 1 := by
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (10 : ℝ) ^ 3 * (Cf : ℝ) / (ε / 4) by positivity)).le
    have e : (10 : ℝ) ^ 3 * (Cf : ℝ) = 1000 * (Cf : ℝ) := by norm_num
    have h' : (d : ℝ) ≤ (10 : ℝ) ^ 3 * (Cf : ℝ) / (ε / 4) + 1 := this
    rw [e] at h'
    exact h'
  obtain ⟨D, u, hum, humeas, hue, hcost⟩ := theorem_3_5 (n := n) p d (ε / 4) L f J h hp hp1
    ha.le hL0.le hf hJ hmeas (arityLE_of J d har) herr hload (ε / 4) ha
  have hcost' : activeCost p (force J D) ≤ 2 * (2 ^ d * L) := by
    have h1 : (1 : ℝ) + (ε / 4) / (ε / 4) = 2 := by rw [div_self ha.ne']; norm_num
    rw [h1] at hcost
    have h2 : (2 - p) ^ d ≤ (2 : ℝ) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
    nlinarith [mul_le_mul_of_nonneg_right h2 hL0.le]
  obtain ⟨_, hw⟩ := lemma_4_1 p (force J D) u hp hp1 (force_inc J D hJ) hum humeas
  set w : ℕ := ⌈4 * 2 ^ d * L / ε⌉₊ with hwdef
  obtain ⟨hwidth, _, _, herr2, hmark⟩ := hw w
  refine ⟨truncatedDNF (force J D) u w, ?_, ?_⟩
  · have h1 : ((width (truncatedDNF (force J D) u w) : ℕ) : ℝ) ≤ (w : ℝ) := by exact_mod_cast hwidth
    refine h1.trans ?_
    exact est ε (K + 1) Cf d hε hε1 (by linarith) (Nat.cast_nonneg _) hCfK hd_le
  · have htri := error_triangle p hp.le hp1.le f u (evalDNF (truncatedDNF (force J D) u w))
    have hwpos : (0 : ℝ) < (w : ℝ) + 1 := by positivity
    have hwge : 4 * 2 ^ d * L / ε ≤ (w : ℝ) := Nat.le_ceil _
    have h3 : activeCost p (force J D) / ((w : ℝ) + 1) ≤ ε / 2 := by
      rw [div_le_iff₀ hwpos]
      have : 4 * 2 ^ d * L ≤ ε * ((w : ℝ) + 1) := by
        rw [div_le_iff₀ hε] at hwge; nlinarith
      nlinarith
    linarith

end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_theorem_1_2 := @NarrowDNF.Approx.chk_theorem_1_2
