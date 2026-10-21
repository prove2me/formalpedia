-- Prove2me | solution 1 for NetPriceDisc.Random.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:34:30.604008+00:00
-- url     : https://prove2.me/submissions/ec589482-1da7-4938-9273-e10f22013e61

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
import Theorems.Thm_NetPriceDisc_Random_eq_29
import Theorems.Thm_NetPriceDisc_Random_lemma_5_2
import Theorems.Thm_NetPriceDisc_Random_footnote_6
import Theorems.Thm_NetPriceDisc_Random_eq_14
import Theorems.Thm_NetPriceDisc_Random_theorem_5_1_moderate
import Theorems.Thm_NetPriceDisc_Random_theorem_5_1_dense
open Matrix

namespace NetPriceDisc.Random.PDRAux
open NetPriceDisc.Random

lemma wt_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset (Fin n × Fin n)) :
    0 ≤ q ^ S.card * (1 - q) ^ ((Finset.univ : Finset (Fin n)).offDiag.card - S.card) := by
  have : 0 ≤ 1 - q := by linarith
  positivity

lemma erExpect_mono {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {F H : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset, F (adjOf S) ≤ H (adjOf S)) :
    erExpect n q F ≤ erExpect n q H := by
  unfold erExpect
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S hS) (wt_nonneg hq0 hq1 S)

lemma erExpect_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset, 0 ≤ F (adjOf S)) :
    0 ≤ erExpect n q F := by
  unfold erExpect
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (wt_nonneg hq0 hq1 S) (h S hS)

lemma erExpect_add {n : ℕ} {q : ℝ} (F H : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => F G + H G) = erExpect n q F + erExpect n q H := by
  unfold erExpect; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro S _; ring

lemma erExpect_const_mul {n : ℕ} {q : ℝ} (c : ℝ) (F : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => c * F G) = c * erExpect n q F := by
  unfold erExpect; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _; ring

lemma adjOf_nonneg {n : ℕ} (S : Finset (Fin n × Fin n)) : ∀ i j, 0 ≤ adjOf S i j := by
  intro i j; unfold adjOf; split_ifs <;> norm_num

lemma adjOf_bin {n : ℕ} (S : Finset (Fin n × Fin n)) : ∀ i j, adjOf S i j = 0 ∨ adjOf S i j = 1 := by
  intro i j; unfold adjOf; split_ifs <;> simp

lemma adjOf_diag {n : ℕ} (S : Finset (Fin n × Fin n))
    (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) : ∀ i, adjOf S i i = 0 := by
  intro i; unfold adjOf
  have : (i, i) ∉ S := by
    intro h; have := hS h; simp at this
  simp [this]

lemma adjOf_ne_zero {n : ℕ} (S : Finset (Fin n × Fin n)) (hS : S.Nonempty) : adjOf S ≠ 0 := by
  obtain ⟨⟨i, j⟩, h⟩ := hS
  intro h0
  have := congrFun (congrFun h0 i) j
  simp [adjOf, h] at this

lemma adjOf_empty {n : ℕ} : adjOf (∅ : Finset (Fin n × Fin n)) = 0 := by
  ext i j; simp [adjOf]

lemma pow_entries_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hA l j))

lemma walks_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    0 ≤ walks A k := by
  unfold walks
  apply Finset.sum_nonneg; intro i _
  simp only [ones, one_mul, mulVec, dotProduct, mul_one]
  apply Finset.sum_nonneg; intro j _
  exact pow_entries_nonneg A hA k i j

lemma walks_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    walks (c • A) k = c ^ k * walks A k := by
  unfold walks
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma sym_nonneg {n : ℕ} (S : Finset (Fin n × Fin n)) :
    ∀ i j, 0 ≤ (adjOf S + (adjOf S)ᵀ) i j := by
  intro i j
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  exact add_nonneg (adjOf_nonneg S i j) (adjOf_nonneg S j i)

end NetPriceDisc.Random.PDRAux

namespace NetPriceDisc.Random.PDRMain
open NetPriceDisc.Random NetPriceDisc.Random.PDRAux

lemma pointwise_sparse {n : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (S : Finset (Fin n × Fin n)) (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    ρ ^ 2 / (1 - ρ) * (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 *
        walks (adjOf S + (adjOf S)ᵀ) 2 ≤
      ρ ^ 2 / (1 - ρ) * walks (adjOf S + (adjOf S)ᵀ) 2 := by
  have hC : 0 ≤ ρ ^ 2 / (1 - ρ) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hw := walks_nonneg _ (sym_nonneg S) 2
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  rcases S.eq_empty_or_nonempty with h0 | hne
  · subst h0
    rw [adjOf_empty]
    simp [walks]
  · have h6 := footnote_6 (adjOf S) (adjOf_bin S) (adjOf_diag S hS) (adjOf_ne_zero S hne)
    have : (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow]
      rw [div_le_one (by positivity)]
      nlinarith
    calc (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 * walks (adjOf S + (adjOf S)ᵀ) 2
        ≤ 1 * walks (adjOf S + (adjOf S)ᵀ) 2 := mul_le_mul_of_nonneg_right this hw
      _ = _ := one_mul _

lemma walks2_bound (n : ℕ) (q X : ℝ) (hn1 : 1 ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hX0 : 0 ≤ X)
    (hxX : (n:ℝ) * q ≤ X) :
    erExpect n q (fun G => walks (G + Gᵀ) 2) ≤ n * (2 * X * (1 + 2 * X)) := by
  rw [lemma_5_2 n q hq0 hq1]
  have hn1r : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have ha1 : 0 ≤ ((n:ℝ) - 1) * q := mul_nonneg (by linarith) hq0
  have ha2 : ((n:ℝ) - 1) * q ≤ X := by
    have : ((n:ℝ) - 1) * q = n * q - q := by ring
    linarith
  have key : (((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q) ≤ X * (1 + 2 * X) := by
    rcases le_or_gt 0 (1 - 3 * q + 2 * (n:ℝ) * q) with hs | hs
    · have hb2 : 1 - 3 * q + 2 * (n:ℝ) * q ≤ 1 + 2 * X := by
        have : 2 * (n:ℝ) * q = 2 * ((n:ℝ) * q) := by ring
        linarith
      exact mul_le_mul ha2 hb2 hs hX0
    · have : (((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha1 hs.le
      have : 0 ≤ X * (1 + 2 * X) := by positivity
      linarith
  calc 2 * (n:ℝ) * ((n:ℝ) - 1) * q * (1 - 3 * q + 2 * (n:ℝ) * q)
      = (2 * (n:ℝ)) * ((((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q)) := by ring
    _ ≤ (2 * (n:ℝ)) * (X * (1 + 2 * X)) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = n * (2 * X * (1 + 2 * X)) := by ring

/-- pointwise facts on regret and fractional regret -/
lemma regret_facts (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (hn : 1 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    0 ≤ regret a c ρ G ∧ 0 ≤ fracRegret a c ρ G ∧
      fracRegret a c ρ G ≤ (1 / ((n:ℝ) * (1 / 2 * ((a - c) / 2) ^ 2))) * regret a c ρ G := by
  have h14 := (eq_14 a c ρ ha hca hρ0 hρ1 G hG).1
  have hC1 : 0 < 1 / 2 * ((a - c) / 2) ^ 2 := by
    have : 0 < a - c := by linarith
    positivity
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : 0 < (n:ℝ) * (1 / 2 * ((a - c) / 2) ^ 2) := mul_pos hnpos hC1
  have h14' : (n:ℝ) * (1 / 2 * ((a - c) / 2) ^ 2) ≤ optProfit a c ρ G := by
    have : (n:ℝ) / 2 * ((a - c) / 2) ^ 2 = (n:ℝ) * (1 / 2 * ((a - c) / 2) ^ 2) := by ring
    linarith
  have hopt : 0 < optProfit a c ρ G := lt_of_lt_of_le hnC h14'
  have hbdd : BddAbove (Set.range (profit a c ρ G)) := by
    by_contra hb
    have := Real.sSup_of_not_bddAbove hb
    unfold optProfit at hopt
    rw [this] at hopt
    exact lt_irrefl _ hopt
  have hle : profit a c ρ G (uniformPrice n a c) ≤ optProfit a c ρ G :=
    le_csSup hbdd ⟨_, rfl⟩
  have hR : 0 ≤ regret a c ρ G := by unfold regret; linarith
  have hF : fracRegret a c ρ G = regret a c ρ G / optProfit a c ρ G := by
    unfold fracRegret regret; field_simp
  refine ⟨hR, ?_, ?_⟩
  · rw [hF]; positivity
  · rw [hF, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left hR hnC h14'

end NetPriceDisc.Random.PDRMain

open NetPriceDisc.Random NetPriceDisc.Random.PDRAux NetPriceDisc.Random.PDRMain in
theorem solution (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) :
    (fun n : ℕ => erExpect n (p n) (regret a c ρ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      Filter.Tendsto (fun n : ℕ => erExpect n (p n) (fracRegret a c ρ)) Filter.atTop (nhds 0) := by
  set C1 : ℝ := 1 / 2 * ((a - c) / 2) ^ 2 with hC1
  set C' : ℝ := ρ ^ 2 / (1 - ρ) with hC'
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC1p : 0 < C1 := by
    have : 0 < a - c := by linarith
    positivity
  have hC'p : 0 < C' := by positivity
  set B := C1 * C' with hB
  have hBp : 0 < B := mul_pos hC1p hC'p
  -- expected regret is nonnegative for n ≥ 1
  have hRnn : ∀ n : ℕ, 1 ≤ n → 0 ≤ erExpect n (p n) (regret a c ρ) := by
    intro n hn
    exact erExpect_nonneg (hp n).1 (hp n).2
      (fun S _ => (regret_facts a c ρ ha hca hρ0 hρ1 hn (adjOf S) (adjOf_nonneg S)).1)
  have hlittle : (fun n : ℕ => erExpect n (p n) (regret a c ρ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨M, N1, hdense⟩ := theorem_5_1_dense a c ρ ha hca hρ0 hρ1 ε hε
    set δ0 := min 1 (ε / (6 * B)) with hδ0
    have hδ0p : 0 < δ0 := lt_min one_pos (by positivity)
    have hδ01 : δ0 ≤ 1 := min_le_left _ _
    have hδ0e : δ0 ≤ ε / (6 * B) := min_le_right _ _
    obtain ⟨N2, hmod⟩ := theorem_5_1_moderate a c ρ ha hca hρ0 hρ1 δ0 M ε hδ0p hε
    rw [Filter.eventually_atTop]
    refine ⟨max (max N1 N2) 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    obtain ⟨hq0, hq1⟩ := hp n
    have hE0 := hRnn n hn1
    rw [Real.norm_of_nonneg hE0, Real.norm_of_nonneg hnpos.le]
    rcases le_total ((n:ℝ) * p n) δ0 with hs | hs
    · -- sparse regime
      have h29 := eq_29 a c ρ ha hca hρ0 hρ1 n (p n) hq0 hq1
      have h2 : erExpect n (p n) (fun G => ρ ^ 2 / (1 - ρ) * (1 / specNorm (G + Gᵀ)) ^ 2 *
          walks (G + Gᵀ) 2) ≤ C' * erExpect n (p n) (fun G => walks (G + Gᵀ) 2) := by
        rw [← erExpect_const_mul]
        apply erExpect_mono hq0 hq1
        intro S hS
        exact pointwise_sparse ρ hρ0 hρ1 S (Finset.mem_powerset.1 hS)
      have h3 := walks2_bound n (p n) δ0 hn1 hq0 hq1 hδ0p.le hs
      have h4 : B * (2 * δ0 * (1 + 2 * δ0)) ≤ ε := by
        have : 2 * δ0 * (1 + 2 * δ0) ≤ 6 * δ0 := by nlinarith
        have h5 : B * (6 * δ0) ≤ ε := by
          have := mul_le_mul_of_nonneg_left hδ0e (by positivity : (0:ℝ) ≤ 6 * B)
          rw [mul_div_cancel₀ _ (by positivity : (6 * B) ≠ 0)] at this
          linarith
        nlinarith
      calc erExpect n (p n) (regret a c ρ)
          ≤ C1 * erExpect n (p n) (fun G => ρ ^ 2 / (1 - ρ) * (1 / specNorm (G + Gᵀ)) ^ 2 *
            walks (G + Gᵀ) 2) := h29
        _ ≤ C1 * (C' * (n * (2 * δ0 * (1 + 2 * δ0)))) := by
            apply mul_le_mul_of_nonneg_left _ hC1p.le
            exact le_trans h2 (mul_le_mul_of_nonneg_left h3 hC'p.le)
        _ = n * (B * (2 * δ0 * (1 + 2 * δ0))) := by rw [hB]; ring
        _ ≤ n * ε := mul_le_mul_of_nonneg_left h4 hnpos.le
        _ = ε * n := by ring
    · rcases le_total ((n:ℝ) * p n) M with hs2 | hs2
      · exact hmod n hnN2 (p n) hq0 hq1 hs hs2
      · exact hdense n hnN1 (p n) hq0 hq1 hs2
  refine ⟨hlittle, ?_⟩
  -- fractional regret
  have hdiv := hlittle.tendsto_div_nhds_zero
  have hdiv2 : Filter.Tendsto (fun n : ℕ => (1 / C1) * (erExpect n (p n) (regret a c ρ) / n))
      Filter.atTop (nhds 0) := by
    have := hdiv.const_mul (1 / C1)
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv2
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    exact erExpect_nonneg (hp n).1 (hp n).2
      (fun S _ => (regret_facts a c ρ ha hca hρ0 hρ1 hn (adjOf S) (adjOf_nonneg S)).2.1)
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have := erExpect_mono (hp n).1 (hp n).2 (F := fracRegret a c ρ)
      (H := fun G => (1 / ((n:ℝ) * C1)) * regret a c ρ G)
      (fun S _ => (regret_facts a c ρ ha hca hρ0 hρ1 hn (adjOf S) (adjOf_nonneg S)).2.2)
    rw [erExpect_const_mul] at this
    calc erExpect n (p n) (fracRegret a c ρ) ≤ 1 / (↑n * C1) * erExpect n (p n) (regret a c ρ) :=
          this
      _ = (1 / C1) * (erExpect n (p n) (regret a c ρ) / n) := by field_simp
