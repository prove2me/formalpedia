-- Prove2me | solution 1 for NetPriceDisc.Random.theorem_5_1_moderate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:34:29.600996+00:00
-- url     : https://prove2.me/submissions/0e2e5a2d-f865-41bc-ab5c-7c7aca8e821f

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
import Theorems.Thm_NetPriceDisc_Random_eq_29
import Theorems.Thm_NetPriceDisc_Random_eq_9
import Theorems.Thm_NetPriceDisc_Random_lemma_5_2
open Matrix
open scoped Matrix.Norms.L2Operator

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

lemma rowcard_le_specNorm_sq {n : ℕ} (S : Finset (Fin n × Fin n)) (i : Fin n) :
    ((Finset.univ.filter (fun j => (i, j) ∈ S)).card : ℝ) ≤
      specNorm (adjOf S + (adjOf S)ᵀ) ^ 2 := by
  set A := adjOf S + (adjOf S)ᵀ with hA
  have h1 := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single i (1:ℝ))
  have hn : ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by simp
  rw [hn, mul_one] at h1
  have h2 := EuclideanSpace.norm_sq_eq ((EuclideanSpace.equiv (Fin n) ℝ).symm
      (A *ᵥ (EuclideanSpace.single i (1:ℝ))))
  simp at h1 h2
  have hlam : 0 ≤ ‖WithLp.toLp 2 (A.col i)‖ := norm_nonneg _
  have h3 : ‖WithLp.toLp 2 (A.col i)‖ ^ 2 ≤ specNorm A ^ 2 := by
    unfold specNorm; exact pow_le_pow_left₀ hlam h1 2
  refine le_trans ?_ (h2 ▸ h3)
  have h4 : ((Finset.univ.filter (fun j => (i, j) ∈ S)).card : ℝ) = ∑ j, adjOf S i j := by
    simp [adjOf, Finset.sum_boole]
  rw [h4]
  apply Finset.sum_le_sum
  intro j _
  simp only [hA, Matrix.add_apply, Matrix.transpose_apply, adjOf]
  split_ifs <;> norm_num



/-- row set -/
def rowSet {n : ℕ} (S : Finset (Fin n × Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (i, j) ∈ S)

lemma card_eq_sum_rowSet {n : ℕ} (S : Finset (Fin n × Fin n)) :
    S.card = ∑ i, (rowSet S i).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_nbij' (fun p => p.2) (fun j => (i, j))
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    simp only [rowSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    obtain ⟨h1, h2⟩ := hp
    rw [← h2]; exact h1
  · intro j hj
    simp only [rowSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨hj, trivial⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    ext <;> simp [hp.2]
  · intro j _; rfl

lemma rowSet_sub {n : ℕ} (S : Finset (Fin n × Fin n))
    (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) (i : Fin n) :
    rowSet S i ⊆ Finset.univ.erase i := by
  intro j hj
  simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have := hS hj
  simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at this
  exact Finset.mem_erase.2 ⟨Ne.symm this, Finset.mem_univ _⟩

lemma erExpect_rowProd {n : ℕ} (q : ℝ) (f : ℕ → ℝ) :
    erExpect n q (fun G => ∏ i, f ((Finset.univ.filter (fun j => G i j = 1)).card)) =
      ∏ i : Fin n, ∑ U ∈ (Finset.univ.erase i).powerset,
        q ^ U.card * (1 - q) ^ ((Finset.univ.erase i).card - U.card) * f U.card := by
  classical
  rw [Finset.prod_univ_sum]
  unfold erExpect
  apply Finset.sum_nbij' (fun S => fun i => rowSet S i)
    (fun x => (Finset.univ : Finset (Fin n)).offDiag.filter (fun p => p.2 ∈ x p.1))
  · intro S hS
    rw [Finset.mem_powerset] at hS
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_powerset.2 (rowSet_sub S hS i)
  · intro x hx
    rw [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  · intro S hS
    rw [Finset.mem_powerset] at hS
    ext p
    simp only [Finset.mem_filter, rowSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hS h, h⟩
  · intro x hx
    rw [Fintype.mem_piFinset] at hx
    funext i
    ext j
    simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      have := Finset.mem_powerset.1 (hx i) h
      exact ⟨Ne.symm (Finset.ne_of_mem_erase this), h⟩
  · intro S hS
    rw [Finset.mem_powerset] at hS
    have hrow : ∀ i, (Finset.univ.filter (fun j => adjOf S i j = 1)) = rowSet S i := by
      intro i; ext j; simp [adjOf, rowSet]
    simp only [hrow]
    show _ = ∏ i, q ^ (rowSet S i).card * (1 - q) ^ ((Finset.univ.erase i).card - (rowSet S i).card) * f (rowSet S i).card
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (rowSet S i).card ≤
        (Finset.univ.erase i).card := fun i _ => Finset.card_le_card (rowSet_sub S hS i)
    have hcardE : ∀ i : Fin n, (Finset.univ.erase i).card = n - 1 := by
      intro i; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hT : (Finset.univ : Finset (Fin n)).offDiag.card - S.card =
        ∑ i, ((Finset.univ.erase i).card - (rowSet S i).card) := by
      rw [Finset.sum_tsub_distrib _ hle, ← card_eq_sum_rowSet, Finset.offDiag_card]
      simp [hcardE]
      congr 1
      rcases n with _ | n
      · simp
      · rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_comm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum, ← card_eq_sum_rowSet, ← hT]



lemma row_factor_le {α : Type*} (s : Finset α) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) * (if U.card < K then (1:ℝ) else 0)
      ≤ Real.exp (-((s.card.choose K : ℝ) * q ^ K * (1 - q) ^ (s.card - K))) := by
  have h1q : 0 ≤ 1 - q := by linarith
  set η := (s.card.choose K : ℝ) * q ^ K * (1 - q) ^ (s.card - K)
  have htot : ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) = 1 := by
    rw [Finset.sum_pow_mul_eq_add_pow]; simp
  have hsplit : ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) *
      (if U.card < K then (1:ℝ) else 0) = 1 - ∑ U ∈ s.powerset, q ^ U.card *
      (1 - q) ^ (s.card - U.card) * (if U.card < K then (0:ℝ) else 1) := by
    have : ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) *
        (if U.card < K then (1:ℝ) else 0) + ∑ U ∈ s.powerset, q ^ U.card *
        (1 - q) ^ (s.card - U.card) * (if U.card < K then (0:ℝ) else 1) =
        ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro U _; split_ifs <;> ring
    linarith
  have hge : η ≤ ∑ U ∈ s.powerset, q ^ U.card *
      (1 - q) ^ (s.card - U.card) * (if U.card < K then (0:ℝ) else 1) := by
    have hsub : Finset.powersetCard K s ⊆ s.powerset := fun U hU => Finset.mem_powerset.2 (Finset.mem_powersetCard.1 hU).1
    calc η = ∑ U ∈ Finset.powersetCard K s, q ^ U.card *
          (1 - q) ^ (s.card - U.card) * (if U.card < K then (0:ℝ) else 1) := by
            rw [Finset.sum_congr rfl (g := fun _ => q ^ K * (1 - q) ^ (s.card - K))]
            · rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]; ring
            · intro U hU
              rw [(Finset.mem_powersetCard.1 hU).2]; simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
            intro U _ _; split_ifs <;> positivity)
  rw [hsplit]
  have := Real.add_one_le_exp (-η)
  linarith

lemma row_factor_nonneg {α : Type*} (s : Finset α) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    0 ≤ ∑ U ∈ s.powerset, q ^ U.card * (1 - q) ^ (s.card - U.card) *
      (if U.card < K then (1:ℝ) else 0) := by
  have h1q : 0 ≤ 1 - q := by linarith
  apply Finset.sum_nonneg; intro U _; split_ifs <;> positivity

/-- lower bound for η in the moderate regime -/
lemma eta_lower (n K : ℕ) (q δ M : ℝ) (hK : 2 * K ≤ n) (hn : 1 ≤ n) (hq0 : 0 ≤ q)
    (hδ : 0 < δ) (hδq : δ ≤ n * q) (hqM : n * q ≤ M) (hq2 : q ≤ 1 / 2) :
    (δ / 2) ^ K / K.factorial * Real.exp (-(2 * M)) ≤
      ((n - 1).choose K : ℝ) * q ^ K * (1 - q) ^ (n - 1 - K) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hch := Nat.pow_le_choose (α := ℝ) K (n - 1)
  have hcast : ((n - 1 + 1 - K : ℕ) : ℝ) ≥ n / 2 := by
    have : n - 1 + 1 - K = n - K := by omega
    rw [this, Nat.cast_sub (by omega)]
    have : (2 * K : ℝ) ≤ n := by exact_mod_cast hK
    linarith
  -- q ≥ δ / n
  have hqδ : δ / n ≤ q := by rw [div_le_iff₀ hnpos]; linarith
  have hA : (δ / 2) ^ K / K.factorial ≤ ((n - 1).choose K : ℝ) * q ^ K := by
    calc (δ / 2) ^ K / K.factorial = ((n:ℝ) / 2) ^ K / K.factorial * (δ / n) ^ K := by
          rw [div_pow, div_pow, div_pow]; field_simp
      _ ≤ ((n - 1 + 1 - K : ℕ) : ℝ) ^ K / K.factorial * q ^ K := by
          apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) hqδ K) (by positivity) (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hcast K
      _ ≤ ((n - 1).choose K : ℝ) * q ^ K := by
          apply mul_le_mul_of_nonneg_right hch (by positivity)
  have hB : Real.exp (-(2 * M)) ≤ (1 - q) ^ (n - 1 - K) := by
    have h1q : 0 < 1 - q := by linarith
    have hlog : -(2 * q) ≤ Real.log (1 - q) := by
      have := Real.one_sub_inv_le_log_of_pos h1q
      have h2 : -(2 * q) ≤ 1 - (1 - q)⁻¹ := by
        rw [show 1 - (1 - q)⁻¹ = -(q / (1 - q)) by field_simp; ring]
        rw [neg_le_neg_iff, div_le_iff₀ h1q]; nlinarith
      linarith
    calc Real.exp (-(2 * M)) ≤ Real.exp (n * Real.log (1 - q)) := by
          apply Real.exp_le_exp.2; nlinarith
      _ = (1 - q) ^ n := by rw [Real.exp_nat_mul, Real.exp_log h1q]
      _ ≤ (1 - q) ^ (n - 1 - K) := pow_le_pow_of_le_one h1q.le (by linarith) (by omega)
  calc (δ / 2) ^ K / K.factorial * Real.exp (-(2 * M)) ≤
      (((n - 1).choose K : ℝ) * q ^ K) * (1 - q) ^ (n - 1 - K) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring

/-- bad event indicator: every row has fewer than `K` arcs. -/
noncomputable def badInd {n : ℕ} (K : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ i, (fun r : ℕ => if r < K then (1:ℝ) else 0) ((Finset.univ.filter (fun j => G i j = 1)).card)

lemma badInd_nonneg {n : ℕ} (K : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ badInd K G := by
  unfold badInd; apply Finset.prod_nonneg; intro i _; dsimp only; split_ifs <;> norm_num

lemma pointwise_mod {n : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (K : ℕ) (hK : 1 ≤ K)
    (S : Finset (Fin n × Fin n)) (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    ρ ^ 2 / (1 - ρ) * (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 *
        walks (adjOf S + (adjOf S)ᵀ) 2 ≤
      ρ ^ 2 / (1 - ρ) * ((1 / (K:ℝ)) * walks (adjOf S + (adjOf S)ᵀ) 2 +
        (n:ℝ) * badInd K (adjOf S)) := by
  have hC : 0 ≤ ρ ^ 2 / (1 - ρ) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hw := walks_nonneg _ (sym_nonneg S) 2
  have hb := badInd_nonneg K (adjOf S)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  rcases S.eq_empty_or_nonempty with h0 | hne
  · subst h0
    rw [adjOf_empty]
    simp [walks]
    positivity
  · have hG0 := adjOf_ne_zero S hne
    have h9 := (eq_9 (adjOf S) (adjOf_nonneg S) hG0 2 (by norm_num)).2
    rw [walks_smul] at h9
    by_cases hall : ∀ i, (Finset.univ.filter (fun j => adjOf S i j = 1)).card < K
    · have : badInd K (adjOf S) = 1 := by
        unfold badInd; apply Finset.prod_eq_one; intro i _; simp [hall i]
      rw [this]
      have : 0 ≤ (1 / (K:ℝ)) * walks (adjOf S + (adjOf S)ᵀ) 2 := by positivity
      linarith
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hrow : (Finset.univ.filter (fun j => adjOf S i j = 1)) =
          Finset.univ.filter (fun j => (i, j) ∈ S) := by
        ext j; simp [adjOf]
      rw [hrow] at hi
      have hsp := rowcard_le_specNorm_sq S i
      have hKle : (K:ℝ) ≤ specNorm (adjOf S + (adjOf S)ᵀ) ^ 2 :=
        le_trans (by exact_mod_cast hi) hsp
      have hsp2 : 0 < specNorm (adjOf S + (adjOf S)ᵀ) ^ 2 := lt_of_lt_of_le hKpos hKle
      have : (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 ≤ 1 / (K:ℝ) := by
        rw [div_pow, one_pow]
        exact one_div_le_one_div_of_le hKpos hKle
      have h2 : (1 / specNorm (adjOf S + (adjOf S)ᵀ)) ^ 2 * walks (adjOf S + (adjOf S)ᵀ) 2 ≤
          1 / (K:ℝ) * walks (adjOf S + (adjOf S)ᵀ) 2 := mul_le_mul_of_nonneg_right this hw
      have : 0 ≤ (n:ℝ) * badInd K (adjOf S) := by positivity
      linarith

lemma erExpect_badInd {n : ℕ} (q : ℝ) (K : ℕ) :
    erExpect n q (badInd K) = ∏ i : Fin n, ∑ U ∈ (Finset.univ.erase i).powerset,
        q ^ U.card * (1 - q) ^ ((Finset.univ.erase i).card - U.card) *
          (fun r : ℕ => if r < K then (1:ℝ) else 0) U.card := by
  have h : badInd (n := n) K = fun G => ∏ i, (fun r : ℕ => if r < K then (1:ℝ) else 0)
      ((Finset.univ.filter (fun j => G i j = 1)).card) := by
    funext G; rfl
  rw [h]
  exact erExpect_rowProd q (fun r : ℕ => if r < K then (1:ℝ) else 0)

end NetPriceDisc.Random.PDRAux

open NetPriceDisc.Random NetPriceDisc.Random.PDRAux in
theorem solution (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (δ M ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 → δ ≤ (n : ℝ) * q → (n : ℝ) * q ≤ M →
      erExpect n q (regret a c ρ) ≤ ε * n := by
  set C1 : ℝ := 1 / 2 * ((a - c) / 2) ^ 2 with hC1
  set C' : ℝ := ρ ^ 2 / (1 - ρ) with hC'
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC1p : 0 < C1 := by
    have : 0 < a - c := by linarith
    positivity
  have hC'p : 0 < C' := by positivity
  set B := C1 * C' with hB
  have hBp : 0 < B := mul_pos hC1p hC'p
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set K : ℕ := ⌈4 * B * M' * (1 + 2 * M') / ε⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK1
  have hKbig : B * (2 * M' * (1 + 2 * M')) / K ≤ ε / 2 := by
    have h1 : 4 * B * M' * (1 + 2 * M') / ε ≤ K := by
      have := Nat.le_ceil (4 * B * M' * (1 + 2 * M') / ε)
      have h2 : ((⌈4 * B * M' * (1 + 2 * M') / ε⌉₊ : ℕ) : ℝ) ≤ K := by
        rw [hK]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hε] at h1
    rw [div_le_iff₀ hKpos]
    nlinarith
  set τ := ε / (2 * B) with hτ
  have hτp : 0 < τ := by positivity
  set c0 := (δ / 2) ^ K / (K.factorial : ℝ) * Real.exp (-(2 * M)) with hc0
  have hc0p : 0 < c0 := by positivity
  refine ⟨2 * K + 2 + ⌈2 * M'⌉₊ + ⌈1 / (c0 * τ)⌉₊ + 1, ?_⟩
  intro n hn q hq0 hq1 hδq hqM
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hnK : 2 * K ≤ n := by omega
  have hn2M : 2 * M ≤ n := by
    have := Nat.le_ceil (2 * M')
    have h2 : ((⌈2 * M'⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈2 * M'⌉₊ ≤ n)
    have : M ≤ M' := le_max_left _ _
    linarith
  have hq2 : q ≤ 1 / 2 := by
    have : 2 * ((n:ℝ) * q) ≤ n := by linarith
    have : (n:ℝ) * (2 * q) ≤ n * 1 := by linarith
    have := le_of_mul_le_mul_left this hnpos
    linarith
  have hnc : 1 / (c0 * τ) ≤ n := by
    have := Nat.le_ceil (1 / (c0 * τ))
    have h2 : ((⌈1 / (c0 * τ)⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈1 / (c0 * τ)⌉₊ ≤ n)
    linarith
  -- Step 1: eq_29
  have h29 := eq_29 a c ρ ha hca hρ0 hρ1 n q hq0 hq1
  -- Step 2: pointwise
  have h2 : erExpect n q (fun G => ρ ^ 2 / (1 - ρ) * (1 / specNorm (G + Gᵀ)) ^ 2 *
      walks (G + Gᵀ) 2) ≤ C' * ((1 / (K:ℝ)) * erExpect n q (fun G => walks (G + Gᵀ) 2) +
        (n:ℝ) * erExpect n q (badInd K)) := by
    rw [← erExpect_const_mul, ← erExpect_const_mul, ← erExpect_add, ← erExpect_const_mul]
    apply erExpect_mono hq0 hq1
    intro S hS
    exact pointwise_mod ρ hρ0 hρ1 K hK1 S (Finset.mem_powerset.1 hS)
  -- Step 3: walks expectation
  have h3 : erExpect n q (fun G => walks (G + Gᵀ) 2) ≤ n * (2 * M' * (1 + 2 * M')) := by
    rw [lemma_5_2 n q hq0 hq1]
    have hxM : (n:ℝ) * q ≤ M' := le_trans hqM (le_max_left _ _)
    have hn1r : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have ha1 : 0 ≤ ((n:ℝ) - 1) * q := mul_nonneg (by linarith) hq0
    have ha2 : ((n:ℝ) - 1) * q ≤ M' := by
      have : ((n:ℝ) - 1) * q = n * q - q := by ring
      linarith
    have key : (((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q) ≤ M' * (1 + 2 * M') := by
      rcases le_or_gt 0 (1 - 3 * q + 2 * (n:ℝ) * q) with hs | hs
      · have hb2 : 1 - 3 * q + 2 * (n:ℝ) * q ≤ 1 + 2 * M' := by
          have : 2 * (n:ℝ) * q = 2 * ((n:ℝ) * q) := by ring
          linarith
        exact mul_le_mul ha2 hb2 hs hM'0
      · have : (((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ha1 hs.le
        have : 0 ≤ M' * (1 + 2 * M') := by positivity
        linarith
    calc 2 * (n:ℝ) * ((n:ℝ) - 1) * q * (1 - 3 * q + 2 * (n:ℝ) * q)
        = (2 * (n:ℝ)) * ((((n:ℝ) - 1) * q) * (1 - 3 * q + 2 * (n:ℝ) * q)) := by ring
      _ ≤ (2 * (n:ℝ)) * (M' * (1 + 2 * M')) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = n * (2 * M' * (1 + 2 * M')) := by ring
  -- Step 4: probability of the bad event
  have h4 : erExpect n q (badInd K) ≤ τ := by
    rw [erExpect_badInd]
    have hcardE : ∀ i : Fin n, (Finset.univ.erase i).card = n - 1 := by
      intro i; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hrow : ∀ i : Fin n, ∑ U ∈ (Finset.univ.erase i).powerset,
        q ^ U.card * (1 - q) ^ ((Finset.univ.erase i).card - U.card) *
          (fun r : ℕ => if r < K then (1:ℝ) else 0) U.card ≤ Real.exp (-c0) := by
      intro i
      refine le_trans (row_factor_le (Finset.univ.erase i) hq0 hq1 K) ?_
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff, hcardE]
      exact eta_lower n K q δ M hnK hn1 hq0 hδ hδq hqM hq2
    calc ∏ i : Fin n, ∑ U ∈ (Finset.univ.erase i).powerset,
          q ^ U.card * (1 - q) ^ ((Finset.univ.erase i).card - U.card) *
            (fun r : ℕ => if r < K then (1:ℝ) else 0) U.card
        ≤ ∏ _i : Fin n, Real.exp (-c0) := by
          apply Finset.prod_le_prod
          · intro i _; exact row_factor_nonneg _ hq0 hq1 K
          · intro i _; exact hrow i
      _ = Real.exp (-(n * c0)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          ring_nf
      _ ≤ 1 / (n * c0) := by
          have hpos : 0 < (n:ℝ) * c0 := by positivity
          rw [Real.exp_neg, ← one_div]
          apply one_div_le_one_div_of_le hpos
          have := Real.add_one_le_exp ((n:ℝ) * c0)
          linarith
      _ ≤ τ := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_le_iff₀ (by positivity)] at hnc
          nlinarith
  -- Combine
  have hE0 : 0 ≤ erExpect n q (badInd K) :=
    erExpect_nonneg hq0 hq1 (fun S _ => badInd_nonneg K _)
  calc erExpect n q (regret a c ρ) ≤ C1 * erExpect n q (fun G => ρ ^ 2 / (1 - ρ) *
        (1 / specNorm (G + Gᵀ)) ^ 2 * walks (G + Gᵀ) 2) := h29
    _ ≤ C1 * (C' * ((1 / (K:ℝ)) * erExpect n q (fun G => walks (G + Gᵀ) 2) +
        (n:ℝ) * erExpect n q (badInd K))) := mul_le_mul_of_nonneg_left h2 hC1p.le
    _ ≤ C1 * (C' * ((1 / (K:ℝ)) * (n * (2 * M' * (1 + 2 * M'))) + (n:ℝ) * τ)) := by
        apply mul_le_mul_of_nonneg_left _ hC1p.le
        apply mul_le_mul_of_nonneg_left _ hC'p.le
        have : (1 / (K:ℝ)) * erExpect n q (fun G => walks (G + Gᵀ) 2) ≤
            (1 / (K:ℝ)) * (n * (2 * M' * (1 + 2 * M'))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have : (n:ℝ) * erExpect n q (badInd K) ≤ n * τ :=
          mul_le_mul_of_nonneg_left h4 hnpos.le
        linarith
    _ = n * (B * (2 * M' * (1 + 2 * M')) / K) + n * (B * τ) := by
        rw [hB]; field_simp
    _ ≤ n * (ε / 2) + n * (ε / 2) := by
        have : B * τ = ε / 2 := by rw [hτ]; field_simp
        rw [this]
        have := mul_le_mul_of_nonneg_left hKbig hnpos.le
        linarith
    _ = ε * n := by ring
