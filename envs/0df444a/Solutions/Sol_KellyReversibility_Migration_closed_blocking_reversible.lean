-- Prove2me | solution 1 for KellyReversibility.Migration.closed_blocking_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:47:11.719233+00:00
-- url     : https://prove2.me/submissions/936963f0-1e54-4b43-9051-4b9f199667e5

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyReversibility_Migration_BlockingRates

set_option autoImplicit false

namespace B8E71E28

open KellyStochasticNetworks KellyReversibility.Migration

lemma Tjk_j {J : ℕ} (j k : Fin J) (n : Fin J → ℕ) : Tjk j k n j = n j - 1 := by
  simp [Tjk]

lemma Tjk_k {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) : Tjk j k n k = n k + 1 := by
  simp [Tjk, Ne.symm hjk]

lemma Tjk_o {J : ℕ} {j k i : Fin J} (hij : i ≠ j) (hik : i ≠ k) (n : Fin J → ℕ) :
    Tjk j k n i = n i := by
  simp [Tjk, hij, hik]

lemma Tjk_inv {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) (hn : 1 ≤ n j) :
    Tjk k j (Tjk j k n) = n := by
  funext i
  simp only [Tjk]
  split_ifs <;> subst_vars <;> first | omega | (exfalso; tauto)

lemma Tjk_inv' {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (m : Fin J → ℕ) (hm : 1 ≤ m k) :
    Tjk j k (Tjk k j m) = m := by
  funext i
  simp only [Tjk]
  split_ifs <;> subst_vars <;> first | omega | (exfalso; tauto)

/-- split a finite sum at two distinct indices -/
lemma sum_split {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (f : Fin J → ℕ) :
    ∑ i, f i = f j + (f k + ∑ i ∈ (Finset.univ.erase j).erase k, f i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩)]

lemma prod_split {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (f : Fin J → ℝ) :
    ∏ i, f i = f j * (f k * ∏ i ∈ (Finset.univ.erase j).erase k, f i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩)]

lemma sum_Tjk {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) (hn : 1 ≤ n j) :
    ∑ i, Tjk j k n i = ∑ i, n i := by
  rw [sum_split hjk, sum_split hjk n, Tjk_j, Tjk_k hjk]
  have : ∑ i ∈ (Finset.univ.erase j).erase k, Tjk j k n i
      = ∑ i ∈ (Finset.univ.erase j).erase k, n i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    exact Tjk_o hi.2.1 hi.1 n
  rw [this]; omega

lemma psiPhiProd_succ {J : ℕ} (ψ φ : Fin J → ℕ → ℝ) (j : Fin J) (a : ℕ) :
    psiPhiProd ψ φ j (a + 1) = psiPhiProd ψ φ j a * (ψ j a / φ j (a + 1)) := by
  unfold psiPhiProd
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

lemma psiPhiProd_pos {J : ℕ} (ψ φ : Fin J → ℕ → ℝ) (j : Fin J)
    (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r) (hψpos : ∀ j r, 0 < ψ j r) (m : ℕ) :
    0 < psiPhiProd ψ φ j m := by
  unfold psiPhiProd
  apply Finset.prod_pos
  intro r hr
  simp only [Finset.mem_Icc] at hr
  exact div_pos (hψpos _ _) (hφpos _ _ hr.1)

lemma weight_pos {J : ℕ} (α : Fin J → ℝ) (ψ φ : Fin J → ℕ → ℝ)
    (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r) (hψpos : ∀ j r, 0 < ψ j r) (hα : ∀ j, 0 < α j)
    (n : Fin J → ℕ) : 0 < blockingWeight α ψ φ n := by
  unfold blockingWeight
  apply Finset.prod_pos
  intro i _
  exact mul_pos (pow_pos (hα i) _) (psiPhiProd_pos ψ φ i hφpos hψpos _)

/-- the termwise detailed balance identity -/
lemma term_eq {J : ℕ} (N : ℕ)
    (lam : Fin J → Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hbal : BlockingBalance lam α) (n m : Fin J → ℕ) (j k : Fin J) :
    (if ∑ i, n i = N then B * blockingWeight α ψ φ n else 0) *
        (if m = Tjk j k n then lam j k * φ j (n j) * ψ k (n k) else 0)
      = (if ∑ i, m i = N then B * blockingWeight α ψ φ m else 0) *
        (if n = Tjk k j m then lam k j * φ k (m k) * ψ j (m j) else 0) := by
  by_cases hjk : j = k
  · subst hjk; simp [hlamdiag]
  by_cases hn : n j = 0
  · have h2 : ¬ n = Tjk k j m := by
      intro h
      have := congrFun h j
      rw [Tjk_k (Ne.symm hjk)] at this
      omega
    simp [hn, hφ0, h2]
  have hn1 : 1 ≤ n j := Nat.one_le_iff_ne_zero.2 hn
  by_cases hm : m = Tjk j k n
  · subst hm
    rw [if_pos rfl, if_pos (Tjk_inv hjk n hn1).symm, sum_Tjk hjk n hn1]
    obtain ⟨a, ha⟩ : ∃ a, n j = a + 1 := ⟨n j - 1, by omega⟩
    rw [Tjk_j, Tjk_k hjk, ha, Nat.add_sub_cancel]
    by_cases hs : ∑ i, n i = N
    · rw [if_pos hs, if_pos hs]
      unfold blockingWeight
      rw [prod_split hjk, prod_split hjk (fun i => α i ^ Tjk j k n i *
        psiPhiProd ψ φ i (Tjk j k n i))]
      simp only [Tjk_j, Tjk_k hjk, ha, Nat.add_sub_cancel]
      have hR : ∏ i ∈ (Finset.univ.erase j).erase k,
          α i ^ Tjk j k n i * psiPhiProd ψ φ i (Tjk j k n i)
          = ∏ i ∈ (Finset.univ.erase j).erase k, α i ^ n i * psiPhiProd ψ φ i (n i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_erase] at hi
        rw [Tjk_o hi.2.1 hi.1 n]
      rw [hR, psiPhiProd_succ, psiPhiProd_succ]
      set R := ∏ i ∈ (Finset.univ.erase j).erase k, α i ^ n i * psiPhiProd ψ φ i (n i)
      have e1 : φ j (a + 1) * (φ j (a + 1))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (hφpos j (a + 1) (by omega)))
      have e2 : φ k (n k + 1) * (φ k (n k + 1))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (hφpos k (n k + 1) (by omega)))
      have hb := hbal j k
      simp only [div_eq_mul_inv]
      set C := B * R * psiPhiProd ψ φ j a * psiPhiProd ψ φ k (n k) * α j ^ a * α k ^ n k
        * ψ j a * ψ k (n k)
      linear_combination (C * α j * lam j k) * e1 - (C * α k * lam k j) * e2 + C * hb
    · rw [if_neg hs, if_neg hs]; simp
  · by_cases hmk : m k = 0
    · simp [hm, hmk, hφ0]
    have h2 : ¬ n = Tjk k j m := by
      intro h
      apply hm
      rw [h, Tjk_inv' hjk m (Nat.one_le_iff_ne_zero.2 hmk)]
    simp [hm, h2]

end B8E71E28

open KellyStochasticNetworks KellyReversibility.Migration in
theorem solution {J : ℕ} (hJ : 0 < J) (N : ℕ)
    (lam : Fin J → Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hconn : ClosedConnected lam)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hψpos : ∀ j r, 0 < ψ j r)
    (hα : ∀ j, 0 < α j) (hbal : BlockingBalance lam α)
    (hB : HasSum (fun n : {n : Fin J → ℕ // ∑ j, n j = N} => blockingWeight α ψ φ n.1) B⁻¹) :
    let π : (Fin J → ℕ) → ℝ := fun n =>
      if ∑ j, n j = N then B * blockingWeight α ψ φ n else 0
    DetailedBalance π (closedBlockingRates lam φ ψ)
      ∧ FullBalance π (closedBlockingRates lam φ ψ)
      ∧ (∀ n : Fin J → ℕ, ∑ j, n j = N → 0 < π n)
      ∧ HasSum π 1 := by
  intro π
  have hDB : DetailedBalance π (closedBlockingRates lam φ ψ) := by
    intro n m
    simp only [π, closedBlockingRates, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j k => (if ∑ i, m i = N then B * blockingWeight α ψ φ m else 0) *
        if n = Tjk j k m then lam j k * φ j (m j) * ψ k (m k) else 0)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    exact B8E71E28.term_eq N lam φ ψ α B hlamdiag hφ0 hφpos hbal n m j k
  -- positivity of B
  have i0 : Fin J := ⟨0, hJ⟩
  let s0 : {n : Fin J → ℕ // ∑ j, n j = N} :=
    ⟨fun i => if i = i0 then N else 0, by simp⟩
  have hBinv : 0 < B⁻¹ := by
    have h1 := le_hasSum hB s0 (fun t _ => (B8E71E28.weight_pos α ψ φ hφpos hψpos hα t.1).le)
    exact lt_of_lt_of_le (B8E71E28.weight_pos α ψ φ hφpos hψpos hα s0.1) h1
  have hBpos : 0 < B := inv_pos.1 hBinv
  refine ⟨hDB, ?_, ?_, ?_⟩
  · intro n
    have : ∀ m, π m * closedBlockingRates lam φ ψ m n = π n * closedBlockingRates lam φ ψ n m :=
      fun m => (hDB n m).symm
    simp_rw [this]
    rw [tsum_mul_left]
  · intro n hn
    simp only [π, if_pos hn]
    exact mul_pos hBpos (B8E71E28.weight_pos α ψ φ hφpos hψpos hα n)
  · have h1 : HasSum (fun n : {n : Fin J → ℕ // ∑ j, n j = N} =>
        B * blockingWeight α ψ φ n.1) 1 := by
      have := hB.mul_left B
      rwa [mul_inv_cancel₀ hBpos.ne'] at this
    have h2 := (hasSum_subtype_iff_indicator (s := {n : Fin J → ℕ | ∑ j, n j = N})
      (f := fun n => B * blockingWeight α ψ φ n)).1 h1
    convert h2 using 1
    funext n
    simp only [π, Set.indicator_apply, Set.mem_ofPred_eq]
