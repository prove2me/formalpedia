-- Prove2me | solution 1 for KellyReversibility.Migration.open_blocking_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:45:45.709995+00:00
-- url     : https://prove2.me/submissions/18e81549-c5c3-4482-8a52-01776a9674dc

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyReversibility_Migration_BlockingRates

set_option autoImplicit false

namespace DA4C2393

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

lemma prod_split {J : ℕ} {j k : Fin J} (hjk : j ≠ k) (f : Fin J → ℝ) :
    ∏ i, f i = f j * (f k * ∏ i ∈ (Finset.univ.erase j).erase k, f i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩)]

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


/-- termwise detailed balance for transfers -/
lemma term_eq {J : ℕ}
    (lam : Fin J → Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hbal : BlockingBalance lam α) (n m : Fin J → ℕ) (j k : Fin J) :
    B * blockingWeight α ψ φ n *
        (if m = Tjk j k n then lam j k * φ j (n j) * ψ k (n k) else 0)
      = B * blockingWeight α ψ φ m *
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
    rw [if_pos rfl, if_pos (Tjk_inv hjk n hn1).symm]
    obtain ⟨a, ha⟩ : ∃ a, n j = a + 1 := ⟨n j - 1, by omega⟩
    rw [Tjk_j, Tjk_k hjk, ha, Nat.add_sub_cancel]
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
  · by_cases hmk : m k = 0
    · simp [hm, hmk, hφ0]
    have h2 : ¬ n = Tjk k j m := by
      intro h
      apply hm
      rw [h, Tjk_inv' hjk m (Nat.one_le_iff_ne_zero.2 hmk)]
    simp [hm, h2]

lemma weight_out {J : ℕ} (α : Fin J → ℝ) (ψ φ : Fin J → ℕ → ℝ) (n : Fin J → ℕ) (j : Fin J)
    (a : ℕ) (ha : n j = a + 1) :
    blockingWeight α ψ φ n
      = blockingWeight α ψ φ (Tout j n) * (α j * (ψ j a / φ j (a + 1))) := by
  unfold blockingWeight
  rw [← Finset.mul_prod_erase Finset.univ (fun i => α i ^ n i * psiPhiProd ψ φ i (n i))
      (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => α i ^ Tout j n i * psiPhiProd ψ φ i (Tout j n i)) (Finset.mem_univ j)]
  have hR : ∏ i ∈ Finset.univ.erase j, α i ^ Tout j n i * psiPhiProd ψ φ i (Tout j n i)
      = ∏ i ∈ Finset.univ.erase j, α i ^ n i * psiPhiProd ψ φ i (n i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Tout, hij]
  have htj : Tout j n j = a := by simp [Tout, ha]
  rw [hR, htj, ha, psiPhiProd_succ, pow_succ]
  ring

lemma out_eq {J : ℕ} (mu nu : Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hout : ∀ j, α j * mu j = nu j) (n m : Fin J → ℕ) (j : Fin J) :
    B * blockingWeight α ψ φ n * (if m = Tout j n then mu j * φ j (n j) else 0)
      = B * blockingWeight α ψ φ m * (if n = Tin j m then nu j * ψ j (m j) else 0) := by
  by_cases hn : n j = 0
  · have h2 : ¬ n = Tin j m := by
      intro h
      have := congrFun h j
      simp [Tin] at this
      omega
    simp [hn, hφ0, h2]
  obtain ⟨a, ha⟩ : ∃ a, n j = a + 1 := ⟨n j - 1, by omega⟩
  by_cases hm : m = Tout j n
  · subst hm
    have hinv : n = Tin j (Tout j n) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [Tin, Tout]; omega
      · simp [Tin, Tout, hi]
    rw [if_pos rfl, if_pos hinv]
    have hw := weight_out α ψ φ n j a ha
    have htj : Tout j n j = a := by simp [Tout, ha]
    rw [htj, hw, ha, ← hout j]
    have hne : φ j (a + 1) ≠ 0 := ne_of_gt (hφpos j (a + 1) (by omega))
    have e1 : ψ j a / φ j (a + 1) * φ j (a + 1) = ψ j a := div_mul_cancel₀ _ hne
    linear_combination (B * blockingWeight α ψ φ (Tout j n) * α j * mu j) * e1
  · have h2 : ¬ n = Tin j m := by
      intro h
      apply hm
      rw [h]
      funext i
      by_cases hi : i = j
      · subst hi; simp [Tin, Tout]
      · simp [Tin, Tout, hi]
    simp [hm, h2]

lemma db_main {J : ℕ}
    (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (B : ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hbal : BlockingBalance lam α) (hout : ∀ j, α j * mu j = nu j) :
    DetailedBalance (fun n => B * blockingWeight α ψ φ n) (openBlockingRates lam mu nu φ ψ) := by
  intro n m
  have hA : B * blockingWeight α ψ φ n * closedBlockingRates lam φ ψ n m
      = B * blockingWeight α ψ φ m * closedBlockingRates lam φ ψ m n := by
    simp only [closedBlockingRates, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j k => B * blockingWeight α ψ φ m *
        if n = Tjk j k m then lam j k * φ j (m j) * ψ k (m k) else 0)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    exact term_eq lam φ ψ α B hlamdiag hφ0 hφpos hbal n m j k
  have hO : ∀ n m : Fin J → ℕ,
      B * blockingWeight α ψ φ n * (∑ j, if m = Tout j n then mu j * φ j (n j) else 0)
        = B * blockingWeight α ψ φ m * (∑ k, if n = Tin k m then nu k * ψ k (m k) else 0) := by
    intro n m
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => out_eq mu nu φ ψ α B hφ0 hφpos hout n m j
  simp only [openBlockingRates, mul_add]
  rw [hA, hO n m, ← hO m n]
  ring

lemma hasSum_pi_prod (J : ℕ) : ∀ (f : Fin J → ℕ → ℝ) (s : Fin J → ℝ),
    (∀ i x, 0 ≤ f i x) → (∀ i, HasSum (f i) (s i)) →
    HasSum (fun n : Fin J → ℕ => ∏ i, f i (n i)) (∏ i, s i) := by
  induction J with
  | zero =>
    intro f s _ _
    have := hasSum_single (f := fun n : Fin 0 → ℕ => ∏ i, f i (n i)) (default : Fin 0 → ℕ)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)
    simpa using this
  | succ J ih =>
    intro f s hf hs
    have ih' : HasSum (fun y : Fin J → ℕ => ∏ i : Fin J, f i.succ (y i)) (∏ i : Fin J, s i.succ) :=
      ih (fun i => f i.succ) (fun i => s i.succ) (fun i x => hf _ _) (fun i => hs _)
    have h0 : HasSum (f 0) (s 0) := hs 0
    have hnn0 : (0 : ℕ → ℝ) ≤ f 0 := fun x => hf 0 x
    have hnn1 : (0 : (Fin J → ℕ) → ℝ) ≤ fun y : Fin J → ℕ => ∏ i : Fin J, f i.succ (y i) :=
      fun y => Finset.prod_nonneg fun i _ => hf _ _
    have hsum := Summable.mul_of_nonneg h0.summable ih'.summable hnn0 hnn1
    have hm := h0.mul ih' hsum
    refine (Fin.consEquiv (fun _ : Fin (J + 1) => ℕ)).hasSum_iff.1 ?_
    rw [Fin.prod_univ_succ]
    have hfun : ((fun n : Fin (J + 1) → ℕ => ∏ i, f i (n i)) ∘ ⇑(Fin.consEquiv fun _ => ℕ))
        = fun x : ℕ × (Fin J → ℕ) => f 0 x.1 * ∏ i : Fin J, f i.succ (x.2 i) := by
      funext p
      simp [Fin.prod_univ_succ]
    rw [hfun]
    exact hm

end DA4C2393

open KellyStochasticNetworks KellyReversibility.Migration in
theorem solution {J : ℕ}
    (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ ψ : Fin J → ℕ → ℝ) (α g : Fin J → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hmu : ∀ j, 0 ≤ mu j) (hnu : ∀ j, 0 ≤ nu j)
    (hconn : OpenConnected lam mu nu)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hψpos : ∀ j r, 0 < ψ j r)
    (hα : ∀ j, 0 < α j) (hbal : BlockingBalance lam α) (hout : ∀ j, α j * mu j = nu j)
    (hg : ∀ j, HasSum (fun m : ℕ => α j ^ m * psiPhiProd ψ φ j m) (g j)) :
    let B : ℝ := ∏ j, (g j)⁻¹
    let π : (Fin J → ℕ) → ℝ := fun n => B * blockingWeight α ψ φ n
    let πj : Fin J → ℕ → ℝ := fun j m => (g j)⁻¹ * (α j ^ m * psiPhiProd ψ φ j m)
    DetailedBalance π (openBlockingRates lam mu nu φ ψ)
      ∧ FullBalance π (openBlockingRates lam mu nu φ ψ)
      ∧ (∀ n, 0 < π n)
      ∧ HasSum π 1
      ∧ (∀ j, HasSum (πj j) 1)
      ∧ (∀ (j : Fin J) (m : ℕ), HasSum (fun n : {n : Fin J → ℕ // n j = m} => π n.1) (πj j m))
      ∧ (∀ n, π n = ∏ j, πj j (n j)) := by
  intro B π πj
  have hgpos : ∀ j, 0 < g j := fun j => by
    have h := le_hasSum (hg j) 0 (fun m _ =>
      (mul_pos (pow_pos (hα j) m) (DA4C2393.psiPhiProd_pos ψ φ j hφpos hψpos m)).le)
    have h0 : α j ^ 0 * psiPhiProd ψ φ j 0 = 1 := by simp [psiPhiProd]
    linarith
  have hBpos : 0 < B := Finset.prod_pos fun j _ => inv_pos.2 (hgpos j)
  have hπj_nonneg : ∀ j x, 0 ≤ πj j x := fun j x =>
    mul_nonneg (inv_pos.2 (hgpos j)).le
      (mul_pos (pow_pos (hα j) x) (DA4C2393.psiPhiProd_pos ψ φ j hφpos hψpos x)).le
  have hπj : ∀ j, HasSum (πj j) 1 := fun j => by
    have := (hg j).mul_left (g j)⁻¹
    rwa [inv_mul_cancel₀ (hgpos j).ne'] at this
  have hprod : ∀ n, π n = ∏ j, πj j (n j) := fun n => by
    simp only [π, πj, B, blockingWeight]
    rw [← Finset.prod_mul_distrib]
  have hDB : DetailedBalance π (openBlockingRates lam mu nu φ ψ) :=
    DA4C2393.db_main lam mu nu φ ψ α B hlamdiag hφ0 hφpos hbal hout
  refine ⟨hDB, ?_, fun n => mul_pos hBpos (DA4C2393.weight_pos α ψ φ hφpos hψpos hα n),
    ?_, hπj, ?_, hprod⟩
  · intro n
    have : ∀ m, π m * openBlockingRates lam mu nu φ ψ m n
        = π n * openBlockingRates lam mu nu φ ψ n m := fun m => (hDB n m).symm
    simp_rw [this]
    rw [tsum_mul_left]
  · have h := DA4C2393.hasSum_pi_prod J πj (fun _ => 1) hπj_nonneg hπj
    rw [Finset.prod_const_one] at h
    convert h using 1
    funext n
    exact hprod n
  · intro j m
    let f' : Fin J → ℕ → ℝ := fun i x => if i = j then (if x = m then πj j m else 0) else πj i x
    have hf'0 : ∀ i x, 0 ≤ f' i x := by
      intro i x
      simp only [f']
      split_ifs
      · exact hπj_nonneg _ _
      · exact le_refl 0
      · exact hπj_nonneg _ _
    have hf's : ∀ i, HasSum (f' i) (if i = j then πj j m else 1) := by
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [f']
        exact hasSum_ite_eq m _
      · simp only [f', if_neg hi]
        exact hπj i
    have h : HasSum (fun n : Fin J → ℕ => ∏ i, f' i (n i)) (πj j m) := by
      have := DA4C2393.hasSum_pi_prod J f' _ hf'0 hf's
      convert this using 1
      simp
    have hind : HasSum ({n : Fin J → ℕ | n j = m}.indicator π) (πj j m) := by
      convert h using 1
      funext n
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hn
      · rw [hprod n]
        apply Finset.prod_congr rfl
        intro i _
        simp only [f']
        by_cases hi : i = j
        · subst hi; rw [if_pos rfl, if_pos hn, hn]
        · rw [if_neg hi]
      · symm
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [f', hn]
    exact (hasSum_subtype_iff_indicator (s := {n : Fin J → ℕ | n j = m}) (f := π)).2 hind
