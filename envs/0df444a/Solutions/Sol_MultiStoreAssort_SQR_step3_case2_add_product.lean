-- Prove2me | solution 1 for MultiStoreAssort.SQR.step3_case2_add_product
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:36:35.430842+00:00
-- url     : https://prove2.me/submissions/708f088a-cbaa-4e47-aa09-fcf8b14c95d3

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

open MultiStoreAssort.SQR

namespace SQR2Aux

open MultiStoreAssort.SMR

theorem discFactor_eq {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ)
    (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n)
    (hk : k ∈ Sbar S \ S i) : discFactor c S i k = Real.exp (-(cs i)) := by
  classical
  rw [Finset.mem_sdiff] at hk
  obtain ⟨hk1, hk2⟩ := hk
  unfold discFactor
  have hne : (Finset.univ.filter (fun j => k ∈ S j)).Nonempty := by
    unfold Sbar at hk1
    rw [Finset.mem_sup] at hk1
    obtain ⟨j, -, hj⟩ := hk1
    exact ⟨j, by simp [hj]⟩
  have hcongr : (Finset.univ.filter (fun j => k ∈ S j)).sup (fun j => (Real.exp (-(c i j k))).toNNReal)
      = (Finset.univ.filter (fun j => k ∈ S j)).sup (fun _ => (Real.exp (-(cs i))).toNNReal) := by
    apply Finset.sup_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hij : i ≠ j := by rintro rfl; exact hk2 hj
    rw [hsw.2 i j k hij]
  rw [hcongr, Finset.sup_const hne, Real.coe_toNNReal _ (Real.exp_pos _).le]

theorem storeRev_eq {m n : ℕ} (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ)
    (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    ∑ k, r k * pQ v c S i k = rev8 r v (Real.exp (-(cs i))) (Sbar S) (S i) := by
  classical
  have hSi : S i ⊆ Sbar S := by
    intro x hx; unfold Sbar; exact Finset.mem_sup.mpr ⟨i, Finset.mem_univ _, hx⟩
  set β := Real.exp (-(cs i))
  set A := Sbar S \ S i
  have hdisj : Disjoint (S i) A := Finset.disjoint_sdiff
  have hden : denomM v c S i = 1 + Vs v (S i) + β * Vs v A := by
    unfold denomM Vs
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl; rw [discFactor_eq c cs hsw S i l hl]; ring
  rw [← Finset.sum_subset (Finset.subset_univ (S i ∪ A))]
  · rw [Finset.sum_union hdisj]
    have h1 : ∑ k ∈ S i, r k * pQ v c S i k = Ws r v (S i) / (1 + Vs v (S i)) := by
      unfold Ws Vs; rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro k hk
      simp only [pQ, hk, if_true]; ring
    have h2 : ∑ k ∈ A, r k * pQ v c S i k =
        β * Ws r v A / ((1 + Vs v (S i)) * (1 + Vs v (S i) + β * Vs v A)) := by
      unfold Ws; rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro k hk
      have hk' : k ∉ S i := (Finset.mem_sdiff.mp hk).2
      have hk2 : k ∈ Sbar S \ S i := hk
      rw [pQ, if_neg hk', if_pos hk2, discFactor_eq c cs hsw S i k hk, ← hden]
      unfold Vs; ring
    rw [h1, h2]; rfl
  · intro k _ hk
    have h1 : k ∉ S i := fun h => hk (Finset.mem_union_left _ h)
    have h2 : k ∉ A := fun h => hk (Finset.mem_union_right _ h)
    simp [pQ, h1, h2, A]

theorem revQ_eq {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (cs : Fin m → ℝ) (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) :
    revQ lam r v c S = ∑ i, lam i * rev8 r v (Real.exp (-(cs i))) (Sbar S) (S i) := by
  unfold revQ
  apply Finset.sum_congr rfl; intro i _
  rw [storeRev_eq r v c cs hsw S i]

theorem Sbar_eq {m n : ℕ} (S : Fin m → Finset (Fin n)) (L : Fin m) (h : ∀ i, S i ⊆ S L) :
    Sbar S = S L := by
  unfold Sbar
  apply le_antisymm
  · exact Finset.sup_le (fun i _ => h i)
  · exact Finset.le_sup (f := S) (Finset.mem_univ L)

theorem rev8_self {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (X : Finset (Fin n)) :
    rev8 r v β X X = Ws r v X / (1 + Vs v X) := by
  simp [rev8, Ws]

theorem Ws_nonneg {n : ℕ} (r v : Fin n → ℝ) (hr : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (X : Finset (Fin n)) : 0 ≤ Ws r v X :=
  Finset.sum_nonneg (fun k _ => (mul_pos (hr k) (hv k)).le)

theorem Vs_nonneg {n : ℕ} (v : Fin n → ℝ) (hv : ∀ k, 0 < v k) (X : Finset (Fin n)) :
    0 ≤ Vs v X :=
  Finset.sum_nonneg (fun k _ => (hv k).le)

theorem single_eq {n : ℕ} (r v : Fin n → ℝ) (X : Finset (Fin n)) :
    MultiStoreAssort.SMR.single r v X = Ws r v X / (1 + Vs v X) := by
  unfold MultiStoreAssort.SMR.single ChoiceCDLP.MNL.mnlObjective Ws Vs
  rw [add_comm (∑ j ∈ X, v j) 1]

/-- In an optimal single-store assortment, every product's revenue is at least the optimal value. -/
theorem r_ge_opt {n : ℕ} (r v : Fin n → ℝ) (hr : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (St : Finset (Fin n)) (hopt : MultiStoreAssort.SMR.IsOptSingle r v St) (j : Fin n)
    (hj : j ∈ St) : Ws r v St / (1 + Vs v St) ≤ r j := by
  have h := hopt (St.erase j)
  rw [single_eq, single_eq] at h
  have hW : Ws r v St = r j * v j + Ws r v (St.erase j) := by
    unfold Ws; exact (Finset.add_sum_erase St (fun k => r k * v k) hj).symm
  have hV : Vs v St = v j + Vs v (St.erase j) := by
    unfold Vs; exact (Finset.add_sum_erase St v hj).symm
  rw [hW, hV] at h ⊢
  set a := Ws r v (St.erase j)
  set b := Vs v (St.erase j)
  have ha : 0 ≤ a := Ws_nonneg r v hr hv _
  have hb : 0 ≤ b := Vs_nonneg v hv _
  have hvj := hv j
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  have key : a * v j ≤ r j * (1 + b) * v j := by nlinarith
  have key2 : a ≤ r j * (1 + b) := le_of_mul_le_mul_right key hvj
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end SQR2Aux

open MultiStoreAssort.SMR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St)
    (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (hro : ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i))
    (hsub : S (Fin.last (M + 1)) ⊂ St) (j : Fin n) (hj : j.val = (S (Fin.last (M + 1))).card) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (insert j (S (Fin.last (M + 1))))) := by
  classical
  set L := Fin.last (M + 1)
  set A := S L with hA
  have hpcard : ∀ p, p ≤ n → (prefixSet n p).card = p := by
    intro p hp; unfold prefixSet; rw [Fin.card_filter_val_lt]; omega
  -- j ∉ A and j ∈ St
  have hjA : j ∉ A := by
    obtain ⟨p, -, hpn, hAp⟩ := hro L
    rw [← hA] at hAp
    rw [hAp] at hj ⊢
    rw [hpcard p hpn] at hj
    simp [prefixSet, hj]
  have hjSt : j ∈ St := by
    obtain ⟨q, -, hqn, hStq⟩ := hSt.1
    have hlt := Finset.card_lt_card hsub
    rw [hStq, hpcard q hqn] at hlt
    rw [hStq]; simp [prefixSet]; omega
  have hopt := hSt.2.1
  have hrj := SQR2Aux.r_ge_opt r v hrpos hv St hopt j hjSt
  have hoptW : ∀ T, Ws r v T / (1 + Vs v T) ≤ r j := by
    intro T; have := hopt T; rw [SQR2Aux.single_eq, SQR2Aux.single_eq] at this; linarith
  set A' := insert j A
  set S' := Function.update S L A'
  have hSb : Sbar S = A := SQR2Aux.Sbar_eq S L (fun i => hchain i L (Fin.le_last i))
  have hS'L : S' L = A' := Function.update_self _ _ _
  have hS'i : ∀ i, i ≠ L → S' i = S i := fun i hi => Function.update_of_ne hi _ _
  have hSb' : Sbar S' = A' := by
    rw [SQR2Aux.Sbar_eq S' L, hS'L]
    intro i
    by_cases hi : i = L
    · rw [hi]
    · rw [hS'i i hi, hS'L]; exact (hchain i L (Fin.le_last i)).trans (Finset.subset_insert _ _)
  rw [SQR2Aux.revQ_eq lam r v c cs hsw S, SQR2Aux.revQ_eq lam r v c cs hsw S', hSb, hSb']
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hlam i)
  set β := Real.exp (-(cs i))
  have hβ0 : 0 < β := Real.exp_pos _
  have hβ1 : β ≤ 1 := by
    have := hsw.1 i
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrj0 := hrpos j
  have hvj := hv j
  by_cases hi : i = L
  · rw [hi, hS'L]
    show rev8 r v β A A ≤ rev8 r v β A' A'
    rw [SQR2Aux.rev8_self, SQR2Aux.rev8_self]
    have hW : Ws r v A' = r j * v j + Ws r v A := by unfold Ws; rw [Finset.sum_insert hjA]
    have hV : Vs v A' = v j + Vs v A := by unfold Vs; rw [Finset.sum_insert hjA]
    have h0 := hoptW A
    rw [hW, hV]
    have ha := SQR2Aux.Ws_nonneg r v hrpos hv A
    have hb := SQR2Aux.Vs_nonneg v hv A
    rw [div_le_iff₀ (by linarith)] at h0
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · rw [hS'i i hi]
    set X := S i
    have hXA : X ⊆ A := hchain i L (Fin.le_last i)
    have hjX : j ∉ X := fun h => hjA (hXA h)
    have hdiff : A' \ X = insert j (A \ X) := by
      ext x; simp only [A', Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · left; exact h1
        · right; exact ⟨h1, h2⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · subst h1; exact ⟨Or.inl rfl, hjX⟩
        · exact ⟨Or.inr h1, h2⟩
    have hjAX : j ∉ A \ X := fun h => hjA (Finset.mem_sdiff.mp h).1
    unfold rev8
    rw [hdiff]
    have hW : Ws r v (insert j (A \ X)) = r j * v j + Ws r v (A \ X) := by
      unfold Ws; rw [Finset.sum_insert hjAX]
    have hV : Vs v (insert j (A \ X)) = v j + Vs v (A \ X) := by
      unfold Vs; rw [Finset.sum_insert hjAX]
    rw [hW, hV]
    apply add_le_add le_rfl
    have h0 := hoptW (A \ X)
    set w := Ws r v (A \ X)
    set y := Vs v (A \ X)
    have hw := SQR2Aux.Ws_nonneg r v hrpos hv (A \ X)
    have hy := SQR2Aux.Vs_nonneg v hv (A \ X)
    have hP := SQR2Aux.Vs_nonneg v hv X
    set P := 1 + Vs v X
    rw [div_le_iff₀ (by linarith)] at h0
    have key : β * w ≤ r j * (P + β * y) := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hPpos : 0 < P := by linarith
    have := mul_le_mul_of_nonneg_left key (le_of_lt (mul_pos (mul_pos hβ0 hPpos) hvj))
    nlinarith
