-- Prove2me | solution 1 for MultiStoreAssort.SQR.step3_case1_replace_stilde
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:38:01.342536+00:00
-- url     : https://prove2.me/submissions/4ad25128-51d1-41c3-9d30-7be58e879b49

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

/-- (B.6)–(B.8): replacing a store's assortment `U ⊇ T` by the single-store optimum `T` does not
decrease that store's revenue when the overall union `A` is fixed. -/
theorem rev8_replace {n : ℕ} (r v : Fin n → ℝ) (hr : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (A T U : Finset (Fin n)) (hTU : T ⊆ U) (hUA : U ⊆ A)
    (hopt : Ws r v U / (1 + Vs v U) ≤ Ws r v T / (1 + Vs v T)) :
    rev8 r v β A U ≤ rev8 r v β A T := by
  classical
  unfold rev8
  apply add_le_add hopt
  have hTA : T ⊆ A := hTU.trans hUA
  have hsd : A \ U ⊆ A \ T := Finset.sdiff_subset_sdiff (le_refl A) hTU
  have hW : Ws r v (A \ U) ≤ Ws r v (A \ T) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (mul_pos (hr k) (hv k)).le)
  have hVsd : Vs v (A \ U) ≤ Vs v (A \ T) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (hv k).le)
  have hVTU : Vs v T ≤ Vs v U :=
    Finset.sum_le_sum_of_subset_of_nonneg hTU (fun k _ _ => (hv k).le)
  have hsumU : Vs v (A \ U) + Vs v U = Vs v A := by unfold Vs; exact Finset.sum_sdiff hUA
  have hsumT : Vs v (A \ T) + Vs v T = Vs v A := by unfold Vs; exact Finset.sum_sdiff hTA
  have hw0 := Ws_nonneg r v hr hv (A \ U)
  have ha := Vs_nonneg v hv T
  have hy := Vs_nonneg v hv (A \ U)
  have hx := Vs_nonneg v hv (A \ T)
  set wU := Ws r v (A \ U)
  set wT := Ws r v (A \ T)
  set a := Vs v T
  set b := Vs v U
  set x := Vs v (A \ T)
  set y := Vs v (A \ U)
  have hden : (1 + a) * (1 + a + β * x) ≤ (1 + b) * (1 + b + β * y) := by
    have h1 : 1 + a + β * x ≤ 1 + b + β * y := by nlinarith
    have h2 : 0 ≤ 1 + a + β * x := by nlinarith
    calc (1 + a) * (1 + a + β * x) ≤ (1 + b) * (1 + a + β * x) := by nlinarith
      _ ≤ (1 + b) * (1 + b + β * y) := by nlinarith
  have hpos : 0 < (1 + a) * (1 + a + β * x) := by
    apply mul_pos <;> nlinarith
  calc β * wU / ((1 + b) * (1 + b + β * y)) ≤ β * wU / ((1 + a) * (1 + a + β * x)) :=
        div_le_div_of_nonneg_left (mul_nonneg hβ0.le hw0) hpos hden
    _ ≤ β * wT / ((1 + a) * (1 + a + β * x)) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left hW hβ0.le

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
    (K : ℕ) (hK : K ≤ M) (hlow : ∀ i : Fin (M + 2), i.val < K → S i ⊆ St)
    (hhigh : ∀ i : Fin (M + 2), K ≤ i.val → St ⊂ S i) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      MultiStoreAssort.SMR.revQ lam r v c (fun i => if K ≤ i.val ∧ i ≠ Fin.last (M + 1) then St else S i) := by
  classical
  set L := Fin.last (M + 1)
  set S' : Fin (M + 2) → Finset (Fin n) := fun i => if K ≤ i.val ∧ i ≠ L then St else S i
  have hStL : St ⊆ S L := (hhigh L (by simp [L]; omega)).subset
  have hS'L : S' L = S L := by simp [S']
  have hSb : Sbar S = S L := SQR2Aux.Sbar_eq S L (fun i => hchain i L (Fin.le_last i))
  have hSb' : Sbar S' = S L := by
    rw [SQR2Aux.Sbar_eq S' L, hS'L]
    intro i
    rw [hS'L]
    simp only [S']
    split_ifs
    · exact hStL
    · exact hchain i L (Fin.le_last i)
  rw [SQR2Aux.revQ_eq lam r v c cs hsw S, SQR2Aux.revQ_eq lam r v c cs hsw S', hSb, hSb']
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hlam i)
  simp only [S']
  split_ifs with hi
  · have hβ0 : 0 < Real.exp (-(cs i)) := Real.exp_pos _
    have hβ1 : Real.exp (-(cs i)) ≤ 1 := by
      have := hsw.1 i
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hopt := hSt.2.1 (S i)
    rw [SQR2Aux.single_eq, SQR2Aux.single_eq] at hopt
    exact SQR2Aux.rev8_replace r v hrpos hv _ hβ0 hβ1 (S L) St (S i) (hhigh i hi.1).subset
      (hchain i L (Fin.le_last i)) hopt
  · exact le_rfl
