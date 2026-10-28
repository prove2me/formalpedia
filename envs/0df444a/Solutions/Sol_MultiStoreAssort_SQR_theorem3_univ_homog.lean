-- Prove2me | solution 1 for MultiStoreAssort.SQR.theorem3_univ_homog
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T15:57:30.874253+00:00
-- url     : https://prove2.me/submissions/c02b0069-f15c-4943-b8d9-c530629974b3

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model
import Theorems.Thm_MultiStoreAssort_SQR_theorem4_nested_revenue_ordered

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

open MultiStoreAssort.SQR MultiStoreAssort.SMR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (c0 : ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hu : UnivHomog c c0) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      (∀ i, i ≠ Fin.last (M + 1) → S i = S 0) ∧ S 0 ⊆ St ∧ St ⊆ S (Fin.last (M + 1)) ∧
      MultiStoreAssort.SMR.IsRevenueOrdered (S 0) ∧ MultiStoreAssort.SMR.IsRevenueOrdered (S (Fin.last (M + 1))) := by
  classical
  set L := Fin.last (M + 1)
  have hsw : StoreWiseHomog c (fun _ => c0) := ⟨fun _ => hu.1, fun i j k h => hu.2 i j k h⟩
  obtain ⟨S, hopt, hch, hlow, hhigh, hro⟩ := theorem4_nested_revenue_ordered lam r v c (fun _ => c0) hn
    hlam hlam1 hr hrpos hv hcii hsw hmin (fun _ _ _ => le_rfl) St hSt
  have h0L : (0 : Fin (M + 2)) ≠ L := by
    intro h; have := congrArg Fin.val h; simp [L] at this
  have hle : ∀ i : Fin (M + 2), i ≠ L → i ≤ (Fin.last M).castSucc := by
    intro i hi
    rw [Fin.le_def]; simp only [Fin.val_castSucc, Fin.val_last]
    have : i.val ≠ M + 1 := fun h => hi (Fin.ext (by simp [L, h]))
    have := i.isLt; omega
  have hlastne : (Fin.last M).castSucc ≠ L := by
    intro h; have := congrArg Fin.val h; simp [L] at this
  have hsubSt : ∀ i, i ≠ L → S i ⊆ St := fun i hi =>
    (hch i _ (hle i hi) hlastne).trans hlow
  have hsubL : ∀ i, S i ⊆ S L := by
    intro i; by_cases hi : i = L
    · rw [hi]
    · exact (hsubSt i hi).trans hhigh
  set β := Real.exp (-c0)
  obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image (Finset.univ.filter (fun i => i ≠ L))
    (fun i => rev8 r v β (S L) (S i)) ⟨0, by simp [h0L]⟩
  have hi0L : i0 ≠ L := (Finset.mem_filter.mp hi0mem).2
  set S' : Fin (M + 2) → Finset (Fin n) := fun i => if i = L then S L else S i0
  have hS'L : S' L = S L := by simp [S']
  have hS'i : ∀ i, i ≠ L → S' i = S i0 := fun i hi => by simp [S', hi]
  have hS'sub : ∀ i, S' i ⊆ S' L := by
    intro i; rw [hS'L]; by_cases hi : i = L
    · rw [hi, hS'L]
    · rw [hS'i i hi]; exact hsubL i0
  have hge : revQ lam r v c S ≤ revQ lam r v c S' := by
    rw [SQR2Aux.revQ_eq lam r v c (fun _ => c0) hsw S, SQR2Aux.revQ_eq lam r v c (fun _ => c0) hsw S',
      SQR2Aux.Sbar_eq S L hsubL, SQR2Aux.Sbar_eq S' L hS'sub, hS'L]
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hlam i)
    by_cases hi : i = L
    · rw [hi, hS'L]
    · rw [hS'i i hi]; exact hi0max i (by simp [hi])
  refine ⟨S', fun S'' => (hopt S'').trans hge, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hS'i i hi, hS'i 0 h0L]
  · rw [hS'i 0 h0L]; exact hsubSt i0 hi0L
  · rw [hS'L]; exact hhigh
  · rw [hS'i 0 h0L]; exact hro i0
  · rw [hS'L]; exact hro L
