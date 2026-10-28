-- Prove2me | solution 1 for MultiStoreAssort.SQR.theorem2_two_store
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T15:58:49.189692+00:00
-- url     : https://prove2.me/submissions/d4db758c-918c-445e-90ff-d01ccb6ad844

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model
import Theorems.Thm_MultiStoreAssort_SQR_theorem3_univ_homog

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
theorem solution {n : ℕ} (l : ℝ) (r v : Fin n → ℝ) (c : Fin 2 → Fin 2 → Fin n → ℝ)
    (c0 : ℝ) (hn : 0 < n) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0) (hu : UnivHomog c c0)
    (St : Finset (Fin n)) (hSt : MultiStoreAssort.SMR.IsStilde r v St) :
    ∃ S : Fin 2 → Finset (Fin n), IsOptQ ![l, 1 - l] r v c S ∧
      MultiStoreAssort.SMR.IsRevenueOrdered (S 0) ∧ MultiStoreAssort.SMR.IsRevenueOrdered (S 1) ∧
      (l < 1 / 2 → S 1 ⊆ St ∧ St ⊆ S 0) ∧ (1 / 2 ≤ l → S 0 ⊆ St ∧ St ⊆ S 1) := by
  classical
  have hlam : ∀ i, 0 ≤ (![l, 1 - l] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp <;> linarith
  have hsum : ∑ i, (![l, 1 - l] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
  rcases le_or_gt (1 / 2) l with hl | hl
  · obtain ⟨S, hopt, -, h0, h1, hro0, hro1⟩ := theorem3_univ_homog (M := 0) ![l, 1 - l] r v c c0 hn
      hlam hsum hr hrpos hv hcii hu (by intro i; fin_cases i <;> simp <;> linarith) St hSt
    exact ⟨S, hopt, hro0, hro1, fun h => absurd h (not_lt.mpr hl), fun _ => ⟨h0, h1⟩⟩
  · -- swap the two stores
    set c' : Fin 2 → Fin 2 → Fin n → ℝ := fun i j k => c i.rev j.rev k
    have hu' : UnivHomog c' c0 := ⟨hu.1, fun i j k h => hu.2 _ _ _ (fun h' => h (Fin.rev_injective h'))⟩
    have hcii' : ∀ i k, c' i i k = 0 := fun i k => hcii _ _
    have hlam' : ∀ i, 0 ≤ (![1 - l, l] : Fin 2 → ℝ) i := by
      intro i; fin_cases i <;> simp <;> linarith
    have hsum' : ∑ i, (![1 - l, l] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
    obtain ⟨S', hopt', -, h0, h1, hro0, hro1⟩ := theorem3_univ_homog (M := 0) ![1 - l, l] r v c' c0 hn
      hlam' hsum' hr hrpos hv hcii' hu' (by intro i; fin_cases i <;> simp <;> linarith) St hSt
    have hsw : StoreWiseHomog c (fun _ => c0) := ⟨fun _ => hu.1, fun i j k h => hu.2 i j k h⟩
    have hsw' : StoreWiseHomog c' (fun _ => c0) := ⟨fun _ => hu'.1, fun i j k h => hu'.2 i j k h⟩
    have key : ∀ T : Fin 2 → Finset (Fin n),
        revQ ![1 - l, l] r v c' (fun i => T i.rev) = revQ ![l, 1 - l] r v c T := by
      intro T
      have hSb : Sbar (fun i => T i.rev) = Sbar T := by
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨j, -, hj⟩ := Finset.mem_sup.mp hx
          exact Finset.mem_sup.mpr ⟨j.rev, Finset.mem_univ _, hj⟩
        · intro x hx
          obtain ⟨j, -, hj⟩ := Finset.mem_sup.mp hx
          exact Finset.mem_sup.mpr ⟨j.rev, Finset.mem_univ _, by simpa using hj⟩
      rw [SQR2Aux.revQ_eq _ r v c' (fun _ => c0) hsw', SQR2Aux.revQ_eq _ r v c (fun _ => c0) hsw, hSb]
      simp [Fin.sum_univ_two]
      ring
    refine ⟨fun i => S' i.rev, ?_, ?_, ?_, fun _ => ?_, fun h => absurd h (not_le.mpr hl)⟩
    · intro T
      rw [← key T, ← key (fun i => S' i.rev)]
      simp only [Fin.rev_rev]
      exact hopt' _
    · simpa using hro1
    · simpa using hro0
    · exact ⟨by simpa using h0, by simpa using h1⟩
