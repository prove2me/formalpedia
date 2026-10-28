-- Prove2me | solution 1 for MultiStoreAssort.SQR.propositionB2_nested_revenue_ordered
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T14:05:56.949199+00:00
-- url     : https://prove2.me/submissions/801e6c5c-4e9f-4646-81bc-eb11b7122d42

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model
import Theorems.Thm_MultiStoreAssort_SQR_propositionB1_subset_last

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


theorem claim {m : ℕ} (l d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, l i < 0 → 0 < l j → d i ≤ d j) (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y)
    (hy : ∑ i, l i / (d i + y) ≤ 0) : ∑ i, l i / (d i + x) ≤ 0 := by
  classical
  by_cases hneg : ∃ i, l i < 0
  · have hne : (Finset.univ.filter (fun i => l i < 0)).Nonempty := by
      obtain ⟨i, hi⟩ := hneg; exact ⟨i, by simp [hi]⟩
    set D := (Finset.univ.filter (fun i => l i < 0)).sup' hne d
    have hDge : ∀ i, l i < 0 → d i ≤ D := fun i hi =>
      Finset.le_sup' d (by simp [hi])
    have hDle : ∀ j, 0 < l j → D ≤ d j := by
      intro j hj
      apply Finset.sup'_le
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hsep i j hi hj
    have hDpos : 0 < D := by
      obtain ⟨i, hi⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact lt_of_lt_of_le (hd i) (hDge i hi)
    set ρ := (D + y) / (D + x)
    have hρ : 0 < ρ := div_pos (by linarith) (by linarith)
    have hterm : ∀ i, l i / (d i + x) ≤ ρ * (l i / (d i + y)) := by
      intro i
      have hdi := hd i
      have hsign : l i * (D - d i) ≤ 0 := by
        rcases lt_trichotomy (l i) 0 with h | h | h
        · have := hDge i h; nlinarith
        · rw [h]; simp
        · have := hDle i h; nlinarith
      have hid : l i / (d i + x) - ρ * (l i / (d i + y)) =
          l i * (D - d i) * (y - x) / ((d i + y) * (d i + x) * (D + x)) := by
        have h1 : d i + y ≠ 0 := by linarith
        have h2 : d i + x ≠ 0 := by linarith
        have h3 : D + x ≠ 0 := by linarith
        simp only [ρ]
        field_simp
        ring
      have : l i * (D - d i) * (y - x) / ((d i + y) * (d i + x) * (D + x)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg hsign (by linarith)
        · have : 0 < d i + y := by linarith
          have : 0 < d i + x := by linarith
          have : 0 < D + x := by linarith
          positivity
      linarith
    calc ∑ i, l i / (d i + x) ≤ ∑ i, ρ * (l i / (d i + y)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = ρ * ∑ i, l i / (d i + y) := by rw [Finset.mul_sum]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hy
  · push Not at hneg
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ l i / (d i + y) := fun i _ =>
      div_nonneg (hneg i) (by linarith [hd i])
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm hy (Finset.sum_nonneg hnn))
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i _
    have h1 := hz i (Finset.mem_univ _)
    have hdy : d i + y ≠ 0 := by linarith [hd i]
    have : l i = 0 := by
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact h
      · exact absurd h hdy
    rw [this, zero_div]


/-- Three-point quasi-convexity of `F x = ∑ (aᵢ + bᵢ x)/(dᵢ + x)` under sign separation of
`tᵢ = bᵢ dᵢ - aᵢ` (the argument of Lemma B.4). -/
theorem qc_core {m : ℕ} (a b d : Fin m → ℝ) (hd0 : ∀ i, 0 < d i)
    (hsep0 : ∀ i j, b i * d i - a i < 0 → 0 < b j * d j - a j → d i ≤ d j)
    (x z y : ℝ) (hx : 0 ≤ x) (hxz : x < z) (hzy : z < y) :
    ∑ i, (a i + b i * z) / (d i + z) ≤
      max (∑ i, (a i + b i * x) / (d i + x)) (∑ i, (a i + b i * y) / (d i + y)) := by
  set f : ℝ → ℝ := fun x => ∑ i, (a i + b i * x) / (d i + x) with hf
  set t : Fin m → ℝ := fun i => b i * d i - a i
  have hdiff : ∀ x y, 0 ≤ x → 0 ≤ y →
      f y - f x = (y - x) * ∑ i, t i / (d i + y) / (d i + x) := by
    intro x y hx hy
    simp only [hf, t]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : d i + x ≠ 0 := by linarith [hd0 i]
    have h2 : d i + y ≠ 0 := by linarith [hd0 i]
    field_simp
    ring
  have hsep : ∀ z, 0 ≤ z → ∀ i j, t i / (d i + z) < 0 → 0 < t j / (d j + z) → d i ≤ d j := by
    intro z hz i j hi hj
    have hzi : 0 < d i + z := by linarith [hd0 i]
    have hzj : 0 < d j + z := by linarith [hd0 j]
    have hti : t i < 0 := by
      by_contra h; push Not at h; exact absurd hi (not_lt.mpr (div_nonneg h hzi.le))
    have htj : 0 < t j := by
      by_contra h; push Not at h; exact absurd hj (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h hzj.le))
    exact hsep0 i j hti htj
  show f z ≤ max (f x) (f y)
  have hz : 0 ≤ z := by linarith
  have hy0 : 0 ≤ y := by linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hcon
  have e1 := hdiff x z hx hz
  have e2 := hdiff z y hz hy0
  set l : Fin m → ℝ := fun i => t i / (d i + z)
  have s1 : 0 < ∑ i, l i / (d i + x) := by
    have : 0 < (z - x) * ∑ i, t i / (d i + z) / (d i + x) := by linarith
    exact pos_of_mul_pos_right this (by linarith)
  have s2 : ∑ i, l i / (d i + y) < 0 := by
    have hc : ∑ i, l i / (d i + y) = ∑ i, t i / (d i + y) / (d i + z) := by
      apply Finset.sum_congr rfl; intro i _; simp only [l]; rw [div_div, div_div, mul_comm]
    rw [hc]
    have : (y - z) * ∑ i, t i / (d i + y) / (d i + z) < 0 := by linarith
    exact neg_of_mul_neg_right this (by linarith)
  have := claim l d hd0 (hsep z hz) x y hx (by linarith) s2.le
  linarith

/-- `∑_{A∖X} = ∑_{B∖X} + ∑_{A∖B}` for `X ⊆ B ⊆ A`. -/
theorem sum_sdiff3 {n : ℕ} (f : Fin n → ℝ) (X B A : Finset (Fin n)) (hXB : X ⊆ B) (hBA : B ⊆ A) :
    ∑ k ∈ A \ X, f k = ∑ k ∈ B \ X, f k + ∑ k ∈ A \ B, f k := by
  have h1 := Finset.sum_sdiff (f := f) hBA
  have h2 := Finset.sum_sdiff (f := f) hXB
  have h3 := Finset.sum_sdiff (f := f) (hXB.trans hBA)
  linarith

/-- `∑_{(insert k A)∖X} = ∑_{A∖X} + f k` for `X ⊆ A`, `k ∉ A`. -/
theorem sum_insert_sdiff {n : ℕ} (f : Fin n → ℝ) (X A : Finset (Fin n)) (k : Fin n) (hXA : X ⊆ A)
    (hk : k ∉ A) : ∑ j ∈ insert k A \ X, f j = ∑ j ∈ A \ X, f j + f k := by
  have h1 := Finset.sum_sdiff (f := f) (hXA.trans (Finset.subset_insert k A))
  have h2 := Finset.sum_sdiff (f := f) hXA
  rw [Finset.sum_insert hk] at h1
  linarith

theorem real_termN (lam β E G P W' V' ρ x e : ℝ) (hβE : β * E = 1) (hβ : 0 < β) (hP : 0 < P)
    (hV' : 0 ≤ V') (hx : 0 ≤ x) :
    lam * (G / P + β * (W' + ρ * x + e) / (P * (P + β * (V' + x)))) =
      lam * G / P + (lam * W' / P + lam * ρ / P * x) / (P * E + V' + x) +
        lam * β * e / (P * (P + β * (V' + x))) := by
  have hE : E = β⁻¹ := eq_inv_of_mul_eq_one_right hβE
  subst hE
  have h1 : P + β * (V' + x) ≠ 0 := by positivity
  have h2 : P * β⁻¹ + V' + x ≠ 0 := by positivity
  field_simp
  ring

theorem real_termT (lam WB VB ρ x e : ℝ) (hVB : 0 ≤ VB) (hx : 0 ≤ x) :
    lam * ((WB + ρ * x + e) / (1 + (VB + x))) =
      (lam * WB + lam * ρ * x) / ((1 + VB) + x) + lam * e / (1 + VB + x) := by
  have h1 : 1 + (VB + x) ≠ 0 := by positivity
  have h2 : 1 + VB + x ≠ 0 := by positivity
  field_simp
  ring

open MultiStoreAssort.SMR in
/-- General form of (B.4)/(B.5): let `T` be a block of stores (containing `L`) all offering
`A = S L`, every other store offering a subset of `B ⊆ A`, and every product of `A ∖ B` ranked
after a product `k ∉ A`. Then giving the block `A ∪ {k}` or giving it `B` is at least as good. -/
theorem gen_move {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hsw : StoreWiseHomog c cs) (hmono : Monotone cs)
    (S : Fin m → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (L : Fin m) (T : Finset (Fin m)) (hLT : L ∈ T) (hT : ∀ i ∈ T, S i = S L)
    (B : Finset (Fin n)) (hB : ∀ i, i ∉ T → S i ⊆ B) (hBA : B ⊆ S L)
    (k : Fin n) (hk : k ∉ S L) (hkD : ∀ j ∈ S L \ B, k < j) :
    revQ lam r v c S ≤ max (revQ lam r v c (fun i => if i ∈ T then insert k (S L) else S i))
                           (revQ lam r v c (fun i => if i ∈ T then B else S i)) := by
  classical
  set A := S L with hAdef
  by_cases hD : A \ B = ∅
  · have hAB : A ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hD
    have hBeq : B = A := Finset.Subset.antisymm hBA hAB
    have : (fun i => if i ∈ T then B else S i) = S := by
      funext i; split_ifs with hi
      · rw [hBeq, hT i hi]
      · rfl
    rw [this]; exact le_max_right _ _
  have hDne : (A \ B).Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
  set D := A \ B with hDdef
  set vD := Vs v D with hvDdef
  set wD := Ws r v D with hwDdef
  have hsplitW : ∀ X, X ⊆ B → Ws r v (A \ X) = Ws r v (B \ X) + wD := by
    intro X hX; rw [hwDdef, hDdef]; unfold Ws; exact sum_sdiff3 _ _ _ _ hX hBA
  have hsplitV : ∀ X, X ⊆ B → Vs v (A \ X) = Vs v (B \ X) + vD := by
    intro X hX; rw [hvDdef, hDdef]; unfold Vs; exact sum_sdiff3 _ _ _ _ hX hBA
  have hinsW : ∀ X, X ⊆ A → Ws r v (insert k A \ X) = Ws r v (A \ X) + r k * v k := by
    intro X hX; unfold Ws; exact sum_insert_sdiff (fun j => r j * v j) X A k hX hk
  have hinsV : ∀ X, X ⊆ A → Vs v (insert k A \ X) = Vs v (A \ X) + v k := by
    intro X hX; unfold Vs; exact sum_insert_sdiff v X A k hX hk
  have hvD : 0 < vD := Finset.sum_pos (fun j _ => hv j) hDne
  set ρ := wD / vD with hρdef
  have hρv : ρ * vD = wD := div_mul_cancel₀ _ hvD.ne'
  have hρ0 : 0 ≤ ρ := div_nonneg (Ws_nonneg r v hrpos hv D) hvD.le
  have hρk : ρ ≤ r k := by
    rw [div_le_iff₀ hvD]
    simp only [wD, vD, Ws, Vs]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have := hr (hkD j hj)
    have := hv j
    nlinarith
  -- store parameters
  set β : Fin m → ℝ := fun i => Real.exp (-(cs i))
  set E : Fin m → ℝ := fun i => Real.exp (cs i)
  have hβE : ∀ i, β i * E i = 1 := by
    intro i; simp only [β, E]; rw [← Real.exp_add]; simp
  have hβ0 : ∀ i, 0 < β i := fun i => Real.exp_pos _
  have hE1 : ∀ i, 1 ≤ E i := fun i => Real.one_le_exp (hsw.1 i).le
  set P : Fin m → ℝ := fun i => 1 + Vs v (S i)
  have hP : ∀ i, 0 < P i := fun i => by
    have := Vs_nonneg v hv (S i); simp only [P]; linarith
  set WB := Ws r v B
  set VB := Vs v B
  have hVB : 0 ≤ VB := Vs_nonneg v hv B
  set a : Fin m → ℝ := fun i => if i ∈ T then lam i * WB else lam i * Ws r v (B \ S i) / P i
  set b : Fin m → ℝ := fun i => if i ∈ T then lam i * ρ else lam i * ρ / P i
  set d : Fin m → ℝ := fun i => if i ∈ T then 1 + VB else P i * E i + Vs v (B \ S i)
  set cc : Fin m → ℝ := fun i => if i ∈ T then 0 else lam i * Ws r v (S i) / P i
  set F : ℝ → ℝ := fun x => ∑ i, (a i + b i * x) / (d i + x) with hF
  -- generic store identity
  have hterm : ∀ (U : Finset (Fin n)) (x e : ℝ), 0 ≤ x → 0 ≤ e → B ⊆ U →
      (∀ i, i ∉ T → Ws r v (U \ S i) = Ws r v (B \ S i) + ρ * x + e ∧
        Vs v (U \ S i) = Vs v (B \ S i) + x) →
      Ws r v U = WB + ρ * x + e → Vs v U = VB + x →
      ∀ i, (if i ∈ T then lam i * rev8 r v (β i) U U else lam i * rev8 r v (β i) U (S i)) ≥
        cc i + (a i + b i * x) / (d i + x) ∧
      (e = 0 → (if i ∈ T then lam i * rev8 r v (β i) U U else lam i * rev8 r v (β i) U (S i)) =
        cc i + (a i + b i * x) / (d i + x)) := by
    intro U x e hx he hBU hN hWU hVU i
    by_cases hi : i ∈ T
    · simp only [hi, if_true, cc, a, b, d]
      rw [rev8_self, hWU, hVU, real_termT _ _ _ _ _ _ hVB hx]
      have : 0 ≤ lam i * e / (1 + VB + x) := by
        have := hlam i; positivity
      constructor
      · linarith
      · intro he0; rw [he0]; simp
    · simp only [hi, if_false, cc, a, b, d]
      obtain ⟨h1, h2⟩ := hN i hi
      unfold rev8
      rw [h1, h2]
      have hV' : 0 ≤ Vs v (B \ S i) := Vs_nonneg v hv _
      rw [real_termN (lam i) (β i) (E i) (Ws r v (S i)) (P i) (Ws r v (B \ S i)) (Vs v (B \ S i))
        ρ x e (hβE i) (hβ0 i) (hP i) hV' hx]
      have : 0 ≤ lam i * β i * e / (P i * (P i + β i * (Vs v (B \ S i) + x))) := by
        have := hlam i; have := hβ0 i; have := hP i; positivity
      constructor
      · simp only [P] at this ⊢; linarith
      · intro he0; rw [he0]; simp
  have hSi_sub : ∀ i, i ∉ T → S i ⊆ B := hB
  -- the three profiles
  set S1 : Fin m → Finset (Fin n) := fun i => if i ∈ T then insert k A else S i
  set S2 : Fin m → Finset (Fin n) := fun i => if i ∈ T then B else S i
  have hSb : Sbar S = A := by
    apply Sbar_eq S L; intro i
    by_cases hi : i ∈ T
    · rw [hT i hi]
    · exact (hB i hi).trans hBA
  have hSb1 : Sbar S1 = insert k A := by
    rw [Sbar_eq S1 L]
    · simp [S1, hLT]
    · intro i; simp only [S1, hLT, if_true]; split_ifs with hi
      · exact le_rfl
      · exact (hB i hi).trans (hBA.trans (Finset.subset_insert _ _))
  have hSb2 : Sbar S2 = B := by
    rw [Sbar_eq S2 L]
    · simp [S2, hLT]
    · intro i; simp only [S2, hLT, if_true]; split_ifs with hi
      · exact le_rfl
      · exact hB i hi
  have hWA : Ws r v A = WB + ρ * vD + 0 := by
    have := hsplitW ∅ (Finset.empty_subset _)
    rw [Finset.sdiff_empty, Finset.sdiff_empty] at this; rw [this, hρv]; ring
  have hVA : Vs v A = VB + vD := by
    have := hsplitV ∅ (Finset.empty_subset _)
    rw [Finset.sdiff_empty, Finset.sdiff_empty] at this; exact this
  -- E0
  have E0 : revQ lam r v c S = ∑ i, cc i + F vD := by
    rw [SQR2Aux.revQ_eq lam r v c cs hsw S, hSb, hF, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h := (hterm A vD 0 hvD.le le_rfl hBA (fun i hi => by
      refine ⟨?_, ?_⟩
      · rw [hsplitW _ (hB i hi), hρv]; ring
      · rw [hsplitV _ (hB i hi)]) hWA hVA i).2 rfl
    by_cases hi : i ∈ T
    · simp only [hi, if_true] at h; rw [hT i hi]; exact h
    · simp only [hi, if_false] at h; exact h
  -- E1
  have x1pos : 0 ≤ vD + v k := by linarith [hv k]
  have he1 : 0 ≤ wD - ρ * vD + (r k - ρ) * v k := by
    rw [hρv]; have := hv k; nlinarith
  have hkA : k ∉ A := hk
  have E1 : ∑ i, cc i + F (vD + v k) ≤ revQ lam r v c S1 := by
    rw [SQR2Aux.revQ_eq lam r v c cs hsw S1, hSb1, hF, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have h := (hterm (insert k A) (vD + v k) (wD - ρ * vD + (r k - ρ) * v k) x1pos he1
      (hBA.trans (Finset.subset_insert _ _))
      (fun i hi => by
        refine ⟨?_, ?_⟩
        · rw [hinsW _ ((hB i hi).trans hBA), hsplitW _ (hB i hi)]; ring
        · rw [hinsV _ ((hB i hi).trans hBA), hsplitV _ (hB i hi)]; ring)
      (by have := hinsW ∅ (Finset.empty_subset _); rw [Finset.sdiff_empty, Finset.sdiff_empty] at this
          rw [this, hWA, ← hρv]; ring)
      (by have := hinsV ∅ (Finset.empty_subset _); rw [Finset.sdiff_empty, Finset.sdiff_empty] at this
          rw [this, hVA]; ring) i).1
    by_cases hi : i ∈ T
    · simp only [hi, if_true] at h; simp only [S1, hi, if_true]; exact h
    · simp only [hi, if_false] at h; simp only [S1, hi, if_false]; exact h
  -- E2
  have E2 : revQ lam r v c S2 = ∑ i, cc i + F 0 := by
    rw [SQR2Aux.revQ_eq lam r v c cs hsw S2, hSb2, hF, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h := (hterm B 0 0 le_rfl le_rfl le_rfl (fun i hi => by simp) (by simp [WB])
      (by simp [VB]) i).2 rfl
    by_cases hi : i ∈ T
    · simp only [hi, if_true] at h; simp only [S2, hi, if_true]; exact h
    · simp only [hi, if_false] at h; simp only [S2, hi, if_false]; exact h
  -- quasi-convexity
  have hd0 : ∀ i, 0 < d i := by
    intro i; simp only [d]; split_ifs
    · linarith
    · have := hP i; have := hE1 i; have := Vs_nonneg v hv (B \ S i); nlinarith
  -- d for non-block stores: P (E - 1) + 1 + VB
  have hdN : ∀ i, i ∉ T → d i = P i * (E i - 1) + 1 + VB := by
    intro i hi
    simp only [d, hi, if_false, P, VB]
    have := Finset.sum_sdiff (f := v) (hB i hi)
    simp only [Vs] at this ⊢; linarith
  have hdT : ∀ i, i ∈ T → d i = 1 + VB := by intro i hi; simp [d, hi]
  have hdmin : ∀ i j, i ∈ T → d i ≤ d j := by
    intro i j hi
    rw [hdT i hi]
    by_cases hj : j ∈ T
    · rw [hdT j hj]
    · rw [hdN j hj]; have := hP j; have := hE1 j; nlinarith
  have hdmono : ∀ i j, i ∉ T → j ∉ T → i ≤ j → d i ≤ d j := by
    intro i j hi hj hij
    rw [hdN i hi, hdN j hj]
    have h1 : P i ≤ P j := by
      simp only [P]
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := v) (hchain i j hij) (fun k _ _ => (hv k).le)
      simp only [Vs]; linarith
    have h2 : E i ≤ E j := Real.exp_le_exp.mpr (hmono hij)
    have := hP i; have := hE1 i
    nlinarith
  have hab : ∀ i j, d j < d i → a i * b j ≤ a j * b i := by
    intro i j hji
    by_cases hi : i ∈ T
    · exact absurd (hdmin i j hi) (not_le.mpr hji)
    by_cases hj : j ∈ T
    · simp only [a, b, hi, hj, if_true, if_false]
      have hW : Ws r v (B \ S i) ≤ WB :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun k _ _ => (mul_pos (hrpos k) (hv k)).le)
      have := hlam i; have := hlam j; have := hP i
      have hq : lam i * Ws r v (B \ S i) / P i * (lam j * ρ) =
          (lam i * lam j * ρ / P i) * Ws r v (B \ S i) := by ring
      have hq2 : lam j * WB * (lam i * ρ / P i) = (lam i * lam j * ρ / P i) * WB := by ring
      rw [hq, hq2]
      apply mul_le_mul_of_nonneg_left hW; positivity
    · simp only [a, b, hi, hj, if_false]
      have hjl : j < i := by
        by_contra h; push Not at h; exact absurd (hdmono i j hi hj h) (not_le.mpr hji)
      have hW : Ws r v (B \ S i) ≤ Ws r v (B \ S j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset_sdiff le_rfl (hchain j i hjl.le))
          (fun k _ _ => (mul_pos (hrpos k) (hv k)).le)
      have := hlam i; have := hlam j; have := hP i; have := hP j
      have hq : lam i * Ws r v (B \ S i) / P i * (lam j * ρ / P j) =
          (lam i * lam j * ρ / (P i * P j)) * Ws r v (B \ S i) := by field_simp
      have hq2 : lam j * Ws r v (B \ S j) / P j * (lam i * ρ / P i) =
          (lam i * lam j * ρ / (P i * P j)) * Ws r v (B \ S j) := by field_simp
      rw [hq, hq2]
      apply mul_le_mul_of_nonneg_left hW; positivity
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i; simp only [a]; split_ifs
    · exact mul_nonneg (hlam i) (Ws_nonneg r v hrpos hv B)
    · have := hP i; have := hlam i; have := Ws_nonneg r v hrpos hv (B \ S i); positivity
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i; simp only [b]; split_ifs
    · exact mul_nonneg (hlam i) hρ0
    · have := hP i; have := hlam i; positivity
  have hsep : ∀ i j, b i * d i - a i < 0 → 0 < b j * d j - a j → d i ≤ d j := by
    intro i j hti htj
    by_contra hlt; push Not at hlt
    have hab' := hab i j hlt
    have hbj : 0 < b j := by
      rcases (hb0 j).lt_or_eq with h | h
      · exact h
      · rw [← h] at htj; have := ha0 j; linarith
    have hai : 0 < a i := by have := hb0 i; have := hd0 i; nlinarith
    have hbi : 0 < b i := by
      rcases (hb0 i).lt_or_eq with h | h
      · exact h
      · rw [← h] at hab'; have := mul_pos hai hbj; linarith
    have := hd0 i; have := hd0 j
    nlinarith [mul_pos hbi hbj]
  have hQ := qc_core a b d hd0 hsep 0 vD (vD + v k) le_rfl hvD (by linarith [hv k])
  show revQ lam r v c S ≤ max (revQ lam r v c S1) (revQ lam r v c S2)
  rw [E0]
  rw [max_comm] at hQ
  calc ∑ i, cc i + F vD ≤ ∑ i, cc i + max (F (vD + v k)) (F 0) := by
        simp only [hF] at hQ ⊢; linarith
    _ = max (∑ i, cc i + F (vD + v k)) (∑ i, cc i + F 0) := by rw [max_add_add_left]
    _ ≤ max (revQ lam r v c S1) (revQ lam r v c S2) := by
        rw [E2]; exact max_le_max E1 le_rfl

end SQR2Aux

namespace SQR2B2

/-- Revenue of (8) written in terms of `G = W(S₁)`, `P = 1 + V(S₁)`, `w = W(S₂∖S₁)`, `y = V(S₂∖S₁)`. -/
noncomputable def h (β G P w y : ℝ) : ℝ := G / P + β * w / (P * (P + β * y))

/-- Moving a product with revenue `r` and attraction `t` into `S₁` (`t > 0`) or out of `S₁`
(`t < 0`): the change in revenue factors as a positive/negative multiple of `r - θ`. -/
theorem move_identity (β G P w y t r : ℝ) (hP : 0 < P) (hQ : 0 < P + β * y) (hPt : 0 < P + t)
    (hQs : 0 < P + β * y + (1 - β) * t) (hQb : 0 < P + β * y - β + (1 - β) * t) :
    h β (G + r * t) (P + t) (w - r * t) (y - t) - h β G P w y =
    t * (P + β * y + (1 - β) * t - β) / ((P + t) * (P + β * y + (1 - β) * t)) *
      (r - ((G * (P + β * y) / P + β * w * ((1 - β) * P + (P + β * y)) / (P * (P + β * y))) +
        (G / P + β * w / (P * (P + β * y))) * ((1 - β) * t)) / (P + β * y - β + (1 - β) * t)) := by
  unfold h
  have h1 : P + t + β * (y - t) = P + β * y + (1 - β) * t := by ring
  rw [h1]
  set Q := P + β * y with hQdef
  set s := (1 - β) * t with hsdef
  have e1 : (P + t) ≠ 0 := hPt.ne'
  have e2 : Q + s ≠ 0 := hQs.ne'
  have e3 : Q - β + s ≠ 0 := hQb.ne'
  have e4 : P ≠ 0 := hP.ne'
  have e5 : Q ≠ 0 := hQ.ne'
  field_simp
  rw [hsdef]
  ring

/-- The exchange inequality behind Lemma B.2: if neither adding product `j` nor removing product
`k` improves (8), then `r_j ≤ r_k`. -/
theorem exchange (β G P w y vj uk rj rk : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hG : 0 ≤ G)
    (hw : 0 ≤ w) (hvj : 0 < vj) (huk : 0 < uk) (hPu : 1 ≤ P - uk) (hyv : vj ≤ y)
    (h1 : h β (G + rj * vj) (P + vj) (w - rj * vj) (y - vj) ≤ h β G P w y)
    (h2 : h β (G + rk * (-uk)) (P + (-uk)) (w - rk * (-uk)) (y - (-uk)) ≤ h β G P w y) :
    rj ≤ rk := by
  have hy : 0 ≤ y := by linarith
  have hP : 0 < P := by linarith
  have hQ : 0 < P + β * y := by nlinarith
  set Q := P + β * y with hQdef
  set g := G / P + β * w / (P * Q)
  set N0 := G * Q / P + β * w * ((1 - β) * P + Q) / (P * Q)
  -- N0 - g (Q - β) ≥ 0
  have hN : 0 ≤ N0 - g * (Q - β) := by
    have : N0 - g * (Q - β) = β * G / P + β * w * ((1 - β) * P + β) / (P * Q) := by
      simp only [N0, g]; field_simp; ring
    rw [this]
    have : 0 ≤ (1 - β) * P + β := by nlinarith
    positivity
  set s1 := (1 - β) * vj
  set s2 := (1 - β) * (-uk)
  have hD1 : 0 < Q - β + s1 := by
    have : 0 ≤ s1 := by positivity
    nlinarith
  have hD2 : 0 < Q - β + s2 := by
    simp only [s2, hQdef]; nlinarith
  -- adding j
  have i1 := move_identity β G P w y vj rj hP hQ (by linarith) (by nlinarith) hD1
  have i2 := move_identity β G P w y (-uk) rk hP hQ (by linarith) (by simp only [hQdef] at hD2 ⊢; nlinarith) hD2
  set θ1 := (N0 + g * s1) / (Q - β + s1)
  set θ2 := (N0 + g * s2) / (Q - β + s2)
  have hc1 : 0 < vj * (Q + s1 - β) / ((P + vj) * (Q + s1)) := by
    have : 0 < Q + s1 := by linarith
    have : 0 < Q + s1 - β := by linarith
    have : 0 < P + vj := by linarith
    positivity
  have hc2 : 0 < uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) := by
    have : 0 < Q + s2 := by linarith
    have : 0 < Q + s2 - β := by linarith
    have : 0 < P + -uk := by linarith
    positivity
  have hr1 : rj ≤ θ1 := by
    have : vj * (Q + s1 - β) / ((P + vj) * (Q + s1)) * (rj - θ1) ≤ 0 := by
      rw [← i1]; linarith
    by_contra hc; push Not at hc
    have := mul_pos hc1 (sub_pos.mpr hc); linarith
  have hr2 : θ2 ≤ rk := by
    have e : -uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2) =
        -(uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2)) := by ring
    have : -uk * (Q + s2 - β) / ((P + -uk) * (Q + s2)) * (rk - θ2) ≤ 0 := by
      rw [← i2]; linarith
    rw [e] at this
    by_contra hc; push Not at hc
    have := mul_neg_of_pos_of_neg hc2 (sub_neg.mpr hc); linarith
  have hθ : θ1 ≤ θ2 := by
    rw [div_le_div_iff₀ hD1 hD2]
    have hs : s2 ≤ s1 := by simp only [s1, s2]; nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hN]
  linarith

open MultiStoreAssort.SQR in
/-- Every optimal solution of (8) is revenue-ordered within `S₂` (for `0 ≤ β < 1`). -/
theorem opt_ordered {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (S2 X : Finset (Fin n))
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hXmem : X ⊆ S2) (hopt : ∀ T, T ⊆ S2 → MultiStoreAssort.SQR.rev8 r v β S2 T ≤ MultiStoreAssort.SQR.rev8 r v β S2 X) :
    IsRevOrderedWithin S2 X := by
  classical
  -- every product outside X has a lower revenue (higher index) than every product inside X
  have hord : ∀ j ∈ S2, j ∉ X → ∀ k ∈ X, k < j := by
    intro j hjS hjX k hkX
    by_contra hlt
    push Not at hlt
    have hjk : j < k := lt_of_le_of_ne hlt (by rintro rfl; exact hjX hkX)
    have hrjk : r k < r j := hr hjk
    set G := Ws r v X
    set P := 1 + Vs v X
    set w := Ws r v (S2 \ X)
    set y := Vs v (S2 \ X)
    have hG : 0 ≤ G := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
    have hw : 0 ≤ w := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
    have hjd : j ∈ S2 \ X := Finset.mem_sdiff.mpr ⟨hjS, hjX⟩
    have hyv : v j ≤ y := Finset.single_le_sum (f := v) (fun k _ => (hv k).le) hjd
    have hPu : 1 ≤ P - v k := by
      have : Vs v X = v k + Vs v (X.erase k) := by
        unfold Vs; exact (Finset.add_sum_erase X v hkX).symm
      have : 0 ≤ Vs v (X.erase k) := Finset.sum_nonneg (fun k _ => (hv k).le)
      simp only [P]; linarith
    -- adding j does not help
    have h1 := hopt (insert j X) (Finset.insert_subset hjS hXmem)
    have e1 : S2 \ insert j X = (S2 \ X).erase j := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have h1' : SQR2B2.h β (G + r j * v j) (P + v j) (w - r j * v j) (y - v j) ≤ SQR2B2.h β G P w y := by
      have l : rev8 r v β S2 (insert j X) = SQR2B2.h β (G + r j * v j) (P + v j) (w - r j * v j) (y - v j) := by
        unfold rev8 SQR2B2.h
        have a1 : Ws r v (insert j X) = G + r j * v j := by
          unfold Ws; rw [Finset.sum_insert hjX]; simp only [G, Ws]; ring
        have a2 : 1 + Vs v (insert j X) = P + v j := by
          unfold Vs; rw [Finset.sum_insert hjX]; simp only [P, Vs]; ring
        have a3 : Ws r v (S2 \ insert j X) = w - r j * v j := by
          rw [e1]; unfold Ws; rw [Finset.sum_erase_eq_sub hjd]; rfl
        have a4 : Vs v (S2 \ insert j X) = y - v j := by
          rw [e1]; unfold Vs; rw [Finset.sum_erase_eq_sub hjd]; rfl
        rw [a1, a2, a3, a4]
      have r0 : rev8 r v β S2 X = SQR2B2.h β G P w y := rfl
      rw [← l, ← r0]; exact h1
    -- removing k does not help
    have h2 := hopt (X.erase k) ((Finset.erase_subset k X).trans hXmem)
    have hkd : k ∉ S2 \ X := fun h => (Finset.mem_sdiff.mp h).2 hkX
    have e2 : S2 \ X.erase k = insert k (S2 \ X) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = k
        · left; exact hx
        · right; exact ⟨h1, fun h => h2 ⟨hx, h⟩⟩
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨hXmem hkX, fun h => h.1 rfl⟩
        · exact ⟨h1, fun h => h2 h.2⟩
    have h2' : SQR2B2.h β (G + r k * (-v k)) (P + (-v k)) (w - r k * (-v k)) (y - (-v k)) ≤
        SQR2B2.h β G P w y := by
      have l : rev8 r v β S2 (X.erase k) =
          SQR2B2.h β (G + r k * (-v k)) (P + (-v k)) (w - r k * (-v k)) (y - (-v k)) := by
        unfold rev8 SQR2B2.h
        have a1 : Ws r v (X.erase k) = G + r k * (-v k) := by
          unfold Ws; rw [Finset.sum_erase_eq_sub hkX]; simp only [G, Ws]; ring
        have a2 : 1 + Vs v (X.erase k) = P + (-v k) := by
          unfold Vs; rw [Finset.sum_erase_eq_sub hkX]; simp only [P, Vs]; ring
        have a3 : Ws r v (S2 \ X.erase k) = w - r k * (-v k) := by
          rw [e2]; unfold Ws; rw [Finset.sum_insert hkd]; simp only [w, Ws]; ring
        have a4 : Vs v (S2 \ X.erase k) = y - (-v k) := by
          rw [e2]; unfold Vs; rw [Finset.sum_insert hkd]; simp only [y, Vs]; ring
        rw [a1, a2, a3, a4]
      have r0 : rev8 r v β S2 X = SQR2B2.h β G P w y := rfl
      rw [← l, ← r0]; exact h2
    have := SQR2B2.exchange β G P w y (v j) (v k) (r j) (r k) hβ0 hβ1 hG hw (hv j) (hv k) hPu hyv
      h1' h2'
    linarith
  refine ⟨X.sup (fun k => k.val + 1), ?_⟩
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    refine ⟨hXmem hx, ?_⟩
    have := Finset.le_sup (f := fun k : Fin n => k.val + 1) hx
    omega
  · rintro ⟨hxS, hxlt⟩
    by_contra hxX
    obtain ⟨k, hkX, hk⟩ := Finset.exists_mem_eq_sup X
      (by by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he; rw [he] at hxlt; simp at hxlt)
      (fun k : Fin n => k.val + 1)
    rw [hk] at hxlt
    have := hord x hxS hxX k hkX
    rw [Fin.lt_def] at this
    omega


open MultiStoreAssort.SQR in
/-- Existence of a smallest (minimum-cardinality) optimal solution of (8). -/
theorem exists_smallest {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (A : Finset (Fin n)) :
    ∃ X, X ⊆ A ∧ (∀ T, T ⊆ A → rev8 r v β A T ≤ rev8 r v β A X) ∧
      ∀ Y, Y ⊆ A → (∀ T, T ⊆ A → rev8 r v β A T ≤ rev8 r v β A Y) → X.card ≤ Y.card := by
  classical
  obtain ⟨X0, hX0, hX0max⟩ := Finset.exists_max_image A.powerset (fun T => rev8 r v β A T)
    ⟨∅, Finset.empty_mem_powerset _⟩
  set O := A.powerset.filter (fun Y => ∀ T, T ⊆ A → rev8 r v β A T ≤ rev8 r v β A Y)
  have hO : X0 ∈ O := by
    simp only [O, Finset.mem_filter]
    exact ⟨hX0, fun T hT => hX0max T (Finset.mem_powerset.mpr hT)⟩
  obtain ⟨X, hXO, hXmin⟩ := Finset.exists_min_image O Finset.card ⟨X0, hO⟩
  simp only [O, Finset.mem_filter, Finset.mem_powerset] at hXO
  refine ⟨X, hXO.1, hXO.2, ?_⟩
  intro Y hY hYopt
  exact hXmin Y (by simp only [O, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hY, hYopt⟩)

open MultiStoreAssort.SQR in
/-- The smallest optimal solution of (8) is antitone in `β` (comparative statics behind the
Claim in the proof of Lemma B.1, without the uniqueness assumption). -/
theorem smallest_mono {n : ℕ} (r v : Fin n → ℝ) (A X' X'' : Finset (Fin n)) (β' β'' : ℝ)
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k)
    (hβ'' : 0 ≤ β'') (hββ : β'' ≤ β') (hβ' : β' < 1)
    (hX' : X' ⊆ A) (hopt' : ∀ T, T ⊆ A → rev8 r v β' A T ≤ rev8 r v β' A X')
    (hmin' : ∀ Y, Y ⊆ A → (∀ T, T ⊆ A → rev8 r v β' A T ≤ rev8 r v β' A Y) → X'.card ≤ Y.card)
    (hX'' : X'' ⊆ A) (hopt'' : ∀ T, T ⊆ A → rev8 r v β'' A T ≤ rev8 r v β'' A X'') :
    X' ⊆ X'' := by
  classical
  obtain ⟨J', hJ'⟩ := opt_ordered r v β' A X' hr hrpos hv (by linarith) hβ' hX' hopt'
  obtain ⟨J'', hJ''⟩ := opt_ordered r v β'' A X'' hr hrpos hv hβ'' (by linarith) hX'' hopt''
  rcases le_total J' J'' with hJ | hJ
  · rw [hJ', hJ'']; intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  by_contra hns
  have hsub : X'' ⊆ X' := by
    rw [hJ', hJ'']; intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  have hss : X'' ⊂ X' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hns (h ▸ le_rfl)⟩
  have hlt := Finset.card_lt_card hss
  have a1 : rev8 r v β' A X'' < rev8 r v β' A X' := by
    by_contra h; push Not at h
    have := hmin' X'' hX'' (fun T hT => (hopt' T hT).trans h); omega
  have a2 := hopt'' X' hX'
  have key : ∀ (β1 β2 : ℝ) (S : Finset (Fin n)), 0 ≤ β1 → 0 ≤ β2 →
      rev8 r v β1 A S - rev8 r v β2 A S =
        (β1 - β2) * Ws r v (A \ S) /
          ((1 + Vs v S + β1 * Vs v (A \ S)) * (1 + Vs v S + β2 * Vs v (A \ S))) := by
    intro β1 β2 S h1 h2
    unfold rev8
    have hV : 0 ≤ Vs v S := Finset.sum_nonneg (fun k _ => (hv k).le)
    have hy : 0 ≤ Vs v (A \ S) := Finset.sum_nonneg (fun k _ => (hv k).le)
    have e1 : 1 + Vs v S ≠ 0 := by positivity
    have e2 : 1 + Vs v S + β1 * Vs v (A \ S) ≠ 0 := by positivity
    have e3 : 1 + Vs v S + β2 * Vs v (A \ S) ≠ 0 := by positivity
    field_simp
    ring
  have k1 := key β' β'' X' (by linarith) hβ''
  have k2 := key β' β'' X'' (by linarith) hβ''
  have hgt : (β' - β'') * Ws r v (A \ X'') /
        ((1 + Vs v X'' + β' * Vs v (A \ X'')) * (1 + Vs v X'' + β'' * Vs v (A \ X''))) <
      (β' - β'') * Ws r v (A \ X') /
        ((1 + Vs v X' + β' * Vs v (A \ X')) * (1 + Vs v X' + β'' * Vs v (A \ X'))) := by
    rw [← k1, ← k2]; linarith
  have hsd : A \ X' ⊆ A \ X'' := Finset.sdiff_subset_sdiff (le_refl A) hsub
  have hW : Ws r v (A \ X') ≤ Ws r v (A \ X'') :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (mul_pos (hrpos k) (hv k)).le)
  have hW0 : 0 ≤ Ws r v (A \ X') := Finset.sum_nonneg (fun k _ => (mul_pos (hrpos k) (hv k)).le)
  have hsum' : Vs v (A \ X') + Vs v X' = Vs v A := by unfold Vs; exact Finset.sum_sdiff hX'
  have hsum'' : Vs v (A \ X'') + Vs v X'' = Vs v A := by unfold Vs; exact Finset.sum_sdiff hX''
  have hy' : Vs v (A \ X') ≤ Vs v (A \ X'') :=
    Finset.sum_le_sum_of_subset_of_nonneg hsd (fun k _ _ => (hv k).le)
  have hy0 : 0 ≤ Vs v (A \ X') := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hy0' : 0 ≤ Vs v (A \ X'') := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hV0 : 0 ≤ Vs v X'' := Finset.sum_nonneg (fun k _ => (hv k).le)
  have hV0' : 0 ≤ Vs v X' := Finset.sum_nonneg (fun k _ => (hv k).le)
  set y1 := Vs v (A \ X')
  set y2 := Vs v (A \ X'')
  set w1 := Ws r v (A \ X')
  set w2 := Ws r v (A \ X'')
  have hd1 : 1 + Vs v X'' + β' * y2 ≤ 1 + Vs v X' + β' * y1 := by nlinarith
  have hd2 : 1 + Vs v X'' + β'' * y2 ≤ 1 + Vs v X' + β'' * y1 := by nlinarith
  have p1 : 0 < 1 + Vs v X'' + β' * y2 := by nlinarith
  have p2 : 0 < 1 + Vs v X'' + β'' * y2 := by nlinarith
  have hden : (1 + Vs v X'' + β' * y2) * (1 + Vs v X'' + β'' * y2) ≤
      (1 + Vs v X' + β' * y1) * (1 + Vs v X' + β'' * y1) :=
    mul_le_mul hd1 hd2 p2.le (by linarith)
  have hle : (β' - β'') * w1 / ((1 + Vs v X' + β' * y1) * (1 + Vs v X' + β'' * y1)) ≤
      (β' - β'') * w2 / ((1 + Vs v X'' + β' * y2) * (1 + Vs v X'' + β'' * y2)) := by
    calc (β' - β'') * w1 / ((1 + Vs v X' + β' * y1) * (1 + Vs v X' + β'' * y1))
        ≤ (β' - β'') * w1 / ((1 + Vs v X'' + β' * y2) * (1 + Vs v X'' + β'' * y2)) :=
          div_le_div_of_nonneg_left (mul_nonneg (by linarith) hW0) (mul_pos p1 p2) hden
      _ ≤ (β' - β'') * w2 / ((1 + Vs v X'' + β' * y2) * (1 + Vs v X'' + β'' * y2)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by linarith)) (mul_pos p1 p2).le
  linarith

open MultiStoreAssort.SQR in
/-- For a nonempty `A` and `0 ≤ β < 1`, the empty set is never optimal for (8): offering the
top-revenue product of `A` first is strictly better. -/
theorem empty_not_opt {n : ℕ} (r v : Fin n → ℝ) (β : ℝ) (A : Finset (Fin n))
    (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hA : A.Nonempty) : rev8 r v β A ∅ < rev8 r v β A {A.min' hA} := by
  classical
  set j := A.min' hA
  have hj : j ∈ A := Finset.min'_mem A hA
  have hmax : ∀ x ∈ A, r x ≤ r j := fun x hx => hr.antitone (Finset.min'_le A x hx)
  set W := Ws r v A
  set V := Vs v A
  have hWV : W ≤ r j * V := by
    simp only [W, V, Ws, Vs]; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x hx; have := hmax x hx; have := hv x; nlinarith
  have hVv : v j ≤ V := Finset.single_le_sum (f := v) (fun k _ => (hv k).le) hj
  have hWj : Ws r v (A \ {j}) = W - r j * v j := by
    have := Finset.sum_sdiff (f := fun x => r x * v x) (Finset.singleton_subset_iff.mpr hj)
    simp only [Finset.sum_singleton] at this; simp only [W, Ws]; linarith
  have hVj : Vs v (A \ {j}) = V - v j := by
    have := Finset.sum_sdiff (f := v) (Finset.singleton_subset_iff.mpr hj)
    simp only [Finset.sum_singleton] at this; simp only [V, Vs]; linarith
  have l0 : rev8 r v β A ∅ = β * W / (1 + β * V) := by
    simp [rev8, Ws, Vs, W, V]
  have l1 : rev8 r v β A {j} = r j * v j / (1 + v j) +
      β * (W - r j * v j) / ((1 + v j) * (1 + v j + β * (V - v j))) := by
    unfold rev8; rw [hWj, hVj]; simp [Ws, Vs]
  rw [l0, l1]
  have hvj := hv j
  have hrj := hrpos j
  set K := 1 + v j + β * (V - v j)
  have hK : 0 < K := by simp only [K]; nlinarith
  have hQ : 0 < 1 + β * V := by nlinarith
  have hbr : (1 + v j) * K - (1 + β * V) = v j * (2 + v j + β * V - β - β * v j) := by
    simp only [K]; ring
  have hbr0 : 0 ≤ (1 + v j) * K - (1 + β * V) := by
    rw [hbr]; apply mul_nonneg hvj.le; nlinarith
  have key : r j * v j / (1 + v j) + β * (W - r j * v j) / ((1 + v j) * K) - β * W / (1 + β * V) =
      (r j * v j * (1 - β) * (1 + v j) + β * (r j * V - W) * ((1 + v j) * K - (1 + β * V))) /
        ((1 + v j) * K * (1 + β * V)) := by
    have e1 : (1 + v j) ≠ 0 := by positivity
    have e2 : K ≠ 0 := hK.ne'
    have e3 : (1 + β * V) ≠ 0 := hQ.ne'
    rw [div_add_div _ _ e1 (mul_ne_zero e1 e2), div_sub_div _ _ (mul_ne_zero e1 (mul_ne_zero e1 e2)) e3,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero e1 (mul_ne_zero e1 e2)) e3)
        (mul_ne_zero (mul_ne_zero e1 e2) e3)]
    simp only [K]; ring
  have : 0 < (r j * v j * (1 - β) * (1 + v j) + β * (r j * V - W) * ((1 + v j) * K - (1 + β * V))) /
        ((1 + v j) * K * (1 + β * V)) := by
    apply div_pos
    · have h1 : 0 < r j * v j * (1 - β) * (1 + v j) := by
        have : 0 < 1 - β := by linarith
        positivity
      have h2 : 0 ≤ β * (r j * V - W) * ((1 + v j) * K - (1 + β * V)) := by
        apply mul_nonneg (mul_nonneg hβ0 (by linarith)) hbr0
      linarith
    · positivity
  linarith

end SQR2B2

open MultiStoreAssort.SQR MultiStoreAssort.SMR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hn : 0 < n) (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧ (∀ i j, i ≤ j → S i ⊆ S j) ∧
      ∀ i, MultiStoreAssort.SMR.IsRevenueOrdered (S i) := by
  classical
  set L := Fin.last (M + 1) with hLdef
  set β : Fin (M + 2) → ℝ := fun i => Real.exp (-(cs i)) with hβdef
  have hβ0 : ∀ i, 0 ≤ β i := fun i => (Real.exp_pos _).le
  have hβ1 : ∀ i, β i < 1 := fun i => Real.exp_lt_one_iff.mpr (by linarith [hsw.1 i])
  have hβanti : ∀ i j, i ≤ j → β j ≤ β i := fun i j h =>
    Real.exp_le_exp.mpr (by linarith [hmono h])
  choose sm hsmA hsmopt hsmmin using
    fun (i : Fin (M + 2)) (A : Finset (Fin n)) => SQR2B2.exists_smallest r v (β i) A
  set N : Finset (Fin n) → Fin (M + 2) → Finset (Fin n) :=
    fun A i => if i = L then A else sm i A with hNdef
  have hNL : ∀ A, N A L = A := fun A => by simp [N]
  have hNne : ∀ A i, i ≠ L → N A i = sm i A := fun A i hi => by simp [N, hi]
  have hNsub : ∀ A i, N A i ⊆ A := by
    intro A i; by_cases hi : i = L
    · rw [hi, hNL]
    · rw [hNne A i hi]; exact hsmA i A
  have hSbN : ∀ A, Sbar (N A) = A := fun A => by
    rw [SQR2Aux.Sbar_eq (N A) L (fun i => by rw [hNL]; exact hNsub A i), hNL]
  have hlastle : ∀ j : Fin (M + 2), L ≤ j → j = L := fun j h => le_antisymm (Fin.le_last j) h
  have hNchain : ∀ A i j, i ≤ j → N A i ⊆ N A j := by
    intro A i j hij
    by_cases hj : j = L
    · rw [hj, hNL]; exact hNsub A i
    · have hi : i ≠ L := by rintro rfl; exact hj (hlastle j hij)
      rw [hNne A i hi, hNne A j hj]
      exact SQR2B2.smallest_mono r v A (sm i A) (sm j A) (β i) (β j) hr hrpos hv (hβ0 j)
        (hβanti i j hij) (hβ1 i) (hsmA i A) (hsmopt i A) (hsmmin i A) (hsmA j A) (hsmopt j A)
  have hNge : ∀ S : Fin (M + 2) → Finset (Fin n), (∀ i, S i ⊆ S L) →
      revQ lam r v c S ≤ revQ lam r v c (N (S L)) := by
    intro S hS
    rw [SQR2Aux.revQ_eq lam r v c cs hsw S, SQR2Aux.revQ_eq lam r v c cs hsw (N (S L)),
      SQR2Aux.Sbar_eq S L hS, hSbN]
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hlam i)
    by_cases hi : i = L
    · rw [hi, hNL]
    · rw [hNne _ i hi]; exact hsmopt i (S L) (S i) (hS i)
  -- an optimal profile from Proposition B.1
  obtain ⟨S0, hS0opt, hS0sub⟩ := propositionB1_subset_last lam r v c cs hlam hlam1 hr hrpos hv
    hcii hsw hmin (fun i => hmono (Fin.le_last i))
  have hS0sub' : ∀ i, S0 i ⊆ S0 L := by
    intro i; by_cases hi : i = L
    · rw [hi]
    · exact hS0sub i hi
  have hNopt0 : IsOptQ lam r v c (N (S0 L)) := fun S' => (hS0opt S').trans (hNge S0 hS0sub')
  -- optimal assortments are nonempty
  have hpos : ∀ A, IsOptQ lam r v c (N A) → A.Nonempty := by
    intro A hA
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    set j0 : Fin n := ⟨0, hn⟩
    have h1 := hA (fun _ => {j0})
    have e0 : revQ lam r v c (N A) = 0 := by
      rw [SQR2Aux.revQ_eq lam r v c cs hsw, hSbN, hne]
      apply Finset.sum_eq_zero; intro i _
      have : N ∅ i = ∅ := Finset.subset_empty.mp (hNsub ∅ i)
      rw [this]; simp [rev8, Ws, Vs]
    have e1 : revQ lam r v c (fun _ => {j0}) = r j0 * v j0 / (1 + v j0) := by
      rw [SQR2Aux.revQ_eq lam r v c cs hsw, SQR2Aux.Sbar_eq _ L (fun _ => le_rfl)]
      simp only [SQR2Aux.rev8_self]
      rw [← Finset.sum_mul, hlam1, one_mul]; simp [Ws, Vs]
    rw [e0, e1] at h1
    have : 0 < r j0 * v j0 / (1 + v j0) := by have := hrpos j0; have := hv j0; positivity
    linarith
  -- inversion count
  let pairs : Finset (Fin n) → Finset (Fin n × Fin n) :=
    fun A => ((Finset.univ \ A) ×ˢ A).filter (fun p => p.1 < p.2)
  have hmem : ∀ A p, p ∈ pairs A ↔ p.1 ∉ A ∧ p.2 ∈ A ∧ p.1 < p.2 := by
    intro A p; simp [pairs, Finset.mem_product, and_assoc]
  have main : ∀ g, ∀ A, (pairs A).card = g → IsOptQ lam r v c (N A) →
      ∃ A', MultiStoreAssort.SMR.IsRevenueOrdered A' ∧ IsOptQ lam r v c (N A') := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
    intro A hg hopt
    have hAne := hpos A hopt
    by_cases hinv : ∃ i, i ∉ A ∧ ∃ j ∈ A, i < j
    · obtain ⟨i0, hi0, j0, hj0, hij0⟩ := hinv
      have hmiss : (Finset.univ \ A).Nonempty := ⟨i0, by simp [hi0]⟩
      set k := (Finset.univ \ A).min' hmiss with hkdef
      have hkA : k ∉ A := by
        have := Finset.min'_mem _ hmiss; simp only [Finset.mem_sdiff] at this; exact this.2
      have hkmin : ∀ x, x < k → x ∈ A := by
        intro x hx; by_contra hxA
        have := Finset.min'_le _ x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxA⟩)
        exact absurd hx (not_lt.mpr this)
      have hkj : k < j0 := lt_of_le_of_lt (Finset.min'_le _ i0 (by simp [hi0])) hij0
      set S := N A with hSdef
      set T := Finset.univ.filter (fun i => S i = A) with hTdef
      have hLT : L ∈ T := by simp [T, S, hNL]
      have hT : ∀ i ∈ T, S i = S L := by
        intro i hi; simp only [T, Finset.mem_filter] at hi; rw [hi.2, hSdef, hNL]
      set B := A.filter (fun j => j < k) ∪ (Finset.univ.filter (fun i => i ∉ T)).sup S with hBdef
      have hB : ∀ i, i ∉ T → S i ⊆ B := by
        intro i hi
        exact (Finset.le_sup (f := S) (by simp [hi])).trans Finset.subset_union_right
      have hBA : B ⊆ S L := by
        rw [hSdef, hNL]
        apply Finset.union_subset (Finset.filter_subset _ _)
        exact Finset.sup_le (fun i _ => hNsub A i)
      have hSL : S L = A := hNL A
      have hkD : ∀ j ∈ S L \ B, k < j := by
        intro j hj
        rw [hSL, Finset.mem_sdiff] at hj
        rcases lt_trichotomy j k with h | h | h
        · exact absurd (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj.1, h⟩)) hj.2
        · exact absurd (h ▸ hj.1) hkA
        · exact h
      have hgen := SQR2Aux.gen_move lam r v c cs hlam hr hrpos hv hsw hmono S (hNchain A) L T hLT hT
        B hB hBA k (by rw [hSL]; exact hkA) hkD
      rw [hSL] at hgen
      set S1 : Fin (M + 2) → Finset (Fin n) := fun i => if i ∈ T then insert k A else S i
      set S2 : Fin (M + 2) → Finset (Fin n) := fun i => if i ∈ T then B else S i
      have hS1L : S1 L = insert k A := by simp [S1, hLT]
      have hS2L : S2 L = B := by simp [S2, hLT]
      have hS1sub : ∀ i, S1 i ⊆ S1 L := by
        intro i; rw [hS1L]; simp only [S1]; split_ifs with hi
        · exact le_rfl
        · exact (hNsub A i).trans (Finset.subset_insert _ _)
      have hS2sub : ∀ i, S2 i ⊆ S2 L := by
        intro i; rw [hS2L]; simp only [S2]; split_ifs with hi
        · exact le_rfl
        · exact hB i hi
      rcases le_max_iff.mp hgen with h1 | h2
      · -- move I: add k
        have hopt' : IsOptQ lam r v c (N (insert k A)) := by
          intro S'; have := hNge S1 hS1sub; rw [hS1L] at this
          exact (hopt S').trans (h1.trans this)
        have hlt : (pairs (insert k A)).card < (pairs A).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨(k, j0), ?_, ?_⟩
            · rw [hmem]; exact ⟨hkA, hj0, hkj⟩
            · rw [hmem]; simp
          · intro p hp
            rw [hmem] at hp ⊢
            obtain ⟨hp1, hp2, hp3⟩ := hp
            have hp1' : p.1 ∉ A := fun h => hp1 (Finset.mem_insert_of_mem h)
            rcases Finset.mem_insert.mp hp2 with h | h
            · exact absurd (hkmin p.1 (h ▸ hp3)) hp1'
            · exact ⟨hp1', h, hp3⟩
        exact ih _ (hg ▸ hlt) (insert k A) rfl hopt'
      · -- move II: shrink to B
        have hopt' : IsOptQ lam r v c (N B) := by
          intro S'; have := hNge S2 hS2sub; rw [hS2L] at this
          exact (hopt S').trans (h2.trans this)
        -- every product of A ∖ B ranks after every product of B
        have hpre : ∀ i, i ∉ T → ∃ J : ℕ, S i = A.filter (fun x => x.val < J) := by
          intro i hi
          have hiL : i ≠ L := fun h => hi (h ▸ hLT)
          rw [hSdef, hNne A i hiL]
          exact SQR2B2.opt_ordered r v (β i) A (sm i A) hr hrpos hv (hβ0 i) (hβ1 i) (hsmA i A)
            (hsmopt i A)
        have hDB : ∀ j' ∈ A, j' ∉ B → ∀ j ∈ B, j < j' := by
          intro j' hj'A hj'B j hjB
          have hkj' : k < j' := hkD j' (by rw [hSL]; exact Finset.mem_sdiff.mpr ⟨hj'A, hj'B⟩)
          rcases Finset.mem_union.mp hjB with h | h
          · exact lt_trans (Finset.mem_filter.mp h).2 hkj'
          · obtain ⟨i, hi, hji⟩ := Finset.mem_sup.mp h
            have hiT : i ∉ T := (Finset.mem_filter.mp hi).2
            obtain ⟨J, hJ⟩ := hpre i hiT
            have hj'S : j' ∉ S i := fun hh => hj'B (hB i hiT hh)
            rw [hJ] at hji hj'S
            simp only [Finset.mem_filter, not_and, not_lt] at hji hj'S
            have := hj'S hj'A
            rw [Fin.lt_def]; omega
        -- the largest product of A is not in B
        set jm := A.max' hAne
        have hjmA : jm ∈ A := Finset.max'_mem A hAne
        have hjmB : jm ∉ B := by
          intro hB'
          rcases Finset.mem_union.mp hB' with h | h
          · have := (Finset.mem_filter.mp h).2
            have := Finset.le_max' A j0 hj0
            exact absurd (lt_of_lt_of_le hkj this) (not_lt.mpr (le_of_lt (by assumption)))
          · obtain ⟨i, hi, hji⟩ := Finset.mem_sup.mp h
            have hiT : i ∉ T := (Finset.mem_filter.mp hi).2
            obtain ⟨J, hJ⟩ := hpre i hiT
            apply hiT
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hJ]; rw [hJ] at hji
            ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
            intro hx
            have := Finset.le_max' A x hx
            have := (Finset.mem_filter.mp hji).2
            rw [Fin.le_def] at *; omega
        have hlt : (pairs B).card < (pairs A).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨(k, jm), ?_, ?_⟩
            · rw [hmem]; exact ⟨hkA, hjmA, lt_of_lt_of_le hkj (Finset.le_max' A j0 hj0)⟩
            · rw [hmem]; intro h; exact hjmB h.2.1
          · intro p hp
            rw [hmem] at hp ⊢
            obtain ⟨hp1, hp2, hp3⟩ := hp
            have hBA' : B ⊆ A := by rw [← hSL]; exact hBA
            refine ⟨?_, hBA' hp2, hp3⟩
            intro hpA
            exact absurd (hDB p.1 hpA hp1 p.2 hp2) (not_lt.mpr hp3.le)
        exact ih _ (hg ▸ hlt) B rfl hopt'
    · -- no inversion: A is a nonempty prefix
      push Not at hinv
      refine ⟨A, ⟨A.sup (fun k => k.val + 1), ?_, ?_, ?_⟩, hopt⟩
      · obtain ⟨x, hx⟩ := hAne
        have := Finset.le_sup (f := fun k : Fin n => k.val + 1) hx; omega
      · apply Finset.sup_le; intro x _; have := x.isLt; omega
      · ext x
        simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hx; have := Finset.le_sup (f := fun k : Fin n => k.val + 1) hx
          omega
        · intro hxlt
          by_contra hxA
          obtain ⟨k, hkA, hk⟩ := Finset.exists_mem_eq_sup A hAne (fun k : Fin n => k.val + 1)
          rw [hk] at hxlt
          have := hinv x hxA k hkA
          rw [Fin.le_def] at this
          have hxk : x = k := Fin.ext (by omega)
          exact hxA (hxk ▸ hkA)
  obtain ⟨A, hAro, hAopt⟩ := main _ (S0 L) rfl hNopt0
  refine ⟨N A, hAopt, hNchain A, ?_⟩
  intro i
  by_cases hi : i = L
  · rw [hi, hNL]; exact hAro
  · rw [hNne A i hi]
    obtain ⟨J, hJ1, hJn, hAJ⟩ := hAro
    obtain ⟨J', hJ'⟩ := SQR2B2.opt_ordered r v (β i) A (sm i A) hr hrpos hv (hβ0 i) (hβ1 i)
      (hsmA i A) (hsmopt i A)
    have hAne : A.Nonempty := by
      rw [hAJ]; exact ⟨⟨0, by omega⟩, by simp [prefixSet]; omega⟩
    have hsmne : (sm i A).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have h1 := SQR2B2.empty_not_opt r v (β i) A hr hrpos hv (hβ0 i) (hβ1 i) hAne
      have h2 := hsmopt i A {A.min' hAne} (Finset.singleton_subset_iff.mpr (Finset.min'_mem A hAne))
      rw [he] at h2; linarith
    refine ⟨min J J', ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hsmne
      rw [hJ', hAJ] at hx
      simp only [Finset.mem_filter, prefixSet, Finset.mem_univ, true_and] at hx
      omega
    · omega
    · rw [hJ', hAJ]; ext x
      simp only [Finset.mem_filter, prefixSet, Finset.mem_univ, true_and]
      omega
