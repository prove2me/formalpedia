-- Prove2me | solution 1 for MultiStoreAssort.SQR.eqB4_case1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:58:31.596489+00:00
-- url     : https://prove2.me/submissions/a9985924-877a-40ab-9992-c48fa1d749e2

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

open MultiStoreAssort.SMR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) (S : Fin (M + 2) → Finset (Fin n)) (hchain : ∀ i j, i ≤ j → S i ⊆ S j)
    (k : Fin n) (hk : k ∉ S (Fin.last (M + 1))) (hkmin : ∀ j, j < k → j ∈ S (Fin.last (M + 1)))
    (hcase : (S (Fin.last (M + 1))).filter (fun j => j < k) ⊆ S (Fin.last M).castSucc) :
    MultiStoreAssort.SMR.revQ lam r v c S ≤
      max (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (insert k (S (Fin.last (M + 1))))))
        (MultiStoreAssort.SMR.revQ lam r v c (Function.update S (Fin.last (M + 1)) (S (Fin.last M).castSucc))) := by
  classical
  set L := Fin.last (M + 1)
  set Bm := S (Fin.last M).castSucc
  have hle : ∀ i : Fin (M + 2), i ≠ L → i ≤ (Fin.last M).castSucc := by
    intro i hi
    rw [Fin.le_def]; simp only [Fin.val_castSucc, Fin.val_last]
    have : i.val ≠ M + 1 := fun h => hi (Fin.ext (by simp [L, h]))
    have := i.isLt; omega
  have h := SQR2Aux.gen_move lam r v c cs hlam hr hrpos hv hsw hmono S hchain L {L}
    (Finset.mem_singleton_self L) (fun i hi => by rw [Finset.mem_singleton.mp hi])
    Bm (fun i hi => hchain _ _ (hle i (by simpa using hi)))
    (hchain _ _ (Fin.le_last _)) k hk (by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      rcases lt_trichotomy j k with h | h | h
      · exact absurd (hcase (Finset.mem_filter.mpr ⟨hj.1, h⟩)) hj.2
      · exact absurd (h ▸ hj.1) hk
      · exact h)
  have e1 : (fun i => if i ∈ ({L} : Finset _) then insert k (S L) else S i) =
      Function.update S L (insert k (S L)) := by
    funext i; by_cases hi : i = L
    · subst hi; simp
    · simp [hi]
  have e2 : (fun i => if i ∈ ({L} : Finset _) then Bm else S i) = Function.update S L Bm := by
    funext i; by_cases hi : i = L
    · subst hi; simp
    · simp [hi]
  rw [e1, e2] at h
  exact h
