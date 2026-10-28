-- Prove2me | solution 1 for MultiStoreAssort.SQR.propositionB1_subset_last
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T15:44:38.607858+00:00
-- url     : https://prove2.me/submissions/0b82370f-84e6-46bc-8f98-d355a15444c2

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

namespace SQR2B3

set_option maxHeartbeats 4000000 in
theorem polyx_C2A (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) := by
  have hD : 0 < (a + c + 1)*(a + b + c + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1) := by positivity
  have key : (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) = (a^2*c + 2*a*b*c*x + a*c^2*x + a*c^2 + 2*a*c*d*x - a*c*x^2 + 2*a*c + b^2*c*x^2 + b*c^2*x^2 + b*c^2*x + 2*b*c*d*x^2 - 2*b*c*x^2 + 3*b*c*x + c^3*x + c^2*d*x^2 + c^2*d*x - c^2*x^2 + c^2*x + c^2 + c*d^2*x^2 - c*d*x^2 + 2*c*d*x - c*x^2 + c) / ((a + c + 1)*(a + b + c + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hD.le
  have key2 : ∀ u : ℝ, u = 1 - x → a^2*c + 2*a*b*c*x + a*c^2*x + a*c^2 + 2*a*c*d*x - a*c*x^2 + 2*a*c + b^2*c*x^2 + b*c^2*x^2 + b*c^2*x + 2*b*c*d*x^2 - 2*b*c*x^2 + 3*b*c*x + c^3*x + c^2*d*x^2 + c^2*d*x - c^2*x^2 + c^2*x + c^2 + c*d^2*x^2 - c*d*x^2 + 2*c*d*x - c*x^2 + c = a^2*c*u^2 + 2*a^2*c*u*x + a^2*c*x^2 + 2*a*b*c*u*x + 2*a*b*c*x^2 + a*c^2*u^2 + 3*a*c^2*u*x + 2*a*c^2*x^2 + 2*a*c*d*u*x + 2*a*c*d*x^2 + 2*a*c*u^2 + 4*a*c*u*x + a*c*x^2 + b^2*c*x^2 + b*c^2*u*x + 2*b*c^2*x^2 + 2*b*c*d*x^2 + 3*b*c*u*x + b*c*x^2 + c^3*u*x + c^3*x^2 + c^2*d*u*x + 2*c^2*d*x^2 + c^2*u^2 + 3*c^2*u*x + c^2*x^2 + c*d^2*x^2 + 2*c*d*u*x + c*d*x^2 + c*u^2 + 2*c*u*x := by
    intro u hu
    subst hu
    ring
  rw [key2 (1 - x) rfl]
  have hu : 0 ≤ 1 - x := by linarith
  set u := 1 - x
  positivity


set_option maxHeartbeats 4000000 in
theorem polyx_C23A (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ ((((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c) := by
  have hD : 0 < (a + c + 1)*(a + b + c + 1)*(a + b + c*x + d*x + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1) := by positivity
  have key : ((((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c) = (-2*a^2*b*c*x^2 + 2*a^2*b*c*x - a*b^2*c*x^3 - a*b^2*c*x^2 + 2*a*b^2*c*x - a*b*c^2*x^3 - a*b*c^2*x^2 + 2*a*b*c^2*x - 2*a*b*c*d*x^3 + 2*a*b*c*d*x^2 - 4*a*b*c*x^2 + 4*a*b*c*x - b^3*c*x^2 + b^3*c*x - b^2*c^2*x^3 + b^2*c^2*x - b^2*c*d*x^3 + b^2*c*d*x^2 - b^2*c*x^3 - b^2*c*x^2 + 2*b^2*c*x - b*c^3*x^3 + b*c^3*x^2 - b*c^2*d*x^3 + b*c^2*d*x^2 - b*c^2*x^3 - b*c^2*x^2 + 2*b*c^2*x - 2*b*c*d*x^3 + 2*b*c*d*x^2 - 2*b*c*x^2 + 2*b*c*x) / ((a + c + 1)*(a + b + c + 1)*(a + b + c*x + d*x + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hD.le
  have key2 : ∀ u : ℝ, u = 1 - x → -2*a^2*b*c*x^2 + 2*a^2*b*c*x - a*b^2*c*x^3 - a*b^2*c*x^2 + 2*a*b^2*c*x - a*b*c^2*x^3 - a*b*c^2*x^2 + 2*a*b*c^2*x - 2*a*b*c*d*x^3 + 2*a*b*c*d*x^2 - 4*a*b*c*x^2 + 4*a*b*c*x - b^3*c*x^2 + b^3*c*x - b^2*c^2*x^3 + b^2*c^2*x - b^2*c*d*x^3 + b^2*c*d*x^2 - b^2*c*x^3 - b^2*c*x^2 + 2*b^2*c*x - b*c^3*x^3 + b*c^3*x^2 - b*c^2*d*x^3 + b*c^2*d*x^2 - b*c^2*x^3 - b*c^2*x^2 + 2*b*c^2*x - 2*b*c*d*x^3 + 2*b*c*d*x^2 - 2*b*c*x^2 + 2*b*c*x = 2*a^2*b*c*u^2*x + 2*a^2*b*c*u*x^2 + 2*a*b^2*c*u^2*x + 3*a*b^2*c*u*x^2 + 2*a*b*c^2*u^2*x + 3*a*b*c^2*u*x^2 + 2*a*b*c*d*u*x^2 + 4*a*b*c*u^2*x + 4*a*b*c*u*x^2 + b^3*c*u^2*x + b^3*c*u*x^2 + b^2*c^2*u^2*x + 2*b^2*c^2*u*x^2 + b^2*c*d*u*x^2 + 2*b^2*c*u^2*x + 3*b^2*c*u*x^2 + b*c^3*u*x^2 + b*c^2*d*u*x^2 + 2*b*c^2*u^2*x + 3*b*c^2*u*x^2 + 2*b*c*d*u*x^2 + 2*b*c*u^2*x + 2*b*c*u*x^2 := by
    intro u hu
    subst hu
    ring
  rw [key2 (1 - x) rfl]
  have hu : 0 ≤ 1 - x := by linarith
  set u := 1 - x
  positivity



set_option maxHeartbeats 4000000 in
theorem c4_struct (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) := by
  have p1 : 0 < 1 + a := by linarith
  have p12 : 0 < 1 + a + b := by linarith
  have p13 : 0 < 1 + a + c := by linarith
  have p123 : 0 < 1 + a + b + c := by linarith
  have b1 : 0 < 1 + a + b + c + x * d := by positivity
  have b2 : 0 < 1 + a + x * (b + c + d) := by positivity
  have b3 : 0 < 1 + a + c + x * (b + d) := by positivity
  have b4 : 0 < 1 + a + b + x * (c + d) := by positivity
  have key : (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) = x / ((1 + a + c) * (1 + a + b + c)) *
      (((1 + a + c) * (1 + a + x * (b + c + d)) + (1 + a + b) * (1 + a + b + c + x * d)) *
        ((1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d)) -
          (1 + a + b + c + x * d) * (1 + a + x * (b + c + d))) /
        ((1 + a + b + c + x * d) * (1 + a + x * (b + c + d)) *
          ((1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d))))) := by
    field_simp
    ring
  rw [key]
  have hprod : (1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d)) -
      (1 + a + b + c + x * d) * (1 + a + x * (b + c + d)) = b * c * (1 - x) * (1 - x) := by ring
  rw [hprod]
  have hu : 0 ≤ 1 - x := by linarith
  positivity
noncomputable def h (β G P w y : ℝ) : ℝ := G / P + β * w / (P * (P + β * y))

theorem frac_diff (K V s t : ℝ) (hK : 0 < K) (hs : 0 < K + s * V) (ht : 0 < K + t * V) :
    t / (K * (K + t * V)) - s / (K * (K + s * V)) = (t - s) / ((K + t * V) * (K + s * V)) := by
  rw [div_sub_div _ _ (mul_ne_zero hK.ne' ht.ne') (mul_ne_zero hK.ne' hs.ne'),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hK.ne' ht.ne') (mul_ne_zero hK.ne' hs.ne'))
      (mul_ne_zero ht.ne' hs.ne')]
  ring

set_option maxHeartbeats 4000000 in
/-- The four-group inequality behind Lemma B.3 and its mirror (Case 2 of Proposition B.1). -/
theorem b3_core (a b c d W1 W2 W3 W4 x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hW2 : 0 ≤ W2) (hW3 : 0 ≤ W3) (hW4 : 0 ≤ W4) (hb0 : b = 0 → W2 = 0) (hc0 : c = 0 → W3 = 0)
    (hy : 0 ≤ y) (hxy : y ≤ x) (hx1 : x ≤ 1) :
    (b * W3 ≤ c * W2 → 0 ≤ ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * ((h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d))) + ((h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d)))) ∧
    (c * W2 ≤ b * W3 → 0 ≤ ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (h x (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d)) + (h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d)) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d))) := by
  have hx : 0 ≤ x := le_trans hy hxy
  -- monotonicity in the second discount factor
  have hm1 : y / ((1 + a + c) * (1 + a + c + y * (b + d))) ≤ x / ((1 + a + c) * (1 + a + c + x * (b + d))) := by
    have e := frac_diff (1 + a + c) (b + d) y x (by linarith) (by nlinarith) (by nlinarith)
    have : 0 ≤ (x - y) / ((1 + a + c + x * (b + d)) * (1 + a + c + y * (b + d))) := by
      apply div_nonneg (by linarith)
      have : 0 < 1 + a + c + x * (b + d) := by nlinarith
      have : 0 < 1 + a + c + y * (b + d) := by nlinarith
      positivity
    linarith
  have hm2 : x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d))) ≤
      y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d))) := by
    have e1 := frac_diff (1 + a + b + c) d y x (by linarith) (by nlinarith) (by nlinarith)
    have e2 := frac_diff (1 + a + c) (b + d) y x (by linarith) (by nlinarith) (by nlinarith)
    have p1 : 0 < 1 + a + c + x * (b + d) := by nlinarith
    have p2 : 0 < 1 + a + c + y * (b + d) := by nlinarith
    have q1 : 1 + a + c + x * (b + d) ≤ 1 + a + b + c + x * d := by nlinarith
    have q2 : 1 + a + c + y * (b + d) ≤ 1 + a + b + c + y * d := by nlinarith
    have : (x - y) / ((1 + a + b + c + x * d) * (1 + a + b + c + y * d)) ≤
        (x - y) / ((1 + a + c + x * (b + d)) * (1 + a + c + y * (b + d))) := by
      apply div_le_div_of_nonneg_left (by linarith) (mul_pos p1 p2)
      exact mul_le_mul q1 q2 p2.le (by linarith)
    linarith
  have A2 := polyx_C2A a b c d x ha hb hc hd hx hx1
  have A23 := polyx_C23A a b c d x ha hb hc hd hx hx1
  have A4 := c4_struct a b c d x ha hb hc hd hx hx1
  have B3 : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) := by
    have h0 := polyx_C2A a c b d x ha hc hb hd hx hx1
    have e : (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) = (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + c + b))) * (x / ((1 + a) * (1 + a + x * (c + b + d))) - 1 / (1 + a + c)) + 1 / (1 + a + c + b) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) := by ring
    rw [e]; exact h0
  have B23 : 0 ≤ ((((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) * c) := by
    have h0 := polyx_C23A a c b d x ha hc hb hd hx hx1
    have e : ((((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) * c) = ((((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + c + b))) * (x / ((1 + a) * (1 + a + x * (c + b + d))) - 1 / (1 + a + c)) + 1 / (1 + a + c + b) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) * c + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + c + b))) * (x / ((1 + a) * (1 + a + x * (c + b + d))) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + c + b) - 1 / (1 + a + b)) * b) := by ring
    rw [e]; exact h0
  have B4 : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d))) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) := by
    have h0 := c4_struct a c b d x ha hc hb hd hx hx1
    have e : (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d))) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) = (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + c + b))) * (x / ((1 + a) * (1 + a + x * (c + b + d))) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + x / ((1 + a + c + b) * (1 + a + c + b + x * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) := by ring
    rw [e]; exact h0
  have hC1A : ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c)) * (1 / (1 + a) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) = 0 := by field_simp; ring
  have hC1B : ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)) * (1 / (1 + a)) + (1 - (1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (1 / (1 + a + c)) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - 1 / (1 + a + c)) = 0 := by field_simp; ring
  constructor
  · intro hcase
    have e : ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * ((h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d))) + ((h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d))) =
        ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c)) * (1 / (1 + a) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * W1 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W2 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * W3 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := by
      unfold h; ring
    rw [e, hC1A, zero_mul, zero_add]
    have c2 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) := by linarith
    have c23 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c := by nlinarith
    have c4 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) := by linarith
    have c4w : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := mul_nonneg c4 hW4
    set C2 := (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d))))
    set C3 := (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c))
    have key : 0 ≤ C2 * W2 + C3 * W3 := by
      rcases hc.lt_or_eq with hcp | hc0'
      · have e2 : c * (C2 * W2 + C3 * W3) = C2 * (c * W2 - b * W3) + W3 * (C2 * b + C3 * c) := by ring
        have : 0 ≤ c * (C2 * W2 + C3 * W3) := by
          rw [e2]; exact add_nonneg (mul_nonneg c2 (by linarith)) (mul_nonneg hW3 c23)
        by_contra hneg; push Not at hneg
        have := mul_neg_of_pos_of_neg hcp hneg; linarith
      · rw [hc0 hc0'.symm]; simp only [mul_zero, add_zero]; exact mul_nonneg c2 hW2
    linarith
  · intro hcase
    have e : ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (h x (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d)) + (h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d)) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d)) =
        ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)) * (1 / (1 + a)) + (1 - (1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (1 / (1 + a + c)) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - 1 / (1 + a + c)) * W1 + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W2 + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) * W3 + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d))) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := by
      unfold h; ring
    rw [e, hC1B, zero_mul, zero_add]
    have c3 : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) := B3
    have c23 : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * b + (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) * c := by nlinarith
    have c4 : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d))) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) := by linarith
    have c4w : 0 ≤ (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - x / ((1 + a + b) * (1 + a + b + x * (c + d))) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := mul_nonneg c4 hW4
    set C2 := (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d)))) + (1 - ((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c)))) * (x / ((1 + a + c) * (1 + a + c + x * (b + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + b) - y / ((1 + a + c) * (1 + a + c + y * (b + d))))
    set C3 := (((1 + a) * (1 + a + c) / ((1 + a + b) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + c)) + 1 / (1 + a + b + c) - x / ((1 + a + b) * (1 + a + b + x * (c + d))))
    have key : 0 ≤ C2 * W2 + C3 * W3 := by
      rcases hb.lt_or_eq with hbp | hb0'
      · have e2 : b * (C2 * W2 + C3 * W3) = C3 * (b * W3 - c * W2) + W2 * (C2 * b + C3 * c) := by ring
        have : 0 ≤ b * (C2 * W2 + C3 * W3) := by
          rw [e2]; exact add_nonneg (mul_nonneg c3 (by linarith)) (mul_nonneg hW2 c23)
        by_contra hneg; push Not at hneg
        have := mul_neg_of_pos_of_neg hbp hneg; linarith
      · rw [hb0 hb0'.symm]; simp only [mul_zero, zero_add]; exact mul_nonneg c3 hW3
    linarith
end SQR2B3

namespace SQR2B3

theorem select (li lL δ u u' γ : ℝ) (hl : lL ≤ li) (hL : 0 ≤ lL) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (h : 0 ≤ γ * u + (1 - γ) * u' + δ) :
    0 ≤ lL * δ ∨ 0 ≤ li * u + lL * δ ∨ 0 ≤ li * u' + lL * δ := by
  by_cases h0 : 0 ≤ lL * δ
  · exact Or.inl h0
  push Not at h0
  have hLp : 0 < lL := by
    rcases hL.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1] at h0; simp at h0
  have hδ : δ < 0 := by
    by_contra h2; push Not at h2; nlinarith
  rcases le_total u' u with hu | hu
  · right; left
    have : -δ ≤ u := by nlinarith
    nlinarith
  · right; right
    have : -δ ≤ u' := by nlinarith
    nlinarith

theorem groups {n : ℕ} (f : Fin n → ℝ) (X Y U : Finset (Fin n)) (hXU : X ⊆ U) (hYU : Y ⊆ U) :
    ∑ k ∈ X, f k = ∑ k ∈ X ∩ Y, f k + ∑ k ∈ X \ Y, f k ∧
    ∑ k ∈ Y, f k = ∑ k ∈ X ∩ Y, f k + ∑ k ∈ Y \ X, f k ∧
    ∑ k ∈ X ∪ Y, f k = ∑ k ∈ X ∩ Y, f k + ∑ k ∈ X \ Y, f k + ∑ k ∈ Y \ X, f k ∧
    ∑ k ∈ U \ X, f k = ∑ k ∈ Y \ X, f k + ∑ k ∈ U \ (X ∪ Y), f k ∧
    ∑ k ∈ U \ Y, f k = ∑ k ∈ X \ Y, f k + ∑ k ∈ U \ (X ∪ Y), f k ∧
    ∑ k ∈ U \ (X ∩ Y), f k = ∑ k ∈ X \ Y, f k + ∑ k ∈ Y \ X, f k + ∑ k ∈ U \ (X ∪ Y), f k := by
  classical
  have h1 := Finset.sum_inter_add_sum_sdiff X Y f
  have h2 := Finset.sum_inter_add_sum_sdiff Y X f
  rw [Finset.inter_comm] at h2
  have h3 := Finset.sum_union_inter (s₁ := X) (s₂ := Y) (f := f)
  have hXYU : X ∪ Y ⊆ U := Finset.union_subset hXU hYU
  have s1 := Finset.sum_sdiff (f := f) hXU
  have s2 := Finset.sum_sdiff (f := f) hYU
  have s3 := Finset.sum_sdiff (f := f) (Finset.inter_subset_left.trans hXU : X ∩ Y ⊆ U)
  have s4 := Finset.sum_sdiff (f := f) hXYU
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end SQR2B3

open MultiStoreAssort.SQR MultiStoreAssort.SMR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmax : ∀ i, cs i ≤ cs (Fin.last (M + 1))) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧
      ∀ i, i ≠ Fin.last (M + 1) → S i ⊆ S (Fin.last (M + 1)) := by
  classical
  set L := Fin.last (M + 1) with hLdef
  obtain ⟨S0, -, hS0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (M + 2) → Finset (Fin n)))
    (fun S => revQ lam r v c S) ⟨fun _ => ∅, Finset.mem_univ _⟩
  have hS0opt : IsOptQ lam r v c S0 := fun S' => hS0 S' (Finset.mem_univ _)
  set O := (Finset.univ : Finset (Fin (M + 2) → Finset (Fin n))).filter (fun S => IsOptQ lam r v c S)
  obtain ⟨S, hSO, hSmax⟩ := Finset.exists_max_image O (fun S => (S L).card)
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS0opt⟩⟩
  have hSopt : IsOptQ lam r v c S := (Finset.mem_filter.mp hSO).2
  refine ⟨S, hSopt, ?_⟩
  intro i hiL
  by_contra hXY
  set X := S i with hXdef
  set Y := S L with hYdef
  set U := Sbar S with hUdef
  have hsubU : ∀ j, S j ⊆ U := fun j => by
    intro x hx; show x ∈ Finset.univ.sup S; exact Finset.le_sup (f := S) (Finset.mem_univ j) hx
  have hXU : X ⊆ U := hsubU i
  have hYU : Y ⊆ U := hsubU L
  -- the modified profile and its revenue
  have hrev : ∀ Z, Z ⊆ X ∪ Y →
      revQ lam r v c (Function.update (Function.update S i Z) L (X ∪ Y)) =
        revQ lam r v c S + (lam i * (rev8 r v (Real.exp (-(cs i))) U Z - rev8 r v (Real.exp (-(cs i))) U X) +
          lam L * (rev8 r v (Real.exp (-(cs L))) U (X ∪ Y) - rev8 r v (Real.exp (-(cs L))) U Y)) := by
    intro Z hZ
    set S' := Function.update (Function.update S i Z) L (X ∪ Y)
    have hS'L : S' L = X ∪ Y := Function.update_self _ _ _
    have hS'i : S' i = Z := by
      simp only [S']; rw [Function.update_of_ne hiL, Function.update_self]
    have hS'j : ∀ j, j ≠ i → j ≠ L → S' j = S j := by
      intro j hji hjL; simp only [S']; rw [Function.update_of_ne hjL, Function.update_of_ne hji]
    have hSb : Sbar S' = U := by
      apply Finset.Subset.antisymm
      · simp only [Sbar]; apply Finset.sup_le; intro j _
        by_cases hjL : j = L
        · rw [hjL, hS'L]; exact Finset.union_subset hXU hYU
        by_cases hji : j = i
        · rw [hji, hS'i]; exact hZ.trans (Finset.union_subset hXU hYU)
        · rw [hS'j j hji hjL]; exact hsubU j
      · simp only [U, Sbar]; apply Finset.sup_le; intro j _
        have hle : S' L ⊆ Sbar S' := by
          intro x hx; show x ∈ Finset.univ.sup S'; exact Finset.le_sup (f := S') (Finset.mem_univ L) hx
        by_cases hjL : j = L
        · rw [hjL]; exact (Finset.subset_union_right).trans (hS'L ▸ hle)
        by_cases hji : j = i
        · rw [hji]; exact (Finset.subset_union_left).trans (hS'L ▸ hle)
        · rw [← hS'j j hji hjL]; intro x hx; show x ∈ Finset.univ.sup S'
          exact Finset.le_sup (f := S') (Finset.mem_univ j) hx
    rw [SQR2Aux.revQ_eq lam r v c cs hsw S', SQR2Aux.revQ_eq lam r v c cs hsw S, hSb]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_add i L (Ne.symm (Ne.symm hiL))]
    · rw [hS'i, hS'L]; ring
    · intro j _ hj; rw [hS'j j hj.1 hj.2]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro h; exact absurd (Finset.mem_univ L) h
  have improve : ∀ Z, Z ⊆ X ∪ Y →
      revQ lam r v c S ≤ revQ lam r v c (Function.update (Function.update S i Z) L (X ∪ Y)) → False := by
    intro Z hZ hle
    set S' := Function.update (Function.update S i Z) L (X ∪ Y)
    have hopt' : IsOptQ lam r v c S' := fun S'' => (hSopt S'').trans hle
    have hc := hSmax S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopt'⟩)
    have hS'L : S' L = X ∪ Y := Function.update_self _ _ _
    rw [hS'L] at hc
    have hss : Y ⊂ X ∪ Y := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_right, fun he => hXY ?_⟩
      rw [he]; exact Finset.subset_union_left
    have := Finset.card_lt_card hss
    omega
  -- group quantities
  obtain ⟨gw1, gw2, gw3, gw4, gw5, gw6⟩ := SQR2B3.groups (fun k => r k * v k) X Y U hXU hYU
  obtain ⟨gv1, gv2, gv3, gv4, gv5, gv6⟩ := SQR2B3.groups v X Y U hXU hYU
  have hw1 : Ws r v X = Ws r v (X ∩ Y) + Ws r v (X \ Y) := gw1
  have hw2 : Ws r v Y = Ws r v (X ∩ Y) + Ws r v (Y \ X) := gw2
  have hw3 : Ws r v (X ∪ Y) = Ws r v (X ∩ Y) + Ws r v (X \ Y) + Ws r v (Y \ X) := gw3
  have hw4 : Ws r v (U \ X) = Ws r v (Y \ X) + Ws r v (U \ (X ∪ Y)) := gw4
  have hw5 : Ws r v (U \ Y) = Ws r v (X \ Y) + Ws r v (U \ (X ∪ Y)) := gw5
  have hw6 : Ws r v (U \ (X ∩ Y)) = Ws r v (X \ Y) + Ws r v (Y \ X) + Ws r v (U \ (X ∪ Y)) := gw6
  have hv1 : Vs v X = Vs v (X ∩ Y) + Vs v (X \ Y) := gv1
  have hv2 : Vs v Y = Vs v (X ∩ Y) + Vs v (Y \ X) := gv2
  have hv3 : Vs v (X ∪ Y) = Vs v (X ∩ Y) + Vs v (X \ Y) + Vs v (Y \ X) := gv3
  have hv4 : Vs v (U \ X) = Vs v (Y \ X) + Vs v (U \ (X ∪ Y)) := gv4
  have hv5 : Vs v (U \ Y) = Vs v (X \ Y) + Vs v (U \ (X ∪ Y)) := gv5
  have hv6 : Vs v (U \ (X ∩ Y)) = Vs v (X \ Y) + Vs v (Y \ X) + Vs v (U \ (X ∪ Y)) := gv6
  set W1 := Ws r v (X ∩ Y); set W2 := Ws r v (X \ Y); set W3 := Ws r v (Y \ X)
  set W4 := Ws r v (U \ (X ∪ Y))
  set a := Vs v (X ∩ Y); set b := Vs v (X \ Y); set cc := Vs v (Y \ X); set d := Vs v (U \ (X ∪ Y))
  have hWnn : ∀ G, 0 ≤ Ws r v G := fun G => SQR2Aux.Ws_nonneg r v hrpos hv G
  have hVnn : ∀ G, 0 ≤ Vs v G := fun G => SQR2Aux.Vs_nonneg v hv G
  have hzero : ∀ G, Vs v G = 0 → Ws r v G = 0 := by
    intro G hG
    rcases G.eq_empty_or_nonempty with he | hne
    · rw [he]; simp [Ws]
    · have := Finset.sum_pos (fun k _ => hv k) hne; simp only [Vs] at hG; linarith
  set x := Real.exp (-(cs i))
  set y := Real.exp (-(cs L))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hxy : y ≤ x := Real.exp_le_exp.mpr (by linarith [hmax i])
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hsw.1 i])
  -- the five store revenues in group form
  have eX : rev8 r v x U X = SQR2B3.h x (W1 + W2) (1 + (a + b)) (W3 + W4) (cc + d) := by
    show SQR2B3.h x (Ws r v X) (1 + Vs v X) (Ws r v (U \ X)) (Vs v (U \ X)) = _
    rw [hw1, hv1, hw4, hv4]
  have eY : rev8 r v y U Y = SQR2B3.h y (W1 + W3) (1 + (a + cc)) (W2 + W4) (b + d) := by
    show SQR2B3.h y (Ws r v Y) (1 + Vs v Y) (Ws r v (U \ Y)) (Vs v (U \ Y)) = _
    rw [hw2, hv2, hw5, hv5]
  have eI : rev8 r v x U (X ∩ Y) = SQR2B3.h x W1 (1 + a) (W2 + W3 + W4) (b + cc + d) := by
    show SQR2B3.h x (Ws r v (X ∩ Y)) (1 + Vs v (X ∩ Y)) (Ws r v (U \ (X ∩ Y))) (Vs v (U \ (X ∩ Y))) = _
    rw [hw6, hv6]
  have eUL : rev8 r v y U (X ∪ Y) = SQR2B3.h y (W1 + W2 + W3) (1 + (a + b + cc)) W4 d := by
    show SQR2B3.h y (Ws r v (X ∪ Y)) (1 + Vs v (X ∪ Y)) (Ws r v (U \ (X ∪ Y))) (Vs v (U \ (X ∪ Y))) = _
    rw [hw3, hv3]
  have eYi : rev8 r v x U Y = SQR2B3.h x (W1 + W3) (1 + (a + cc)) (W2 + W4) (b + d) := by
    show SQR2B3.h x (Ws r v Y) (1 + Vs v Y) (Ws r v (U \ Y)) (Vs v (U \ Y)) = _
    rw [hw2, hv2, hw5, hv5]
  have core := SQR2B3.b3_core a b cc d W1 W2 W3 W4 x y (hVnn _) (hVnn _) (hVnn _) (hVnn _)
    (hWnn _) (hWnn _) (hWnn _) (hzero _) (hzero _) hy0 hxy hx1
  have hl := hmin i
  have hlL := hlam L
  have hab : 0 < 1 + a := by linarith [hVnn (X ∩ Y)]
  have hb' := hVnn (X \ Y)
  have hc' := hVnn (Y \ X)
  rcases le_total (b * W3) (cc * W2) with hcase | hcase
  · -- Case 1 (R₂ ≥ R₃): compare with (X∩Y, X∪Y) and (X, X∪Y)
    have h1 := core.1 hcase
    set γ := (1 + a) * (1 + a + b) / ((1 + a + cc) * (1 + a + b + cc))
    have hγ0 : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hsel := SQR2B3.select (lam i) (lam L)
      (SQR2B3.h y (W1 + W2 + W3) (1 + (a + b + cc)) W4 d - SQR2B3.h y (W1 + W3) (1 + (a + cc)) (W2 + W4) (b + d))
      (SQR2B3.h x W1 (1 + a) (W2 + W3 + W4) (b + cc + d) - SQR2B3.h x (W1 + W2) (1 + (a + b)) (W3 + W4) (cc + d))
      0 γ hl hlL hγ0 hγ1 (by linarith)
    rcases hsel with h | h | h
    · apply improve X Finset.subset_union_left
      rw [hrev X Finset.subset_union_left, eY, eUL]; simp only [sub_self, mul_zero, zero_add]; linarith
    · apply improve (X ∩ Y) (Finset.inter_subset_left.trans Finset.subset_union_left)
      rw [hrev _ (Finset.inter_subset_left.trans Finset.subset_union_left), eX, eY, eI, eUL]; linarith
    · apply improve X Finset.subset_union_left
      rw [hrev X Finset.subset_union_left, eY, eUL]; simp only [sub_self, mul_zero, zero_add]
      simp only [mul_zero, zero_add] at h; linarith
  · -- Case 2 (R₂ ≤ R₃): compare with (X∩Y, X∪Y) and (Y, X∪Y)
    have h2 := core.2 hcase
    set γ := (1 + a) * (1 + a + cc) / ((1 + a + b) * (1 + a + b + cc))
    have hγ0 : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hsel := SQR2B3.select (lam i) (lam L)
      (SQR2B3.h y (W1 + W2 + W3) (1 + (a + b + cc)) W4 d - SQR2B3.h y (W1 + W3) (1 + (a + cc)) (W2 + W4) (b + d))
      (SQR2B3.h x W1 (1 + a) (W2 + W3 + W4) (b + cc + d) - SQR2B3.h x (W1 + W2) (1 + (a + b)) (W3 + W4) (cc + d))
      (SQR2B3.h x (W1 + W3) (1 + (a + cc)) (W2 + W4) (b + d) - SQR2B3.h x (W1 + W2) (1 + (a + b)) (W3 + W4) (cc + d))
      γ hl hlL hγ0 hγ1 (by linarith)
    rcases hsel with h | h | h
    · apply improve X Finset.subset_union_left
      rw [hrev X Finset.subset_union_left, eY, eUL]; simp only [sub_self, mul_zero, zero_add]; linarith
    · apply improve (X ∩ Y) (Finset.inter_subset_left.trans Finset.subset_union_left)
      rw [hrev _ (Finset.inter_subset_left.trans Finset.subset_union_left), eX, eY, eI, eUL]; linarith
    · apply improve Y Finset.subset_union_right
      rw [hrev Y Finset.subset_union_right, eX, eY, eYi, eUL]; linarith
