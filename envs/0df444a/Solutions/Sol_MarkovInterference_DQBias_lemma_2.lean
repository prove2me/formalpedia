-- Prove2me | solution 1 for MarkovInterference.DQBias.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:41:29.937425+00:00
-- url     : https://prove2.me/submissions/58322249-f892-4e26-bdd3-42cfb03ddfaf

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain

set_option autoImplicit false
open MarkovInterference.DQBias
open scoped Matrix

section
variable {S : Type} [Fintype S] [DecidableEq S]

lemma pow_mulVec_one (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ) :
    (P ^ k) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    have : P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
      ext i; simp [Matrix.mulVec, dotProduct, hP.2 i]
    rw [this, ih]

lemma pow_mulVec_fix (P : Matrix S S ℝ) (v : S → ℝ) (hv : P *ᵥ v = v) (k : ℕ) :
    (P ^ k) *ᵥ v = v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

lemma fixed_const (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ)
    (hk : ∀ i j, 0 < (P ^ k) i j) (v : S → ℝ) (hv : P *ᵥ v = v) (i j : S) : v i = v j := by
  have hQ := pow_mulVec_fix P v hv k
  have h1 := pow_mulVec_one P hP k
  have : Nonempty S := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max v
  have hsum : ∑ j, (P ^ k) i0 j * (v i0 - v j) = 0 := by
    have e1 : ∑ j, (P ^ k) i0 j = 1 := by
      have := congrFun h1 i0
      simpa [Matrix.mulVec, dotProduct] using this
    have e2 : ∑ j, (P ^ k) i0 j * v j = v i0 := by
      have := congrFun hQ i0
      simpa [Matrix.mulVec, dotProduct] using this
    calc ∑ j, (P ^ k) i0 j * (v i0 - v j)
        = ∑ j, (v i0 * (P ^ k) i0 j) - ∑ j, (P ^ k) i0 j * v j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [← Finset.mul_sum, e1, e2]; ring
  have hall : ∀ j, v j = v i0 := by
    intro j
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (P ^ k) i0 j * (v i0 - v j) :=
      fun j _ => mul_nonneg (hk i0 j).le (sub_nonneg.2 (hi0 j))
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hk i0 j).ne'
    · linarith
  rw [hall i, hall j]

lemma ker_trivial (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P) (hp : IsPrimitive P)
    (hrho : IsStationaryDist P rho) (v : S → ℝ)
    (h : (1 - P + onesRho rho) *ᵥ v = 0) : v = 0 := by
  have e : onesRho rho *ᵥ v = (rho ⬝ᵥ v) • (fun _ => (1 : ℝ)) := by
    ext i; simp [onesRho, Matrix.mulVec, Matrix.vecMulVec, dotProduct]
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, e] at h
  have hdot : rho ⬝ᵥ v = 0 := by
    have := congrArg (fun w => rho ⬝ᵥ w) h
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, hrho.2.2,
      smul_eq_mul, dotProduct_zero] at this
    have hs : rho ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by simpa [dotProduct] using hrho.2.1
    rw [hs] at this
    linarith
  rw [hdot, zero_smul, add_zero] at h
  have hv : P *ᵥ v = v := by
    have := sub_eq_zero.1 h
    exact this.symm
  obtain ⟨k, hk⟩ := hp
  have hc := fixed_const P hP k hk v hv
  funext i
  have hs : rho ⬝ᵥ v = v i := by
    have : ∀ j, v j = v i := fun j => hc j i
    simp only [dotProduct, this, ← Finset.sum_mul, hrho.2.1, one_mul]
  simp [← hs, hdot]

lemma isUnit_A (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P) (hp : IsPrimitive P)
    (hrho : IsStationaryDist P rho) : IsUnit (1 - P + onesRho rho).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have : (1 - P + onesRho rho) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.1 (ker_trivial P rho hP hp hrho _ this)


lemma n1_row (M : Matrix S S ℝ) (i : S) : ∑ j, |M i j| ≤ norm1inf M :=
  le_ciSup (f := fun i => ∑ j, |M i j|) (Finite.bddAbove_range _) i

lemma n1_nonneg (M : Matrix S S ℝ) : 0 ≤ norm1inf M :=
  Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => abs_nonneg _))

lemma n1_le (M : Matrix S S ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ i, ∑ j, |M i j| ≤ a) :
    norm1inf M ≤ a :=
  Real.iSup_le h ha

lemma n1_add (A B : Matrix S S ℝ) : norm1inf (A + B) ≤ norm1inf A + norm1inf B := by
  apply n1_le _ _ (add_nonneg (n1_nonneg A) (n1_nonneg B))
  intro i
  calc ∑ j, |(A + B) i j| ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun j _ => by simpa using abs_add_le (A i j) (B i j))
    _ = ∑ j, |A i j| + ∑ j, |B i j| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (n1_row A i) (n1_row B i)

lemma n1_sub (A B : Matrix S S ℝ) : norm1inf (A - B) ≤ norm1inf A + norm1inf B := by
  apply n1_le _ _ (add_nonneg (n1_nonneg A) (n1_nonneg B))
  intro i
  calc ∑ j, |(A - B) i j| ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun j _ => by simpa using abs_sub (A i j) (B i j))
    _ = ∑ j, |A i j| + ∑ j, |B i j| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (n1_row A i) (n1_row B i)

lemma n1_mul (A B : Matrix S S ℝ) : norm1inf (A * B) ≤ norm1inf A * norm1inf B := by
  apply n1_le _ _ (mul_nonneg (n1_nonneg A) (n1_nonneg B))
  intro i
  calc ∑ j, |(A * B) i j| ≤ ∑ j, ∑ k, |A i k| * |B k j| := by
        apply Finset.sum_le_sum; intro j _
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    _ ≤ ∑ k, |A i k| * norm1inf B :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (n1_row B k) (abs_nonneg _))
    _ = (∑ k, |A i k|) * norm1inf B := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (n1_row A i) (n1_nonneg B)

lemma n1_sum (f : ℕ → Matrix S S ℝ) (n : ℕ) :
    norm1inf (∑ k ∈ Finset.range n, f k) ≤ ∑ k ∈ Finset.range n, norm1inf (f k) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    apply n1_le _ _ le_rfl
    intro i; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (n1_add _ _).trans (add_le_add ih le_rfl)

lemma pow_entries_nonneg (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ) :
    ∀ i j, 0 ≤ (P ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hP.1 l j))

lemma norm_pow_le_one (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ) :
    norm1inf (P ^ k) ≤ 1 := by
  apply n1_le _ _ zero_le_one
  intro i
  have h1 := congrFun (pow_mulVec_one P hP k) i
  simp only [Matrix.mulVec, dotProduct, mul_one] at h1
  calc ∑ j, |(P ^ k) i j| = ∑ j, (P ^ k) i j :=
        Finset.sum_congr rfl (fun j _ => abs_of_nonneg (pow_entries_nonneg P hP k i j))
    _ = 1 := h1
    _ ≤ 1 := le_rfl

lemma norm_E_le (P : Matrix S S ℝ) (rho : S → ℝ) (hrho : IsStationaryDist P rho) : norm1inf (onesRho rho) ≤ 1 := by
  apply n1_le _ _ zero_le_one
  intro i
  calc ∑ j, |onesRho rho i j| = ∑ j, rho j :=
        Finset.sum_congr rfl (fun j _ => by
          simp [onesRho, Matrix.vecMulVec_apply, abs_of_nonneg (hrho.1 j)])
    _ = 1 := hrho.2.1
    _ ≤ 1 := le_rfl


lemma E_apply (rho : S → ℝ) (i j : S) : onesRho rho i j = rho j := by
  simp [onesRho, Matrix.vecMulVec_apply]

lemma alg_identities (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P)
    (hrho : IsStationaryDist P rho) (hU : IsUnit (1 - P + onesRho rho).det) :
    (groupInv P rho) * onesRho rho = 0 ∧
    (groupInv P rho) * (1 - P) = 1 - onesRho rho ∧
    onesRho rho * P = onesRho rho := by
  set E := onesRho rho with hEdef
  set A : Matrix S S ℝ := 1 - P + E with hA
  have hEE : E * E = E := by
    ext i j
    simp only [Matrix.mul_apply, hEdef, E_apply]
    rw [← Finset.sum_mul, hrho.2.1, one_mul]
  have hEP : E * P = E := by
    ext i j
    simp only [Matrix.mul_apply, hEdef, E_apply]
    simpa [Matrix.vecMul, dotProduct] using congrFun hrho.2.2 j
  have hPE : P * E = E := by
    ext i j
    simp only [Matrix.mul_apply, hEdef, E_apply]
    rw [← Finset.sum_mul, hP.2 i, one_mul]
  have hAE : A * E = E := by
    rw [hA, add_mul, sub_mul, one_mul, hPE, hEE]; abel
  have hAinvE : A⁻¹ * E = E := by
    calc A⁻¹ * E = A⁻¹ * (A * E) := by rw [hAE]
      _ = E := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hU, one_mul]
  have hG : groupInv P rho = A⁻¹ - E := rfl
  refine ⟨?_, ?_, hEP⟩
  · rw [hG, sub_mul, hAinvE, hEE, sub_self]
  · have h1P : 1 - P = A - E := by rw [hA]; abel
    have e1 : A⁻¹ * (1 - P) = 1 - E := by
      rw [h1P, Matrix.mul_sub, Matrix.nonsing_inv_mul A hU, hAinvE]
    have e2 : E * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hEP, sub_self]
    rw [hG, sub_mul, e1, e2, sub_zero]

lemma telescope (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P)
    (hrho : IsStationaryDist P rho) (hU : IsUnit (1 - P + onesRho rho).det) (n : ℕ) :
    ∑ k ∈ Finset.range n, (P ^ k - onesRho rho) =
      groupInv P rho - groupInv P rho * P ^ n := by
  obtain ⟨hGE, hGP, hEP⟩ := alg_identities P rho hP hrho hU
  set E := onesRho rho
  set G := groupInv P rho
  have hEPn : ∀ n : ℕ, E * P ^ n = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, hEP]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have key : G * P ^ n - G * P ^ (n + 1) = P ^ n - E := by
      calc G * P ^ n - G * P ^ (n + 1) = G * (1 - P) * P ^ n := by
            rw [pow_succ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = P ^ n - E := by rw [hGP, Matrix.sub_mul, Matrix.one_mul, hEPn]
    have : G * P ^ (n + 1) = G * P ^ n - (P ^ n - E) := by rw [← key]; abel
    rw [this]; abel

lemma norm_G_le (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P)
    (hrho : IsStationaryDist P rho) (hU : IsUnit (1 - P + onesRho rho).det) (n : ℕ) :
    norm1inf (groupInv P rho) ≤
      ∑ k ∈ Finset.range n, norm1inf (P ^ k - onesRho rho) +
        norm1inf (groupInv P rho) * norm1inf (P ^ n - onesRho rho) := by
  obtain ⟨hGE, hGP, hEP⟩ := alg_identities P rho hP hrho hU
  have h1 : groupInv P rho =
      ∑ k ∈ Finset.range n, (P ^ k - onesRho rho) + groupInv P rho * (P ^ n - onesRho rho) := by
    rw [telescope P rho hP hrho hU n, Matrix.mul_sub, hGE, sub_zero]; abel
  calc norm1inf (groupInv P rho)
      = norm1inf (∑ k ∈ Finset.range n, (P ^ k - onesRho rho) +
          groupInv P rho * (P ^ n - onesRho rho)) := by rw [← h1]
    _ ≤ _ := (n1_add _ _).trans
        (add_le_add (n1_sum (fun k => P ^ k - onesRho rho) n) (n1_mul _ _))

lemma norm_D_le_two (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P)
    (hrho : IsStationaryDist P rho) (k : ℕ) : norm1inf (P ^ k - onesRho rho) ≤ 2 := by
  have := n1_sub (P ^ k) (onesRho rho)
  linarith [norm_pow_le_one P hP k, norm_E_le P rho hrho]

end

lemma real_bound (C lam : ℝ) (hC : 1 ≤ C) (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ m : ℕ, 2 * (m : ℝ) + C * lam ^ m / (1 - lam) ≤ (2 * Real.log C + 1) / (1 - lam) := by
  have ht : 0 < 1 - lam := by linarith
  have hlogneg : Real.log lam < 0 := Real.log_neg h0 h1
  have hL : 1 - lam ≤ -Real.log lam := by linarith [Real.log_le_sub_one_of_pos h0]
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hCpos : 0 < C := by linarith
  rcases le_or_gt C 2 with hC2 | hC2
  · refine ⟨0, ?_⟩
    simp only [Nat.cast_zero, mul_zero, pow_zero, mul_one, zero_add]
    apply div_le_div_of_nonneg_right _ ht.le
    have h := Real.one_sub_inv_le_log_of_pos hCpos
    have hinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hCpos.ne'
    nlinarith [inv_pos.2 hCpos]
  · set a : ℝ := Real.log (C / 2) with ha
    have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
    set L : ℝ := -Real.log lam with hLdef
    have hLpos : 0 < L := by linarith
    have hal0 : 0 ≤ a / L := div_nonneg ha0 hLpos.le
    set m : ℕ := ⌈a / L⌉₊ with hm
    refine ⟨m, ?_⟩
    set φ : ℝ := (m : ℝ) - a / L with hφ
    have hφ0 : 0 ≤ φ := by have := Nat.le_ceil (a / L); rw [hφ]; linarith
    have hφ1 : φ ≤ 1 := by have := Nat.ceil_lt_add_one hal0; rw [hφ]; linarith
    have hCm : C * lam ^ m = 2 * lam ^ φ := by
      have e1 : C = 2 * Real.exp a := by
        rw [ha, Real.exp_log (by linarith)]; ring
      have e2 : lam ^ m = Real.exp (Real.log lam * (m : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos h0]
      have e3 : lam ^ φ = Real.exp (Real.log lam * φ) := Real.rpow_def_of_pos h0 φ
      rw [e1, e2, e3, mul_assoc, ← Real.exp_add]
      congr 2
      have key : Real.log lam * (a / L) = -a := by
        have : L ≠ 0 := hLpos.ne'
        field_simp
        rw [hLdef]; ring
      rw [hφ, mul_sub, key]; ring
    have hbern : lam ^ φ ≤ 1 - φ * (1 - lam) := by
      have := rpow_one_add_le_one_add_mul_self (s := -(1 - lam)) (by linarith) hφ0 hφ1
      have e : (1 : ℝ) + -(1 - lam) = lam := by ring
      rw [e] at this
      linarith
    have hal : a / L ≤ a / (1 - lam) := div_le_div_of_nonneg_left ha0 ht hL
    have hstep : 2 * (m : ℝ) + C * lam ^ m / (1 - lam) ≤ 2 * (a / L) + 2 / (1 - lam) := by
      rw [hCm]
      have h2 : 2 * lam ^ φ / (1 - lam) ≤ 2 * (1 - φ * (1 - lam)) / (1 - lam) :=
        div_le_div_of_nonneg_right (by linarith) ht.le
      have h3 : 2 * (1 - φ * (1 - lam)) / (1 - lam) = 2 / (1 - lam) - 2 * φ := by
        field_simp
      have h4 : (m : ℝ) = φ + a / L := by rw [hφ]; ring
      rw [h4] at *
      linarith
    have hfin : 2 * (a / (1 - lam)) + 2 / (1 - lam) ≤ (2 * Real.log C + 1) / (1 - lam) := by
      have : 2 * (a / (1 - lam)) + 2 / (1 - lam) = (2 * a + 2) / (1 - lam) := by ring
      rw [this]
      apply div_le_div_of_nonneg_right _ ht.le
      have : a = Real.log C - Real.log 2 := by rw [ha, Real.log_div (by linarith) (by norm_num)]
      linarith
    linarith

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (rho : S → ℝ) (C lam : ℝ)
    (hP : IsStochastic P) (hp : IsPrimitive P) (hrho : IsStationaryDist P rho)
    (hC : 1 ≤ C) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmix : ∀ k : ℕ, norm1inf (P ^ k - onesRho rho) ≤ C * lam ^ k) :
    norm1inf (groupInv P rho) ≤ (2 * Real.log C + 1) / (1 - lam) := by
  have hU := isUnit_A P rho hP hp hrho
  obtain ⟨m, hm⟩ := real_bound C lam hC hlam0 hlam1
  have ht : 0 < 1 - lam := by linarith
  set g := norm1inf (groupInv P rho) with hg
  set B := 2 * (m : ℝ) + C * lam ^ m / (1 - lam) with hB
  have hbound : ∀ n : ℕ, m ≤ n → g ≤ B + g * (C * lam ^ n) := by
    intro n hn
    have h1 := norm_G_le P rho hP hrho hU n
    have hsum : ∑ k ∈ Finset.range n, norm1inf (P ^ k - onesRho rho) ≤ B := by
      rw [← Finset.sum_range_add_sum_Ico _ hn]
      have e1 : ∑ k ∈ Finset.range m, norm1inf (P ^ k - onesRho rho) ≤ 2 * (m : ℝ) := by
        calc _ ≤ ∑ k ∈ Finset.range m, (2 : ℝ) :=
              Finset.sum_le_sum (fun k _ => norm_D_le_two P rho hP hrho k)
          _ = 2 * (m : ℝ) := by simp [mul_comm]
      have e2 : ∑ k ∈ Finset.Ico m n, norm1inf (P ^ k - onesRho rho) ≤
          C * lam ^ m / (1 - lam) := by
        calc _ ≤ ∑ k ∈ Finset.Ico m n, C * lam ^ k :=
              Finset.sum_le_sum (fun k _ => hmix k)
          _ = C * ∑ k ∈ Finset.Ico m n, lam ^ k := by rw [Finset.mul_sum]
          _ ≤ C * (lam ^ m / (1 - lam)) :=
              mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hlam0.le hlam1) (by linarith)
          _ = _ := by ring
      linarith
    have h2 : g * norm1inf (P ^ n - onesRho rho) ≤ g * (C * lam ^ n) :=
      mul_le_mul_of_nonneg_left (hmix n) (n1_nonneg _)
    linarith
  have hlim : ∀ ε > 0, g ≤ B + ε := by
    intro ε hε
    have ht0 : Filter.Tendsto (fun n : ℕ => g * (C * lam ^ n)) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).const_mul C
      simpa using this.const_mul g
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 (ht0.eventually (gt_mem_nhds hε)))
    have := hbound (max m N) (le_max_left _ _)
    have := hN (max m N) (le_max_right _ _)
    linarith
  have : g ≤ B := le_of_forall_pos_le_add hlim
  linarith
