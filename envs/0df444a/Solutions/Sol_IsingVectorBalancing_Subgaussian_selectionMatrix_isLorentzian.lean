-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.selectionMatrix_isLorentzian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:21:54.445974+00:00
-- url     : https://prove2.me/submissions/bcb025d7-675c-4e42-9930-c0a5192c1c38

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IsingVectorBalancing.Subgaussian.Dev.SL
open IsingVectorBalancing.Subgaussian Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- quadratic form -/
def qf (Q : Matrix C C ℝ) (z : C → ℝ) : ℝ := z ⬝ᵥ Q *ᵥ z

/-- no two-dimensional subspace on which `Q` is positive definite -/
def Good (Q : Matrix C C ℝ) : Prop :=
  ∀ u w : C → ℝ, ¬ (0 < qf Q u ∧ (u ⬝ᵥ Q *ᵥ w) ^ 2 < qf Q u * qf Q w)

theorem eig_dot {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (i j : C) : (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 := by
  have := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [dotProduct_comm] using this

theorem quad_eig {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (w : C → ℝ) :
    w ⬝ᵥ A.mulVec w = ∑ c, hA.eigenvalues c * (⇑(hA.eigenvectorBasis c) ⬝ᵥ w) ^ 2 := by
  set U : Matrix C C ℝ := (hA.eigenvectorUnitary : Matrix C C ℝ) with hUdef
  have hU : ∀ i c, U i c = hA.eigenvectorBasis c i := by
    intro i c; simp [hUdef, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose, hUdef] using this
  set y : C → ℝ := fun c => ⇑(hA.eigenvectorBasis c) ⬝ᵥ w with hy
  have hw : w = ∑ c, y c • ⇑(hA.eigenvectorBasis c) := by
    have : w = (U * Uᵀ) *ᵥ w := by rw [hUU]; simp
    rw [this, ← Matrix.mulVec_mulVec]
    ext i
    simp [Matrix.mulVec, dotProduct, hU, hy, Finset.sum_apply, mul_comm]
  have hA' : A.mulVec w = ∑ c, (y c * hA.eigenvalues c) • ⇑(hA.eigenvectorBasis c) := by
    conv_lhs => rw [hw]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, smul_smul]
  conv_lhs => rw [hA', hw]
  simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, eig_dot, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hy]; ring

theorem herm_of_sym {Q : Matrix C C ℝ} (h : ∀ a b, Q a b = Q b a) : Q.IsHermitian := by
  ext a b; simp [Matrix.conjTranspose_apply, h a b]

theorem sym_form {Q : Matrix C C ℝ} (h : ∀ a b, Q a b = Q b a)
    (x z : C → ℝ) : z ⬝ᵥ Q *ᵥ x = x ⬝ᵥ Q *ᵥ z := by
  rw [dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose]
  have : Qᵀ = Q := by ext a b; simp [h b a]
  rw [this]

theorem pd2 {p β r a b : ℝ} (hp : 0 < p) (hβ : β ^ 2 < p * r) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 * p + 2 * a * b * β + b ^ 2 * r := by
  have key : p * (a ^ 2 * p + 2 * a * b * β + b ^ 2 * r) = (a * p + b * β) ^ 2 + b ^ 2 * (p * r - β ^ 2) := by
    ring
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by tauto
    have : 0 < a ^ 2 := by positivity
    nlinarith
  · have : 0 < b ^ 2 := by positivity
    have h1 : 0 < p * (a ^ 2 * p + 2 * a * b * β + b ^ 2 * r) := by
      rw [key]; nlinarith [sq_nonneg (a * p + b * β), mul_pos this (sub_pos.mpr hβ)]
    exact pos_of_mul_pos_right h1 hp.le

theorem qf_comb {Q : Matrix C C ℝ} (h : ∀ a b, Q a b = Q b a) (u w : C → ℝ) (a b : ℝ) :
    qf Q (a • u + b • w) = a ^ 2 * qf Q u + 2 * a * b * (u ⬝ᵥ Q *ᵥ w) + b ^ 2 * qf Q w := by
  simp only [qf, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [sym_form h w u]; ring

/-- If `Q` is nonpositive on the hyperplane `y ⬝ z = 0`, then `Q` is Good. -/
theorem good_of_hyperplane {Q : Matrix C C ℝ} (h : ∀ a b, Q a b = Q b a) (y : C → ℝ)
    (hy : ∀ z, y ⬝ᵥ z = 0 → qf Q z ≤ 0) : Good Q := by
  rintro u w ⟨hu, hβ⟩
  obtain ⟨a, b, hab, hz⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ y ⬝ᵥ (a • u + b • w) = 0 := by
    by_cases h1 : y ⬝ᵥ u = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h1]⟩
    · refine ⟨y ⬝ᵥ w, -(y ⬝ᵥ u), Or.inr (neg_ne_zero.mpr h1), ?_⟩
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  have := hy _ hz
  rw [qf_comb h] at this
  linarith [pd2 hu hβ hab]

theorem good_of_lor {Q : Matrix C C ℝ} (hQ : IsLorentzian Q) : Good Q := by
  obtain ⟨_, hH, hle⟩ := hQ
  have h : ∀ a b, Q a b = Q b a := fun a b => by
    have := congrFun (congrFun hH.eq b) a
    simpa [Matrix.conjTranspose_apply] using this
  rintro u w ⟨hu, hβ⟩
  set q := qf Q u
  set β := u ⬝ᵥ Q *ᵥ w
  -- z = w - (β / q) u is Q-orthogonal to u and has positive form
  set z := w - (β / q) • u with hzdef
  have hz0 : u ⬝ᵥ Q *ᵥ z = 0 := by
    simp only [hzdef, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    change β - β / q * q = 0
    field_simp; ring
  have hzpos : 0 < qf Q z := by
    have e : z = (-(β / q)) • u + (1 : ℝ) • w := by
      rw [hzdef]; simp [sub_eq_add_neg, add_comm]
    rw [e, qf_comb h]
    have : (-(β / q)) ^ 2 * q + 2 * (-(β / q)) * 1 * β + 1 ^ 2 * qf Q w
        = qf Q w - β ^ 2 / q := by field_simp; ring
    rw [this, sub_pos, div_lt_iff₀ hu]; linarith
  -- now the eigen argument (as in theorem 5)
  by_cases hex : ∃ c0, 0 < hH.eigenvalues c0
  · obtain ⟨c0, hc0⟩ := hex
    have huniq : ∀ c, 0 < hH.eigenvalues c → c = c0 := fun c hc =>
      Finset.card_le_one.mp hle c (by simpa using hc) c0 (by simpa using hc0)
    set e : C → ℝ := ⇑(hH.eigenvectorBasis c0)
    obtain ⟨a, b, hab, hs⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
        a * (e ⬝ᵥ u) + b * (e ⬝ᵥ z) = 0 := by
      by_cases hs1 : e ⬝ᵥ u = 0
      · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hs1]⟩
      · exact ⟨e ⬝ᵥ z, -(e ⬝ᵥ u), Or.inr (neg_ne_zero.mpr hs1), by ring⟩
    have hle0 : qf Q (a • u + b • z) ≤ 0 := by
      unfold qf
      rw [quad_eig hH]
      refine Finset.sum_nonpos fun c _ => ?_
      by_cases hc : 0 < hH.eigenvalues c
      · have : c = c0 := huniq c hc
        subst this
        have h0 : ⇑(hH.eigenvectorBasis c) ⬝ᵥ (a • u + b • z) = 0 := by
          simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; exact hs
        rw [h0]; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (sq_nonneg _)
    rw [qf_comb h, hz0] at hle0
    have := pd2 (β := 0) (r := qf Q z) hu (by nlinarith) hab
    linarith
  · have hex' : ∀ c, hH.eigenvalues c ≤ 0 := fun c => not_lt.mp (fun h => hex ⟨c, h⟩)
    have h2 : qf Q u ≤ 0 := by
      unfold qf; rw [quad_eig hH]
      exact Finset.sum_nonpos fun c _ => mul_nonpos_of_nonpos_of_nonneg (hex' c) (sq_nonneg _)
    linarith

theorem lor_of_good {Q : Matrix C C ℝ} (h : ∀ a b, Q a b = Q b a) (hnn : ∀ a b, 0 ≤ Q a b)
    (hg : Good Q) : IsLorentzian Q := by
  refine ⟨hnn, herm_of_sym h, ?_⟩
  set hH := herm_of_sym h
  by_contra hc
  rw [not_le, Finset.one_lt_card] at hc
  obtain ⟨i, hi, j, hj, hij⟩ := hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  apply hg (⇑(hH.eigenvectorBasis i)) (⇑(hH.eigenvectorBasis j))
  have hv : ∀ k l, ⇑(hH.eigenvectorBasis k) ⬝ᵥ Q *ᵥ ⇑(hH.eigenvectorBasis l)
      = hH.eigenvalues l * if k = l then 1 else 0 := by
    intro k l
    rw [hH.mulVec_eigenvectorBasis, dotProduct_smul, eig_dot, smul_eq_mul]
  simp only [qf, hv, if_neg hij, mul_one, mul_zero, if_true]
  exact ⟨hi, by rw [sq, zero_mul]; exact mul_pos hi hj⟩

theorem good_congr {A : Matrix C C ℝ} (hA : Good A) (P : Matrix C C ℝ) :
    Good (Pᵀ * A * P) := by
  have hb : ∀ u w : C → ℝ, u ⬝ᵥ (Pᵀ * A * P) *ᵥ w = (P *ᵥ u) ⬝ᵥ A *ᵥ (P *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.vecMul_transpose]
  intro u w hc
  apply hA (P *ᵥ u) (P *ᵥ w)
  simpa [qf, hb] using hc

end IsingVectorBalancing.Subgaussian.Dev.SL
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IsingVectorBalancing.Subgaussian.Dev.SL
open IsingVectorBalancing.Subgaussian Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- equality case: a positive matrix fixing a positive vector `v` is a contraction, with
equality only on multiples of `v`. -/
theorem eq_case {R : Matrix C C ℝ} (hsym : ∀ a b, R a b = R b a) (hpos : ∀ a b, 0 < R a b)
    (v : C → ℝ) (hv : ∀ a, 0 < v a) (hRv : ∀ a, ∑ b, R a b * v b = v a)
    (u : C → ℝ) (hu : u ⬝ᵥ u ≤ qf R u) : ∃ c : ℝ, ∀ a, u a = c * v a := by
  set s : C → ℝ := fun a => u a / v a with hs
  have hus : ∀ a, u a = s a * v a := fun a => by
    simp only [hs]; field_simp [(hv a).ne']
  have h1 : ∑ a, ∑ b, R a b * v a * v b * s a ^ 2 = u ⬝ᵥ u := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : ∑ b, R a b * v a * v b * s a ^ 2 = s a ^ 2 * v a * ∑ b, R a b * v b := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    rw [this, hRv, hus a]; ring
  have h2 : ∑ a, ∑ b, R a b * v a * v b * s b ^ 2 = u ⬝ᵥ u := by
    rw [Finset.sum_comm, ← h1]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym]; ring
  have h3 : ∑ a, ∑ b, R a b * v a * v b * (s a * s b) = qf R u := by
    simp only [qf, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hus a, hus b]; ring
  have hid : ∑ a, ∑ b, R a b * v a * v b * (s a - s b) ^ 2 = 2 * (u ⬝ᵥ u - qf R u) := by
    have : ∀ a b, R a b * v a * v b * (s a - s b) ^ 2 = R a b * v a * v b * s a ^ 2
        + R a b * v a * v b * s b ^ 2 - 2 * (R a b * v a * v b * (s a * s b)) := fun a b => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h1, h2, h3]; ring
  have hnn : ∀ a b, 0 ≤ R a b * v a * v b * (s a - s b) ^ 2 := fun a b =>
    mul_nonneg (mul_nonneg (mul_nonneg (hpos a b).le (hv a).le) (hv b).le) (sq_nonneg _)
  have hzero : ∑ a, ∑ b, R a b * v a * v b * (s a - s b) ^ 2 = 0 := by
    apply le_antisymm
    · rw [hid]; linarith
    · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b
  have hall : ∀ a b, s a = s b := by
    intro a b
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg fun b _ => hnn a b)).mp hzero a (Finset.mem_univ _)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn a b)).mp ha b (Finset.mem_univ _)
    have hp : 0 < R a b * v a * v b := mul_pos (mul_pos (hpos a b) (hv a)) (hv b)
    have := (mul_eq_zero.mp hb).resolve_left hp.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  by_cases hne : Nonempty C
  · obtain ⟨a0⟩ := hne
    exact ⟨s a0, fun a => by rw [hus a, hall a a0]⟩
  · exact ⟨0, fun a => (hne ⟨a⟩).elim⟩

/-- the step: a positive matrix that is an `x`-weighted sum of Good matrices `Qi i`
with `Qi i x = Q e_i` is Good. -/
theorem good_step {Q : Matrix C C ℝ} (hsym : ∀ a b, Q a b = Q b a) (hpos : ∀ a b, 0 < Q a b)
    (x : C → ℝ) (hx : ∀ i, 0 < x i) (Qi : C → Matrix C C ℝ)
    (hdec : ∀ a b, Q a b = ∑ i, x i * Qi i a b)
    (hcol : ∀ i a, ∑ b, Qi i a b * x b = Q a i)
    (hsymi : ∀ i a b, Qi i a b = Qi i b a)
    (hgood : ∀ i, Good (Qi i)) : Good Q := by
  set y : C → ℝ := Q *ᵥ x with hydef
  have hy : ∀ i, 0 < y i := fun i => by
    simp only [hydef, mulVec, dotProduct]
    exact Finset.sum_pos (fun b _ => mul_pos (hpos i b) (hx b)) ⟨i, Finset.mem_univ _⟩
  -- (I)
  have hQsum : Q = ∑ i, x i • Qi i := by
    ext a b; simp [Matrix.sum_apply, hdec]
  have hI : ∀ z, qf Q z ≤ ∑ i, (x i / y i) * (Q *ᵥ z) i ^ 2 := by
    intro z
    have hq : qf Q z = ∑ i, x i * qf (Qi i) z := by
      simp only [qf]
      rw [hQsum, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hq]
    refine Finset.sum_le_sum fun i _ => ?_
    have hqx : qf (Qi i) x = y i := by
      simp only [qf, dotProduct, hydef, mulVec]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hcol i a, hsym, mul_comm]
    have hβ : x ⬝ᵥ Qi i *ᵥ z = (Q *ᵥ z) i := by
      rw [← sym_form (hsymi i)]
      simp only [dotProduct, mulVec]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hcol i a, hsym, mul_comm]
    have hg := hgood i x z
    rw [hqx, hβ] at hg
    have hle : y i * qf (Qi i) z ≤ (Q *ᵥ z) i ^ 2 := by
      by_contra hc; exact hg ⟨hy i, lt_of_not_ge hc⟩
    rw [div_mul_eq_mul_div, le_div_iff₀ (hy i)]
    nlinarith [hx i]
  -- rescaling
  set Λ : C → ℝ := fun a => Real.sqrt (x a / y a) with hΛdef
  have hΛ : ∀ a, 0 < Λ a := fun a => Real.sqrt_pos.mpr (div_pos (hx a) (hy a))
  have hΛ2 : ∀ a, Λ a * Λ a = x a / y a := fun a =>
    Real.mul_self_sqrt (div_pos (hx a) (hy a)).le
  set R : Matrix C C ℝ := Matrix.of fun a b => Λ a * Q a b * Λ b with hRdef
  set v : C → ℝ := fun a => Λ a * y a with hvdef
  have hRsym : ∀ a b, R a b = R b a := fun a b => by simp only [hRdef, of_apply, hsym a b]; ring
  have hRpos : ∀ a b, 0 < R a b := fun a b => by
    simp only [hRdef, of_apply]; exact mul_pos (mul_pos (hΛ a) (hpos a b)) (hΛ b)
  have hv : ∀ a, 0 < v a := fun a => mul_pos (hΛ a) (hy a)
  have hRv : ∀ a, ∑ b, R a b * v b = v a := by
    intro a
    have : ∀ b, R a b * v b = Λ a * (Q a b * x b) := fun b => by
      simp only [hRdef, of_apply, hvdef]
      have := hΛ2 b
      have hyb := (hy b).ne'
      calc Λ a * Q a b * Λ b * (Λ b * y b) = Λ a * Q a b * (Λ b * Λ b) * y b := by ring
        _ = Λ a * (Q a b * x b) := by rw [this]; field_simp
    rw [Finset.sum_congr rfl (fun b _ => this b), ← Finset.mul_sum]
    simp only [hvdef, hydef, mulVec, dotProduct]
  have hRw : ∀ w a, (R *ᵥ w) a = Λ a * (Q *ᵥ (fun b => Λ b * w b)) a := by
    intro w a
    simp only [hRdef, mulVec, dotProduct, of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_; ring
  have hqR : ∀ w, qf R w = qf Q (fun b => Λ b * w b) := by
    intro w
    simp only [qf, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hRw]; ring
  have hI' : ∀ w, qf R w ≤ (R *ᵥ w) ⬝ᵥ (R *ᵥ w) := by
    intro w
    rw [hqR]
    refine (hI _).trans (le_of_eq ?_)
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hRw, ← hΛ2]; ring
  -- (C') on R
  have hRH := herm_of_sym hRsym
  have hC' : ∀ w, v ⬝ᵥ w = 0 → qf R w ≤ 0 := by
    intro w hw
    unfold qf
    rw [quad_eig hRH]
    refine Finset.sum_nonpos fun j _ => ?_
    by_cases hj : 0 < hRH.eigenvalues j
    · set e : C → ℝ := ⇑(hRH.eigenvectorBasis j)
      have hRe : R *ᵥ e = hRH.eigenvalues j • e := hRH.mulVec_eigenvectorBasis j
      have hee : e ⬝ᵥ e = 1 := by simpa using eig_dot hRH j j
      have hqe : qf R e = hRH.eigenvalues j := by
        simp only [qf, hRe, dotProduct_smul, hee, smul_eq_mul, mul_one]
      have hRR : (R *ᵥ e) ⬝ᵥ (R *ᵥ e) = hRH.eigenvalues j ^ 2 := by
        rw [hRe, smul_dotProduct, dotProduct_smul, hee]; simp [sq]
      have h1 := hI' e
      rw [hqe, hRR] at h1
      have hge : 1 ≤ hRH.eigenvalues j := by nlinarith
      obtain ⟨c, hc⟩ := eq_case hRsym hRpos v hv hRv e (by rw [hee, hqe]; exact hge)
      have : e ⬝ᵥ w = 0 := by
        have : e = c • v := funext fun a => by simp [hc a]
        rw [this, smul_dotProduct, hw, smul_zero]
      rw [this]; simp
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hj) (sq_nonneg _)
  refine good_of_hyperplane hsym y fun z hz => ?_
  have := hC' (fun a => z a / Λ a) (by
    simp only [dotProduct, hvdef] at hz ⊢
    rw [← hz]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp [(hΛ a).ne'])
  rw [hqR] at this
  have e : (fun b => Λ b * (z b / Λ b)) = z := funext fun b => by field_simp [(hΛ b).ne']
  rwa [e] at this

end IsingVectorBalancing.Subgaussian.Dev.SL
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IsingVectorBalancing.Subgaussian.Dev.SL
open IsingVectorBalancing.Subgaussian Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- weight of the pairs inside a tail assignment -/
def wt {m : ℕ} (A : Matrix C C ℝ) (r : Fin m → C) : ℝ :=
  ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), A (r i) (r j)

/-- one term of the selection matrix -/
def Tm {m : ℕ} (A : Matrix C C ℝ) (t : Fin m → C → ℝ) (a b : C) (r : Fin m → C) : ℝ :=
  (∏ j, t j (r j)) * (A a b * (∏ j, A a (r j)) * (∏ j, A b (r j)) * wt A r)

/-- the selection matrix -/
def Mm {m : ℕ} (A : Matrix C C ℝ) (t : Fin m → C → ℝ) : Matrix C C ℝ :=
  Matrix.of fun a b => ∑ r : Fin m → C, Tm A t a b r

theorem wt_cons {m : ℕ} (A : Matrix C C ℝ) (i : C) (r : Fin m → C) :
    wt A (Fin.cons i r : Fin (m + 1) → C) = (∏ j, A i (r j)) * wt A r := by
  simp only [wt, Finset.prod_filter, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    lt_self_iff_false, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    Fin.not_lt_zero, one_mul]

theorem sum_cons {m : ℕ} (f : (Fin (m + 1) → C) → ℝ) :
    ∑ r, f r = ∑ i, ∑ r : Fin m → C, f (Fin.cons i r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => C)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem prod_sym {m : ℕ} {A : Matrix C C ℝ} (hs : ∀ a b, A a b = A b a) (i : C)
    (r : Fin m → C) : ∏ j, A (r j) i = ∏ j, A i (r j) :=
  Finset.prod_congr rfl fun j _ => hs _ _

theorem Mm_sym {m : ℕ} {A : Matrix C C ℝ} (hs : ∀ a b, A a b = A b a) (t : Fin m → C → ℝ)
    (a b : C) : Mm A t a b = Mm A t b a := by
  simp only [Mm, of_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Tm]; rw [hs a b]; ring

theorem Mm_nonneg {m : ℕ} {A : Matrix C C ℝ} (hA : ∀ a b, 0 ≤ A a b) (t : Fin m → C → ℝ)
    (ht : ∀ j c, 0 ≤ t j c) (a b : C) : 0 ≤ Mm A t a b := by
  simp only [Mm, of_apply, Tm, wt]
  refine Finset.sum_nonneg fun r _ => ?_
  have := hA a b
  have h1 : 0 ≤ ∏ j, t j (r j) := Finset.prod_nonneg fun j _ => ht _ _
  have h2 : 0 ≤ ∏ j, A a (r j) := Finset.prod_nonneg fun j _ => hA _ _
  have h3 : 0 ≤ ∏ j, A b (r j) := Finset.prod_nonneg fun j _ => hA _ _
  have h4 : 0 ≤ ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), A (r i) (r j) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hA _ _
  positivity

theorem Mm_pos {m : ℕ} {A : Matrix C C ℝ} (hA : ∀ a b, 0 < A a b) (t : Fin m → C → ℝ)
    (ht : ∀ j c, 0 < t j c) (a b : C) : 0 < Mm A t a b := by
  simp only [Mm, of_apply, Tm, wt]
  refine Finset.sum_pos (fun r _ => ?_) ⟨fun _ => a, Finset.mem_univ _⟩
  have := hA a b
  have h1 : 0 < ∏ j, t j (r j) := Finset.prod_pos fun j _ => ht _ _
  have h2 : 0 < ∏ j, A a (r j) := Finset.prod_pos fun j _ => hA _ _
  have h3 : 0 < ∏ j, A b (r j) := Finset.prod_pos fun j _ => hA _ _
  have h4 : 0 < ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), A (r i) (r j) :=
    Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hA _ _
  positivity

/-- the tails seen after fixing the first tail coordinate at `i` -/
def tl {m : ℕ} (A : Matrix C C ℝ) (t : Fin (m + 1) → C → ℝ) (i : C) : Fin m → C → ℝ :=
  fun j c => t j.succ c * A c i

/-- the pieces of the decomposition -/
def Qi {m : ℕ} (A : Matrix C C ℝ) (t : Fin (m + 1) → C → ℝ) (i : C) : Matrix C C ℝ :=
  Matrix.of fun a b => A a i * Mm A (tl A t i) a b * A b i

theorem Mm_dec {m : ℕ} {A : Matrix C C ℝ} (hs : ∀ a b, A a b = A b a)
    (t : Fin (m + 1) → C → ℝ) (a b : C) :
    Mm A t a b = ∑ i, t 0 i * Qi A t i a b := by
  simp only [Mm, of_apply, Qi]
  rw [sum_cons]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Tm, tl, wt_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.prod_mul_distrib, prod_sym hs i r]
  ring

theorem Qi_swap {m : ℕ} {A : Matrix C C ℝ} (hs : ∀ a b, A a b = A b a)
    (t : Fin (m + 1) → C → ℝ) (i a b : C) : Qi A t i a b = Qi A t b a i := by
  simp only [Qi, Mm, of_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Tm, tl, Finset.prod_mul_distrib, prod_sym hs i r, prod_sym hs b r]
  rw [hs b i]; ring

theorem Mm_zero (A : Matrix C C ℝ) (t : Fin 0 → C → ℝ) : Mm A t = A := by
  ext a b
  simp [Mm, Tm, wt]

theorem good_diag {M : Matrix C C ℝ} (hM : Good M) (d : C → ℝ) :
    Good (Matrix.of fun a b => d a * M a b * d b) := by
  have : (Matrix.of fun a b => d a * M a b * d b) = (diagonal d)ᵀ * M * diagonal d := by
    ext a b; simp [diagonal_transpose, diagonal_mul, mul_diagonal]
  rw [this]; exact good_congr hM _

theorem good_Mm : ∀ (m : ℕ) (A : Matrix C C ℝ), (∀ a b, A a b = A b a) → (∀ a b, 0 < A a b) →
    Good A → ∀ t : Fin m → C → ℝ, (∀ j c, 0 < t j c) → Good (Mm A t) := by
  intro m
  induction m with
  | zero => intro A _ _ hg t _; rw [Mm_zero]; exact hg
  | succ m ih =>
    intro A hs hp hg t ht
    refine good_step (fun a b => Mm_sym hs t a b) (fun a b => Mm_pos hp t ht a b) (t 0)
      (fun i => ht 0 i) (Qi A t) (fun a b => Mm_dec hs t a b) ?_ ?_ ?_
    · intro i a
      rw [Mm_dec hs t a i]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Qi_swap hs t i a b, mul_comm]
    · intro i a b
      simp only [Qi, of_apply]; rw [Mm_sym hs]; ring
    · intro i
      exact good_diag (ih A hs hp hg (tl A t i) fun j c => mul_pos (ht _ _) (hp _ _)) _

end IsingVectorBalancing.Subgaussian.Dev.SL
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IsingVectorBalancing.Subgaussian.Dev.SL
open IsingVectorBalancing.Subgaussian Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem cont_bil (F : ℝ → Matrix C C ℝ) (hc : ∀ a b, Continuous fun ε => F ε a b)
    (u w : C → ℝ) : Continuous fun ε => u ⬝ᵥ F ε *ᵥ w := by
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_finsetSum _ fun b _ => (hc a b).mul continuous_const)

theorem good_limit (F : ℝ → Matrix C C ℝ) (hc : ∀ a b, Continuous fun ε => F ε a b)
    (hg : ∀ ε, 0 < ε → Good (F ε)) : Good (F 0) := by
  rintro u w ⟨h1, h2⟩
  set S : Set ℝ := {ε | 0 < qf (F ε) u ∧ (u ⬝ᵥ F ε *ᵥ w) ^ 2 < qf (F ε) u * qf (F ε) w}
  have hS : IsOpen S := by
    have c1 := cont_bil F hc u u
    have c2 := cont_bil F hc u w
    have c3 := cont_bil F hc w w
    exact (isOpen_lt continuous_const c1).inter (isOpen_lt (c2.pow 2) (c1.mul c3))
  have h0 : (0 : ℝ) ∈ S := ⟨h1, h2⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS 0 h0
  have hmem : δ / 2 ∈ S := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  exact hg (δ / 2) (by linarith) u w hmem

/-- the perturbation matrix `1 + ε J` -/
def Pm (ε : ℝ) : Matrix C C ℝ := 1 + ε • Matrix.of (fun _ _ => (1 : ℝ))

def Aε (A : Matrix C C ℝ) (ε : ℝ) : Matrix C C ℝ := (Pm ε)ᵀ * A * Pm ε

theorem Aε_apply (A : Matrix C C ℝ) (ε : ℝ) (a b : C) :
    Aε A ε a b = ∑ d, (∑ c, ((1 : Matrix C C ℝ) a c + ε) * A c d) * ((1 : Matrix C C ℝ) d b + ε) := by
  simp [Aε, Pm, Matrix.mul_apply]

theorem Aε_cont (A : Matrix C C ℝ) (a b : C) : Continuous fun ε => Aε A ε a b := by
  simp only [Aε_apply]
  fun_prop

theorem Aε_zero (A : Matrix C C ℝ) : Aε A 0 = A := by
  simp [Aε, Pm]

theorem Aε_pos {A : Matrix C C ℝ} (hA : ∀ a b, 0 ≤ A a b) {a0 b0 : C} (h0 : 0 < A a0 b0)
    {ε : ℝ} (hε : 0 < ε) (a b : C) : 0 < Aε A ε a b := by
  rw [Aε_apply]
  have hone : ∀ c a : C, 0 ≤ (1 : Matrix C C ℝ) c a := fun c a => by
    rw [Matrix.one_apply]; split_ifs <;> norm_num
  have hin : ∀ d, 0 ≤ ∑ c, ((1 : Matrix C C ℝ) a c + ε) * A c d := fun d =>
    Finset.sum_nonneg fun c _ => mul_nonneg (by linarith [hone a c]) (hA c d)
  have hterm : 0 < (∑ c, ((1 : Matrix C C ℝ) a c + ε) * A c b0) * ((1 : Matrix C C ℝ) b0 b + ε) := by
    refine mul_pos ?_ (by linarith [hone b0 b])
    have : 0 < ((1 : Matrix C C ℝ) a a0 + ε) * A a0 b0 := mul_pos (by linarith [hone a a0]) h0
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun c => ((1 : Matrix C C ℝ) a c + ε) * A c b0)
      (fun c _ => mul_nonneg (by linarith [hone a c]) (hA c b0)) (Finset.mem_univ a0))
  exact lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun d =>
      (∑ c, ((1 : Matrix C C ℝ) a c + ε) * A c d) * ((1 : Matrix C C ℝ) d b + ε))
    (fun d _ => mul_nonneg (hin d) (by linarith [hone d b])) (Finset.mem_univ b0))

theorem Aε_sym {A : Matrix C C ℝ} (hs : ∀ a b, A a b = A b a) (ε : ℝ) (a b : C) :
    Aε A ε a b = Aε A ε b a := by
  have hT : Aᵀ = A := by ext a b; simp [hs b a]
  have : (Aε A ε)ᵀ = Aε A ε := by
    simp only [Aε, Matrix.transpose_mul, Matrix.transpose_transpose, hT, Matrix.mul_assoc]
  have := congrFun (congrFun this b) a
  simpa using this

theorem Mm_cont {m : ℕ} (Af : ℝ → Matrix C C ℝ) (tf : ℝ → Fin m → C → ℝ)
    (hA : ∀ c d, Continuous fun ε => Af ε c d) (ht : ∀ j c, Continuous fun ε => tf ε j c)
    (a b : C) : Continuous fun ε => Mm (Af ε) (tf ε) a b := by
  simp only [Mm, of_apply, Tm, wt]
  refine continuous_finsetSum _ fun r _ => ?_
  refine (continuous_finsetProd _ fun j _ => ht _ _).mul ?_
  refine (((hA a b).mul (continuous_finsetProd _ fun j _ => hA _ _)).mul
    (continuous_finsetProd _ fun j _ => hA _ _)).mul ?_
  exact continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => hA _ _

theorem sum_split (m : ℕ) (f : (Fin (m+2) → C) → ℝ) :
    ∑ c, f c = ∑ a, ∑ b, ∑ t : Fin m → C, f (Fin.cons a (Fin.cons b t)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+2) => C)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => C)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem expand (m : ℕ) (A : Matrix C C ℝ)
    (x y : C → ℝ) (tail : Fin m → C → ℝ) :
    selectionPolynomial A (selections x y tail) =
      ∑ a, ∑ b, x a * y b * ∑ t : Fin m → C, Tm A tail a b t := by
  unfold selectionPolynomial
  rw [sum_split]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Tm, wt, selections, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.prod_filter]
  have h1 : ∀ x : Fin m, (1 : Fin (m+2)) < x.succ.succ := fun x => by
    simp [Fin.lt_def]
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff, h1]
  ring

theorem selMatrix_eq (m : ℕ) (A : Matrix C C ℝ) (tail : Fin m → C → ℝ) :
    (Matrix.of fun c c' =>
      selectionPolynomial A (selections (Pi.single c 1) (Pi.single c' 1) tail)) = Mm A tail := by
  ext a b
  simp only [Matrix.of_apply, Mm]
  rw [expand]
  simp [Pi.single_apply]

end IsingVectorBalancing.Subgaussian.Dev.SL

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.SL Matrix in
theorem chk_selectionMatrix_isLorentzian {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ)
    (A : Matrix C C ℝ) (hA : IsLorentzian A)
    (tail : Fin m → C → ℝ) (htail : ∀ i c, 0 ≤ tail i c) :
    IsLorentzian (Matrix.of fun c c' =>
      selectionPolynomial A (selections (Pi.single c 1) (Pi.single c' 1) tail)) := by
  rw [selMatrix_eq]
  have hnn := hA.1
  have hs : ∀ a b, A a b = A b a := fun a b => by
    have := congrFun (congrFun hA.2.1.eq b) a
    simpa [Matrix.conjTranspose_apply] using this
  have hgA := good_of_lor hA
  refine lor_of_good (fun a b => Mm_sym hs tail a b) (fun a b => Mm_nonneg hnn tail htail a b) ?_
  by_cases h0 : ∀ a b, A a b = 0
  · rintro u w ⟨h1, _⟩
    have : Mm A tail = 0 := by
      ext a b; simp [Mm, Tm, h0]
    rw [this] at h1
    simp [qf] at h1
  · push Not at h0
    obtain ⟨a0, b0, hne⟩ := h0
    have hpos0 : 0 < A a0 b0 := lt_of_le_of_ne (hnn a0 b0) (Ne.symm hne)
    set F : ℝ → Matrix C C ℝ := fun ε => Mm (Aε A ε) (fun j c => tail j c + ε) with hF
    have hF0 : F 0 = Mm A tail := by simp [hF, Aε_zero]
    rw [← hF0]
    refine good_limit F (fun a b => Mm_cont _ _ (fun c d => Aε_cont A c d)
      (fun j c => continuous_const.add continuous_id) a b) fun ε hε => ?_
    exact good_Mm m (Aε A ε) (Aε_sym hs ε) (Aε_pos hnn hpos0 hε)
      (good_congr hgA (Pm ε)) _ (fun j c => by linarith [htail j c])

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_selectionMatrix_isLorentzian := @IsingVectorBalancing.Subgaussian.chk_selectionMatrix_isLorentzian
