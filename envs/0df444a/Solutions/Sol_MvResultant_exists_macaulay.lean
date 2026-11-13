-- Prove2me | solution 1 for MvResultant.exists_macaulay
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T19:13:11.498378+00:00
-- url     : https://prove2.me/submissions/e9f078cb-8559-4c9d-af3d-0b2c0d6895c8

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper MvPolynomial Finset

namespace MacAux

variable {n : ℕ}

/-- total degree of the Macaulay matrix -/
def Dt (D : Fin n → ℕ) : ℕ := ∑ j, (D j - 1) + 1

/-- monomials of degree `d` -/
abbrev Mon (n d : ℕ) := {β : Fin n →₀ ℕ // β.degree = d}

instance finite_mon (n d : ℕ) : Finite (Mon n d) := by
  refine Finite.of_injective
    (fun a : Mon n d => fun j : Fin n =>
      (⟨a.1 j, Nat.lt_succ_of_le (by have := Finsupp.le_degree j a.1; rw [a.2] at this; exact this)⟩ :
        Fin (d + 1))) ?_
  intro a b h
  apply Subtype.ext
  ext j
  have := congrFun h j
  simpa using congrArg Fin.val this

noncomputable instance fintype_mon (n d : ℕ) : Fintype (Mon n d) := Fintype.ofFinite _

lemma degree_eq_sum (β : Fin n →₀ ℕ) : β.degree = ∑ j, β j := Finsupp.degree_eq_sum β

variable (D : Fin n → ℕ) (i : Fin n)

/-- indices `j ≠ i` whose pure power divides `x^β` -/
def S (β : Fin n →₀ ℕ) : Finset (Fin n) := univ.filter (fun j => j ≠ i ∧ D j ≤ β j)

/-- the form assigned to the row `x^β` (indices `≠ i` first, `i` last) -/
def jOf (β : Fin n →₀ ℕ) : Fin n := if h : (S D i β).Nonempty then (S D i β).min' h else i

lemma jOf_le (β : Fin n →₀ ℕ) (hβ : β.degree = Dt D) : D (jOf D i β) ≤ β (jOf D i β) := by
  unfold jOf
  split_ifs with h
  · have := (S D i β).min'_mem h
    simp only [S, mem_filter, mem_univ, true_and] at this
    exact this.2
  · simp only [S, not_nonempty_iff_eq_empty, filter_eq_empty_iff, mem_univ, true_implies,
      not_and, not_le] at h
    rw [degree_eq_sum, Dt] at hβ
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)] at hβ
    have h1 : ∑ j ∈ univ.erase i, β j ≤ ∑ j ∈ univ.erase i, (D j - 1) :=
      sum_le_sum fun j hj => by have := h (ne_of_mem_erase hj); omega
    omega

lemma jOf_eq_i (β : Fin n →₀ ℕ) (h : jOf D i β = i) : ∀ j, j ≠ i → β j < D j := by
  intro j hj
  by_contra hc
  push Not at hc
  unfold jOf at h
  have hne : (S D i β).Nonempty := ⟨j, by simp [S, hj, hc]⟩
  rw [dif_pos hne] at h
  have := (S D i β).min'_mem hne
  rw [h] at this
  simp [S] at this

/-- the shift: `x^β / x_j^{D_j}` -/
noncomputable def sh (β : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  β - Finsupp.single (jOf D i β) (D (jOf D i β))

lemma single_le (β : Fin n →₀ ℕ) (hβ : β.degree = Dt D) :
    Finsupp.single (jOf D i β) (D (jOf D i β)) ≤ β := by
  intro k
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h]; exact jOf_le D i β hβ
  · exact Nat.zero_le _

lemma sh_add (β : Fin n →₀ ℕ) (hβ : β.degree = Dt D) :
    sh D i β + Finsupp.single (jOf D i β) (D (jOf D i β)) = β :=
  tsub_add_cancel_of_le (single_le D i β hβ)

lemma degree_sub_sh (β γ : Fin n →₀ ℕ) (hβ : β.degree = Dt D)
    (hγ : γ.degree = Dt D) (h : sh D i β ≤ γ) :
    (γ - sh D i β).degree = D (jOf D i β) := by
  have h1 := congrArg Finsupp.degree (sh_add D i β hβ)
  have h2 := congrArg Finsupp.degree (tsub_add_cancel_of_le h)
  rw [map_add, Finsupp.degree_single, hβ] at h1
  rw [map_add, hγ] at h2
  omega

/-- the Macaulay matrix -/
noncomputable def mac : Matrix (Mon n (Dt D)) (Mon n (Dt D)) (MvPolynomial (ResVar n D) ℂ) :=
  Matrix.of fun β γ =>
    if h : sh D i β.1 ≤ γ.1 then
      X ⟨jOf D i β.1, ⟨γ.1 - sh D i β.1, degree_sub_sh D i β.1 γ.1 β.2 γ.2 h⟩⟩
    else 0

lemma sub_sh_eq_iff (β γ : Mon n (Dt D)) (h : sh D i β.1 ≤ γ.1) :
    γ.1 - sh D i β.1 = Finsupp.single (jOf D i β.1) (D (jOf D i β.1)) ↔ γ = β := by
  constructor
  · intro h'
    apply Subtype.ext
    rw [← sh_add D i β.1 β.2, ← h', add_tsub_cancel_of_le h]
  · intro h'
    rw [h']
    exact tsub_eq_of_eq_add_rev (sh_add D i β.1 β.2).symm

/-- the diagonal line `t ↦ (x_1^{D_1}, …, t x_i^{D_i}, …, x_n^{D_n})` -/
noncomputable def line (v : ResVar n D) : Polynomial ℂ :=
  if v.2.1 = Finsupp.single v.1 (D v.1) then
    (if v.1 = i then (Polynomial.X : Polynomial ℂ) else 1) else 0

lemma mac_line :
    aeval (line D i) (mac D i).det =
      Polynomial.X ^ (univ.filter (fun β : Mon n (Dt D) => jOf D i β.1 = i)).card := by
  classical
  rw [AlgHom.map_det]
  have hdiag : (aeval (line D i)).mapMatrix (mac D i) =
      Matrix.diagonal (fun β : Mon n (Dt D) =>
        if jOf D i β.1 = i then (Polynomial.X : Polynomial ℂ) else 1) := by
    refine Matrix.ext fun β γ => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, mac, Matrix.of_apply,
      Matrix.diagonal_apply]
    by_cases hβγ : β = γ
    · cases hβγ
      have hle : sh D i β.1 ≤ β.1 := tsub_le_self
      rw [dif_pos hle, aeval_X, if_pos rfl, line]
      simp only
      rw [if_pos ((sub_sh_eq_iff D i β β hle).mpr rfl)]
    · rw [if_neg hβγ]
      split_ifs with hle
      · rw [aeval_X, line]
        simp only
        rw [if_neg (fun h => hβγ ((sub_sh_eq_iff D i β γ hle).mp h).symm)]
      · exact map_zero (aeval (R := ℂ) (line D i))
  rw [hdiag, Matrix.det_diagonal, prod_ite, prod_const, prod_const_one, mul_one]

lemma card_le (hD : ∀ j, 1 ≤ D j) :
    (univ.filter (fun β : Mon n (Dt D) => jOf D i β.1 = i)).card ≤
      ∏ j ∈ univ.erase i, D j := by
  classical
  have hcard : ∏ j ∈ univ.erase i, D j =
      (univ : Finset ((j : {j : Fin n // j ≠ i}) → Fin (D j))).card := by
    rw [card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact prod_subtype (univ.erase i) (p := fun j => j ≠ i) (by simp) D
  rw [hcard]
  refine card_le_card_of_injOn
    (fun β : Mon n (Dt D) => if h : jOf D i β.1 = i then
      (fun j : {j : Fin n // j ≠ i} => (⟨β.1 j, jOf_eq_i D i β.1 h j j.2⟩ : Fin (D j)))
      else fun j => ⟨0, by have := hD j; omega⟩) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  intro β hβ β' hβ' heq
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hβ hβ'
  simp only [dif_pos hβ, dif_pos hβ'] at heq
  have hj : ∀ j, j ≠ i → β.1 j = β'.1 j := fun j hj => by
    have := congrFun heq ⟨j, hj⟩
    simpa using congrArg Fin.val this
  have hsum := β.2.trans β'.2.symm
  have s1 : β.1.degree = β.1 i + ∑ j ∈ univ.erase i, β.1 j := by
    rw [degree_eq_sum, add_sum_erase _ _ (mem_univ i)]
  have s2 : β'.1.degree = β'.1 i + ∑ j ∈ univ.erase i, β'.1 j := by
    rw [degree_eq_sum, add_sum_erase _ _ (mem_univ i)]
  have h2 : ∑ j ∈ univ.erase i, β.1 j = ∑ j ∈ univ.erase i, β'.1 j :=
    sum_congr rfl fun j hj' => hj j (ne_of_mem_erase hj')
  apply Subtype.ext
  ext j
  by_cases hji : j = i
  · rw [hji]; omega
  · exact hj j hji

/-- the polynomial `x^s F_j` written over the degree-`Dt` monomials -/
lemma monomial_mul_eq_sum (β : Mon n (Dt D)) (F : MvPolynomial (Fin n) ℂ)
    (hF : F.IsHomogeneous (D (jOf D i β.1))) :
    monomial (sh D i β.1) (1 : ℂ) * F =
      ∑ γ : Mon n (Dt D), monomial γ.1
        (if sh D i β.1 ≤ γ.1 then coeff (γ.1 - sh D i β.1) F else 0) := by
  classical
  ext d
  rw [coeff_monomial_mul', coeff_sum]
  simp only [coeff_monomial, one_mul]
  by_cases hd : d.degree = Dt D
  · rw [sum_eq_single (⟨d, hd⟩ : Mon n (Dt D))]
    · simp
    · intro γ _ hγ
      rw [if_neg]
      intro h; exact hγ (Subtype.ext h)
    · simp
  · rw [sum_eq_zero]
    · split_ifs with hle
      · by_contra hc
        apply hd
        have hdeg := hF hc
        have hw1 : ∀ e : Fin n →₀ ℕ, Finsupp.weight (1 : Fin n → ℕ) e = e.degree :=
          fun e => by rw [Finsupp.degree_eq_weight_one]; rfl
        rw [hw1] at hdeg
        have h1 := congrArg Finsupp.degree (sh_add D i β.1 β.2)
        have h2 := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single, β.2] at h1
        rw [map_add] at h2
        omega
      · rfl
    · intro γ _
      rw [if_neg]
      intro h; exact hd (h ▸ γ.2)

lemma mac_vanish (F : Fin n → MvPolynomial (Fin n) ℂ) (hF : ∀ j, (F j).IsHomogeneous (D j))
    (x : Fin n → ℂ) (hx0 : x ≠ 0) (hx : ∀ j, eval x (F j) = 0) :
    aeval (fun v : ResVar n D => coeff v.2.1 (F v.1)) (mac D i).det = 0 := by
  classical
  rw [AlgHom.map_det]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun γ : Mon n (Dt D) => eval x (monomial γ.1 (1 : ℂ)), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hx0
    intro h0
    have := congrFun h0 ⟨Finsupp.single k (Dt D), Finsupp.degree_single _ _⟩
    simp only [eval_monomial, Finsupp.prod_single_index, pow_zero, one_mul, Pi.zero_apply] at this
    exact hk (pow_eq_zero_iff (by unfold Dt; omega) |>.mp this)
  · funext β
    simp only [Matrix.mulVec, dotProduct, AlgHom.mapMatrix_apply, Matrix.map_apply, mac,
      Matrix.of_apply, Pi.zero_apply]
    have hrow : ∀ γ : Mon n (Dt D),
        aeval (fun v : ResVar n D => coeff v.2.1 (F v.1))
          (if h : sh D i β.1 ≤ γ.1 then
            (X ⟨jOf D i β.1, ⟨γ.1 - sh D i β.1, degree_sub_sh D i β.1 γ.1 β.2 γ.2 h⟩⟩ :
              MvPolynomial (ResVar n D) ℂ) else 0) * eval x (monomial γ.1 (1 : ℂ)) =
        eval x (monomial γ.1
          (if sh D i β.1 ≤ γ.1 then coeff (γ.1 - sh D i β.1) (F (jOf D i β.1)) else 0)) := by
      intro γ
      split_ifs with h
      · rw [aeval_X, eval_monomial, eval_monomial, one_mul]
      · rw [map_zero, zero_mul, monomial_zero, map_zero]
    rw [sum_congr rfl fun γ _ => hrow γ, ← map_sum,
      ← monomial_mul_eq_sum D i β (F (jOf D i β.1)) (hF _), map_mul, hx, mul_zero]

end MacAux

open MacAux in
theorem solution {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j) (i : Fin n) :
    ∃ Q : MvPolynomial (ResVar n D) ℂ,
      (∀ F : Fin n → MvPolynomial (Fin n) ℂ, (∀ j, (F j).IsHomogeneous (D j)) →
        (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ j, MvPolynomial.eval x (F j) = 0) →
        MvPolynomial.aeval (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (F v.1)) Q = 0) ∧
      ∃ M ≤ ∏ j ∈ Finset.univ.erase i, D j,
        MvPolynomial.aeval (fun v : ResVar n D =>
          if v.2.1 = Finsupp.single v.1 (D v.1) then
            (if v.1 = i then (Polynomial.X : Polynomial ℂ) else 1) else 0) Q =
          Polynomial.X ^ M := by
  classical
  refine ⟨(mac D i).det, fun F hF ⟨x, hx0, hx⟩ => mac_vanish D i F hF x hx0 hx,
    _, card_le D i hD, ?_⟩
  exact mac_line D i
