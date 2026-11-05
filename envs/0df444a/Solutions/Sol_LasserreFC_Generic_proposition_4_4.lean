-- Prove2me | solution 1 for LasserreFC.Generic.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:55:25.55548+00:00
-- url     : https://prove2.me/submissions/d22c6636-c35b-4b5e-80cd-859c50ea7192

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Cond43

namespace LasserreFC.Generic.P44Red

open MvPolynomial LasserreFC.Generic

variable {n : ℕ}

/-- dehomogenisation `x₀ ↦ 1`, `x_{k+1} ↦ x_k` -/
noncomputable def dehom : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.cons (1 : MvPolynomial (Fin n) ℂ) X)

lemma eval_cons (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (Fin.cons 1 x) q = eval x (dehom q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [dehom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval_X, hp]
    congr 1
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [dehom]
    · simp [dehom]

lemma dehom_pderiv (k : Fin n) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    dehom (pderiv k.succ q) = pderiv k (dehom q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [dehom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
      map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    congr 2
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [dehom, pderiv_X, Fin.succ_ne_zero]
    · simp only [dehom, aeval_X, Fin.cons_succ, pderiv_X, Pi.single_apply, Fin.succ_inj]
      split_ifs <;> simp

lemma dehom_homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    dehom (homog D p) = map Complex.ofRealHom p := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  unfold homog
  rw [map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [dehom]

lemma eval_homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) :
    eval (Fin.cons 1 x) (homog D p) = aeval x p := by
  rw [eval_cons, dehom_homog, eval_map, aeval_def]
  rfl

lemma eval_pderiv_homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) (k : Fin n) :
    eval (Fin.cons 1 x) (pderiv k.succ (homog D p)) = aeval x (pderiv k p) := by
  rw [eval_cons, dehom_pderiv, dehom_homog, pderiv_map, eval_map, aeval_def]
  rfl

lemma eval_pderiv2_homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) (k s : Fin n) :
    eval (Fin.cons 1 x) (pderiv k.succ (pderiv s.succ (homog D p))) =
      aeval x (pderiv k (pderiv s p)) := by
  rw [eval_cons, dehom_pderiv, dehom_pderiv, dehom_homog, pderiv_map, pderiv_map, eval_map,
    aeval_def]
  rfl

lemma homog_isHomogeneous (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) :
    (homog D p).IsHomogeneous D := by
  unfold homog
  apply IsHomogeneous.sum
  intro α hα
  have hdeg : Finsupp.degree α ≤ D := by
    have := le_totalDegree hα
    rw [Finsupp.degree_eq_sum]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    omega
  have h1 : (C (Complex.ofReal (p.coeff α)) * X 0 ^ (D - Finsupp.degree α) :
      MvPolynomial (Fin (n + 1)) ℂ).IsHomogeneous (0 + (D - Finsupp.degree α)) :=
    (isHomogeneous_C _ _).mul (isHomogeneous_X_pow _ _)
  have h2 : (∏ k : Fin n, X k.succ ^ α k : MvPolynomial (Fin (n + 1)) ℂ).IsHomogeneous
      (∑ k, α k) := IsHomogeneous.prod _ _ _ (fun k _ => isHomogeneous_X_pow _ _)
  have := h1.mul h2
  convert this using 1
  rw [Finsupp.degree_eq_sum] at hdeg ⊢
  omega

/-- Euler's identity at `x̃ = (1, x)` for a zero of `p`. -/
lemma eval_pderiv0_homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D)
    (x : Fin n → ℂ) (hx : aeval x p = 0) :
    eval (Fin.cons 1 x) (pderiv 0 (homog D p)) = -∑ k, x k * aeval x (pderiv k p) := by
  have h := congrArg (eval (Fin.cons 1 x)) (homog_isHomogeneous D p hp).sum_X_mul_pderiv
  rw [map_sum, Fin.sum_univ_succ] at h
  simp only [map_mul, eval_X, Fin.cons_zero, Fin.cons_succ, one_mul, map_nsmul,
    eval_homog, hx, smul_zero, eval_pderiv_homog] at h
  linear_combination h

end LasserreFC.Generic.P44Red

namespace LasserreFC.Generic.P44Red

open MvPolynomial Matrix LasserreFC.Generic

lemma rank_lt_of_ker {K m k : Type*} [Field K] [Fintype m] [Fintype k] [DecidableEq k]
    (M : Matrix m k K) (a : k → K) (ha : a ≠ 0) (hM : M *ᵥ a = 0) :
    M.rank < Fintype.card k := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : 0 < Module.finrank K (LinearMap.ker M.mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨a, by simpa using hM⟩, by simpa using ha⟩
  unfold Matrix.rank
  omega

lemma exists_ker_of_rank_lt {K m k : Type*} [Field K] [Fintype m] [Fintype k] [DecidableEq k]
    (M : Matrix m k K) (h : M.rank < Fintype.card k) : ∃ a : k → K, a ≠ 0 ∧ M *ᵥ a = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  unfold Matrix.rank at h
  have h2 : 0 < Module.finrank K (LinearMap.ker M.mulVecLin) := by omega
  obtain ⟨⟨a, ha⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
  exact ⟨a, by simpa using hne, by simpa using ha⟩

variable {n m1 m2 : ℕ}

/-- the point `x̃ = (1, u)` -/
noncomputable def xt (u : Fin n → ℝ) : Fin (n + 1) → ℂ := Fin.cons 1 (fun k => (u k : ℂ))

lemma xt_ne (u : Fin n → ℝ) : xt u ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [xt] at this

lemma aeval_ofReal (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    aeval (fun k => (u k : ℂ)) p = ((eval u p : ℝ) : ℂ) := by
  rw [show (fun k => (u k : ℂ)) = (algebraMap ℝ ℂ) ∘ u from rfl, aeval_algebraMap_apply]
  rfl

lemma homog_xt (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) :
    eval (xt u) (homog D p) = ((eval u p : ℝ) : ℂ) := by
  rw [xt, eval_homog, aeval_ofReal]

lemma hgradx_xt (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) (k : Fin n) :
    hgradx D p (xt u) k = ((grad p u k : ℝ) : ℂ) := by
  rw [hgradx, xt, eval_pderiv_homog, aeval_ofReal]
  rfl

lemma hhessx_xt (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) (k s : Fin n) :
    hhessx D p (xt u) k s = ((hess p u k s : ℝ) : ℂ) := by
  rw [hhessx, xt, eval_pderiv2_homog, aeval_ofReal]
  rfl

lemma hgrad_xt (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) (u : Fin n → ℝ)
    (hu : eval u p = 0) :
    hgrad D p (xt u) = Fin.cons (-((∑ k, u k * grad p u k : ℝ) : ℂ))
      (fun k => ((grad p u k : ℝ) : ℂ)) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [hgrad, xt, eval_pderiv0_homog D p hp _ (by rw [aeval_ofReal, hu]; simp)]
    simp only [Fin.cons_zero, aeval_ofReal]
    push_cast
    rfl
  · rw [Fin.cons_succ, ← hgradx_xt D p u k]
    rfl

end LasserreFC.Generic.P44Red

namespace LasserreFC.Generic.P44Red

open MvPolynomial Matrix LasserreFC.Generic

variable {n m1 m2 : ℕ}

lemma sys45_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (D0 : ℕ)
    (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ) (p : ι → MvPolynomial (Fin n) ℝ) (Dq : ℕ)
    (q : MvPolynomial (Fin n) ℝ) :
    Sys45 D0 p0 (fun i => D (e i)) (fun i => p (e i)) Dq q ↔ Sys45 D0 p0 D p Dq q := by
  unfold Sys45
  have hmat : ∀ xt, gradMat45 D0 p0 (fun i => D (e i)) (fun i => p (e i)) xt =
      (gradMat45 D0 p0 D p xt).submatrix (Equiv.refl _) (e.optionCongr) := by
    intro xt; ext k c; cases c <;> rfl
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
  simp only [hmat, Matrix.rank_submatrix, hcard]
  constructor
  · rintro ⟨xt, h0, hr, hp, hq⟩
    exact ⟨xt, h0, hr, fun i => by simpa using hp (e.symm i), hq⟩
  · rintro ⟨xt, h0, hr, hp, hq⟩
    exact ⟨xt, h0, hr, fun i => hp (e i), hq⟩

lemma sys410_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (D0 : ℕ)
    (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ) (p : ι → MvPolynomial (Fin n) ℝ) :
    Sys410 D0 p0 (fun i => D (e i)) (fun i => p (e i)) ↔ Sys410 D0 p0 D p := by
  unfold Sys410
  have hmat : ∀ xt y, Ptilde D0 p0 (fun i => D (e i)) (fun i => p (e i)) xt y =
      (Ptilde D0 p0 D p xt y).submatrix (Equiv.refl _) (Equiv.sumCongr e.optionCongr e) := by
    intro xt y
    ext k c
    rcases k with k | k <;> rcases c with (_ | c) | c <;> rfl
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
  simp only [hmat, Matrix.rank_submatrix, hcard]
  constructor
  · rintro ⟨xt, h0, y, hy, hr, hp, hq⟩
    exact ⟨xt, h0, y, hy, hr, fun i => by simpa using hp (e.symm i),
      fun i => by simpa using hq (e.symm i)⟩
  · rintro ⟨xt, h0, y, hy, hr, hp, hq⟩
    exact ⟨xt, h0, y, hy, hr, fun i => hp (e i), fun i => hq (e i)⟩

/-- the active set as a `Finset` -/
noncomputable def actF (P : POP n m1 m2) (u : Fin n → ℝ) : Finset (Fin m2) :=
  Finset.univ.filter fun j => eval u (P.g j) = 0

lemma zero_on (P : POP n m1 m2) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (u : Fin n → ℝ)
    (hu : u ∈ P.K) (J : Finset (Fin m2)) (hJ : J ⊆ actF P u) (e : Fin m1 ⊕ J) :
    eval (xt u) (homog (consDeg d d' J e) (consPoly P J e)) = 0 := by
  rw [homog_xt]
  rcases e with i | ⟨j, hj⟩
  · simp [consPoly, hu.1 i]
  · have := (Finset.mem_filter.mp (hJ hj)).2
    simp [consPoly, this]

lemma deg_cons {P : POP n m1 m2} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (hadm : P.Admissible d0 d d') (J : Finset (Fin m2)) (e : Fin m1 ⊕ J) :
    (consPoly P J e).totalDegree ≤ consDeg d d' J e := by
  rcases e with i | j
  · exact hadm.2.1 i
  · exact hadm.2.2 j

lemma part_i (P : POP n m1 m2) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (u : Fin n → ℝ)
    (hu : u ∈ P.K) (ha : Cond43a P d d') : (actF P u).card ≤ n - m1 := by
  by_contra hc
  obtain ⟨J, hJA, hJc⟩ := Finset.exists_subset_card_eq (show n - m1 + 1 ≤ (actF P u).card by omega)
  exact ha J hJc ⟨xt u, xt_ne u, zero_on P d d' u hu J hJA⟩

/-- reindexing between the active-set subtype and the `Finset` coercion -/
def eS (P : POP n m1 m2) (u : Fin n → ℝ) :
    (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) ≃ (Fin m1 ⊕ actF P u) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun j => by simp [actF]))

lemma consPoly_eS (P : POP n m1 m2) (u : Fin n → ℝ) (e : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) :
    consPoly P (actF P u) (eS P u e) = Sum.elim P.h (fun j => P.g j.1) e := by
  rcases e with i | j <;> rfl

lemma consDeg_eS (P : POP n m1 m2) (u : Fin n → ℝ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ)
    (e : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) :
    consDeg d d' (actF P u) (eS P u e) = Sum.elim d (fun j => d' j.1) e := by
  rcases e with i | j <;> rfl

lemma part_ii {P : POP n m1 m2} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (hadm : P.Admissible d0 d d') (u : Fin n → ℝ)
    (hu : u ∈ P.K) (ha : Cond43a P d d') (hb : Cond43b P d d') : CQC P u := by
  classical
  set A := actF P u with hAdef
  have hA := part_i P d d' u hu ha
  have hF : (Sum.elim (fun i : Fin m1 => grad (P.h i) u)
      (fun j : {j : Fin m2 // eval u (P.g j) = 0} => grad (P.g j.1) u)) =
      (fun e => grad (consPoly P A e) u) ∘ eS P u := by
    funext e; rcases e with i | j <;> rfl
  by_contra hcq
  unfold CQC at hcq
  rw [hF, linearIndependent_equiv] at hcq
  obtain ⟨c, hsum, e0, hc0⟩ := Fintype.not_linearIndependent_iff.mp hcq
  have hk : ∀ k, ∑ e, c e * grad (consPoly P A e) u k = 0 := by
    intro k
    have := congrFun hsum k
    simpa [Finset.sum_apply] using this
  let M : Matrix (Fin (n + 1)) (Fin m1 ⊕ A) ℂ := Matrix.of fun k e =>
    hgrad (consDeg d d' A e) (consPoly P A e) (xt u) k
  have hM : M *ᵥ (fun e => (c e : ℂ)) = 0 := by
    have hcol : ∀ e, hgrad (consDeg d d' A e) (consPoly P A e) (xt u) =
        Fin.cons (-((∑ k, u k * grad (consPoly P A e) u k : ℝ) : ℂ))
          (fun k => ((grad (consPoly P A e) u k : ℝ) : ℂ)) := by
      intro e
      apply hgrad_xt _ _ (deg_cons hadm A e)
      have := zero_on P d d' u hu A le_rfl e
      rw [homog_xt] at this
      exact_mod_cast this
    funext i
    simp only [mulVec, dotProduct, M, of_apply, hcol, Pi.zero_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero]
      have : ∑ e, (-((∑ k, u k * grad (consPoly P A e) u k : ℝ) : ℂ)) * (c e : ℂ) =
          ((-∑ k, u k * ∑ e, c e * grad (consPoly P A e) u k : ℝ) : ℂ) := by
        push_cast
        simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun k _ => ?_))
        ring
      rw [this]
      simp [hk]
    · simp only [Fin.cons_succ]
      have : ∑ e, ((grad (consPoly P A e) u k : ℝ) : ℂ) * (c e : ℂ) =
          ((∑ e, c e * grad (consPoly P A e) u k : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl (fun e _ => ?_)
        ring
      rw [this, hk]
      simp
  have hc' : (fun e => (c e : ℂ)) ≠ 0 := by
    intro h
    apply hc0
    have := congrFun h e0
    simpa using this
  have hr := rank_lt_of_ker M _ hc' hM
  apply hb A hA
  refine ⟨xt u, xt_ne u, zero_on P d d' u hu A le_rfl, ?_⟩
  simpa using hr

lemma mu_inactive {P : POP n m1 m2} {u : Fin n → ℝ} {mu : Fin m2 → ℝ}
    (h14 : ∀ j, mu j * eval u (P.g j) = 0) (j : Fin m2) (hj : eval u (P.g j) ≠ 0) : mu j = 0 := by
  rcases mul_eq_zero.mp (h14 j) with h | h
  · exact h
  · exact absurd h hj

lemma grad_f_eq {P : POP n m1 m2} {u : Fin n → ℝ} {lam : Fin m1 → ℝ} {mu : Fin m2 → ℝ}
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0) (k : Fin n) :
    grad P.f u k = ∑ e : Fin m1 ⊕ actF P u, Sum.elim lam (fun j => mu j.1) e *
      grad (consPoly P (actF P u) e) u k := by
  have h := congrFun h13 k
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h, Fintype.sum_sum_type]
  congr 1
  change _ = ∑ j : actF P u, mu j.1 * grad (P.g j.1) u k
  rw [Finset.sum_coe_sort (actF P u) (fun j => mu j * grad (P.g j) u k)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have : eval u (P.g j) ≠ 0 := by simpa [actF] using hj
  simp [mu_inactive h14 j this]

lemma part_iii {P : POP n m1 m2} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (hadm : P.Admissible d0 d d') (u : Fin n → ℝ) (hu : u ∈ P.K)
    (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0)
    (ha : Cond43a P d d') (hc : Cond43c P d0 d d') :
    (∀ i, lam i ≠ 0) ∧ ∀ j, eval u (P.g j) = 0 → mu j ≠ 0 := by
  classical
  set A := actF P u with hAdef
  have hA := part_i P d d' u hu ha
  let mult : Fin m1 ⊕ A → ℝ := Sum.elim lam (fun j => mu j.1)
  have hkey : ∀ c, mult c ≠ 0 := by
    intro c hc0
    apply hc A hA c
    let a : Option {e : Fin m1 ⊕ A // e ≠ c} → ℂ :=
      fun o => Option.elim o 1 (fun e => -((mult e.1 : ℝ) : ℂ))
    have ha0 : a ≠ 0 := by
      intro h; have := congrFun h none; simp [a] at this
    have hM : gradMat45 d0 P.f (fun e : {e : Fin m1 ⊕ A // e ≠ c} => consDeg d d' A e.1)
        (fun e => consPoly P A e.1) (xt u) *ᵥ a = 0 := by
      funext k
      simp only [mulVec, dotProduct, Fintype.sum_option, gradMat45, of_apply, Option.elim,
        a, hgradx_xt, Pi.zero_apply, mul_one]
      have hf := grad_f_eq h13 h14 k
      rw [Fintype.sum_eq_add_sum_subtype_ne _ c] at hf
      simp only [mult] at hc0
      rw [show Sum.elim lam (fun j => mu j.1) c = 0 from hc0, zero_mul, zero_add] at hf
      rw [hf]
      push_cast
      simp only [mul_neg, Finset.sum_neg_distrib, mult]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    refine ⟨xt u, xt_ne u, ?_, fun e => zero_on P d d' u hu A le_rfl e.1,
      zero_on P d d' u hu A le_rfl c⟩
    have := rank_lt_of_ker _ a ha0 hM
    rw [Fintype.card_option] at this
    omega
  refine ⟨fun i => hkey (Sum.inl i), fun j hj => hkey (Sum.inr ⟨j, by simp [hAdef, actF, hj]⟩)⟩

/-- `(1.3)` re-indexed over the active constraints `Fin m₁ ⊕ J(u)` (as a subtype). -/
lemma grad_f_eq' {P : POP n m1 m2} {u : Fin n → ℝ} {lam : Fin m1 → ℝ} {mu : Fin m2 → ℝ}
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0) (k : Fin n) :
    grad P.f u k = ∑ e : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0},
      Sum.elim lam (fun j => mu j.1) e * grad (Sum.elim P.h (fun j => P.g j.1) e) u k := by
  rw [grad_f_eq h13 h14 k, ← (eS P u).sum_comp]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rcases e with i | j <;> rfl

lemma hess_lagr_eq (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (k s : Fin n) :
    hess (lagr P u lam mu) u k s = hess P.f u k s -
      ∑ e : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0},
        Sum.elim lam (fun j => mu j.1) e * hess (Sum.elim P.h (fun j => P.g j.1) e) u k s := by
  classical
  simp only [hess, lagr, map_sub, map_sum, pderiv_C_mul, map_mul, eval_C]
  rw [Fintype.sum_sum_type, sub_add_eq_sub_sub]
  congr 1
  simp only [Sum.elim_inr]
  exact Finset.sum_subtype _ (fun j => by simp) (fun j => mu j * eval u (pderiv k (pderiv s (P.g j))))

lemma part_iv (hm1 : m1 ≤ n) {P : POP n m1 m2} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (u : Fin n → ℝ) (hu : u ∈ P.K)
    (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0)
    (ha : Cond43a P d d') (hd : Cond43d P d0 d d') : (Hmat P u lam mu).det ≠ 0 := by
  classical
  set A := actF P u with hAdef
  have hA := part_i P d d' u hu ha
  let q : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → MvPolynomial (Fin n) ℝ :=
    Sum.elim P.h (fun j => P.g j.1)
  let dq : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℕ := Sum.elim d (fun j => d' j.1)
  let mult : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℝ := Sum.elim lam (fun j => mu j.1)
  have hd' : ¬ Sys410 d0 P.f dq q := by
    intro h
    apply hd A hA
    rw [← sys410_equiv (eS P u)]
    have e1 : (fun e => consDeg d d' A (eS P u e)) = dq := funext (consDeg_eS P u d d')
    have e2 : (fun e => consPoly P A (eS P u e)) = q := funext (consPoly_eS P u)
    rw [e1, e2]
    exact h
  have hq0 : ∀ e, eval (xt u) (homog (dq e) (q e)) = 0 := by
    intro e
    rw [homog_xt]
    rcases e with i | ⟨j, hj⟩
    · simp [q, hu.1 i]
    · simp [q, hj]
  have hG : ∀ e k, Gmat P u e k = grad (q e) u k := by
    intro e k; rcases e with i | j <;> rfl
  have hcardι : Fintype.card (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) ≤ n := by
    rw [Fintype.card_congr (eS P u)]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]
    omega
  intro hdet
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set v : Fin n → ℝ := z ∘ Sum.inl with hvdef
  set w := z ∘ Sum.inr with hwdef
  have hH : Hmat P u lam mu *ᵥ z =
      Sum.elim (hess (lagr P u lam mu) u *ᵥ v + (Gmat P u)ᵀ *ᵥ w) (Gmat P u *ᵥ v) := by
    simp only [Hmat, fromBlocks_mulVec, zero_mulVec, add_zero, v, w]
  rw [hH] at hz
  have hz1 : hess (lagr P u lam mu) u *ᵥ v + (Gmat P u)ᵀ *ᵥ w = 0 := by
    funext k; exact congrFun hz (Sum.inl k)
  have hz2 : Gmat P u *ᵥ v = 0 := by
    funext e; exact congrFun hz (Sum.inr e)
  -- common bookkeeping for the witness of (4.10)
  have hgy : ∀ (y0 : Fin n → ℝ), Gmat P u *ᵥ y0 = 0 → ∀ e,
      hgradx (dq e) (q e) (xt u) ⬝ᵥ (fun k => (y0 k : ℂ)) = 0 := by
    intro y0 hy0 e
    have := congrFun hy0 e
    simp only [mulVec, dotProduct, hG, Pi.zero_apply] at this
    simp only [dotProduct, hgradx_xt]
    exact_mod_cast this
  apply hd'
  by_cases hv : v = 0
  · -- `G(u)` has dependent rows: use the last `k` columns of `P̃`
    have hw0 : w ≠ 0 := by
      intro hw; apply hz0; funext e; rcases e with k | e
      · exact congrFun hv k
      · exact congrFun hw e
    have hGw : (Gmat P u)ᵀ *ᵥ w = 0 := by
      rw [hv, mulVec_zero, zero_add] at hz1; exact hz1
    have hr1 := rank_lt_of_ker _ w hw0 hGw
    rw [rank_transpose] at hr1
    obtain ⟨y0, hy0, hGy0⟩ := exists_ker_of_rank_lt (Gmat P u)
      (by rw [Fintype.card_fin]; omega)
    refine ⟨xt u, xt_ne u, fun k => (y0 k : ℂ), ?_, ?_, hq0, hgy y0 hGy0⟩
    · intro h; apply hy0; funext k; have := congrFun h k; simpa using this
    · let a : Option (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) ⊕
          (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) → ℂ := Sum.elim 0 (fun e => (w e : ℂ))
      have ha0 : a ≠ 0 := by
        intro h; apply hw0; funext e; have := congrFun h (Sum.inr e); simpa [a] using this
      have hM : Ptilde d0 P.f dq q (xt u) (fun k => (y0 k : ℂ)) *ᵥ a = 0 := by
        rw [Ptilde, fromBlocks_mulVec]
        funext r
        rcases r with k | k
        · simp [a]
        · have := congrFun hGw k
          simp only [mulVec, dotProduct, transpose_apply, hG, Pi.zero_apply] at this
          simp only [Sum.elim_inr, Pi.add_apply, a]
          simp only [mulVec, dotProduct, of_apply, hgradx_xt, Function.comp_apply, Sum.elim_inl,
            Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
          exact_mod_cast this
      have := rank_lt_of_ker _ a ha0 hM
      simp only [Fintype.card_sum, Fintype.card_option] at this ⊢
      omega
  · refine ⟨xt u, xt_ne u, fun k => (v k : ℂ), ?_, ?_, hq0, hgy v hz2⟩
    · intro h; apply hv; funext k; have := congrFun h k; simpa using this
    · let a : Option (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) ⊕
          (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) → ℂ :=
        Sum.elim (fun o => Option.elim o 1 (fun e => -((mult e : ℝ) : ℂ))) (fun e => (w e : ℂ))
      have ha0 : a ≠ 0 := by
        intro h; have := congrFun h (Sum.inl none); simp [a] at this
      have hM : Ptilde d0 P.f dq q (xt u) (fun k => (v k : ℂ)) *ᵥ a = 0 := by
        rw [Ptilde, fromBlocks_mulVec]
        funext r
        rcases r with k | k
        · have hf := grad_f_eq' h13 h14 k
          simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply, zero_mulVec, add_zero]
          simp only [mulVec, dotProduct, Fintype.sum_option, gradMat45, of_apply, Option.elim,
            Function.comp_apply, a, Sum.elim_inl, hgradx_xt, mul_one, mul_neg,
            Finset.sum_neg_distrib]
          rw [hf]
          push_cast
          rw [← sub_eq_add_neg, sub_eq_zero]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [mult, q]
          ring
        · have h1 := congrFun hz1 k
          simp only [Pi.add_apply, Pi.zero_apply, mulVec, dotProduct, transpose_apply, hG,
            hess_lagr_eq] at h1
          simp only [Sum.elim_inr, Pi.add_apply, Pi.zero_apply]
          simp only [mulVec, dotProduct, Fintype.sum_option, of_apply, Option.elim,
            Function.comp_apply, a, Sum.elim_inl, Sum.elim_inr, hhessx_xt, hgradx_xt, mul_one,
            mul_neg, Finset.sum_neg_distrib]
          have h2 : ((∑ s, (hess P.f u k s - ∑ e, mult e * hess (q e) u k s) * v s +
              ∑ e, grad (q e) u k * w e : ℝ) : ℂ) = 0 := by
            exact_mod_cast h1
          rw [← h2]
          push_cast
          have e : ∑ x, (∑ x_1, (hess (q x) u k x_1 : ℂ) * (v x_1 : ℂ)) * (mult x : ℂ) =
              ∑ s, (∑ e, (mult e : ℂ) * (hess (q e) u k s : ℂ)) * (v s : ℂ) := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
          rw [e]
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring
      have := rank_lt_of_ker _ a ha0 hM
      simp only [Fintype.card_sum, Fintype.card_option] at this ⊢
      omega

end LasserreFC.Generic.P44Red

open MvPolynomial LasserreFC.Generic LasserreFC.Generic.P44Red in
theorem solution {n m1 m2 : ℕ} (hm1 : m1 ≤ n) (P : POP n m1 m2) (d0 : ℕ)
    (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (hadm : P.Admissible d0 d d')
    (u : Fin n → ℝ) (hu : u ∈ P.K) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (h13 : grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u)
    (h14 : ∀ j, mu j * eval u (P.g j) = 0) :
    (Cond43a P d d' →
        (Finset.univ.filter fun j => eval u (P.g j) = 0).card ≤ n - m1) ∧
      (Cond43a P d d' → Cond43b P d d' → CQC P u) ∧
      (Cond43a P d d' → Cond43c P d0 d d' →
        (∀ i, lam i ≠ 0) ∧ ∀ j, eval u (P.g j) = 0 → mu j ≠ 0) ∧
      (Cond43a P d d' → Cond43d P d0 d d' → (Hmat P u lam mu).det ≠ 0) :=
  ⟨fun ha => part_i P d d' u hu ha,
   fun ha hb => part_ii hadm u hu ha hb,
   fun ha hc => part_iii hadm u hu lam mu h13 h14 ha hc,
   fun ha hd => part_iv hm1 u hu lam mu h13 h14 ha hd⟩
