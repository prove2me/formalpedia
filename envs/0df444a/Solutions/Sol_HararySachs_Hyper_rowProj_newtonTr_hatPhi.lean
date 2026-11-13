-- Prove2me | solution 1 for HararySachs.Hyper.rowProj_newtonTr_hatPhi
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:10:57.475124+00:00
-- url     : https://prove2.me/submissions/6beea714-71fc-45bf-900c-0c90f2528116

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Definitions.Def_HararySachs_Hyper_RowProj
import Theorems.Thm_ShiftOp_iterate_eval_zero
import Theorems.Thm_MvResultant_poisson_block
import Theorems.Thm_HararySachs_Hyper_newtonTr_prod_one_sub_mul
import Theorems.Thm_HararySachs_Hyper_generic_row_points

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace SInvAux

/-! ### Naturality and truncation -/

section General

variable {R S : Type*} [CommRing R] [CommRing S] {n k : ℕ}

lemma zcoord_map (f : R →+* S) (A : Fin n → (Fin (k - 1) → Fin n) → R) (j : Fin n) :
    zcoord (k := k) (fun i t => f (A i t)) j =
      MvPolynomial.map (Polynomial.mapRingHom f) (zcoord (k := k) A j) := by
  simp [zcoord, map_sub, map_sum, MvPolynomial.map_monomial]

lemma phiPoly_map (f : R →+* S) (A : Fin n → (Fin (k - 1) → Fin n) → R)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    phiPoly (k := k) (fun i t => f (A i t)) res = (phiPoly (k := k) A res).map f := by
  unfold phiPoly
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext v
    simp only [Function.comp_apply, zcoord_map, MvPolynomial.coeff_map]

lemma newtonTr_map (f : R →+* S) (Φ : Polynomial R) (d : ℕ) :
    newtonTr (Φ.map f) d = f (newtonTr Φ d) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => simp [newtonTr]
    | succ d =>
      rw [newtonTr, newtonTr, map_sub, map_neg, map_mul, map_sum, map_natCast,
        Polynomial.coeff_map]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [map_mul, ih j (by omega), Polynomial.coeff_map]

lemma newtonTr_congr {Φ Ψ : Polynomial R} (m : ℕ) (h : ∀ j ≤ m, Φ.coeff j = Ψ.coeff j) :
    newtonTr Φ m = newtonTr Ψ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [newtonTr]
    | succ m =>
      rw [newtonTr, newtonTr, h (m + 1) le_rfl]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [ih j (by omega) (fun l hl => h l (by omega)), h (m + 1 - j) (by omega)]

lemma coeff_hatPhi (C : R) (q : ℕ → R) (M j : ℕ) :
    (hatPhi C q M).coeff j = if j = 0 then 1 else if j ≤ M then C ^ (j - 1) * q j else 0 := by
  classical
  unfold hatPhi
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [sum_ite_eq']
  simp only [mem_Icc]
  split_ifs <;> first | omega | simp_all

lemma newtonTr_hatPhi_mono (C : R) (q : ℕ → R) {m M : ℕ} (h : m ≤ M) :
    newtonTr (hatPhi C q m) m = newtonTr (hatPhi C q M) m :=
  newtonTr_congr m fun j hj => by
    rw [coeff_hatPhi, coeff_hatPhi]
    split_ifs <;> first | rfl | omega

lemma hatPhi_map (f : R →+* S) (C : R) (q : ℕ → R) (M : ℕ) :
    (hatPhi C q M).map f = hatPhi (f C) (fun j => f (q j)) M := by
  simp [hatPhi, Polynomial.map_sum, map_pow, map_mul]

lemma eval_hatPhi (C : R) (q : ℕ → R) (M : ℕ) (s : R) :
    (hatPhi C q M).eval s = 1 + ∑ j ∈ Icc 1 M, C ^ (j - 1) * q j * s ^ j := by
  simp [hatPhi, Polynomial.eval_finset_sum]

end General

/-! ### Resultants of the numeric systems -/

variable {n k : ℕ}

/-- the forms `x_j^{k-1} - f_j^b(x)` of a numeric tensor -/
noncomputable def F (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) :
    MvPolynomial (Fin n) ℂ :=
  X j ^ (k - 1) - ∑ t : Fin (k - 1) → Fin n, C (b (j, t)) * ∏ s, X (t s)

/-- the resultant of a system of forms -/
noncomputable def resF (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (G : Fin n → MvPolynomial (Fin n) ℂ) : ℂ :=
  aeval (fun v : ResVar n (fun _ => k - 1) => coeff v.2.1 (G v.1))
    (MvPolynomial.map (Int.castRingHom ℂ) res)

lemma prod_X_eq (t : Fin (k - 1) → Fin n) :
    (∏ s, (X (t s) : MvPolynomial (Fin n) ℂ)) =
      monomial ((univ : Finset (Fin (k - 1))).sum fun a => Finsupp.single (t a) 1) 1 := by
  rw [monomial_sum_one]; rfl

lemma F_hom (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) :
    (F (k := k) b j).IsHomogeneous (k - 1) := by
  unfold F
  refine (isHomogeneous_X_pow _ _).sub (IsHomogeneous.sum _ _ _ fun t _ => ?_)
  have h := IsHomogeneous.prod (univ : Finset (Fin (k - 1))) (fun s => (X (t s) :
    MvPolynomial (Fin n) ℂ)) (fun _ => 1) fun s _ => isHomogeneous_X _ _
  have := (isHomogeneous_C (Fin n) (b (j, t))).mul h
  simpa using this

lemma eval_F (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) (j : Fin n) (p : Fin n → ℂ) (hp : p j = 1) :
    eval p (F (k := k) b j) = 1 - ∑ t : Fin (k - 1) → Fin n, b (j, t) * ∏ s, p (t s) := by
  simp [F, eval_prod, hp]

lemma Q_at (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    aeval b ((phiPoly (k := k) (genTensor n k) res).eval 1) = resF res (F (k := k) b) := by
  set Φ := phiPoly (k := k) (genTensor n k) res
  have h1 : (aeval b : GenRing n k →ₐ[ℚ] ℂ) (Polynomial.eval 1 Φ) =
      Polynomial.eval 1 (Φ.map ((aeval b : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ)) := by
    rw [Polynomial.eval_map]
    have := Polynomial.hom_eval₂ Φ (RingHom.id (GenRing n k))
      ((aeval b : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) 1
    simpa using this
  have h2 : Φ.map ((aeval b : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) =
      phiPoly (k := k) (fun j t => b (j, t)) res := by
    rw [← phiPoly_map]
    congr 1
    funext j t
    simp [genTensor]
  rw [h1, h2]
  unfold phiPoly resF
  simp only [aeval_def, eval₂_map]
  rw [← Polynomial.coe_evalRingHom, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext v
    simp only [Function.comp_apply]
    rw [← MvPolynomial.coeff_map]
    congr 1
    unfold zcoord F
    simp only [map_sub, map_sum, MvPolynomial.map_monomial, Polynomial.coe_evalRingHom,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_one]
    rw [X_pow_eq_monomial]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [prod_X_eq, C_mul_monomial, mul_one]

/-! ### Scaling the variables of row `i` -/

/-- scale the entries of row `i` by `s` -/
def scale (i : Fin n) (s : ℂ) (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    Fin n × (Fin (k - 1) → Fin n) → ℂ :=
  fun v => s ^ (rowWeight (k := k) i v) * b v

lemma aeval_scale_of_wHom (i : Fin n) (s : ℂ) (b : Fin n × (Fin (k - 1) → Fin n) → ℂ)
    {φ : GenRing n k} {j : ℕ} (hφ : IsWeightedHomogeneous (rowWeight i) φ j) :
    aeval (scale i s b) φ = s ^ j * aeval b φ := by
  classical
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, mul_sum]
  refine sum_congr rfl fun μ hμ => ?_
  have hw := hφ (mem_support_iff.mp hμ)
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [scale, mul_pow, prod_mul_distrib, ← pow_mul]
  rw [prod_pow_eq_pow_sum]
  have : ∑ v ∈ μ.support, rowWeight i v * μ v = j := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact sum_congr rfl fun v _ => by rw [smul_eq_mul, mul_comm]
  rw [this]; ring

lemma Q_eq_sum (Q : GenRing n k) (i : Fin n) (N : ℕ) (hN : Q.totalDegree ≤ N) :
    Q = ∑ j ∈ range (N + 1), weightedHomogeneousComponent (rowWeight i) j Q := by
  have hsum := sum_weightedHomogeneousComponent (rowWeight (k := k) i) Q
  rw [finsum_eq_sum_of_support_subset _ (s := range (N + 1))] at hsum
  · exact hsum.symm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [coe_range, Set.mem_Iio]
    by_contra hmd
    apply hm
    apply weightedHomogeneousComponent_eq_zero'
    intro μ hμ
    have h1 := le_totalDegree hμ
    have h2 : (Finsupp.weight (rowWeight (k := k) i)) μ ≤ μ.sum fun _ e => e := by
      rw [Finsupp.weight_apply]
      refine Finset.sum_le_sum fun v _ => ?_
      simp only [rowWeight, smul_eq_mul]; split_ifs <;> simp
    omega

lemma aeval_scale_Q (Q : GenRing n k) (i : Fin n) (N : ℕ) (hN : Q.totalDegree ≤ N) (s : ℂ)
    (b : Fin n × (Fin (k - 1) → Fin n) → ℂ) :
    aeval (scale i s b) Q =
      ∑ j ∈ range (N + 1), s ^ j * aeval b (weightedHomogeneousComponent (rowWeight i) j Q) := by
  conv_lhs => rw [Q_eq_sum Q i N hN]
  rw [map_sum]
  exact sum_congr rfl fun j _ => aeval_scale_of_wHom i s b
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

lemma F_scale_update (i : Fin n) (s : ℂ) (a a' : Fin n × (Fin (k - 1) → Fin n) → ℂ)
    (ha' : ∀ j t, j ≠ i → a' (j, t) = a (j, t)) :
    F (k := k) (scale i s a') = Function.update (F a) i (F (scale i s a') i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj]
    unfold F
    congr 1
    refine sum_congr rfl fun t _ => ?_
    simp [scale, rowWeight, hj, ha' j t hj]

/-! ### The pointwise computation -/

/-- the Poisson numerators, evaluated at a generic numeric tensor -/
lemma pointwise (hk : 2 ≤ k) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) (m : ℕ) (hm : 1 ≤ m)
    (a a' : Fin n × (Fin (k - 1) → Fin n) → ℂ) (ha' : ∀ j t, j ≠ i → a' (j, t) = a (j, t))
    (P : Finset (Fin n → ℂ)) (hcard : P.card = (k - 1) ^ (n - 1))
    (hP : ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i → eval p (F (k := k) a j) = 0)
    (c : ℂ) (hc : c = resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))))
    (hc0 : c ≠ 0) :
    aeval a' (newtonTr (hatPhi
        (weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m) =
      c ^ m * ∑ p ∈ P, (∑ t : Fin (k - 1) → Fin n, a' (i, t) * ∏ s, p (t s)) ^ m := by
  classical
  set Q := (phiPoly (k := k) (genTensor n k) res).eval 1 with hQ
  set w := rowWeight (k := k) i with hw
  set q : ℕ → GenRing n k := fun j => weightedHomogeneousComponent w j Q with hq
  set N := m + Q.totalDegree with hN
  have hNQ : Q.totalDegree ≤ N := by omega
  set y : (Fin n → ℂ) → ℂ := fun p => ∑ t : Fin (k - 1) → Fin n, a' (i, t) * ∏ s, p (t s)
    with hy
  -- the system with row `i` scaled by `s`, and Poisson's formula
  have hD : ∀ j : Fin n, 1 ≤ (fun _ : Fin n => k - 1) j := fun _ => by simp only; omega
  have hcard' : P.card = ∏ j ∈ univ.erase i, (fun _ : Fin n => k - 1) j := by
    rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; exact hcard
  have hPois : ∀ s : ℂ, aeval (scale i s a') Q = c * ∏ p ∈ P, (1 - s * y p) := by
    intro s
    rw [hQ, Q_at, F_scale_update i s a a' ha']
    have h := MvResultant.poisson_block hD res hres i (F (k := k) a)
      (fun j _ => F_hom a j) P hcard' hP (F (scale i s a') i) (F_hom _ i)
    have h' : resF res (Function.update (F (k := k) a) i (F (scale i s a') i)) =
        resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) *
          ∏ p ∈ P, eval p (F (scale i s a') i) := h
    rw [h', ← hc]
    congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [eval_F _ _ _ (hP p hp).1, hy]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    simp [scale, rowWeight]; ring
  -- the constant term is `c`
  have hC : aeval a' (q 0) = c := by
    have h0 := aeval_scale_Q Q i N hNQ 0 a'
    rw [hPois, sum_eq_single 0 (fun j _ hj => by rw [zero_pow hj, zero_mul])
      (fun h => absurd (mem_range.mpr (by omega)) h)] at h0
    simpa using h0.symm
  -- `hatPhi` evaluates to the product of the linear factors
  have hpoly : hatPhi c (fun j => aeval a' (q j)) N =
      ∏ p ∈ P, (1 - Polynomial.C (c * y p) * Polynomial.X) := by
    refine Polynomial.funext fun σ => ?_
    apply mul_left_cancel₀ hc0
    rw [eval_hatPhi]
    have h1 := aeval_scale_Q Q i N hNQ (c * σ) a'
    rw [hPois] at h1
    have h2 : c * (1 + ∑ j ∈ Icc 1 N, c ^ (j - 1) * aeval a' (q j) * σ ^ j) =
        ∑ j ∈ range (N + 1), (c * σ) ^ j * aeval a' (q j) := by
      rw [sum_range_succ', pow_zero, one_mul, hC, mul_add, mul_one, add_comm]
      congr 1
      have hI : Icc 1 N = Ico 1 (N + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
      rw [mul_sum, hI, sum_Ico_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [show 1 + j - 1 = j by omega, show 1 + j = j + 1 by omega, mul_pow, pow_succ]
      ring
    rw [h2, ← h1, Polynomial.eval_prod]
    congr 1
    refine prod_congr rfl fun p _ => ?_
    simp; ring
  -- conclude with Newton's identities for a product
  rw [← RingHom.coe_coe (aeval a' : GenRing n k →ₐ[ℚ] ℂ)]
  rw [← newtonTr_map, hatPhi_map, newtonTr_hatPhi_mono _ _ (show m ≤ N by omega)]
  simp only [RingHom.coe_coe]
  rw [show aeval a' (weightedHomogeneousComponent (rowWeight i) 0 Q) = c from hC]
  rw [show (fun j => aeval a' (weightedHomogeneousComponent (rowWeight i) j Q)) =
    fun j => aeval a' (q j) from rfl, hpoly, newtonTr_prod_one_sub_mul _ _ m hm, mul_sum]
  exact sum_congr rfl fun p _ => by rw [mul_pow]

/-! ### The projection side -/

/-- `f_i^a(∂_v)` on polynomials with complex coefficients -/
noncomputable def opA (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ t : Fin (k - 1) → Fin n, a (i, t) • (List.ofFn t).foldr (fun j q => pderiv j q) p

lemma foldr_pderiv_map (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (l : List (Fin n))
    (p : MvPolynomial (Fin n) (GenRing n k)) :
    MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ)
        (l.foldr (fun j q => pderiv j q) p) =
      l.foldr (fun j q => pderiv j q)
        (MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) p) := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.foldr_cons]; rw [← pderiv_map, ih]

lemma map_rowOp (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) (GenRing n k)) :
    MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) (rowOp i p) =
      opA a i (MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) p) := by
  unfold rowOp opA
  rw [map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, foldr_pderiv_map, MvPolynomial.smul_eq_C_mul]
  simp

lemma map_rowOp_iter (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (m : ℕ)
    (p : MvPolynomial (Fin n) (GenRing n k)) :
    MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) ((rowOp i)^[m] p) =
      (opA a i)^[m] (MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) p) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_rowOp, ih]

lemma opA_add (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (p q : MvPolynomial (Fin n) ℂ) :
    opA (k := k) a i (p + q) = opA a i p + opA a i q := by
  have : ∀ l : List (Fin n), l.foldr (fun j q => pderiv j q) (p + q) =
      l.foldr (fun j q => pderiv j q) p + l.foldr (fun j q => pderiv j q) q := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => simp only [List.foldr_cons]; rw [ih, map_add]
  simp only [opA, this, smul_add, sum_add_distrib]

lemma opA_C_mul (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (x : ℂ)
    (p : MvPolynomial (Fin n) ℂ) : opA (k := k) a i (C x * p) = C x * opA a i p := by
  have : ∀ l : List (Fin n), l.foldr (fun j q => pderiv j q) (C x * p) =
      C x * l.foldr (fun j q => pderiv j q) p := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => simp only [List.foldr_cons]; rw [ih, pderiv_C_mul]
  simp only [opA, this, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm]

lemma opA_zero (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) :
    opA (k := k) a i 0 = 0 := by
  have h := opA_add (k := k) a i 0 0
  rw [add_zero] at h
  simpa using h

lemma opA_sum (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℂ) :
    opA (k := k) a i (∑ l ∈ s, f l) = ∑ l ∈ s, opA a i (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opA_zero]
  | insert y s hy ih => rw [sum_insert hy, sum_insert hy, opA_add, ih]

lemma opA_iter_sum (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (m : ℕ) {ι : Type*}
    (s : Finset ι) (x : ℂ) (f : ι → MvPolynomial (Fin n) ℂ) :
    (opA (k := k) a i)^[m] (C x * ∑ l ∈ s, f l) = C x * ∑ l ∈ s, (opA a i)^[m] (f l) := by
  classical
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, opA_C_mul, opA_sum, ih]
    rfl

lemma map_rowSubst (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (Sx : GenRing n k) :
    MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) (rowSubst i Sx) =
      aeval (fun v : Fin n × (Fin (k - 1) → Fin n) =>
        if v.1 = i then ∏ s, (X (v.2 s) : MvPolynomial (Fin n) ℂ) else C (a v)) Sx := by
  have : (MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ)).comp
      (rowSubst (k := k) i).toRingHom =
      (aeval (fun v : Fin n × (Fin (k - 1) → Fin n) =>
        if v.1 = i then ∏ s, (X (v.2 s) : MvPolynomial (Fin n) ℂ) else C (a v)) :
          GenRing n k →ₐ[ℚ] MvPolynomial (Fin n) ℂ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [rowSubst, MvPolynomial.algebraMap_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowSubst, aeval_X]
      split_ifs <;> simp
  exact congrArg (fun f : GenRing n k →+* MvPolynomial (Fin n) ℂ => f Sx) this

lemma eval_aeval_bv (a : Fin n × (Fin (k - 1) → Fin n) → ℂ) (i : Fin n) (v : Fin n → ℂ)
    (Sx : GenRing n k) :
    eval v (aeval (fun u : Fin n × (Fin (k - 1) → Fin n) =>
        if u.1 = i then ∏ s, (X (u.2 s) : MvPolynomial (Fin n) ℂ) else C (a u)) Sx) =
      aeval (fun u : Fin n × (Fin (k - 1) → Fin n) =>
        if u.1 = i then ∏ s, v (u.2 s) else a u) Sx := by
  have : (eval v).comp (aeval (fun u : Fin n × (Fin (k - 1) → Fin n) =>
        if u.1 = i then ∏ s, (X (u.2 s) : MvPolynomial (Fin n) ℂ) else C (a u)) :
          GenRing n k →ₐ[ℚ] MvPolynomial (Fin n) ℂ).toRingHom =
      (aeval (fun u : Fin n × (Fin (k - 1) → Fin n) =>
        if u.1 = i then ∏ s, v (u.2 s) else a u) : GenRing n k →ₐ[ℚ] ℂ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun u => ?_)
    · simp [MvPolynomial.algebraMap_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      split_ifs <;> simp [eval_prod]
  exact congrArg (fun f : GenRing n k →+* ℂ => f Sx) this

end SInvAux

open SInvAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) (m : ℕ) :
    rowProj i m (newtonTr (hatPhi
        (MvPolynomial.weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => MvPolynomial.weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m) =
      newtonTr (hatPhi
        (MvPolynomial.weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => MvPolynomial.weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m := by
  classical
  set Sm := newtonTr (hatPhi
        (MvPolynomial.weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => MvPolynomial.weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m with hSm
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    simp [hSm, newtonTr, rowProj]
  obtain ⟨Δ, hΔ, hgen⟩ := generic_row_points n k hk hn res hres i
  -- pointwise agreement at generic points
  have hpt : ∀ a : Fin n × (Fin (k - 1) → Fin n) → ℂ, eval a Δ ≠ 0 →
      aeval a (rowProj i m Sm) = aeval a Sm := by
    intro a ha
    obtain ⟨⟨P, hcard, hP⟩, hc0⟩ := hgen a ha
    set c := resF res (Function.update (F (k := k) a) i (X i ^ (k - 1))) with hc
    have hc0' : c ≠ 0 := hc0
    have hP' : ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i → eval p (F (k := k) a j) = 0 := hP
    have hval := pointwise hk res hres i m hm a a (fun _ _ _ => rfl) P hcard hP' c hc hc0'
    rw [hval]
    -- the projection side
    have hpolyv : aeval (fun v : Fin n × (Fin (k - 1) → Fin n) =>
          if v.1 = i then ∏ s, (X (v.2 s) : MvPolynomial (Fin n) ℂ) else C (a v)) Sm =
        C (c ^ m) * ∑ p ∈ P, (∑ l, C (p l) * X l) ^ (m * (k - 1)) := by
      refine MvPolynomial.funext fun v => ?_
      rw [eval_aeval_bv]
      have hv := pointwise hk res hres i m hm a
        (fun u => if u.1 = i then ∏ s, v (u.2 s) else a u)
        (fun j t hj => by simp [hj]) P hcard hP' c hc hc0'
      rw [hv, eval_mul, eval_C, map_sum]
      congr 1
      refine sum_congr rfl fun p _ => ?_
      simp only [eval_pow, eval_sum, eval_mul, eval_C, eval_X, ite_true]
      rw [mul_comm m, pow_mul]
      congr 1
      have e : ∀ t : Fin (k - 1) → Fin n,
          (∏ s, v (t s)) * ∏ s, p (t s) = ∏ s, (p (t s) * v (t s)) := fun t => by
        rw [← prod_mul_distrib]; exact prod_congr rfl fun s _ => mul_comm _ _
      simp only [e]
      rw [← Fintype.prod_sum (fun (_ : Fin (k - 1)) (l : Fin n) => p l * v l), prod_const,
        card_univ, Fintype.card_fin]
    have hB1 : ∀ p : Fin n → ℂ, eval 0 ((opA (k := k) a i)^[m]
        ((∑ l, C (p l) * X l) ^ (m * (k - 1)))) =
        (Nat.factorial (m * (k - 1)) : ℂ) *
          (∑ t : Fin (k - 1) → Fin n, a (i, t) * ∏ s, p (t s)) ^ m := by
      intro p
      have := ShiftOp.iterate_eval_zero (σ := Fin n) (R := ℂ) (k - 1) (fun t => a (i, t)) p m
        (m * (k - 1))
      rw [if_pos rfl] at this
      exact this
    have haev : ∀ Y : MvPolynomial (Fin n) (GenRing n k), (aeval a) (eval 0 Y) =
        eval 0 (MvPolynomial.map ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) Y) := by
      intro Y
      rw [eval_map]
      have := MvPolynomial.hom_eval₂ Y (RingHom.id (GenRing n k))
        ((aeval a : GenRing n k →ₐ[ℚ] ℂ) : GenRing n k →+* ℂ) 0
      simpa [Function.comp_def] using this
    rw [rowProj, map_smul, haev, map_rowOp_iter, map_rowSubst, hpolyv, opA_iter_sum, eval_mul,
      eval_C, map_sum]
    simp only [hB1]
    rw [← mul_sum, Algebra.smul_def, eq_ratCast]
    have hf : (Nat.factorial (m * (k - 1)) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  -- density
  have hD0 : Δ * MvPolynomial.map (algebraMap ℚ ℂ) (rowProj i m Sm - Sm) = 0 := by
    refine MvPolynomial.funext fun a => ?_
    rw [eval_mul, map_zero]
    by_cases ha : eval a Δ = 0
    · rw [ha, zero_mul]
    · rw [eval_map, ← aeval_def, map_sub, hpt a ha, sub_self, mul_zero]
  have h1 := (mul_eq_zero.mp hD0).resolve_left hΔ
  rw [← map_zero (MvPolynomial.map (σ := Fin n × (Fin (k - 1) → Fin n)) (algebraMap ℚ ℂ))] at h1
  exact sub_eq_zero.mp (MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective h1)
