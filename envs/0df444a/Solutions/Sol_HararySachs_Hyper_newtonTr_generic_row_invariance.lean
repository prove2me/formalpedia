-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_generic_row_invariance
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:08:52.94475+00:00
-- url     : https://prove2.me/submissions/d200ff95-d062-4ee5-bac1-50c4d404ff98

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Definitions.Def_HararySachs_Hyper_RowProj
import Theorems.Thm_HararySachs_Hyper_newtonTr_two_gradings
import Theorems.Thm_HararySachs_Hyper_rowProj_newtonTr_hatPhi

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace GenInvAux

/-! ### (A) Graded polynomials in `z` -/

section Graded

variable {σ : Type*}

/-- the coefficient of `z^j` is homogeneous of degree `j` -/
def Gr (Φ : Polynomial (MvPolynomial σ ℚ)) : Prop := ∀ j, (Φ.coeff j).IsHomogeneous j

lemma Gr_add {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : Gr Φ) (h2 : Gr Ψ) : Gr (Φ + Ψ) :=
  fun j => by rw [Polynomial.coeff_add]; exact (h1 j).add (h2 j)

lemma Gr_neg {Φ : Polynomial (MvPolynomial σ ℚ)} (h : Gr Φ) : Gr (-Φ) :=
  fun j => by rw [Polynomial.coeff_neg]; exact (h j).neg

lemma Gr_sub {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : Gr Φ) (h2 : Gr Ψ) : Gr (Φ - Ψ) := by
  rw [sub_eq_add_neg]; exact Gr_add h1 (Gr_neg h2)

lemma Gr_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ ℚ))
    (h : ∀ x ∈ s, Gr (f x)) : Gr (∑ x ∈ s, f x) :=
  fun j => by
    rw [Polynomial.finsetSum_coeff]
    exact IsHomogeneous.sum _ _ _ fun x hx => h x hx j

lemma Gr_mul {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : Gr Φ) (h2 : Gr Ψ) : Gr (Φ * Ψ) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine IsHomogeneous.sum _ _ _ fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]
  exact (h1 x.1).mul (h2 x.2)

lemma Gr_intCast (c : ℤ) : Gr (c : Polynomial (MvPolynomial σ ℚ)) := by
  intro j
  rw [← map_intCast (Polynomial.C : MvPolynomial σ ℚ →+* _) c, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [← map_intCast (C : ℚ →+* MvPolynomial σ ℚ) c]
    exact isHomogeneous_C _ _
  · exact isHomogeneous_zero _ _ _

lemma Gr_eval₂' {τ : Type*} (res : MvPolynomial τ ℤ) (g : τ → Polynomial (MvPolynomial σ ℚ))
    (hg : ∀ v, Gr (g v)) :
    Gr (MvPolynomial.eval₂ (Int.castRingHom _) g res) := by
  induction res using MvPolynomial.induction_on with
  | C a => rw [eval₂_C]; exact Gr_intCast a
  | add p q hp hq => rw [eval₂_add]; exact Gr_add hp hq
  | mul_X p v hp => rw [eval₂_mul, eval₂_X]; exact Gr_mul hp (hg v)

lemma newtonTr_hom {Φ : Polynomial (MvPolynomial σ ℚ)} (h : Gr Φ) (d : ℕ) :
    (newtonTr Φ d).IsHomogeneous d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => rw [newtonTr]; exact isHomogeneous_zero _ _ _
    | succ d =>
      rw [newtonTr]
      refine IsHomogeneous.sub ?_ ?_
      · refine IsHomogeneous.neg ?_
        rw [← map_natCast (C : ℚ →+* MvPolynomial σ ℚ) (d + 1)]
        have := (isHomogeneous_C σ ((d + 1 : ℕ) : ℚ)).mul (h (d + 1))
        rwa [zero_add] at this
      · refine IsHomogeneous.sum _ _ _ fun j _ => ?_
        have := (ih j j.isLt).mul (h (d + 1 - j))
        rwa [show (j : ℕ) + (d + 1 - j) = d + 1 by omega] at this

end Graded

/-! ### (B) The polynomial `Φ` of the generic tensor -/

section Phi

variable {n k : ℕ}

lemma Gr_zcoord_coeff (j : Fin n) (α : Fin n →₀ ℕ) :
    Gr (coeff α (zcoord (k := k) (genTensor n k) j)) := by
  classical
  unfold zcoord
  rw [coeff_sub, coeff_monomial, coeff_sum]
  refine Gr_sub ?_ (Gr_sum _ _ fun t _ => ?_)
  · split_ifs
    · intro j; rw [Polynomial.coeff_one]; split_ifs with h
      · subst h; exact isHomogeneous_one _ _
      · exact isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  · rw [coeff_monomial]
    split_ifs
    · intro j
      rw [Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h; exact isHomogeneous_X _ _
      · exact isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _

lemma phiPoly_eq_eval₂ (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    phiPoly (k := k) (genTensor n k) res =
      MvPolynomial.eval₂ (Int.castRingHom _)
        (fun v : ResVar n (fun _ => k - 1) => coeff v.2.1 (zcoord (k := k) (genTensor n k) v.1))
        res := by
  unfold phiPoly
  rw [aeval_def, eval₂_map]
  congr 1

lemma Gr_phi (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) :
    Gr (phiPoly (k := k) (genTensor n k) res) := by
  rw [phiPoly_eq_eval₂]
  exact Gr_eval₂' res _ fun v => Gr_zcoord_coeff v.1 v.2.1

lemma phi_coeff_zero (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    (phiPoly (k := k) (genTensor n k) res).coeff 0 = 1 := by
  classical
  rw [Polynomial.coeff_zero_eq_eval_zero, phiPoly_eq_eval₂, ← Polynomial.coe_evalRingHom,
    eval₂_comp_left]
  have hmap : ∀ j : Fin n, MvPolynomial.map (Polynomial.evalRingHom (0 : GenRing n k))
      (zcoord (k := k) (genTensor n k) j) = monomial (Finsupp.single j (k - 1)) 1 := by
    intro j
    simp only [zcoord, map_sub, map_sum, MvPolynomial.map_monomial, Polynomial.coe_evalRingHom,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero,
      monomial_zero, sum_const_zero, sub_zero]
  have h1 : ∀ v : ResVar n (fun _ => k - 1),
      (Polynomial.evalRingHom 0) (coeff v.2.1 (zcoord (k := k) (genTensor n k) v.1)) =
        (Int.castRingHom (GenRing n k))
          (if v.2.1 = Finsupp.single v.1 (k - 1) then 1 else 0) := by
    intro v
    rw [← MvPolynomial.coeff_map, hmap, coeff_monomial]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have h2 : ((Polynomial.evalRingHom (0 : GenRing n k)).comp (Int.castRingHom _)) =
      Int.castRingHom (GenRing n k) := RingHom.ext_int _ _
  rw [h2]
  simp only [Function.comp_def, h1]
  have h5 : MvPolynomial.eval₂ (Int.castRingHom (GenRing n k))
      (fun x : ResVar n (fun _ => k - 1) => (Int.castRingHom (GenRing n k))
        (if x.2.1 = Finsupp.single x.1 (k - 1) then 1 else 0)) res =
      (Int.castRingHom (GenRing n k)) (MvPolynomial.eval₂ (RingHom.id ℤ)
        (fun x : ResVar n (fun _ => k - 1) =>
          if x.2.1 = Finsupp.single x.1 (k - 1) then (1 : ℤ) else 0) res) := by
    rw [eval₂_comp_left]; rfl
  rw [h5]
  have h3 := hres.2.1
  rw [aeval_def, Algebra.algebraMap_self] at h3
  rw [h3, map_one]

lemma phi_coeff_eq (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (d : ℕ) :
    (phiPoly (k := k) (genTensor n k) res).coeff d =
      homogeneousComponent d ((phiPoly (k := k) (genTensor n k) res).eval 1) := by
  classical
  set Φ := phiPoly (k := k) (genTensor n k) res
  have hG := Gr_phi (k := k) res
  rw [Polynomial.eval_eq_sum_range, map_sum]
  simp only [one_pow, mul_one]
  have hc : ∀ j, homogeneousComponent d (Φ.coeff j) = if d = j then Φ.coeff j else 0 :=
    fun j => homogeneousComponent_of_mem (mem_homogeneousSubmodule _ _ |>.mpr (hG j))
  simp only [hc, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

lemma Q_constantCoeff (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    constantCoeff ((phiPoly (k := k) (genTensor n k) res).eval 1) = 1 := by
  have h := phi_coeff_eq (k := k) res 0
  rw [phi_coeff_zero res hres, homogeneousComponent_zero] at h
  exact (C_injective _ _ (h.symm.trans C_1.symm))

end Phi

/-! ### (C) The row projection -/

section Proj

variable {n k : ℕ}

/-- `∂_{v_{l₁}} ⋯ ∂_{v_{l_m}}` as a `GenRing`-linear map -/
noncomputable def wordL (l : List (Fin n)) :
    MvPolynomial (Fin n) (GenRing n k) →ₗ[GenRing n k] MvPolynomial (Fin n) (GenRing n k) :=
  l.foldr (fun j L => (pderiv j).toLinearMap ∘ₗ L) LinearMap.id

lemma wordL_apply (l : List (Fin n)) (p : MvPolynomial (Fin n) (GenRing n k)) :
    l.foldr (fun j q => pderiv j q) p = wordL l p := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.foldr_cons, wordL] at ih ⊢; rw [ih]; rfl

/-- `rowOp i` as a `GenRing`-linear map -/
noncomputable def rowOpL (i : Fin n) :
    MvPolynomial (Fin n) (GenRing n k) →ₗ[GenRing n k] MvPolynomial (Fin n) (GenRing n k) :=
  ∑ t : Fin (k - 1) → Fin n, (X (i, t) : GenRing n k) • wordL (List.ofFn t)

lemma rowOp_eq (i : Fin n) : (rowOp (k := k) i) = ⇑(rowOpL i) := by
  funext p
  simp [rowOp, rowOpL, LinearMap.sum_apply, wordL_apply]

lemma rowOp_iter (i : Fin n) (m : ℕ) : (rowOp (k := k) i)^[m] = ⇑(rowOpL i ^ m) := by
  rw [Module.End.coe_pow, rowOp_eq]

lemma rowProj_eq (i : Fin n) (m : ℕ) (Q : GenRing n k) :
    rowProj i m Q = (1 / (Nat.factorial (m * (k - 1)) : ℚ)) •
      eval 0 ((rowOpL i ^ m) (rowSubst i Q)) := by
  rw [rowProj, rowOp_iter]

/-- a polynomial free of the row-`i` variables -/
def Free (i : Fin n) (g : GenRing n k) : Prop := ∀ v ∈ g.vars, v.1 ≠ i

lemma rowSubst_free (i : Fin n) {g : GenRing n k} (hg : Free i g) : rowSubst i g = C g := by
  have := MvPolynomial.hom_congr_vars (f₁ := ((rowSubst (k := k) i : GenRing n k →ₐ[ℚ] _) :
      GenRing n k →+* MvPolynomial (Fin n) (GenRing n k)))
    (f₂ := C) (p₁ := g) (p₂ := g) (by ext; simp [MvPolynomial.algebraMap_eq])
    (fun v hv => by simp [rowSubst, hg v hv]) rfl
  simpa using this

lemma rowProj_mul_free (i : Fin n) (m : ℕ) {g : GenRing n k} (hg : Free i g) (Q : GenRing n k) :
    rowProj i m (g * Q) = g * rowProj i m Q := by
  have he : ∀ x : MvPolynomial (Fin n) (GenRing n k), eval 0 (g • x) = g * eval 0 x :=
    fun x => by rw [MvPolynomial.smul_eq_C_mul, eval_mul, eval_C]
  rw [rowProj_eq, rowProj_eq, map_mul, rowSubst_free i hg, ← MvPolynomial.smul_eq_C_mul, map_smul,
    he, mul_smul_comm]

lemma rowProj_add (i : Fin n) (m : ℕ) (P Q : GenRing n k) :
    rowProj i m (P + Q) = rowProj i m P + rowProj i m Q := by
  rw [rowProj_eq, rowProj_eq, rowProj_eq, map_add, map_add, map_add, smul_add]

lemma free_C (i : Fin n) (c : ℚ) : Free i (C c : GenRing n k) := by
  intro v hv; simp [vars_C] at hv

lemma rowProj_smul (i : Fin n) (m : ℕ) (c : ℚ) (Q : GenRing n k) :
    rowProj i m (c • Q) = c • rowProj i m Q := by
  rw [smul_eq_C_mul, smul_eq_C_mul, rowProj_mul_free i m (free_C i c)]

lemma rowProj_zero (i : Fin n) (m : ℕ) : rowProj i m (0 : GenRing n k) = 0 := by
  rw [rowProj_eq]; simp

lemma rowProj_sum (i : Fin n) (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → GenRing n k) :
    rowProj i m (∑ x ∈ s, f x) = ∑ x ∈ s, rowProj i m (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rowProj_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, rowProj_add, ih]

/-- weighted-degree-`0` polynomials are free of row `i` -/
lemma free_of_wdeg_zero (i : Fin n) {g : GenRing n k}
    (hg : IsWeightedHomogeneous (rowWeight i) g 0) : Free i g := by
  classical
  intro v hv hvi
  rw [mem_vars] at hv
  obtain ⟨μ, hμ, hvμ⟩ := hv
  have h0 := hg (mem_support_iff.mp hμ)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have : μ v • rowWeight i v ≤ ∑ x ∈ μ.support, μ x • rowWeight i x :=
    single_le_sum (f := fun x => μ x • rowWeight i x) (fun _ _ => Nat.zero_le _) hvμ
  rw [h0] at this
  simp [rowWeight, hvi] at this
  exact (Finsupp.mem_support_iff.mp hvμ) this

lemma free_mul (i : Fin n) {g h : GenRing n k} (hg : Free i g) (hh : Free i h) :
    Free i (g * h) := fun v hv => by
  rcases Finset.mem_union.mp (vars_mul g h hv) with h1 | h1
  · exact hg v h1
  · exact hh v h1

lemma free_pow (i : Fin n) {g : GenRing n k} (hg : Free i g) (m : ℕ) : Free i (g ^ m) :=
  fun v hv => hg v (vars_pow g m hv)

lemma free_homogeneousComponent (i : Fin n) {g : GenRing n k} (hg : Free i g) (D : ℕ) :
    Free i (homogeneousComponent D g) := by
  classical
  intro v hv
  apply hg v
  rw [mem_vars] at hv ⊢
  obtain ⟨μ, hμ, hvμ⟩ := hv
  refine ⟨μ, ?_, hvμ⟩
  rw [mem_support_iff] at hμ ⊢
  rw [coeff_homogeneousComponent] at hμ
  split_ifs at hμ
  · exact hμ
  · exact absurd rfl hμ

/-! #### Monomial analysis -/

/-- coefficients homogeneous of total degree `a`, row-degree `b`; `v`-homogeneous of degree `f` -/
def Good (i : Fin n) (a b f : ℕ) (p : MvPolynomial (Fin n) (GenRing n k)) : Prop :=
  (∀ β, (coeff β p).IsHomogeneous a ∧ IsWeightedHomogeneous (rowWeight i) (coeff β p) b) ∧
    p.IsHomogeneous f

lemma Good_mul (i : Fin n) {a b f a' b' f' : ℕ} {p q : MvPolynomial (Fin n) (GenRing n k)}
    (hp : Good i a b f p) (hq : Good i a' b' f' q) : Good i (a + a') (b + b') (f + f') (p * q) := by
  refine ⟨fun β => ?_, hp.2.mul hq.2⟩
  rw [coeff_mul]
  exact ⟨IsHomogeneous.sum _ _ _ fun x _ => (hp.1 x.1).1.mul (hq.1 x.2).1,
    IsWeightedHomogeneous.sum _ _ _ fun x _ => (hp.1 x.1).2.mul (hq.1 x.2).2⟩

lemma Good_one (i : Fin n) : Good (k := k) i 0 0 0 1 := by
  refine ⟨fun β => ?_, isHomogeneous_one _ _⟩
  rw [coeff_one]
  split_ifs
  · exact ⟨isHomogeneous_one _ _, isWeightedHomogeneous_one _ _⟩
  · exact ⟨isHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _⟩

lemma Good_pow (i : Fin n) {a b f : ℕ} {p : MvPolynomial (Fin n) (GenRing n k)}
    (hp : Good i a b f p) (e : ℕ) : Good i (a * e) (b * e) (f * e) (p ^ e) := by
  induction e with
  | zero => simpa using Good_one i
  | succ e ih =>
    rw [pow_succ]
    have := Good_mul i ih hp
    simpa [Nat.mul_succ] using this

lemma Good_prod (i : Fin n) {ι : Type*} (s : Finset ι) (a b f : ι → ℕ)
    (p : ι → MvPolynomial (Fin n) (GenRing n k)) (h : ∀ x ∈ s, Good i (a x) (b x) (f x) (p x)) :
    Good i (∑ x ∈ s, a x) (∑ x ∈ s, b x) (∑ x ∈ s, f x) (∏ x ∈ s, p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good_one i
  | insert y s hy ih =>
    rw [sum_insert hy, sum_insert hy, sum_insert hy, prod_insert hy]
    exact Good_mul i (h y (mem_insert_self y s)) (ih fun x hx => h x (mem_insert_of_mem hx))

lemma Good_X (i : Fin n) (l : Fin n) : Good (k := k) i 0 0 1 (X l) := by
  classical
  refine ⟨fun β => ?_, isHomogeneous_X _ _⟩
  rw [coeff_X']
  split_ifs
  · exact ⟨isHomogeneous_one _ _, isWeightedHomogeneous_one _ _⟩
  · exact ⟨isHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _⟩

lemma Good_rowSubst_X (i : Fin n) (v : Fin n × (Fin (k - 1) → Fin n)) :
    Good i (if v.1 = i then 0 else 1) 0 (if v.1 = i then k - 1 else 0)
      (rowSubst (k := k) i (X v)) := by
  classical
  simp only [rowSubst, aeval_X]
  split_ifs with h
  · have := Good_prod i (univ : Finset (Fin (k - 1))) (fun _ => 0) (fun _ => 0) (fun _ => 1)
      (fun s => (X (v.2 s) : MvPolynomial (Fin n) (GenRing n k))) fun s _ => Good_X i _
    simpa using this
  · refine ⟨fun β => ?_, isHomogeneous_C _ _⟩
    rw [coeff_C]
    split_ifs
    · refine ⟨isHomogeneous_X _ _, ?_⟩
      have := isWeightedHomogeneous_X ℚ (rowWeight (k := k) i) v
      simpa [rowWeight, h] using this
    · exact ⟨isHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _⟩

lemma Good_rowSubst_monomial (i : Fin n) (μ : (Fin n × (Fin (k - 1) → Fin n)) →₀ ℕ) :
    Good i (μ.degree - (Finsupp.weight (rowWeight i)) μ) 0
      ((k - 1) * (Finsupp.weight (rowWeight i)) μ) (rowSubst (k := k) i (monomial μ 1)) := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
  have := Good_prod i μ.support (fun v => (if v.1 = i then 0 else 1) * μ v) (fun v => 0 * μ v)
    (fun v => (if v.1 = i then k - 1 else 0) * μ v)
    (fun v => (rowSubst (k := k) i (X v)) ^ μ v)
    fun v _ => Good_pow i (Good_rowSubst_X i v) (μ v)
  have ha : ∑ v ∈ μ.support, (if v.1 = i then 0 else 1) * μ v =
      μ.degree - (Finsupp.weight (rowWeight i)) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply]
    have hsplit : ∀ v ∈ μ.support, μ v = (if v.1 = i then 0 else 1) * μ v + μ v • rowWeight i v := by
      intro v _; simp only [rowWeight, smul_eq_mul]; split_ifs <;> ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    simp
  have hf : ∑ v ∈ μ.support, (if v.1 = i then k - 1 else 0) * μ v =
      (k - 1) * (Finsupp.weight (rowWeight i)) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [rowWeight, smul_eq_mul]; split_ifs <;> ring
  rw [ha, hf] at this
  simpa using this

/-- invariant along the derivatives: like `Good`, with `c` derivatives already applied -/
def GoodC (i : Fin n) (a b f c : ℕ) (p : MvPolynomial (Fin n) (GenRing n k)) : Prop :=
  (∀ β, (coeff β p).IsHomogeneous a ∧ IsWeightedHomogeneous (rowWeight i) (coeff β p) b) ∧
    p.IsHomogeneous (f - c) ∧ (f < c → p = 0)

lemma GoodC_pderiv (i : Fin n) {a b f c : ℕ} (l : Fin n) {p : MvPolynomial (Fin n) (GenRing n k)}
    (hp : GoodC i a b f c p) : GoodC i a b f (c + 1) (pderiv l p) := by
  classical
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun β => ?_, ?_, ?_⟩
  · rw [coeff_pderiv]
    have e : (↑(β l) + 1 : GenRing n k) = C ((β l : ℚ) + 1) := by
      rw [map_add, map_natCast, map_one]
    rw [e]
    have hh := (h1 (β + Finsupp.single l 1)).1.mul (isHomogeneous_C _ ((β l : ℚ) + 1))
    have hw := (h1 (β + Finsupp.single l 1)).2.mul
      (isWeightedHomogeneous_C (rowWeight (k := k) i) ((β l : ℚ) + 1))
    rw [add_zero] at hh hw
    exact ⟨hh, hw⟩
  · by_cases hlt : f < c
    · rw [h3 hlt, map_zero]; exact isHomogeneous_zero _ _ _
    · intro s hs
      rw [coeff_pderiv] at hs
      have h4 := h2 (left_ne_zero_of_mul hs)
      have hd : ∀ u : Fin n →₀ ℕ, (Finsupp.weight 1) u = u.degree := fun u => by
        rw [Finsupp.degree_eq_weight_one]; rfl
      rw [hd, map_add, Finsupp.degree_single] at h4
      rw [hd]; omega
  · intro hlt
    by_cases hlt' : f < c
    · rw [h3 hlt', map_zero]
    · have hfc : f = c := by omega
      refine MvPolynomial.ext _ _ fun s => ?_
      rw [coeff_pderiv, coeff_zero]
      by_contra hs
      have h4 := h2 (left_ne_zero_of_mul hs)
      have hd : ∀ u : Fin n →₀ ℕ, (Finsupp.weight 1) u = u.degree := fun u => by
        rw [Finsupp.degree_eq_weight_one]; rfl
      rw [hd, map_add, Finsupp.degree_single] at h4
      omega

lemma GoodC_wordL (i : Fin n) {a b f c : ℕ} (l : List (Fin n))
    {p : MvPolynomial (Fin n) (GenRing n k)} (hp : GoodC i a b f c p) :
    GoodC i a b f (c + l.length) (wordL l p) := by
  induction l with
  | nil => simpa [wordL] using hp
  | cons j l ih =>
    have := GoodC_pderiv i j ih
    simpa [wordL, List.length_cons, ← add_assoc] using this

lemma GoodC_smulX (i : Fin n) {a b f c : ℕ} (t : Fin (k - 1) → Fin n)
    {p : MvPolynomial (Fin n) (GenRing n k)} (hp : GoodC i a b f c p) :
    GoodC i (a + 1) (b + 1) f c ((X (i, t) : GenRing n k) • p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun β => ?_, ?_, fun h => by rw [h3 h, smul_zero]⟩
  · rw [coeff_smul, smul_eq_mul, mul_comm]
    refine ⟨(h1 β).1.mul (isHomogeneous_X _ _), (h1 β).2.mul ?_⟩
    have := isWeightedHomogeneous_X ℚ (rowWeight (k := k) i) (i, t)
    simpa [rowWeight] using this
  · rw [smul_eq_C_mul]; simpa using (isHomogeneous_C _ _).mul h2

lemma GoodC_sum (i : Fin n) {a b f c : ℕ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) (GenRing n k)) (h : ∀ x ∈ s, GoodC i a b f c (p x)) :
    GoodC i a b f c (∑ x ∈ s, p x) := by
  refine ⟨fun β => ?_, IsHomogeneous.sum _ _ _ fun x hx => (h x hx).2.1,
    fun hlt => sum_eq_zero fun x hx => (h x hx).2.2 hlt⟩
  rw [coeff_sum]
  exact ⟨IsHomogeneous.sum _ _ _ fun x hx => ((h x hx).1 β).1,
    IsWeightedHomogeneous.sum _ _ _ fun x hx => ((h x hx).1 β).2⟩

lemma GoodC_rowOpL (i : Fin n) {a b f c : ℕ} {p : MvPolynomial (Fin n) (GenRing n k)}
    (hp : GoodC i a b f c p) : GoodC i (a + 1) (b + 1) f (c + (k - 1)) (rowOpL i p) := by
  unfold rowOpL
  rw [LinearMap.sum_apply]
  refine GoodC_sum i _ _ fun t _ => ?_
  rw [LinearMap.smul_apply]
  refine GoodC_smulX i t ?_
  simpa using GoodC_wordL i (List.ofFn t) hp

lemma GoodC_rowOpL_pow (i : Fin n) {a b f : ℕ} (m : ℕ) {p : MvPolynomial (Fin n) (GenRing n k)}
    (hp : GoodC i a b f 0 p) : GoodC i (a + m) (b + m) f (m * (k - 1)) ((rowOpL i ^ m) p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := GoodC_rowOpL i ih
    have e1 : a + (m + 1) = a + m + 1 := by ring
    have e2 : b + (m + 1) = b + m + 1 := by ring
    have e3 : (m + 1) * (k - 1) = m * (k - 1) + (k - 1) := by ring
    rw [e1, e2, e3]; exact this

lemma rowProj_monomial (i : Fin n) (hk : 1 ≤ k - 1) (m : ℕ)
    (μ : (Fin n × (Fin (k - 1) → Fin n)) →₀ ℕ) :
    (rowProj i m (monomial μ (1 : ℚ))).IsHomogeneous
        (μ.degree - (Finsupp.weight (rowWeight i)) μ + m) ∧
      ((Finsupp.weight (rowWeight i)) μ ≠ m → rowProj i m (monomial μ (1 : ℚ)) = 0) := by
  have hG := Good_rowSubst_monomial (k := k) i μ
  have hC : GoodC i (μ.degree - (Finsupp.weight (rowWeight i)) μ) 0
      ((k - 1) * (Finsupp.weight (rowWeight i)) μ) 0 (rowSubst (k := k) i (monomial μ 1)) :=
    ⟨hG.1, by simpa using hG.2, fun h => absurd h (by omega)⟩
  have h := GoodC_rowOpL_pow i m hC
  rw [rowProj_eq, eval_zero, constantCoeff_eq]
  refine ⟨?_, fun hne => ?_⟩
  · rw [smul_eq_C_mul]
    simpa using (isHomogeneous_C _ _).mul (h.1 0).1
  · by_cases hlt : (k - 1) * (Finsupp.weight (rowWeight i)) μ < m * (k - 1)
    · rw [h.2.2 hlt, coeff_zero, smul_zero]
    · have hne' : (k - 1) * (Finsupp.weight (rowWeight i)) μ ≠ m * (k - 1) := by
        intro e
        apply hne
        rw [mul_comm] at e
        exact Nat.eq_of_mul_eq_mul_right (by omega) e
      rw [h.2.1.coeff_eq_zero (by rw [map_zero]; omega), smul_zero]

lemma rowProj_as_sum (i : Fin n) (m : ℕ) (P : GenRing n k) :
    rowProj i m P = ∑ μ ∈ P.support, coeff μ P • rowProj i m (monomial μ 1) := by
  conv_lhs => rw [P.as_sum]
  rw [rowProj_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [← rowProj_smul, smul_monomial, smul_eq_mul, mul_one]

lemma rowProj_homogeneousComponent (i : Fin n) (hk : 1 ≤ k - 1) (m D : ℕ) (P : GenRing n k) :
    homogeneousComponent D (rowProj i m P) = rowProj i m (homogeneousComponent D P) := by
  classical
  rw [rowProj_as_sum, map_sum, homogeneousComponent_apply, rowProj_sum]
  have key : ∀ μ ∈ P.support, homogeneousComponent D (coeff μ P • rowProj i m (monomial μ 1)) =
      if μ.degree = D then coeff μ P • rowProj i m (monomial μ 1) else 0 := by
    intro μ _
    rw [LinearMap.map_smul_of_tower]
    obtain ⟨h1, h2⟩ := rowProj_monomial (k := k) i hk m μ
    by_cases hw : (Finsupp.weight (rowWeight i)) μ = m
    · have hdeg : μ.degree - (Finsupp.weight (rowWeight i)) μ + m = μ.degree := by
        have : (Finsupp.weight (rowWeight i)) μ ≤ μ.degree := by
          rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply]
          refine sum_le_sum fun v _ => ?_
          simp only [rowWeight, smul_eq_mul]; split_ifs <;> simp
        omega
      rw [hdeg] at h1
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr h1)]
      rcases eq_or_ne μ.degree D with hD | hD
      · simp [hD]
      · simp [hD, Ne.symm hD]
    · rw [h2 hw]; simp
  rw [sum_congr rfl key, ← sum_filter]
  refine sum_congr rfl fun μ _ => ?_
  rw [← rowProj_smul, smul_monomial, smul_eq_mul, mul_one]

lemma rowProj_weightedComponent (i : Fin n) (hk : 1 ≤ k - 1) (m : ℕ) (P : GenRing n k) :
    rowProj i m P = rowProj i m (weightedHomogeneousComponent (rowWeight i) m P) := by
  classical
  rw [rowProj_as_sum, weightedHomogeneousComponent_apply, rowProj_sum, ← sum_filter_add_sum_filter_not
    P.support (fun μ => (Finsupp.weight (rowWeight i)) μ = m)]
  have h0 : ∑ μ ∈ P.support with ¬ (Finsupp.weight (rowWeight i)) μ = m,
      coeff μ P • rowProj i m (monomial μ (1 : ℚ)) = 0 :=
    sum_eq_zero fun μ hμ => by
      rw [(rowProj_monomial (k := k) i hk m μ).2 (mem_filter.mp hμ).2, smul_zero]
  rw [h0, add_zero]
  refine sum_congr rfl fun μ _ => ?_
  rw [← rowProj_smul, smul_monomial, smul_eq_mul, mul_one]

lemma rowProj_free_zero (i : Fin n) {g : GenRing n k} (hg : Free i g) : rowProj i 0 g = g := by
  rw [rowProj_eq, rowSubst_free i hg]
  simp

end Proj

/-! ### Naturality -/

section Naturality

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

end Naturality

end GenInvAux

open GenInvAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (i : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k)
        (fun j t => (MvPolynomial.X (j, t) :
          MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ)) res) d =
      ∑ m : Fin (d + 1), (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
        MvPolynomial.eval 0
          ((fun p : MvPolynomial (Fin n) (MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ) =>
              ∑ t : Fin (k - 1) → Fin n, (MvPolynomial.X (i, t) :
                MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ) •
                (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q) p)^[m.val]
            (newtonTr (phiPoly (k := k)
              (fun j t => if j = i then ∏ s, MvPolynomial.X (t s)
                else MvPolynomial.C (MvPolynomial.X (j, t))) res) d)) := by
  classical
  have hr : 1 ≤ k - 1 := by omega
  set Φ := phiPoly (k := k) (genTensor n k) res with hΦdef
  set Q := Φ.eval 1 with hQdef
  set w := rowWeight (k := k) i with hw
  set C0 := weightedHomogeneousComponent w 0 Q with hC0
  have hGr : Gr Φ := Gr_phi res
  have hτhom : ∀ d, ((newtonTr Φ d)).IsHomogeneous d := fun d => newtonTr_hom hGr d
  have hQc : constantCoeff Q = 1 := Q_constantCoeff res hres
  have hC0free : Free i C0 :=
    free_of_wdeg_zero i (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  have hC0c : constantCoeff C0 = 1 := by
    have hQc' : coeff 0 Q = 1 := by rw [← hQc, constantCoeff_eq]
    rw [hC0, constantCoeff_eq, coeff_weightedHomogeneousComponent, map_zero, if_pos rfl, hQc']
  -- triangular induction on the total degree
  have tri : ∀ m, 1 ≤ m → ∀ D, rowProj i m (weightedHomogeneousComponent w m ((newtonTr Φ D))) =
      weightedHomogeneousComponent w m ((newtonTr Φ D)) := by
    intro m hm D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      have K := newtonTr_two_gradings w Q hQc Φ (fun d => phi_coeff_eq res d) m D
      have hS := rowProj_newtonTr_hatPhi n k hk hn res hres i m
      rw [← hΦdef, ← hQdef, ← hw, ← hC0] at hS
      rw [← hC0] at K
      have K' := congrArg (rowProj i m) K
      rw [← rowProj_homogeneousComponent i hr, hS, K, rowProj_sum] at K'
      have hmf : ∀ x : ℕ, rowProj i m (homogeneousComponent (D - x) (C0 ^ m) *
          (((m : ℚ) / x) • weightedHomogeneousComponent w m ((newtonTr Φ x)))) =
          homogeneousComponent (D - x) (C0 ^ m) *
            (((m : ℚ) / x) • rowProj i m (weightedHomogeneousComponent w m ((newtonTr Φ x)))) := fun x => by
        rw [rowProj_mul_free i m (free_homogeneousComponent i (free_pow i hC0free m) (D - x)),
          rowProj_smul]
      simp only [hmf] at K'
      rw [sum_range_succ, sum_range_succ] at K'
      have hlow : ∑ x ∈ range D, homogeneousComponent (D - x) (C0 ^ m) *
            (((m : ℚ) / x) • rowProj i m (weightedHomogeneousComponent w m ((newtonTr Φ x)))) =
          ∑ x ∈ range D, homogeneousComponent (D - x) (C0 ^ m) *
            (((m : ℚ) / x) • weightedHomogeneousComponent w m ((newtonTr Φ x))) :=
        sum_congr rfl fun x hx => by rw [ih x (mem_range.mp hx)]
      rw [hlow, add_left_cancel_iff, Nat.sub_self, homogeneousComponent_zero, ← constantCoeff_eq, map_pow, hC0c,
        one_pow, C_1, one_mul, one_mul] at K'
      by_cases hD : D = 0
      · subst hD
        simp [newtonTr, rowProj_zero]
      · have hne : ((m : ℚ) / D) ≠ 0 := div_ne_zero (by exact_mod_cast (by omega : m ≠ 0))
          (by exact_mod_cast hD)
        exact (smul_right_injective _ hne) K'.symm
  -- assemble
  have hsubst : (fun j t => if j = i then ∏ s, (MvPolynomial.X (t s) :
        MvPolynomial (Fin n) (GenRing n k)) else MvPolynomial.C (MvPolynomial.X (j, t))) =
      fun j t => ((rowSubst (k := k) i : GenRing n k →ₐ[ℚ] _) : GenRing n k →+* _)
        (genTensor n k j t) := by
    funext j t
    simp [rowSubst, genTensor]
  have hgen : (fun j t => (MvPolynomial.X (j, t) : GenRing n k)) = genTensor n k := rfl
  rw [hsubst, phiPoly_map, newtonTr_map, hgen]
  have hterm : ∀ m : Fin (d + 1), (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
      MvPolynomial.eval 0 ((rowOp (k := k) i)^[m.val]
        (((rowSubst (k := k) i : GenRing n k →ₐ[ℚ] _) : GenRing n k →+* _) ((newtonTr Φ d)))) =
      weightedHomogeneousComponent w m.val ((newtonTr Φ d)) := by
    intro m
    have e : (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
        MvPolynomial.eval 0 ((rowOp (k := k) i)^[m.val]
          (((rowSubst (k := k) i : GenRing n k →ₐ[ℚ] _) : GenRing n k →+* _) ((newtonTr Φ d)))) =
        rowProj i m.val ((newtonTr Φ d)) := rfl
    rw [e, rowProj_weightedComponent i hr]
    by_cases hm : m.val = 0
    · rw [hm]
      exact rowProj_free_zero i (free_of_wdeg_zero i
        (weightedHomogeneousComponent_isWeightedHomogeneous _ _))
    · exact tri m.val (by omega) d
  rw [show (fun p : MvPolynomial (Fin n) (GenRing n k) => ∑ t : Fin (k - 1) → Fin n,
      (X (i, t) : GenRing n k) • (List.ofFn t).foldr (fun j q => pderiv j q) p) =
      rowOp (k := k) i from rfl]
  rw [sum_congr rfl fun m _ => hterm m]
  rw [Fin.sum_univ_eq_sum_range (fun m => weightedHomogeneousComponent w m ((newtonTr Φ d)))]
  -- the weighted components above `d` vanish
  have hsum := sum_weightedHomogeneousComponent w ((newtonTr Φ d))
  rw [finsum_eq_sum_of_support_subset _ (s := range (d + 1))] at hsum
  · exact hsum.symm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [coe_range, Set.mem_Iio]
    by_contra hmd
    apply hm
    apply weightedHomogeneousComponent_eq_zero'
    intro μ hμ
    have h1 := hτhom d (mem_support_iff.mp hμ)
    have h2 : (Finsupp.weight w) μ ≤ (Finsupp.weight 1) μ := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
      refine sum_le_sum fun v _ => ?_
      simp only [hw, rowWeight, smul_eq_mul, Pi.one_apply]; split_ifs <;> simp
    omega
