-- Prove2me | solution 1 for KServerConj.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:32:09.799521+00:00
-- url     : https://prove2.me/submissions/687e98e6-3050-49a3-8939-2a5cf73ae2d4

import Definitions.Def_KServerConj_symProd
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Finset.Sym
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

open scoped BigOperators

namespace KServerConj

@[simp] theorem symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, symProd_apply]
    split_ifs <;> ring

theorem symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using symProd_add_left b c a

theorem symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using symProd_smul_left c b a

def symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := symProd_add_right a
      map_smul' c b := symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => symProd_smul_left c a b

@[simp] theorem symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [symProd_apply, Pi.single_apply]

@[simp] theorem sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [symProdBilin, symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [symProd_single_single, Matrix.one_mulVec] using
      sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← symProd_single_single, ← Matrix.mulVec_mulVec, sym2Mat_mulVec_symProd]


end KServerConj

open scoped BigOperators

namespace KServerConj

theorem det_eq_one_of_weight {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (weight : ι → ℕ)
    (h : ∀ i j, weight j ≤ weight i → A i j = (1 : Matrix ι ι R) i j) :
    A.det = 1 := by
  have ht : A.BlockTriangular weight := by
    intro i j hij
    rw [h i j hij.le]
    exact Matrix.one_apply_ne (fun he => (ne_of_lt hij) (congrArg weight he).symm)
  have hb (n : ℕ) : A.toSquareBlock weight n = 1 := by
    ext i j
    change A i.val j.val = (1 : Matrix { a // weight a = n } { a // weight a = n } R) i j
    simpa [Matrix.one_apply, Subtype.ext_iff] using
      h i.val j.val (le_of_eq (j.property.trans i.property.symm))
  simpa [hb] using ht.det

def symCount {ι : Type*} [DecidableEq ι] (a : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => (if i = a then 1 else 0) + (if j = a then 1 else 0), by
    intro i j
    exact Nat.add_comm _ _⟩

@[simp] theorem symCount_mk {ι : Type*} [DecidableEq ι] (a i j : ι) :
    symCount a s(i, j) = (if i = a then 1 else 0) + (if j = a then 1 else 0) := rfl

theorem transvection_col {R : Type*} [CommRing R] {k : ℕ}
    (i j l : Fin k) (c : R) :
    (Matrix.transvection i j c).col l =
      Pi.single l 1 + if l = j then c • Pi.single i 1 else 0 := by
  ext r
  by_cases hl : l = j <;> by_cases hr : r = i <;>
    simp_all [Matrix.transvection, Matrix.col, Matrix.single, Matrix.one_apply,
      Pi.single_apply, eq_comm]

theorem sym2Mat_transvection_weight {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) (p q : Sym2 (Fin k))
    (hw : symCount j q ≤ symCount j p) :
    sym2Mat (Matrix.transvection i j c) p q = (1 : Matrix _ _ R) p q := by
  have hz (z : Sym2 (Fin k)) (hzp : symCount j z < symCount j p) :
      (Pi.single z (1 : R) : Sym2 (Fin k) → R) p = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Sym2 (Fin k) => R)
      (fun he => hzp.ne (congrArg (symCount j) he).symm) (1 : R)
  induction q using Sym2.ind with
  | _ x y =>
    change symProd ((Matrix.transvection i j c).col x)
      ((Matrix.transvection i j c).col y) p = _
    by_cases hx : x = j <;> by_cases hy : y = j
    · have h0 := hz s(i, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      have h1 := hz s(i, j) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, symProd_add_left,
        symProd_add_right, symProd_smul_left, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        show s(j, i) = s(i, j) from Sym2.eq_swap, h0, h1, mul_zero, add_zero]
      simp [hx, hy, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(i, y) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_left, symProd_smul_left, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hx, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(x, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_right, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hy, Matrix.one_apply, Pi.single_apply]
    · simp [transvection_col, hx, hy, symProd_single_single, Matrix.one_apply, Pi.single_apply]

theorem det_sym2Mat_transvection {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) :
    (sym2Mat (Matrix.transvection i j c)).det = 1 := by
  exact det_eq_one_of_weight _ (symCount j) (sym2Mat_transvection_weight i j c hij)


theorem sym2_mk_left_injective {ι : Type*} (i : ι) :
    Function.Injective (fun j : ι => s(i, j)) :=
  fun _ _ h => (Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1)

theorem symCount_eq_zero_of_not_mem_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : Sym2 ι)
    (hp : p ∉ Finset.univ.image (fun j : ι => s(i, j))) : symCount i p = 0 := by
  induction p using Sym2.ind with
  | _ x y =>
    have hx : x ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, congrArg (fun a => s(a, y)) h.symm⟩)
    have hy : y ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, (Sym2.eq_swap : s(i, x) = s(x, i)).trans
        (congrArg (fun a => s(x, a)) h.symm)⟩)
    simp [symCount_mk, hx, hy]

theorem sum_symCount {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ p : Sym2 ι, symCount i p = Fintype.card ι + 1 := by
  have hs : (∑ p ∈ Finset.univ.image (fun j : ι => s(i, j)), symCount i p) =
      ∑ p : Sym2 ι, symCount i p :=
    Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => symCount_eq_zero_of_not_mem_image i p hp)
  rw [← hs, Finset.sum_image (sym2_mk_left_injective i).injOn]
  simp [symCount_mk, Finset.sum_add_distrib]

def symPairMul {ι R : Type*} [CommMonoid R] (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

@[simp] theorem symPairMul_mk {ι R : Type*} [CommMonoid R]
    (d : ι → R) (i j : ι) : symPairMul d s(i, j) = d i * d j := rfl

theorem symPairMul_eq_prod {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) (p : Sym2 ι) :
    symPairMul d p = ∏ i : ι, d i ^ symCount i p := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [symPairMul_mk, symCount_mk, pow_add, Finset.prod_mul_distrib]
    simp only [Finset.prod_pow_boole, Finset.mem_univ, ite_true]

theorem prod_symPairMul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) :
    (∏ p : Sym2 ι, symPairMul d p) = (∏ i : ι, d i) ^ (Fintype.card ι + 1) := by
  simp_rw [symPairMul_eq_prod]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_symCount]
  exact Finset.prod_pow _ _ _

theorem sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    sym2Mat (Matrix.diagonal d) = Matrix.diagonal (symPairMul d) := by
  have hs (i : Fin k) (a : R) :
      (Pi.single i a : Fin k → R) = a • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i a (1 : R)
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [Matrix.mulVec_single_one, sym2Mat_col, Matrix.col_diagonal, symPairMul_mk]
    rw [hs i (d i), hs j (d j), symProd_smul_left, symProd_smul_right,
      symProd_single_single, smul_smul]
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]

theorem det_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    (sym2Mat (Matrix.diagonal d)).det = (Matrix.diagonal d).det ^ (k + 1) := by
  simp only [sym2Mat_diagonal, Matrix.det_diagonal, prod_symPairMul, Fintype.card_fin]

theorem det_sym2Mat {K : Type*} [Field K] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply Matrix.diagonal_transvection_induction
    (fun M : Matrix (Fin k) (Fin k) K => (sym2Mat M).det = M.det ^ (k + 1)) A
  · exact fun d _ => det_sym2Mat_diagonal d
  · intro t
    simpa [Matrix.TransvectionStruct.toMatrix, t.hij] using
      det_sym2Mat_transvection t.i t.j t.c t.hij
  · intro M N hM hN
    rw [sym2Mat_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]


end KServerConj

namespace KServerConj

theorem symProd_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {k : ℕ} (a b : Fin k → R) :
    (fun p => f (symProd a b p)) = symProd (fun i => f (a i)) (fun i => f (b i)) := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [symProd_apply]
    split_ifs <;> simp only [map_mul, map_add]


theorem sym2Mat_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A.map f) = (sym2Mat A).map f := by
  funext p q
  induction q using Sym2.ind with
  | _ i j =>
    exact (congrFun (symProd_map f (A.col i) (A.col j)) p).symm


theorem det_sym2Mat_domain {R : Type*} [CommRing R] [IsDomain R]
    {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_pow, RingHom.map_det, RingHom.map_det]
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← sym2Mat_map]
  exact det_sym2Mat (A.map (algebraMap R (FractionRing R)))


theorem det_sym2Mat_commRing {R : Type*} [CommRing R]
    {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  have h := congrArg
    (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun p : Fin k × Fin k => A p.1 p.2))
    (det_sym2Mat_domain (Matrix.mvPolynomialX (Fin k) (Fin k) ℤ))
  rw [map_pow, RingHom.map_det, RingHom.map_det,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← sym2Mat_map] at h
  simpa only [MvPolynomial.coe_eval₂Hom, Matrix.mvPolynomialX_map_eval₂] using h


end KServerConj

open KServerConj

theorem solution {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  exact det_sym2Mat_commRing A

#print axioms solution
