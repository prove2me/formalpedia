-- Prove2me | solution 1 for HenselianRing.exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T23:36:57.29441+00:00
-- url     : https://prove2.me/submissions/bc8eedd7-995b-484e-b965-30a867c95d66

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Polynomial.Vieta

set_option maxHeartbeats 1600000

noncomputable section

section

section

set_option autoImplicit false

open Polynomial
open scoped BigOperators


namespace PhilipponPolynomialRootSelector

variable {R S ι κ : Type*} [CommRing R] [Fintype ι]

/-- The monic polynomial with prescribed, indexed linear factors. -/
def rootPolynomial (x : ι → R) : R[X] := ∏ i, (X - C (x i))

theorem monic_rootPolynomial (x : ι → R) : (rootPolynomial x).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (x i))

theorem map_rootPolynomial [CommRing S] (f : R →+* S) (x : ι → R) :
    (rootPolynomial x).map f = rootPolynomial (f ∘ x) := by
  simp only [rootPolynomial, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Function.comp_apply]

theorem rootPolynomial_reindex [Fintype κ] (e : ι ≃ κ) (x : κ → R) :
    rootPolynomial (x ∘ e) = rootPolynomial x :=
  Fintype.prod_equiv e _ _ (fun _ => rfl)

section Weights

variable [DecidableEq ι]

/-- Evaluated products with one indexed factor omitted, normalized by `v`. -/
def weights (x : ι → R) (a v : R) (i : ι) : R :=
  v * ∏ j ∈ Finset.univ.erase i, (a - x j)

theorem map_weights [CommRing S] (f : R →+* S) (x : ι → R) (a v : R) (i : ι) :
    f (weights x a v i) = weights (f ∘ x) (f a) (f v) i := by
  simp only [weights, map_mul, map_prod, map_sub, Function.comp_apply]

theorem weights_reindex [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (x : κ → R) (a v : R) (i : ι) :
    weights (x ∘ e) a v i = weights x a v (e i) := by
  unfold weights
  congr 1
  apply Finset.prod_equiv e
  · intro j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, e.injective.ne_iff]
  · intro _ _
    rfl

theorem eval_derivative (x : ι → R) (a : R) :
    (rootPolynomial x).derivative.eval a = ∑ i, ∏ j ∈ Finset.univ.erase i, (a - x j) := by
  simp only [rootPolynomial, derivative_prod_finset, derivative_X_sub_C, mul_one,
    eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C]

private theorem weight_mul_difference (x : ι → R) (a v : R) (i : ι)
    (h : (rootPolynomial x).IsRoot a) : weights x a v i * (a - x i) = 0 := by
  have hz : (∏ j, (a - x j)) = 0 := by
    simpa only [IsRoot, rootPolynomial, eval_prod, eval_sub, eval_X, eval_C] using h
  rw [weights, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i), hz, mul_zero]

/-- At a simple root, the normalized omitted-factor products partition `1`
into orthogonal idempotents, even when some indexed roots coincide. -/
theorem complete_weights (x : ι → R) (a v : R) (h : (rootPolynomial x).IsRoot a)
    (hv : v * (rootPolynomial x).derivative.eval a = 1) :
    CompleteOrthogonalIdempotents (weights x a v) := by
  apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
  constructor
  · intro i j hij
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem (fun k => a - x k)
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    change weights x a v i * (v * ∏ k ∈ Finset.univ.erase j, (a - x k)) = 0
    rw [hb]
    calc
      weights x a v i * (v * ((a - x i) * b)) =
          (weights x a v i * (a - x i)) * (v * b) := by ac_rfl
      _ = 0 := by rw [weight_mul_difference x a v i h, zero_mul]
  · rw [eval_derivative] at hv
    simpa only [weights, Finset.mul_sum] using hv

/-- If exactly one indexed value is `1` and the others are `0`, evaluation
at `1` singles out that index. -/
theorem weights_at_one (x : ι → R) (i₀ : ι) (hx : ∀ i, x i = if i = i₀ then 1 else 0) :
    weights x 1 1 = fun i => if i = i₀ then 1 else 0 := by
  funext i
  by_cases hi : i = i₀
  · subst i
    rw [if_pos rfl, weights, one_mul]
    exact Finset.prod_eq_one (fun j hj => by rw [hx, if_neg (Finset.mem_erase.mp hj).1, sub_zero])
  · rw [if_neg hi, weights, one_mul]
    apply Finset.prod_eq_zero (i := i₀) (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ i₀⟩)
    rw [hx, if_pos rfl, sub_self]

end Weights

/-- Combine polynomial values using scalar idempotent weights. -/
def combine (w : ι → R) (p : ι → R[X]) : R[X] := ∑ i, C (w i) * p i

theorem map_combine [CommRing S] (f : R →+* S) (w : ι → R) (p : ι → R[X]) :
    (combine w p).map f = combine (f ∘ w) (fun i => (p i).map f) := by
  simp only [combine, Polynomial.map_sum, Polynomial.map_mul, map_C, Function.comp_apply]

theorem combine_reindex [Fintype κ] (e : ι ≃ κ) (w : κ → R) (p : κ → R[X]) :
    combine (w ∘ e) (p ∘ e) = combine w p :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem combine_mul (w : ι → R) (hw : CompleteOrthogonalIdempotents w) (p q : ι → R[X]) :
    combine w p * combine w q = combine w (fun i => p i * q i) := by
  classical
  unfold combine
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · calc
      (C (w i) * p i) * (C (w i) * q i) = C (w i * w i) * (p i * q i) := by rw [map_mul]; ac_rfl
      _ = _ := by rw [(hw.idem i).eq]
  · intro j _ hji
    calc
      (C (w i) * p i) * (C (w j) * q j) = C (w i * w j) * (p i * q j) := by rw [map_mul]; ac_rfl
      _ = 0 := by rw [hw.ortho (Ne.symm hji), map_zero, zero_mul]
  · simp

theorem combine_const (w : ι → R) (hw : CompleteOrthogonalIdempotents w) (p : R[X]) :
    combine w (fun _ => p) = p := by
  rw [combine, ← Finset.sum_mul, ← map_sum, hw.complete, map_one, one_mul]

theorem monic_combine (w : ι → R) (hw : CompleteOrthogonalIdempotents w) (p : ι → R[X])
    (n : ℕ) (hm : ∀ i, (p i).Monic) (hd : ∀ i, (p i).natDegree = n) :
    (combine w p).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one n
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hz (i : ι) : (p i).coeff k = 0 := coeff_eq_zero_of_natDegree_lt ((hd i).symm ▸ hk)
    simp only [combine, finsetSum_coeff, coeff_C_mul, hz, mul_zero, Finset.sum_const_zero]
  · have h₁ (i : ι) : (p i).coeff n = 1 := (hd i) ▸ (hm i).coeff_natDegree
    simpa only [combine, finsetSum_coeff, coeff_C_mul, h₁, mul_one] using hw.complete

end PhilipponPolynomialRootSelector

end

section

set_option autoImplicit false

open Polynomial


namespace PhilipponSymmetricPolynomialDescent

variable {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}

private def signedCoeff (p : A[X]) (i : Fin n) : A :=
  (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))

private def equiv (A : Type*) [CommRing A] (n : ℕ) :=
  MvPolynomial.esymmAlgEquiv (Fin n) A (Fintype.card_fin n)

/-- Evaluate a symmetric expression in the indexed roots of a polynomial
by substituting the signed coefficients for elementary symmetric functions. -/
def specialize (p : A[X]) : MvPolynomial.symmetricSubalgebra (Fin n) A →+* A :=
  (MvPolynomial.eval₂Hom (RingHom.id A) (signedCoeff p)).comp (equiv A n).symm.toRingHom

private theorem map_signedCoeff (p : A[X]) (f : A →+* B) (x : Fin n → B)
    (h : p.map f = PhilipponPolynomialRootSelector.rootPolynomial x) (i : Fin n) :
    f (signedCoeff p i) = MvPolynomial.eval₂ f x (MvPolynomial.esymm (Fin n) A (i.val + 1)) := by
  let s : Multiset B := Finset.univ.val.map x
  have hs : s.card = n := by simp [s]
  have hn : n - (i.val + 1) ≤ s.card := by rw [hs]; exact Nat.sub_le _ _
  have hv := Multiset.prod_X_sub_C_coeff s hn
  rw [hs, Nat.sub_sub_self (Nat.succ_le_of_lt i.isLt)] at hv
  have hp : (p.map f).coeff (n - (i.val + 1)) = (-1) ^ (i.val + 1) * s.esymm (i.val + 1) := by
    rw [h, PhilipponPolynomialRootSelector.rootPolynomial, Finset.prod_eq_multiset_prod]
    simpa only [s, Multiset.map_map, Function.comp_apply] using hv
  rw [signedCoeff, map_mul, map_pow, map_neg, map_one, ← coeff_map, hp, ← mul_assoc, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow]
  simp only [MvPolynomial.esymm, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]
  exact (Finset.esymm_map_val x Finset.univ (i.val + 1))

/-- Specialization agrees with substitution in any ring supplying an
indexed factorization of the polynomial into linear factors. -/
theorem map_specialize (p : A[X]) (f : A →+* B) (x : Fin n → B)
    (h : p.map f = PhilipponPolynomialRootSelector.rootPolynomial x)
    (q : MvPolynomial.symmetricSubalgebra (Fin n) A) :
    f (specialize p q) = MvPolynomial.eval₂ f x q.val := by
  let e := equiv A n
  let incl := (MvPolynomial.symmetricSubalgebra (Fin n) A).val.toRingHom
  have heval : f.comp (MvPolynomial.eval₂Hom (RingHom.id A) (signedCoeff p)) =
      (MvPolynomial.eval₂Hom f x).comp (incl.comp e.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hc : incl (e (MvPolynomial.C a)) = MvPolynomial.C a := by
        change (e (algebraMap A _ a)).val = _
        rw [AlgEquiv.commutes]
        rfl
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      change f a = MvPolynomial.eval₂ f x (incl (e (MvPolynomial.C a)))
      rw [hc, MvPolynomial.eval₂_C]
    · intro i
      have hc : incl (e (MvPolynomial.X i)) = MvPolynomial.esymm (Fin n) A (i.val + 1) := by
        change (MvPolynomial.esymmAlgHom (Fin n) A n (MvPolynomial.X i)).val = _
        rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_X]
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change f (signedCoeff p i) = MvPolynomial.eval₂ f x (incl (e (MvPolynomial.X i)))
      rw [hc]
      exact map_signedCoeff p f x h i
  have hd := DFunLike.congr_fun heval (e.symm q)
  change f (specialize p q) = MvPolynomial.eval₂ f x (e (e.symm q)).val at hd
  rwa [e.apply_symm_apply] at hd

private theorem coeffs_mem_symmetric (q : Polynomial (MvPolynomial (Fin n) A))
    (hq : ∀ j, (q.coeff j).IsSymmetric) :
    (↑q.coeffs : Set (MvPolynomial (Fin n) A)) ⊆ (MvPolynomial.symmetricSubalgebra (Fin n) A).toSubring := by
  intro a ha
  obtain ⟨j, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
  exact hq j

/-- Specialize all the coefficients of a polynomial that are symmetric in
one common tuple of indexed roots. -/
def specializePolynomial (p : A[X]) (q : Polynomial (MvPolynomial (Fin n) A))
    (hq : ∀ j, (q.coeff j).IsSymmetric) : A[X] :=
  (q.toSubring _ (coeffs_mem_symmetric q hq)).map (specialize p)

theorem map_specializePolynomial (p : A[X]) (f : A →+* B) (x : Fin n → B)
    (h : p.map f = PhilipponPolynomialRootSelector.rootPolynomial x)
    (q : Polynomial (MvPolynomial (Fin n) A)) (hq : ∀ j, (q.coeff j).IsSymmetric) :
    (specializePolynomial p q hq).map f = q.map (MvPolynomial.eval₂Hom f x) := by
  ext j
  simp only [specializePolynomial, coeff_map]
  rw [map_specialize p f x h, coeff_toSubring']
  rfl

end PhilipponSymmetricPolynomialDescent

end

section

set_option autoImplicit false

open Polynomial
open PhilipponPolynomialRootSelector
open scoped BigOperators


namespace PhilipponHenselFactorResolvent

abbrev Subsets (σ : Type*) (n : ℕ) := {s : Finset σ // s.card = n}

noncomputable instance {σ : Type*} [Fintype σ] (n : ℕ) : Fintype (Subsets σ n) :=
  Fintype.ofFinite _

private def subsetCongr {σ τ : Type*} (e : σ ≃ τ) (n : ℕ) : Subsets σ n ≃ Subsets τ n :=
  Equiv.subtypeEquiv e.finsetCongr (by intro s; simp [Equiv.finsetCongr_apply])

variable {R S σ τ : Type*} [CommRing R] [Fintype σ]

/-- The product of the indexed roots in a subset of the specified size. -/
def subproduct (x : σ → R) {n : ℕ} (s : Subsets σ n) : R := ∏ i ∈ s.val, x i

/-- The resolvent whose indexed roots are the products over the subsets. -/
def resolvent (x : σ → R) (n : ℕ) : R[X] := rootPolynomial (subproduct x : Subsets σ n → R)

theorem monic_resolvent (x : σ → R) (n : ℕ) : (resolvent x n).Monic :=
  monic_rootPolynomial _

omit [Fintype σ] in
private theorem map_subproduct [CommRing S] (f : R →+* S) (x : σ → R)
    {n : ℕ} (s : Subsets σ n) : f (subproduct x s) = subproduct (f ∘ x) s := by
  simp only [subproduct, map_prod, Function.comp_apply]

omit [Fintype σ] in
private theorem subproduct_reindex (e : σ ≃ τ) (x : τ → R)
    {n : ℕ} (s : Subsets σ n) : subproduct (x ∘ e) s = subproduct x (subsetCongr e n s) := by
  unfold subproduct subsetCongr
  exact (Finset.prod_map s.val e.toEmbedding x).symm

theorem map_resolvent [CommRing S] (f : R →+* S) (x : σ → R) (n : ℕ) :
    (resolvent x n).map f = resolvent (f ∘ x) n := by
  unfold resolvent
  rw [map_rootPolynomial]
  congr 1
  funext s
  exact map_subproduct f x s

theorem resolvent_reindex [Fintype τ] (e : σ ≃ τ) (x : τ → R) (n : ℕ) :
    resolvent (x ∘ e) n = resolvent x n := by
  unfold resolvent
  have h : (subproduct (x ∘ e) : Subsets σ n → R) = subproduct x ∘ subsetCongr e n :=
    funext (subproduct_reindex e x)
  rw [h, rootPolynomial_reindex]

/-- Each coefficient of the universal resolvent is symmetric in the roots. -/
theorem symmetric_resolvent_coeff (n k : ℕ) :
    ((resolvent (MvPolynomial.X : σ → MvPolynomial σ R) n).coeff k).IsSymmetric := by
  intro e
  change (MvPolynomial.rename e).toRingHom ((resolvent (MvPolynomial.X : σ → MvPolynomial σ R) n).coeff k) = _
  rw [← coeff_map, map_resolvent]
  have he : (MvPolynomial.rename e).toRingHom ∘ (MvPolynomial.X : σ → MvPolynomial σ R) = MvPolynomial.X ∘ e := by
    funext i
    exact MvPolynomial.rename_X e i
  rw [he, resolvent_reindex]

variable [DecidableEq σ]

private def part (keep : Bool) (s : Finset σ) : Finset σ := if keep then s else sᶜ

private def subpolynomial (x : σ → R) (s : Finset σ) : R[X] :=
  ∏ i ∈ s, (X - C (x i))

omit [Fintype σ] [DecidableEq σ] in
private theorem map_subpolynomial [CommRing S] (f : R →+* S) (x : σ → R) (s : Finset σ) :
    (subpolynomial x s).map f = subpolynomial (f ∘ x) s := by
  simp only [subpolynomial, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Function.comp_apply]

private theorem subpolynomial_part_reindex [Fintype τ] [DecidableEq τ]
    (e : σ ≃ τ) (x : τ → R) {n : ℕ} (s : Subsets σ n) (keep : Bool) :
    subpolynomial (x ∘ e) (part keep s.val) =
      subpolynomial x (part keep (subsetCongr e n s).val) := by
  unfold subpolynomial
  apply Finset.prod_equiv e
  · intro i
    cases keep <;> simp [part, subsetCongr, Equiv.finsetCongr_apply]
  · intro _ _
    rfl

/-- The factor selected by a root of the resolvent, or its complementary
factor, via the normalized omitted factors. -/
def selected (x : σ → R) (n : ℕ) (a v : R) (keep : Bool) : R[X] :=
  combine (weights (subproduct x : Subsets σ n → R) a v)
    (fun s => subpolynomial x (part keep s.val))

theorem map_selected [CommRing S] (f : R →+* S) (x : σ → R) (n : ℕ) (a v : R) (keep : Bool) :
    (selected x n a v keep).map f = selected (f ∘ x) n (f a) (f v) keep := by
  unfold selected
  rw [map_combine]
  congr 1
  · funext s
    change f (weights (subproduct x) a v s) = _
    rw [map_weights]
    congr 1
    funext t
    exact map_subproduct f x t
  · funext s
    exact map_subpolynomial f x (part keep s.val)

theorem selected_reindex [Fintype τ] [DecidableEq τ]
    (e : σ ≃ τ) (x : τ → R) (n : ℕ) (a v : R) (keep : Bool) :
    selected (x ∘ e) n a v keep = selected x n a v keep := by
  unfold selected
  rw [← combine_reindex (subsetCongr e n)]
  congr 1
  · have h : (subproduct (x ∘ e) : Subsets σ n → R) = subproduct x ∘ subsetCongr e n :=
      funext (subproduct_reindex e x)
    rw [h]
    funext s
    exact weights_reindex (subsetCongr e n) (subproduct x) a v s
  · funext s
    exact subpolynomial_part_reindex e x s keep

theorem selected_mul (x : σ → R) (n : ℕ) (a v : R)
    (ha : (resolvent x n).IsRoot a) (hv : v * (resolvent x n).derivative.eval a = 1) :
    selected x n a v false * selected x n a v true = rootPolynomial x := by
  have h := complete_weights (subproduct x : Subsets σ n → R) a v ha hv
  unfold selected
  rw [combine_mul _ h]
  have hh (s : Subsets σ n) :
      subpolynomial x (part false s.val) * subpolynomial x (part true s.val) = rootPolynomial x := by
    simp only [subpolynomial, part, Bool.false_eq_true, if_false, if_true, rootPolynomial]
    rw [mul_comm, ← Finset.prod_union disjoint_compl_right, Finset.union_compl]
  simp only [hh]
  exact combine_const _ h _

/-- Symmetry of the selected factor as a polynomial in a tuple of roots. -/
theorem symmetric_selected_coeff (n k : ℕ) (a v : R) (keep : Bool) :
    ((selected (MvPolynomial.X : σ → MvPolynomial σ R) n (MvPolynomial.C a) (MvPolynomial.C v) keep).coeff k).IsSymmetric := by
  intro e
  change (MvPolynomial.rename e).toRingHom ((selected _ n _ _ keep).coeff k) = _
  rw [← coeff_map, map_selected]
  have he : (MvPolynomial.rename e).toRingHom ∘ (MvPolynomial.X : σ → MvPolynomial σ R) = MvPolynomial.X ∘ e := by
    funext i
    exact MvPolynomial.rename_X e i
  have ha : (MvPolynomial.rename e).toRingHom (MvPolynomial.C a) = MvPolynomial.C a := MvPolynomial.rename_C e a
  have hv : (MvPolynomial.rename e).toRingHom (MvPolynomial.C v) = MvPolynomial.C v := MvPolynomial.rename_C e v
  rw [he, ha, hv, selected_reindex]

theorem monic_selected [Nontrivial R] (x : σ → R) (n : ℕ) (a v : R) (keep : Bool)
    (hcard : Fintype.card σ = n + n)
    (ha : (resolvent x n).IsRoot a) (hv : v * (resolvent x n).derivative.eval a = 1) :
    (selected x n a v keep).Monic := by
  unfold selected
  apply monic_combine _ (complete_weights (subproduct x) a v ha hv) _ n
  · intro s
    exact monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (x i))
  · intro s
    unfold subpolynomial
    rw [natDegree_finsetProd_X_sub_C_eq_card]
    cases keep with
    | false => simp [part, Finset.card_compl, hcard, s.property]
    | true => simpa [part] using s.property

/-- The tuple consisting of ones on a specified subset and zeros elsewhere. -/
def indicator (s : Finset σ) (i : σ) : R := if i ∈ s then 1 else 0

omit [Fintype σ] in
private theorem subproduct_indicator {n : ℕ} (s₀ : Subsets σ n) (s : Subsets σ n) :
    subproduct (indicator s₀.val : σ → R) s = if s = s₀ then 1 else 0 := by
  unfold subproduct
  by_cases he : s = s₀
  · subst s
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun i hi => if_pos hi
  · rw [if_neg he]
    have hns : ¬ s.val ⊆ s₀.val := fun hs => he (Subtype.ext
      (Finset.eq_of_subset_of_card_le hs (by rw [s.property, s₀.property])))
    obtain ⟨i, hi, hi₀⟩ := Finset.not_subset.mp hns
    exact Finset.prod_eq_zero hi (if_neg hi₀)

private theorem subpolynomial_indicator {n : ℕ} (s₀ : Subsets σ n) (keep : Bool) :
    subpolynomial (indicator s₀.val : σ → R) (part keep s₀.val) =
      if keep then (X - 1) ^ n else X ^ (Fintype.card σ - n) := by
  cases keep with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    change (∏ i ∈ s₀.valᶜ, (X - C (indicator s₀.val i : R))) = _
    calc
      _ = ∏ _i ∈ s₀.valᶜ, (X : R[X]) := Finset.prod_congr rfl fun i hi => by
        rw [indicator, if_neg (Finset.mem_compl.mp hi), C_0, sub_zero]
      _ = _ := by rw [Finset.prod_const, Finset.card_compl, s₀.property]
  | true =>
    simp only [if_true]
    change (∏ i ∈ s₀.val, (X - C (indicator s₀.val i : R))) = _
    calc
      _ = ∏ _i ∈ s₀.val, (X - 1 : R[X]) := Finset.prod_congr rfl fun i hi => by
        rw [indicator, if_pos hi, C_1]
      _ = _ := by rw [Finset.prod_const, s₀.property]

theorem rootPolynomial_indicator {n : ℕ} (s₀ : Subsets σ n) :
    rootPolynomial (indicator s₀.val : σ → R) = X ^ (Fintype.card σ - n) * (X - 1) ^ n := by
  have h : subpolynomial (indicator s₀.val : σ → R) (part false s₀.val) *
      subpolynomial (indicator s₀.val : σ → R) (part true s₀.val) = rootPolynomial (indicator s₀.val) := by
    simp only [part, Bool.false_eq_true, if_false, if_true, subpolynomial, rootPolynomial]
    rw [mul_comm, ← Finset.prod_union disjoint_compl_right, Finset.union_compl]
  rw [subpolynomial_indicator s₀ false, subpolynomial_indicator s₀ true] at h
  exact h.symm

theorem resolvent_indicator_simple_root {n : ℕ} (s₀ : Subsets σ n) :
    (resolvent (indicator s₀.val : σ → R) n).IsRoot 1 ∧
      (resolvent (indicator s₀.val : σ → R) n).derivative.eval 1 = 1 := by
  let x : Subsets σ n → R := subproduct (indicator s₀.val)
  have hx : ∀ s, x s = if s = s₀ then 1 else 0 := subproduct_indicator s₀
  constructor
  · change (rootPolynomial x).eval 1 = 0
    rw [rootPolynomial, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ s₀)
    rw [eval_sub, eval_X, eval_C, hx s₀, if_pos rfl, sub_self]
  · change (rootPolynomial x).derivative.eval 1 = 1
    rw [eval_derivative]
    have ht := congrArg (fun w : Subsets σ n → R => ∑ s, w s) (weights_at_one x s₀ hx)
    simpa [weights] using ht

theorem selected_indicator {n : ℕ} (s₀ : Subsets σ n) (keep : Bool) :
    selected (indicator s₀.val : σ → R) n 1 1 keep =
      if keep then (X - 1) ^ n else X ^ (Fintype.card σ - n) := by
  unfold selected
  rw [weights_at_one _ s₀ (subproduct_indicator s₀)]
  unfold combine
  rw [Finset.sum_eq_single s₀]
  · change C (if s₀ = s₀ then (1 : R) else 0) *
      subpolynomial (indicator s₀.val) (part keep s₀.val) = _
    rw [if_pos rfl, C_1, one_mul]
    exact subpolynomial_indicator (R := R) s₀ keep
  · intro i _ hi
    change C (if i = s₀ then (1 : R) else 0) *
      subpolynomial (indicator s₀.val) (part keep i.val) = 0
    rw [if_neg hi, C_0, zero_mul]
  · simp

end PhilipponHenselFactorResolvent

end

section

set_option autoImplicit false

open Polynomial
open PhilipponPolynomialRootSelector (rootPolynomial)
open PhilipponSymmetricPolynomialDescent (specializePolynomial map_specializePolynomial)
open PhilipponHenselFactorResolvent


namespace PhilipponHenselPowerFactorization

universe u

private theorem exists_indexed_roots {A : Type u} [CommRing A] [Nontrivial A]
    (p : A[X]) (hp : p.Monic) {m : ℕ} (hm : p.natDegree = m) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Nontrivial B) (f : A →+* B), Function.Injective f ∧
      ∃ x : Fin m → B, p.map f = rootPolynomial x := by
  obtain ⟨B, _, _, _, _, _, hsplit⟩ := hp.exists_splits_map
  let f := algebraMap A B
  refine ⟨B, inferInstance, inferInstance, f, FaithfulSMul.algebraMap_injective A B, ?_⟩
  obtain ⟨s, hs⟩ := splits_iff_exists_multiset.mp hsplit
  rw [(hp.map f).leadingCoeff, C_1, one_mul] at hs
  have hlen : s.toList.length = m := by
    have h := congrArg natDegree hs
    rw [hp.natDegree_map, hm, natDegree_multiset_prod_X_sub_C_eq_card] at h
    simpa using h.symm
  let x (i : Fin m) := s.toList[(Fin.cast hlen.symm i).val]
  refine ⟨x, ?_⟩
  rw [hs, rootPolynomial]
  calc
    _ = (s.toList.map (fun b => X - C b)).prod := by
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    _ = ∏ i : Fin s.toList.length, (X - C s.toList[i.val]) :=
      (Fin.prod_univ_fun_getElem _ _).symm
    _ = ∏ i : Fin m, (X - C (x i)) :=
      (Fintype.prod_equiv (finCongr hlen.symm) _ _ (fun _ => rfl)).symm

private def specializedResolvent {A : Type*} [CommRing A] (p : A[X]) (m n : ℕ) : A[X] :=
  specializePolynomial p (resolvent (MvPolynomial.X : Fin m → MvPolynomial (Fin m) A) n)
    (symmetric_resolvent_coeff n)

private theorem map_specializedResolvent {A B : Type*} [CommRing A] [CommRing B]
    (p : A[X]) (m n : ℕ) (f : A →+* B) (x : Fin m → B) (h : p.map f = rootPolynomial x) :
    (specializedResolvent p m n).map f = resolvent x n := by
  unfold specializedResolvent
  rw [map_specializePolynomial p f x h, map_resolvent]
  congr 1
  funext i
  exact MvPolynomial.eval₂Hom_X' f x i

private def specializedFactor {A : Type*} [CommRing A] (p : A[X]) (m n : ℕ) (a v : A) (keep : Bool) : A[X] :=
  specializePolynomial p (selected (MvPolynomial.X : Fin m → MvPolynomial (Fin m) A) n
    (MvPolynomial.C a) (MvPolynomial.C v) keep) (fun k => symmetric_selected_coeff n k a v keep)

private theorem map_specializedFactor {A B : Type*} [CommRing A] [CommRing B]
    (p : A[X]) (m n : ℕ) (a v : A) (keep : Bool)
    (f : A →+* B) (x : Fin m → B) (h : p.map f = rootPolynomial x) :
    (specializedFactor p m n a v keep).map f = selected x n (f a) (f v) keep := by
  unfold specializedFactor
  rw [map_specializePolynomial p f x h, map_selected, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
  congr 1
  funext i
  exact MvPolynomial.eval₂Hom_X' f x i

/-- Separate the two groups of roots by the unique simple root of the
subset-product resolvent that reduces to one. -/
theorem exists_factors {A : Type*} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (p : A[X]) (n : ℕ) (hp : p.Monic)
    (hred : p.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ n) :
    ∃ g h : A[X], p = g * h ∧ g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = X ^ n ∧ h.map (Ideal.Quotient.mk I) = (X - 1) ^ n := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · let : Subsingleton A := hA
    exact ⟨1, 1, Subsingleton.elim _ _, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let : Nontrivial A := hA
  let π := Ideal.Quotient.mk I
  have hI := HenselianRing.jac (R := A) (I := I)
  have hproper : I ≠ ⊤ := by
    intro h
    rw [h] at hI
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp (top_unique hI))
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let m := n + n
  have hc : Fintype.card (Fin m) = n + n := Fintype.card_fin m
  have hMd : p.natDegree = m := by
    have hlin : (X - 1 : (A ⧸ I)[X]).Monic := by simpa using monic_X_sub_C (1 : A ⧸ I)
    rw [← hp.natDegree_map π, hred, (monic_X.pow n).natDegree_mul (hlin.pow n),
      natDegree_X_pow, hlin.natDegree_pow]
    have h1 : (X - 1 : (A ⧸ I)[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : A ⧸ I)
    rw [h1, mul_one]
  obtain ⟨B, _, _, f, hf, x, hx⟩ := exists_indexed_roots p hp hMd
  let s : Subsets (Fin m) n := ⟨Finset.univ.map (Fin.natAddEmb n), by simp⟩
  let y : Fin m → A ⧸ I := indicator s.val
  have hy : p.map π = rootPolynomial y := by
    change p.map (Ideal.Quotient.mk I) = rootPolynomial (indicator s.val)
    rw [hred, rootPolynomial_indicator s, hc, Nat.add_sub_cancel]
  let r := specializedResolvent p m n
  have hrB : r.map f = resolvent x n := map_specializedResolvent p m n f x hx
  have hrI : r.map π = resolvent y n := map_specializedResolvent p m n π y hy
  have hrM : r.Monic := monic_of_injective (f := f) hf (hrB.symm ▸ monic_resolvent x n)
  have hsimple := resolvent_indicator_simple_root (R := A ⧸ I) s
  have hr₀ : r.eval 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (r.eval 1) = 0
    rw [← eval_map_apply, map_one, hrI]
    exact hsimple.1
  have hr₁ : π (r.derivative.eval 1) = 1 := by
    rw [← eval_map_apply, map_one, ← derivative_map, hrI]
    exact hsimple.2
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian r hrM 1 hr₀ (by change IsUnit (π _); rw [hr₁]; exact isUnit_one)
  have haMod : π a = 1 := (Ideal.Quotient.eq.mpr haI).trans (map_one π)
  have hdMod : π (r.derivative.eval a) = 1 := by
    rw [← eval_map_apply, haMod, ← derivative_map, hrI]
    exact hsimple.2
  let : IsLocalHom π := isLocalHom_of_le_jacobson_bot I hI
  obtain ⟨u, hu⟩ := (isUnit_map_iff π (r.derivative.eval a)).mp (by rw [hdMod]; exact isUnit_one)
  let v := (↑u⁻¹ : A)
  have hv : v * r.derivative.eval a = 1 := by rw [← hu, Units.inv_mul]
  have hvMod : π v = 1 := by
    have h := congrArg π hv
    rwa [map_mul, hdMod, mul_one, map_one] at h
  have haB : (resolvent x n).IsRoot (f a) := by
    change (resolvent x n).eval (f a) = 0
    rw [← hrB, eval_map_apply, show r.eval a = 0 from ha, map_zero]
  have hvB : f v * (resolvent x n).derivative.eval (f a) = 1 := by
    rw [← hrB, derivative_map, eval_map_apply, ← map_mul, hv, map_one]
  let g := specializedFactor p m n a v false
  let h := specializedFactor p m n a v true
  have hgB := map_specializedFactor p m n a v false f x hx
  have hhB := map_specializedFactor p m n a v true f x hx
  have hmod (keep : Bool) :
      (specializedFactor p m n a v keep).map π = if keep then (X - 1) ^ n else X ^ n := by
    rw [map_specializedFactor p m n a v keep π y hy, haMod, hvMod]
    change selected (indicator s.val : Fin m → A ⧸ I) n 1 1 keep = _
    rw [selected_indicator s, hc, Nat.add_sub_cancel]
  refine ⟨g, h, ?_, ?_, ?_, hmod false, hmod true⟩
  · apply Polynomial.map_injective f hf
    change p.map f = (specializedFactor p m n a v false * specializedFactor p m n a v true).map f
    rw [Polynomial.map_mul, hgB, hhB, selected_mul x n (f a) (f v) haB hvB, hx]
  · exact monic_of_injective (f := f) hf (hgB.symm ▸ monic_selected x n (f a) (f v) false hc haB hvB)
  · exact monic_of_injective (f := f) hf (hhB.symm ▸ monic_selected x n (f a) (f v) true hc haB hvB)

end PhilipponHenselPowerFactorization

end

section

set_option autoImplicit false
open Polynomial
universe u

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (p : A[X]) (n : ℕ) (_ : n ≠ 0) (hp : p.Monic)
    (hred : p.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ n) :
    ∃ g h : A[X], p = g * h ∧ g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = X ^ n ∧ h.map (Ideal.Quotient.mk I) = (X - 1) ^ n := by
  exact PhilipponHenselPowerFactorization.exists_factors I p n hp hred

end

end
