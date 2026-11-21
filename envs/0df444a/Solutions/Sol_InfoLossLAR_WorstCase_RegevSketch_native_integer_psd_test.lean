-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.native_integer_psd_test
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T15:29:22.41549+00:00
-- url     : https://prove2.me/submissions/68bbff5f-1195-4237-bc43-78cc583c0163

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_native_integer_determinant
import Mathlib

section PSDRationalPSD

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace PassFlagsPSD

/-- A rational homogeneous quadratic form is nonnegative on all rational
vectors exactly when it is nonnegative on all integer vectors. -/
theorem quadratic_nonneg_rational_iff_integer {ι : Type*} [Fintype ι]
    (quadratic : (ι → ℚ) → ℚ)
    (homogeneous : ∀ (c : ℚ) (x : ι → ℚ),
      quadratic (fun i => c * x i) = c ^ 2 * quadratic x) :
    (∀ x : ι → ℚ, 0 ≤ quadratic x) ↔
      (∀ z : ι → ℤ, 0 ≤ quadratic (fun i => (z i : ℚ))) := by
  classical
  constructor
  · intro nonneg z
    exact nonneg (fun i => (z i : ℚ))
  · intro nonneg x
    let denominator : ℕ := ∏ i, (x i).den
    let cofactor (i : ι) : ℕ := ∏ j ∈ Finset.univ.erase i, (x j).den
    let z (i : ι) : ℤ := (x i).num * (cofactor i : ℤ)
    have denominator_pos : 0 < denominator := by
      exact Finset.prod_pos (fun i _ => (x i).pos)
    have clears (i : ι) : (z i : ℚ) = (denominator : ℚ) * x i := by
      have factor : (x i).den * cofactor i = denominator :=
        Finset.mul_prod_erase Finset.univ (fun j => (x j).den) (Finset.mem_univ i)
      have den_ne_zero : ((x i).den : ℚ) ≠ 0 := by exact_mod_cast (x i).den_ne_zero
      calc
        (z i : ℚ) = ((x i).den : ℚ) * (cofactor i : ℚ) *
            ((x i).num / ((x i).den : ℚ)) := by
          simp only [z, Int.cast_mul, Int.cast_natCast]
          field_simp
        _ = (denominator : ℚ) * x i := by
          rw [Rat.num_div_den, ← Nat.cast_mul, factor]
    have scaled : 0 ≤ (denominator : ℚ)^2 * quadratic x := by
      simpa only [clears, homogeneous] using nonneg z
    apply nonneg_of_mul_nonneg_right scaled
    positivity


/-- Testing an integer symmetric matrix as rational PSD gives exactly the integer test. -/
theorem rational_posSemidef_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsHermitian) :
    (A.map (fun k => (k : ℚ))).PosSemidef ↔ A.PosSemidef := by
  classical
  let M := A.map (fun k => (k : ℚ))
  have hM : M.IsHermitian := by
    apply IsHermitian.ext
    intro i j
    have hs := Matrix.IsHermitian.ext_iff.mp hA i j
    simpa [M] using congrArg (fun k : ℤ => (k : ℚ)) hs
  let q (x : Fin n → ℚ) := x ⬝ᵥ (M *ᵥ x)
  have homog (c : ℚ) (x : Fin n → ℚ) :
      q (fun i => c * x i) = c^2 * q x := by
    change (c • x) ⬝ᵥ (M *ᵥ (c • x)) = c^2 * (x ⬝ᵥ (M *ᵥ x))
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have hcast (x : Fin n → ℤ) :
      q (fun i => (x i : ℚ)) = ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
    simp only [q,M,dotProduct,mulVec,Matrix.map_apply,Int.cast_sum,Int.cast_mul]
  change M.PosSemidef ↔ A.PosSemidef
  rw [Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.posSemidef_iff_dotProduct_mulVec,
    and_iff_right hM,and_iff_right hA]
  simp only [star_trivial]
  change (∀ x, 0 ≤ q x) ↔ _
  rw [quadratic_nonneg_rational_iff_integer q homog]
  apply forall_congr'
  intro x
  rw [hcast]
  exact_mod_cast Iff.rfl

end PassFlagsPSD

end PSDRationalPSD

section PSDCriterion

open Matrix Polynomial
open scoped BigOperators Pointwise
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NativePSDCriterion

private theorem int_real_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : S.IsHermitian) :
    (S.map (Int.castRingHom ℝ)).PosSemidef ↔ S.PosSemidef := by
  let R := S.map (Int.castRingHom ℝ)
  let Q := S.map (fun k => (k : ℚ))
  have hR : R.IsHermitian := by
    apply IsHermitian.ext
    intro i j
    have h := hS.apply i j
    simpa [R] using congrArg (fun z : ℤ => (z : ℝ)) h
  have hQ : Q.IsHermitian := by
    apply IsHermitian.ext
    intro i j
    have h := hS.apply i j
    simpa [Q] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [← PassFlagsPSD.rational_posSemidef_iff S hS]
  change R.PosSemidef ↔ Q.PosSemidef
  rw [posSemidef_iff_dotProduct_mulVec,posSemidef_iff_dotProduct_mulVec,
    and_iff_right hR,and_iff_right hQ]
  simp only [star_trivial]
  let lift : (Fin n → ℚ) → (Fin n → ℝ) := fun x i => x i
  have hcast (x : Fin n → ℚ) :
      (lift x) ⬝ᵥ (R *ᵥ (lift x)) = ((x ⬝ᵥ (Q *ᵥ x) : ℚ) : ℝ) := by
    simp [dotProduct,mulVec,R,Q,lift]
  constructor
  · intro h x
    have hh := h (lift x)
    rw [hcast] at hh
    exact_mod_cast hh
  · intro h x
    have hd : DenseRange lift := DenseRange.piMap (fun _ => Rat.denseRange_cast)
    apply hd.induction_on (p := fun y => 0 ≤ y ⬝ᵥ (R *ᵥ y)) x
    · apply isClosed_le continuous_const
      simp only [dotProduct,mulVec]
      fun_prop
    · intro a
      rw [hcast]
      exact_mod_cast h a

private theorem prod_coeff_nonneg {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (h : ∀ i ∈ s, ∀ k, 0 ≤ (p i).coeff k) :
    ∀ k, 0 ≤ (∏ i ∈ s, p i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro k; simp [Polynomial.coeff_one]; split_ifs <;> norm_num
  | @insert i s hi ih =>
    intro k
    rw [Finset.prod_insert hi, coeff_mul]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (h i (by simp) _) (ih (fun j hj => h j (by simp [hj])) _)

private theorem real_criterion {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsHermitian) :
    S.PosSemidef ↔ ∀ i : Fin (n+1), 0 ≤ (-S).charpoly.coeff i.val := by
  have hdeg : (-S).charpoly.natDegree = n := by simp
  constructor
  · intro hs
    have hnonpos (i : Fin n) : hS.neg.eigenvalues i ≤ 0 := by
      have hi : hS.neg.eigenvalues i ∈ spectrum ℝ (-S) := by
        rw [hS.neg.spectrum_real_eq_range_eigenvalues]
        exact ⟨i,rfl⟩
      rw [← spectrum.neg_eq, Set.mem_neg] at hi
      have hh := (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hs).2 hi
      exact neg_nonneg.mp hh
    intro k
    rw [hS.neg.charpoly_eq]
    apply prod_coeff_nonneg
    intro i _ j
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C, RCLike.ofReal_real_eq_id,
      id_eq]
    split_ifs <;> linarith [hnonpos i]
  · intro hc
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨hS, ?_⟩
    intro x hx
    change 0 ≤ x
    by_contra! hneg
    have hm : -x ∈ spectrum ℝ (-S) := by
      rw [← spectrum.neg_eq,Set.mem_neg,neg_neg]
      exact hx
    have hz := Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly.mp hm
    have hp : 0 < (-S).charpoly.eval (-x) := by
      rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ]
      apply add_pos_of_nonneg_of_pos
      · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hc ⟨i, by have := Finset.mem_range.mp hi; omega⟩)
          (pow_nonneg (by linarith) _))
      · rw [show (-S).charpoly.coeff n = 1 by simpa only [hdeg] using (-S).charpoly_monic.coeff_natDegree, one_mul]
        exact pow_pos (by linarith) _
    exact hz (isUnit_iff_ne_zero.mpr hp.ne')

theorem coeff_psd_iff {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : S.IsHermitian) :
    (∀ i : Fin (n+1), 0 ≤ (-S).charpoly.coeff i.val) ↔ S.PosSemidef := by
  let R := S.map (Int.castRingHom ℝ)
  have hR : R.IsHermitian := by
    apply IsHermitian.ext
    intro i j
    simpa [R] using congrArg (fun z : ℤ => (z : ℝ)) (hS.apply i j)
  rw [← int_real_psd S hS, real_criterion R hR]
  apply forall_congr'
  intro i
  have he : -R = (-S).map (Int.castRingHom ℝ) := by ext; simp [R]
  rw [he, Matrix.charpoly_map, Polynomial.coeff_map]
  change (0 ≤ _) ↔ (0 : ℝ) ≤ (((-S).charpoly.coeff i.val : ℤ) : ℝ)
  exact_mod_cast Iff.rfl

end NativePSDCriterion

end PSDCriterion

section PSDInterpolate

set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
namespace NativePSDCriterion

def V (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ := vandermonde fun i => (i.val : ℤ)

theorem V_pos (n : ℕ) : 0 < (V n).det := by
  rw [V, det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  apply sub_pos.mpr
  have h : i < j := Finset.mem_Ioi.mp hj
  exact_mod_cast (show i.val < j.val from h)

def sample {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) : ℤ :=
  (Matrix.scalar (Fin n) (t : ℤ) + S).det

theorem sample_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (t : Fin (n+1)) :
    sample S t.val = ∑ k : Fin (n+1), (-S).charpoly.coeff k.val • V n t k := by
  have he := Polynomial.eval_eq_sum_range (p := (-S).charpoly) (t.val : ℤ)
  rw [Matrix.eval_charpoly] at he
  simp only [sub_neg_eq_add, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at he
  rw [sample, he, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]
  rfl

theorem interpolation_sign {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (j : Fin (n+1)) :
    0 ≤ ((V n).updateCol j (fun t => sample S t.val)).det ↔ 0 ≤ (-S).charpoly.coeff j.val := by
  simp_rw [sample_eq]
  rw [Matrix.det_updateCol_sum, smul_eq_mul]
  exact mul_nonneg_iff_of_pos_right (V_pos n)
end NativePSDCriterion

end PSDInterpolate

section PSDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NativePSDCriterion
abbrev Rows := List (List ℤ)

def rangeOf (x : Rows) : List ℕ := List.range x.length
@[fun_prop] theorem rangeOf_poly : Poly rangeOf := Poly.list_indices

def more (x : Rows) : List ℕ := rangeOf (x ++ [[]])
@[fun_prop] theorem more_poly : Poly more := by unfold more; fun_prop

def entry (x : Rows × ℕ × ℕ) : ℤ := (x.1[x.2.1]?.getD [])[x.2.2]?.getD 0
@[fun_prop] theorem entry_poly : Poly entry := by unfold entry; fun_prop

def allOn (slots : List ℕ) (test : ℕ → Bool) : Bool :=
  decide ((slots.filter test).length = slots.length)

theorem allOn_eq (slots : List ℕ) (test : ℕ → Bool) :
    allOn slots test = true ↔ ∀ i ∈ slots, test i = true := by
  simp only [allOn,decide_eq_true_eq,List.length_filter_eq_length_iff]

def isSymm (x : Rows) : Bool :=
  allOn (rangeOf x) fun i => allOn (rangeOf x) fun j => decide (entry (x,i,j) = entry (x,j,i))
@[fun_prop] theorem isSymm_poly : Poly isSymm := by unfold isSymm allOn; fun_prop

def shifted (x : Rows × ℕ) : Rows :=
  (rangeOf x.1).map fun i => (rangeOf x.1).map fun j =>
    (if i = j then (x.2 : ℤ) else 0) + entry (x.1,i,j)
@[fun_prop] theorem shifted_poly : Poly shifted := by unfold shifted; fun_prop

def powerBlock (x : List ℕ × ℕ × ℕ) : Rows :=
  let slots := x.1.take x.2.2
  slots.map fun a => slots.map fun b => if a = b then (x.2.1 : ℤ) else 0
@[fun_prop] theorem powerBlock_poly : Poly powerBlock := by
  have ht : Poly (fun x : List ℕ × ℕ × ℕ => x.1.take x.2.2) :=
    Poly.comp (f := fun z : List ℕ × ℕ => z.1.take z.2) (g := fun x : List ℕ × ℕ × ℕ => (x.1,x.2.2))
      Integration9_9.TM2NativeFiniteDraw.take_poly (by fun_prop)
  unfold powerBlock
  fun_prop

def system (det : Rows → ℤ) (x : Rows × ℕ) : Rows :=
  let slots := more x.1
  slots.map fun i => slots.map fun j =>
    if j = x.2 then det (shifted (x.1,i)) else det (powerBlock (slots,i,j))
theorem system_poly (det : Rows → ℤ) (h : Poly det) : Poly (system det) := by unfold system; fun_prop

def nativeTest (det : Rows → ℤ) (x : Rows) : Bool :=
  isSymm x && allOn (more x) (fun i => decide (0 ≤ det (system det (x,i))))
theorem nativeTest_poly (det : Rows → ℤ) (h : Poly det) : Poly (nativeTest det) := by
  have hs := system_poly det h
  unfold nativeTest allOn
  fun_prop

end NativePSDCriterion

end PSDNative

section PSDCorrect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators
namespace NativePSDCriterion

def rowsOf {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) : Rows :=
  List.ofFn fun a => List.ofFn (fun b => S a b)
variable {n : ℕ}
@[simp] theorem entry_rows (S : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    entry (rowsOf S,i.val,j.val) = S i j := by simp [entry,rowsOf]

private theorem range_map {α : Type} {k : ℕ} (f : ℕ → α) :
    (List.range k).map f = List.ofFn (fun i : Fin k => f i.val) := by
  apply List.ext_getElem <;> simp

theorem symm_iff (S : Matrix (Fin n) (Fin n) ℤ) :
    isSymm (rowsOf S) = true ↔ S.IsHermitian := by
  simp only [isSymm,allOn_eq,rangeOf,rowsOf,List.length_ofFn,List.mem_range,decide_eq_true_eq]
  rw [Matrix.IsHermitian.ext_iff]
  simp only [star_trivial]
  constructor
  · intro h i j
    exact entry_rows S j i ▸ entry_rows S i j ▸ h j.val j.isLt i.val i.isLt
  · intro h i hi j hj
    change entry (rowsOf S, (⟨i,hi⟩ : Fin n).val, (⟨j,hj⟩ : Fin n).val) =
      entry (rowsOf S, (⟨j,hj⟩ : Fin n).val, (⟨i,hi⟩ : Fin n).val)
    exact (entry_rows S ⟨i,hi⟩ ⟨j,hj⟩).trans ((h ⟨j,hj⟩ ⟨i,hi⟩).trans (entry_rows S ⟨j,hj⟩ ⟨i,hi⟩).symm)

theorem shifted_rows (S : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    shifted (rowsOf S,t) = rowsOf (Matrix.scalar (Fin n) (t : ℤ) + S) := by
  have h : rangeOf (rowsOf S) = List.range n := by simp [rangeOf,rowsOf]
  simp only [shifted,h,range_map,entry_rows,Fin.val_inj]
  simp only [rowsOf,Matrix.add_apply,Matrix.scalar_apply,Matrix.diagonal_apply]
  
theorem more_rows (S : Matrix (Fin n) (Fin n) ℤ) : more (rowsOf S) = List.range (n+1) := by
  simp [more,rangeOf,rowsOf]

theorem power_rows (t j : ℕ) (hj : j ≤ n+1) :
    powerBlock (List.range (n+1),t,j) = rowsOf (Matrix.scalar (Fin j) (t : ℤ)) := by
  simp only [powerBlock,List.take_range,Nat.min_eq_left hj,range_map,rowsOf,
    Matrix.scalar_apply,Matrix.diagonal_apply,Fin.val_inj]

variable (det : Rows → ℤ) (hd : ∀ (k : ℕ) (S : Matrix (Fin k) (Fin k) ℤ), det (rowsOf S) = S.det)

include hd

theorem system_rows (S : Matrix (Fin n) (Fin n) ℤ) (j : Fin (n+1)) :
    system det (rowsOf S,j.val) = rowsOf ((V n).updateCol j (fun t => sample S t.val)) := by
  simp only [system,more_rows,range_map]
  unfold rowsOf
  congr 1
  funext a
  congr 1
  funext b
  change (if b.val = j.val then det (shifted (rowsOf S,a.val))
    else det (powerBlock (List.range (n+1),a.val,b.val))) = _
  rw [shifted_rows, hd, power_rows a.val b.val b.isLt.le, hd]
  simp only [Matrix.updateCol_apply, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,V,Matrix.vandermonde_apply,Fin.val_inj, sample]

theorem nativeTest_correct (S : Matrix (Fin n) (Fin n) ℤ) :
    nativeTest det (rowsOf S) = true ↔ S.PosSemidef := by
  simp only [nativeTest, Bool.and_eq_true, symm_iff, more_rows,allOn_eq,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨hs,ht⟩
    apply (coeff_psd_iff S hs).1
    intro j
    apply (interpolation_sign S j).1
    simpa only [system_rows det hd S j, hd] using ht j.val j.isLt
  · intro hs
    refine ⟨hs.isHermitian, ?_⟩
    intro j hj
    let k : Fin (n+1) := ⟨j,hj⟩
    change 0 ≤ det (system det (rowsOf S,k.val))
    rw [system_rows det hd S k,hd,interpolation_sign]
    exact (coeff_psd_iff S hs.isHermitian).2 hs k

end NativePSDCriterion

end PSDCorrect

open OAI.MetricKMedian.Binary.Automatic
open NativePSDCriterion
theorem solution :
    ∃ pos : List (List ℤ) → Bool, Poly pos ∧
      ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℤ),
        (pos (List.ofFn fun a => List.ofFn (S a)) = true ↔ S.PosSemidef) := by
  obtain ⟨det,hpoly,hspec⟩ := InfoLossLAR.WorstCase.RegevSketch.native_integer_determinant
  exact ⟨nativeTest det, nativeTest_poly det hpoly, fun _ S => nativeTest_correct det hspec S⟩
