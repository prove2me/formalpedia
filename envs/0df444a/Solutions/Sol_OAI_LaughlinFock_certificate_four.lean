-- Prove2me | solution 1 for OAI.LaughlinFock.certificate_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:20:54.464699+00:00
-- url     : https://prove2.me/submissions/a96885f7-2b23-406a-a6dc-3d37bd113d4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L025
import Definitions.Def_OAIQ084L026
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L035
import Definitions.Def_OAIQ084L036
import Definitions.Def_OAIQ084L037
import Definitions.Def_OAIQ084L041
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_5
import Theorems.Thm_OAI_LaughlinFock_fourYChecked_7
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_10
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_11
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_12
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_13
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_14
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_15
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_16
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_17
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_18
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_19
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_20
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_21
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_22
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_23
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_8
import Theorems.Thm_OAI_LaughlinFock_integer_certificate_9

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FermionOperators
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fermion Operators. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial


theorem mul_annihilator_apply {Q : ℕ} (M : FockMatrix Q) (j : Orbital Q)
    (A B : Occupation Q) :
    (M * annihilator Q j) A B =
      if j ∈ B then M A (B.erase j) * fermionSign j B else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ B
  · simp [annihilator, hj, mul_ite, fermionSign]
  · simp [annihilator, hj]


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SphereScaling
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sphere Scaling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology

theorem occupationDiagonal_inv_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonalInv Q d * occupationDiagonal Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext A
  exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

theorem occupationDiagonal_mul_inv (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonal Q d * occupationDiagonalInv Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext A
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

 
theorem annihilator_mul_occupationDiagonal (Q : ℕ) (d : Orbital Q → ℂ)
    (j : Orbital Q) :
    annihilator Q j * occupationDiagonal Q d =
      d j • (occupationDiagonal Q d * annihilator Q j) := by
  ext A B
  simp only [occupationDiagonal, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.diagonal_mul, smul_eq_mul]
  by_cases h : j ∈ B ∧ A = B.erase j
  · obtain ⟨hj, rfl⟩ := h
    simp only [annihilator, hj, and_self, ite_true, if_true]
    rw [← Finset.mul_prod_erase B d hj]
    ring
  · simp [annihilator, h]


theorem diagonalConjugate_annihilator (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (j : Orbital Q) :
    diagonalConjugate Q d (annihilator Q j) = d j • annihilator Q j := by
  rw [diagonalConjugate, Matrix.mul_assoc, annihilator_mul_occupationDiagonal,
    Matrix.mul_smul, ← Matrix.mul_assoc, occupationDiagonal_inv_mul Q d hd,
    Matrix.one_mul]

theorem diagonalConjugate_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (A B : FockMatrix Q) :
    diagonalConjugate Q d (A * B) =
      diagonalConjugate Q d A * diagonalConjugate Q d B := by
  symm
  unfold diagonalConjugate
  calc
    _ = occupationDiagonalInv Q d * A *
        (occupationDiagonal Q d * occupationDiagonalInv Q d) * B *
        occupationDiagonal Q d := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [occupationDiagonal_mul_inv Q d hd]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]

theorem diagonalConjugate_sum (Q : ℕ) (d : Orbital Q → ℂ) {ι : Type*}
    (s : Finset ι) (A : ι → FockMatrix Q) :
    diagonalConjugate Q d (∑ i ∈ s, A i) = ∑ i ∈ s, diagonalConjugate Q d (A i) := by
  simp only [diagonalConjugate, Matrix.mul_sum, Matrix.sum_mul]

theorem diagonalConjugate_smul (Q : ℕ) (d : Orbital Q → ℂ) (a : ℂ) (A : FockMatrix Q) :
    diagonalConjugate Q d (a • A) = a • diagonalConjugate Q d A := by
  simp only [diagonalConjugate, Matrix.mul_smul, Matrix.smul_mul]


theorem diagonalConjugate_pair (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (a : Orbital Q → Orbital Q → ℂ) :
    diagonalConjugate Q d (coefficientPairAnnihilator Q a) =
      coefficientPairAnnihilator Q (fun i j => a i j * d i * d j) := by
  unfold coefficientPairAnnihilator
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [diagonalConjugate_smul, diagonalConjugate_mul Q d hd,
      diagonalConjugate_annihilator Q d hd, diagonalConjugate_annihilator Q d hd,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · exact diagonalConjugate_zero Q d

open Filter Topology


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators



theorem increasingPair_sum {X : Type*} [AddCommMonoid X] (Q : ℕ)
    (f : Orbital Q → Orbital Q → X) :
    (∑ ij : IncreasingPair Q, f ij.val.1 ij.val.2) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, if i<j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun ij : Orbital Q × Orbital Q => ij.1 < ij.2)) (by intro ij; simp)
      (fun ij : Orbital Q × Orbital Q => f ij.1 ij.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem basisAnnihilator_pair {Q : ℕ} (i j : Orbital Q) (hij : i<j) :
    basisAnnihilator Q {i,j} = annihilator Q j * annihilator Q i := by
  simp only [basisAnnihilator, sort_pair i j hij, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem coefficientPair_basis_expansion (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
      a ij.val.1 ij.val.2 • basisAnnihilator Q (increasingPairSector Q ij).val := by
  change coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
    a ij.val.1 ij.val.2 • basisAnnihilator Q {ij.val.1,ij.val.2}
  rw [increasingPair_sum Q (fun i j => a i j • basisAnnihilator Q {i,j})]
  unfold coefficientPairAnnihilator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [basisAnnihilator_pair i j hij]
  · rfl

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Polynomial


theorem couplingPolynomial_rescale (c u v : ℝ) (_hu : u ≠ 0) (hv : v ≠ 0)
    (hc : c*u^2 = v^2) (z k : ℕ) :
    couplingPolynomial u v z k =
      C (v^z*u^k) * (((X-1)^z*(C c*X+1)^k).comp (C (u/v)*X)) := by
  have h1 : (C v : Polynomial ℝ) * (C (u/v)*X-1) = C u*X-C v := by
    simp only [mul_sub, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    field_simp
  have h2 : (C u : Polynomial ℝ) * (C c*(C (u/v)*X)+1) = C v*X+C u := by
    simp only [mul_add, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    congr 1
    field_simp
    nlinarith only [hc]
  simp only [couplingPolynomial, mul_comp, pow_comp, sub_comp, add_comp, X_comp,
    one_comp, C_comp]
  rw [show C (v^z*u^k) = (C v)^z*(C u)^k by simp, mul_mul_mul_comm,
    ← mul_pow, ← mul_pow, h1, h2]

theorem polynomialCouplingCoefficient_rescale (c u v : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : c*u^2=v^2) (z k p : ℕ) :
    polynomialCouplingCoefficient u v z k p =
      (((X-1)^z*(C c*X+1)^k : Polynomial ℝ).coeff p) *
      (monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
        (v^z*u^k*(u/v)^p)) := by
  simp only [polynomialCouplingCoefficient, monomialCoefficient,
    couplingPolynomial_rescale c u v hu hv hc, coeff_C_mul, comp_C_mul_X_coeff]
  ring

theorem rationalCoupling_real (c : ℚ) (z k p : ℕ) :
    (((X-1)^z * (C (c : ℝ)*X+1)^k) : Polynomial ℝ).coeff p =
      (rationalCoupling c z k p : ℝ) := by
  have h : (((X-1)^z * (C c*X+1)^k) : Polynomial ℚ).map (algebraMap ℚ ℝ) =
      ((X-1)^z*(C (c:ℝ)*X+1)^k) := by simp
  rw [← h, Polynomial.coeff_map]
  rfl

 

theorem polynomialCouplingCoefficient_rational (c : ℚ) (hc : 0 < c)
    (z k p : ℕ) :
    polynomialCouplingCoefficient (Real.sqrt (1/(1+(c:ℝ))))
      (Real.sqrt ((c:ℝ)/(1+(c:ℝ)))) z k p =
      (rationalCoupling c z k p : ℝ) * Real.sqrt (rationalCouplingWeight c z k p : ℝ) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hC : (0:ℝ) < 1+(c:ℝ) := by linarith
  let u := Real.sqrt (1/(1+(c:ℝ)))
  let v := Real.sqrt ((c:ℝ)/(1+(c:ℝ)))
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos zero_lt_one hC)
  have hv : 0 < v := Real.sqrt_pos.mpr (div_pos hcR hC)
  have hu2 : u^2 = 1/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have hv2 : v^2 = (c:ℝ)/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have huv2 : (u/v)^2 = 1/(c:ℝ) := by
    rw [div_pow, hu2, hv2]
    field_simp
  rw [polynomialCouplingCoefficient_rescale (c:ℝ) u v hu.ne' hv.ne'
    (by rw [hu2, hv2]; ring), rationalCoupling_real]
  congr 1
  let f : ℝ := monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
      (v^z*u^k*(u/v)^p)
  have hf : 0 ≤ f := by dsimp [f, monomialWeight]; positivity
  have hs : f^2 = (rationalCouplingWeight c z k p : ℝ) := by
    dsimp [f, monomialWeight, rationalCouplingWeight]
    push_cast
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      mul_pow, mul_pow, ← pow_mul, mul_comm z 2, pow_mul, hv2,
      ← pow_mul, mul_comm k 2, pow_mul, hu2,
      ← pow_mul, mul_comm p 2, pow_mul, huv2]
    simp only [div_pow, one_pow, pow_add]
    field_simp
  rw [← hs, Real.sqrt_sq hf]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Three. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem rationalAlphaWeight_pos (t : ℕ) (b : RowEntry t) :
    0 < rationalAlphaWeight t b := by
  unfold rationalAlphaWeight
  positivity

theorem rationalCouplingWeight_pos {c : ℚ} (hc : 0 < c) (z k p : ℕ) :
    0 < rationalCouplingWeight c z k p := by
  unfold rationalCouplingWeight
  positivity



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalFour
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem rationalCopyDiagonal_pos (D r : ℕ) : 0 < rationalCopyDiagonal D r := by
  unfold rationalCopyDiagonal
  positivity

theorem rationalCopyWeight_pos (D T p j k : ℕ) : 0 < rationalCopyWeight D T p j k := by
  unfold rationalCopyWeight
  positivity

theorem couplingWeight_copy {D T r p j k : ℕ} (hr : r ≤ D)
    (hD : D ≤ T) (hw : p+j+k=T) (hrjk : r ≤ j+k) :
    2 * rationalCouplingWeight 1 r (j+k-r) j *
      rationalCouplingWeight 1 (D-r) (T-D) p =
        rationalCopyDiagonal D r * rationalCopyWeight D T p j k := by
  have h1 : r+(j+k-r)=j+k := Nat.add_sub_of_le hrjk
  have h2 : D-r+(T-D)=T-r := by omega
  have h3 : T-r-p=j+k-r := by omega
  have hpow : (2:ℚ)^T = 2^r*2^(T-r) := by rw [← pow_add, Nat.add_sub_of_le (hr.trans hD)]
  unfold rationalCouplingWeight rationalCopyDiagonal rationalCopyWeight
  rw [h1, h2, h3, show j+k-j=k by omega]
  norm_num only [one_pow, one_add_one_eq_two, one_mul]
  simp only [pow_add]
  rw [hpow]
  field_simp

 
theorem planarCopyCoefficient_rational {D T : ℕ} (r : CopyLabel D)
    (p j k : ℕ) (hD : D ≤ T) (hw : p+j+k=T) :
    planarCopyCoefficient D T r.val.val p j k =
      (rationalCopyPolynomial D T r.val.val p j k : ℝ) *
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        Real.sqrt (rationalCopyWeight D T p j k : ℝ)) := by
  have hr : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
  have hCoupling (z n a : ℕ) :
      polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z n a =
        (rationalCoupling 1 z n a : ℝ)*Real.sqrt (rationalCouplingWeight 1 z n a : ℝ) := by
    simpa only [Rat.cast_one, show (1:ℝ)+1=2 by norm_num] using
      polynomialCouplingCoefficient_rational 1 (by norm_num) z n a
  unfold planarCopyCoefficient rationalCopyPolynomial
  by_cases hjk : r.val.val ≤ j+k
  · rw [ite_eq_left ⟨r.property, hr, hD, hjk, hw⟩, ite_eq_left hjk, hCoupling, hCoupling,
      Rat.cast_mul]
    have hs : Real.sqrt 2 * Real.sqrt (rationalCouplingWeight 1 r.val.val (j+k-r.val.val) j : ℝ) *
        Real.sqrt (rationalCouplingWeight 1 (D-r.val.val) (T-D) p : ℝ) =
        Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        Real.sqrt (rationalCopyWeight D T p j k : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2),
        ← Real.sqrt_mul (mul_nonneg (by norm_num) (by
          exact_mod_cast (rationalCouplingWeight_pos (by norm_num : (0:ℚ)<1) r.val.val (j+k-r.val.val) j).le))]
      have hc := congrArg (fun q:ℚ => (q:ℝ)) (couplingWeight_copy hr hD hw hjk)
      push_cast at hc
      rw [hc, Real.sqrt_mul (by exact_mod_cast (rationalCopyDiagonal_pos D r.val.val).le)]
    linear_combination ((rationalCoupling 1 r.val.val (j+k-r.val.val) j : ℝ)*
      (rationalCoupling 1 (D-r.val.val) (T-D) p : ℝ))*hs
  · rw [ite_eq_right (by tauto), ite_eq_right hjk]
    simp


theorem rationalFourFactor_pos {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    0 < rationalFourFactor D b c := by
  unfold rationalFourFactor
  positivity

theorem row_copy_weight_product {t D : ℕ} (b c : RowEntry t) :
    rationalAlphaWeight t b * rationalAlphaWeight t c *
      rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) *
      rationalCopyWeight D (rowFourLevel b c) (rowP c) (rowJ c) (rowI b) =
        (rationalFourFactor D b c)^2 := by
  have h1 : (2:ℚ)^(rowJ b+rowI c) = 2^(rowFourLevel b c)/2^(rowP b) := by
    rw [eq_div_iff (by positivity)]
    rw [← pow_add]
    congr 1
    dsimp [rowFourLevel]
    omega
  have h2 : (2:ℚ)^(rowJ c+rowI b) = 2^(rowFourLevel b c)/2^(rowP c) := by
    rw [eq_div_iff (by positivity)]
    rw [← pow_add]
    congr 1
    have := rowFourLevel_symm b c
    dsimp [rowFourLevel] at *
    omega
  unfold rationalAlphaWeight rationalCopyWeight rationalFourFactor
  rw [pow_add (2:ℚ) (rowJ b+rowI c), pow_add (2:ℚ) (rowJ c+rowI b), h1, h2]
  field_simp


theorem planarRowFourTrace_rational (D : ℕ) (t : Fin 8)
    (ell : ℚ) (a : RowEntry t.val → ℚ) (r s : CopyLabel D) :
    planarRowFourTrace D t.val (rationalComparisonRow t ell a).alpha r s =
      Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
      (rationalFourTrace D t.val a r s : ℝ) *
      Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ) := by
  classical
  unfold planarRowFourTrace rationalFourTrace
  push_cast
  simp only [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hD : D ≤ rowFourLevel b c
  · rw [ite_eq_left hD,
      planarCopyCoefficient_rational r _ _ _ hD rfl,
      planarCopyCoefficient_rational s _ _ _ hD (rowFourLevel_symm c b)]
    have hA : 0 ≤ (rationalAlphaWeight t.val b : ℝ) := by
      exact_mod_cast (rationalAlphaWeight_pos t.val b).le
    have hB : 0 ≤ (rationalAlphaWeight t.val c : ℝ) := by
      exact_mod_cast (rationalAlphaWeight_pos t.val c).le
    have hC : 0 ≤ (rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) : ℝ) := by
      exact_mod_cast (rationalCopyWeight_pos _ _ _ _ _).le
    have hR : Real.sqrt (rationalAlphaWeight t.val b : ℝ) *
        Real.sqrt (rationalAlphaWeight t.val c : ℝ) *
        Real.sqrt (rationalCopyWeight D (rowFourLevel b c) (rowP b) (rowJ b) (rowI c) : ℝ) *
        Real.sqrt (rationalCopyWeight D (rowFourLevel b c) (rowP c) (rowJ c) (rowI b) : ℝ) =
          (rationalFourFactor D b c : ℝ) := by
      rw [← Real.sqrt_mul hA, ← Real.sqrt_mul (mul_nonneg hA hB),
        ← Real.sqrt_mul (mul_nonneg (mul_nonneg hA hB) hC)]
      have hc := congrArg (fun q:ℚ => (q:ℝ)) (row_copy_weight_product (D:=D) b c)
      push_cast at hc
      rw [hc, Real.sqrt_sq (by exact_mod_cast (rationalFourFactor_pos D b c).le)]
    dsimp only [rationalComparisonRow]
    push_cast
    linear_combination ((a b:ℝ)*(a c:ℝ)*
      (rationalCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) : ℝ)*
      (rationalCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b) : ℝ)*
      Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ)*
      Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ))*hR
  · simp [planarCopyCoefficient, hD]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem annihilatorList_vacuum_rational {Q : ℕ} (xs : List (Orbital Q))
    (A : Occupation Q) :
    annihilatorList Q xs ∅ A = (rationalWordVacuum xs A : ℂ) := by
  induction xs generalizing A with
  | nil => by_cases h : A=∅ <;> simp [rationalWordVacuum, h, eq_comm]
  | cons x xs ih =>
    rw [annihilatorList_cons, mul_annihilator_apply]
    simp only [rationalWordVacuum]
    split_ifs <;> simp [ih, fermionSign]

theorem rationalWordVacuum_support {Q : ℕ} (xs : List (Orbital Q))
    (A : Occupation Q) (hn : rationalWordVacuum xs A ≠ 0) :
    xs.Nodup ∧ xs.toFinset=A := by
  induction xs generalizing A with
  | nil => simpa [rationalWordVacuum, eq_comm] using hn
  | cons x xs ih =>
    simp only [rationalWordVacuum] at hn
    split_ifs at hn with hx
    · obtain ⟨hxs,hA⟩ := ih (A.erase x) (fun h => hn (by rw [h, zero_mul]))
      refine ⟨List.nodup_cons.mpr ⟨?_,hxs⟩, ?_⟩
      · intro h
        have : x ∈ A.erase x := by rw [← hA]; simpa using h
        exact Finset.notMem_erase x A this
      · rw [List.toFinset_cons, hA, Finset.insert_erase hx]
    · simp at hn

theorem factorialMode_ne_zero (Q : ℕ) (a : Orbital Q) : factorialMode Q a ≠ 0 := by
  unfold factorialMode
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<a.val.factorial)).ne'

theorem copy_pair_factorial (D : ℕ) (r : CopyLabel D) (p j k x y : ℕ)
    (hpk : p+j+k=D) :
    planarCopyCoefficient D D r.val.val p j k * limitPairCoefficient p x y *
      Real.sqrt (x.factorial:ℝ) * Real.sqrt (y.factorial:ℝ) *
      Real.sqrt (j.factorial:ℝ) * Real.sqrt (k.factorial:ℝ) =
    (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D) *
      (rationalHighestTerm D r p j k x y : ℝ) := by
  unfold rationalHighestTerm limitPairCoefficient
  split_ifs with hxy
  · rw [planarCopyCoefficient_rational r p j k le_rfl hpk]
    have hsq : Real.sqrt (rationalCopyWeight D D p j k : ℝ) *
        Real.sqrt ((p.factorial:ℝ)/(2^p*x.factorial*y.factorial)) *
        Real.sqrt (x.factorial:ℝ) * Real.sqrt (y.factorial:ℝ) *
        Real.sqrt (j.factorial:ℝ) * Real.sqrt (k.factorial:ℝ) =
          Real.sqrt 2 * (p.factorial:ℝ)*j.factorial*k.factorial / 2^D := by
      have hn : 0 ≤ (rationalCopyWeight D D p j k : ℝ) := by
        exact_mod_cast (rationalCopyWeight_pos _ _ _ _ _).le
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      simp only [mul_pow, div_pow]
      rw [Real.sq_sqrt hn, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
      have hpow : (2:ℝ)^(j+k+D)*2^p = (2^D)^2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      dsimp only [rationalCopyWeight]
      push_cast
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      field_simp
      nlinarith only [hpow]
    push_cast
    linear_combination (rationalCopyPolynomial D D r.val.val p j k : ℝ)*
      ((x:ℝ)-(y:ℝ))*Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ)*hsq
  · simp



theorem factorial_conjugate_highest (D : ℕ) (r : CopyLabel D) :
    diagonalConjugate 24 (factorialMode 24) (planarHighestFourAnnihilator D r) =
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D : ℂ) •
      (∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
        (rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
          xy.val.1.val xy.val.2.val : ℂ) •
        annihilatorList 24 [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2]) := by
  classical
  unfold planarHighestFourAnnihilator
  rw [diagonalConjugate_sum]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [diagonalConjugate_smul,
    diagonalConjugate_mul _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_mul _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_annihilator _ _ (factorialMode_ne_zero 24),
    diagonalConjugate_annihilator _ _ (factorialMode_ne_zero 24),
    limitPairAnnihilator, diagonalConjugate_pair _ _ (factorialMode_ne_zero 24),
    coefficientPair_basis_expansion, Matrix.mul_sum]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xy _
  have hbasis : basisAnnihilator 24 (increasingPairSector 24 xy).val =
      annihilator 24 xy.val.2 * annihilator 24 xy.val.1 :=
    basisAnnihilator_pair _ _ xy.property
  rw [hbasis]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc := congrArg (fun x:ℝ => (x:ℂ))
    (copy_pair_factorial D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
      xy.val.1.val xy.val.2.val b.property)
  push_cast at hc
  dsimp only [factorialMode, planarLocalCopyMatrix]
  rw [show (annihilator 24 b.val.2.val.2 * annihilator 24 b.val.2.val.1) *
      (annihilator 24 xy.val.2 * annihilator 24 xy.val.1) =
      annihilatorList 24 [xy.val.1, xy.val.2, b.val.2.val.1, b.val.2.val.2] by
    simp only [annihilatorList_cons, annihilatorList_nil, Matrix.one_mul, Matrix.mul_assoc]]
  congr 1
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem occupationFactorial_pos {Q : ℕ} (A : Occupation Q) :
    0 < occupationFactorial A := by
  unfold occupationFactorial
  exact Finset.prod_pos (fun a _ => by positivity)

theorem factorialMode_prod {Q : ℕ} (A : Occupation Q) :
    (∏ a ∈ A, factorialMode Q a) = (Real.sqrt (occupationFactorial A : ℝ) : ℂ) := by
  unfold factorialMode occupationFactorial
  rw [Rat.cast_prod, Real.sqrt_prod _ (by intro a _; positivity)]
  simp

theorem planarFourWedgeMatrix_rational (D : ℕ) (r : CopyLabel D)
    (A : SectorOccupation 24 4) :
    planarFourWedgeMatrix D A r =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D *
        (rationalHighestEntry D r A.val : ℝ) / Real.sqrt (occupationFactorial A.val : ℝ) : ℝ) : ℂ) := by
  classical
  have he := congrArg (fun M : FockMatrix 24 => M ∅ A.val) (factorial_conjugate_highest D r)
  simp only [diagonalConjugate, occupationDiagonalInv, occupationDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Finset.prod_empty, inv_one, one_mul,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    annihilatorList_vacuum_rational] at he
  rw [factorialMode_prod] at he
  have hsum : (∑ b : FourHighestShell 24 D, ∑ xy : IncreasingPair 24,
      (rationalHighestTerm D r b.val.1.val b.val.2.val.1.val b.val.2.val.2.val
        xy.val.1.val xy.val.2.val : ℂ) *
      (rationalWordVacuum [xy.val.1,xy.val.2,b.val.2.val.1,b.val.2.val.2] A.val : ℂ)) =
        (rationalHighestEntry D r A.val : ℂ) := by
    unfold rationalHighestEntry
    push_cast
    rfl
  rw [hsum] at he
  have hn : (Real.sqrt (occupationFactorial A.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast occupationFactorial_pos A.val)).ne'
  have hv : planarHighestFourAnnihilator D r ∅ A.val =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) * Real.sqrt 2 / 2^D : ℝ) : ℂ) *
       (rationalHighestEntry D r A.val : ℂ) / (Real.sqrt (occupationFactorial A.val : ℝ) : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa using he
  unfold planarFourWedgeMatrix annihilatorVector
  rw [hv]
  simp only [map_div₀, map_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp


theorem planarFourGram_rational (D : ℕ) (r s : CopyLabel D) :
    planarFourGram D r s =
      ((Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) *
        (rationalFourGram D r s : ℝ) *
        Real.sqrt (rationalCopyDiagonal D s.val.val : ℝ) : ℝ) : ℂ) := by
  classical
  unfold planarFourGram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, planarFourWedgeMatrix_rational,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  unfold rationalFourGram
  rw [Rat.cast_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  have hn : 0 < (occupationFactorial A.val : ℝ) := by
    exact_mod_cast occupationFactorial_pos A.val
  have hn' : Real.sqrt (occupationFactorial A.val : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsq := Real.sq_sqrt hn.le
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  push_cast
  rw [show 2*D=D*2 by omega, pow_mul]
  field_simp
  rw [hsq, hs2]
  ring

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem fourHighestShell_sum {M : Type*} [AddCommMonoid M] (D : ℕ)
    (f : FourUncoupled 24 → M) :
    (∑ b : FourHighestShell 24 D, f b.val) =
      ∑ p : Fin 47, ∑ jk : IncreasingPair 24,
        if p.val+jk.val.1.val+jk.val.2.val=D then f (p,jk) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun b : FourUncoupled 24 => b.1.val+b.2.val.1.val+b.2.val.2.val=D)) (by simp) f]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem highest_pair_weight_sum (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (xy jk : IncreasingPair 24) :
    (∑ p : Fin 47, if p.val+jk.val.1.val+jk.val.2.val=D then
      rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
        rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
    fastHighestTerm D r A xy.val.1 xy.val.2 jk.val.1 jk.val.2 := by
  have hp : xy.val.1.val+xy.val.2.val-1 < 47 := by
    have hx := xy.val.1.isLt
    have hy := xy.val.2.isLt
    have hxy := xy.property
    change xy.val.1.val < xy.val.2.val at hxy
    omega
  let p : Fin 47 := ⟨xy.val.1.val+xy.val.2.val-1, hp⟩
  rw [Finset.sum_eq_single p]
  · simp [fastHighestTerm, xy.property, jk.property, p]
  · intro b _ hn
    have hd : xy.val.1.val+xy.val.2.val ≠ b.val+1 := by
      intro h
      apply hn
      apply Fin.ext
      dsimp [p]
      omega
    simp [rationalHighestTerm, hd]
  · simp

theorem rationalHighestEntry_expand (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    rationalHighestEntry D r A =
      ∑ j : Orbital 24, ∑ k : Orbital 24, ∑ x : Orbital 24, ∑ y : Orbital 24,
        fastHighestTerm D r A x y j k := by
  classical
  unfold rationalHighestEntry
  rw [fourHighestShell_sum D (fun b => ∑ xy : IncreasingPair 24,
    rationalHighestTerm D r b.1.val b.2.val.1.val b.2.val.2.val xy.val.1.val xy.val.2.val *
      rationalWordVacuum [xy.val.1,xy.val.2,b.2.val.1,b.2.val.2] A)]
  have he : (∑ p : Fin 47, ∑ jk : IncreasingPair 24,
      if p.val+jk.val.1.val+jk.val.2.val=D then
        ∑ xy : IncreasingPair 24,
          rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
            rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
        ∑ jk : IncreasingPair 24, ∑ xy : IncreasingPair 24,
          fastHighestTerm D r A xy.val.1 xy.val.2 jk.val.1 jk.val.2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro jk _
    have hh (p : Fin 47) :
        (if p.val+jk.val.1.val+jk.val.2.val=D then
          ∑ xy : IncreasingPair 24,
            rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
              rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0) =
        ∑ xy : IncreasingPair 24, if p.val+jk.val.1.val+jk.val.2.val=D then
            rationalHighestTerm D r p.val jk.val.1.val jk.val.2.val xy.val.1.val xy.val.2.val *
              rationalWordVacuum [xy.val.1,xy.val.2,jk.val.1,jk.val.2] A else 0 := by
      split_ifs <;> simp
    simp_rw [hh]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun xy _ => highest_pair_weight_sum D r A xy jk)
  rw [he, increasingPair_sum 24 (fun j k => ∑ xy : IncreasingPair 24,
    fastHighestTerm D r A xy.val.1 xy.val.2 j k)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j<k
  · rw [ite_eq_left hjk, increasingPair_sum 24 (fun x y => fastHighestTerm D r A x y j k)]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : x<y
    · rw [ite_eq_left hxy]
    · simp [fastHighestTerm, hxy]
  · simp [fastHighestTerm, hjk]

theorem fastHighestTerm_support (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) (hn : fastHighestTerm D r A x y j k ≠ 0) :
    x ∈ A ∧ y ∈ A ∧ j ∈ A ∧ k ∈ A := by
  unfold fastHighestTerm at hn
  split_ifs at hn with h
  · have hn' : rationalWordVacuum [x,y,j,k] A ≠ 0 := fun hm => hn (by rw [hm, mul_zero])
    obtain ⟨_,hs⟩ := rationalWordVacuum_support _ _ hn'
    simp [← hs]
  · simp at hn

theorem rationalHighestEntry_fast (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    rationalHighestEntry D r A = fastHighestEntry D r A := by
  classical
  rw [rationalHighestEntry_expand]
  unfold fastHighestEntry
  symm
  let f : Orbital 24 × (Orbital 24 × (Orbital 24 × Orbital 24)) → ℚ := fun b =>
    fastHighestTerm D r A b.2.2.1 b.2.2.2 b.1 b.2.1
  have hs : (∑ b ∈ A ×ˢ (A ×ˢ (A ×ˢ A)), f b) =
      ∑ b ∈ Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)), f b := by
    apply Finset.sum_subset (by simp only [Finset.univ_product_univ]; exact Finset.subset_univ _)
    intro b _ hb
    by_contra hn
    obtain ⟨hx,hy,hj,hk⟩ := fastHighestTerm_support D r A b.2.2.1 b.2.2.2 b.1 b.2.1 hn
    exact hb (by simp [hx,hy,hj,hk])
  simpa only [Finset.sum_product] using hs

end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fastHighestTerm_weight (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) (hn : fastHighestTerm D r A x y j k ≠ 0) :
    occupationWeight A = D+1 := by
  unfold fastHighestTerm at hn
  split_ifs at hn with hh
  · have hn' : rationalWordVacuum [x,y,j,k] A ≠ 0 := fun hm => hn (by rw [hm, mul_zero])
    obtain ⟨hnd,hs⟩ := rationalWordVacuum_support _ _ hn'
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true] at hnd
    have hw : occupationWeight A = x.val+y.val+j.val+k.val := by
      unfold occupationWeight
      rw [← hs]
      simp [hnd.1.1, hnd.1.2.1, hnd.1.2.2, hnd.2.1.1, hnd.2.1.2, hnd.2.2,
        Finset.sum_insert, add_assoc]
    rw [hw]
    have hxy : x.val < y.val := hh.1
    omega
  · simp at hn

theorem rationalHighestEntry_weight (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (hw : occupationWeight A ≠ D+1) : rationalHighestEntry D r A = 0 := by
  rw [rationalHighestEntry_fast]
  unfold fastHighestEntry
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_contra hn
  exact hw (fastHighestTerm_weight D r A x y j k hn)


theorem rationalFourGram_fast (D : ℕ) : rationalFourGram D = fastFourGram D := by
  ext r s
  classical
  unfold rationalFourGram fastFourGram highestFourOccupations
  rw [← Finset.sum_subtype ((Finset.univ : Finset (Orbital 24)).powersetCard 4)
    (by intro A; simp [Finset.mem_powersetCard])
    (fun A => 2 * rationalHighestEntry D r A * rationalHighestEntry D s A /
      (2^(2*D) * occupationFactorial A))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs with h
  · rw [rationalHighestEntry_fast, rationalHighestEntry_fast]
  · simp [rationalHighestEntry_weight D r A h]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial


theorem rationalCoupling_integer (c : ℤ) (z k p : ℕ) :
    rationalCoupling (c:ℚ) z k p = (integerCoupling c z k p : ℚ) := by
  have h1 : ((X-1)^z : Polynomial ℚ).coeff = fun h =>
      (-1)^(z-h) * (z.choose h : ℚ) := by
    funext h
    rw [show (X-1:Polynomial ℚ) = X+C (-1) by simp [sub_eq_add_neg]]
    exact coeff_X_add_C_pow (-1) z h
  have h2 : ((C (c:ℚ)*X+1)^k : Polynomial ℚ).coeff = fun h =>
      (k.choose h : ℚ) * (c:ℚ)^h := by
    funext h
    rw [show ((C (c:ℚ)*X+1)^k : Polynomial ℚ) = ((X+1)^k).comp (C (c:ℚ)*X) by simp]
    rw [comp_C_mul_X_coeff, coeff_X_add_one_pow]
  unfold rationalCoupling integerCoupling
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [h1, h2, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro h _
  ring

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rationalCopyPolynomial_integer (D T r p j k : ℕ) :
    rationalCopyPolynomial D T r p j k = (integerCopyPolynomial D T r p j k : ℚ) := by
  simp only [rationalCopyPolynomial, integerCopyPolynomial, apply_ite (fun z:ℤ => (z:ℚ)),
    Int.cast_mul, ← rationalCoupling_integer, Int.cast_one, Int.cast_zero]

theorem rationalFourTrace_integer (D t : ℕ) (a : RowEntry t → ℚ) :
    rationalFourTrace D t a = integerFourTrace D t a := by
  ext r s
  simp only [rationalFourTrace, integerFourTrace, rationalCopyPolynomial_integer]

theorem fastHighestTerm_integer (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) :
    fastHighestTerm D r A x y j k = integerHighestTerm D r A x y j k := by
  unfold fastHighestTerm integerHighestTerm
  split_ifs with hh
  · have hxy : x.val+y.val=(x.val+y.val-1)+1 := by
      have := hh.1
      change x.val<y.val at this
      omega
    simp only [rationalHighestTerm, ite_eq_left hxy, rationalCopyPolynomial_integer]
  · rfl

theorem rationalFourGram_integer (D : ℕ) : rationalFourGram D = integerFourGram D := by
  rw [rationalFourGram_fast]
  ext r s
  simp only [fastFourGram, integerFourGram, fastHighestEntry, integerHighestEntry,
    fastHighestTerm_integer]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerCoupling_fast (c : ℤ) (z k p : ℕ) :
    integerCoupling c z k p = fastIntegerCoupling c z k p := by
  simp only [integerCoupling, fastIntegerCoupling, Nat.choose_eq_fast_choose]

theorem integerCopyPolynomial_fast (D T r p j k : ℕ) :
    integerCopyPolynomial D T r p j k = fastIntegerCopyPolynomial D T r p j k := by
  simp only [integerCopyPolynomial, fastIntegerCopyPolynomial, integerCoupling_fast]
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerHighestEntry_kernel (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    integerHighestEntry D r A = kernelHighestEntry D r A := by
  simp only [integerHighestEntry, kernelHighestEntry, integerHighestTerm, kernelHighestTerm,
    integerCopyPolynomial_fast]

theorem integerFourGram_cached (D : ℕ) (xs : List (Occupation 24 × List ℚ))
    (h : ∀ r A, A ∈ highestFourOccupations D →
      kernelHighestEntry D r A = highestLookup xs r.val.val A) :
    integerFourGram D = cachedFourGram D xs := by
  ext r s
  apply Finset.sum_congr rfl
  intro A hA
  rw [integerHighestEntry_kernel, integerHighestEntry_kernel, h r A hA, h s A hA]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PolynomialPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Positivity. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators
open Polynomial



theorem real_matrix_posSemidef_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (M.map (algebraMap ℝ ℂ)).PosSemidef := by
  have hH : (M.map (algebraMap ℝ ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    have h := Matrix.IsHermitian.ext_iff.mp hM.isHermitian i j
    simpa using congrArg (algebraMap ℝ ℂ) h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  have hRe := hM.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hIm := hM.dotProduct_mulVec_nonneg (fun i => (x i).im)
  apply Complex.nonneg_iff.mpr
  constructor
  · have he : (star x ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ x)).re =
        (fun i => (x i).re) ⬝ᵥ (M *ᵥ fun i => (x i).re) +
        (fun i => (x i).im) ⬝ᵥ (M *ᵥ fun i => (x i).im) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.sum_add_distrib,
        Complex.mul_re, Complex.mul_im, Finset.mul_sum]
    rw [he]
    simpa only [star_trivial, Pi.star_apply] using add_nonneg hRe hIm
  · exact (hH.im_star_dotProduct_mulVec_self x).symm



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LDL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem rational_ldl_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : Matrix ι ι ℚ) (d : ι → ℚ)
    (he : M = L * Matrix.diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  let Lr := L.map (algebraMap ℚ ℝ)
  have hh : (Matrix.diagonal (fun i => (d i : ℝ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  have hr : (M.map (algebraMap ℚ ℝ)).PosSemidef := by
    have ht : (Lᵀ).map (algebraMap ℚ ℝ) = Lrᴴ := by
      ext i j
      simp [Lr]
    rw [he, Matrix.map_mul, Matrix.map_mul, ht]
    have he' : (Matrix.diagonal d).map (algebraMap ℚ ℝ) =
        Matrix.diagonal (fun i => (d i : ℝ)) := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [he']
    exact hh.mul_mul_conjTranspose_same Lr
  have hc := real_matrix_posSemidef_complex (M.map (algebraMap ℚ ℝ)) hr
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate01
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate01. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_1 : highestFourOccupations 1 = ∅ := by
  decide +kernel

theorem fourHighestChecked_1 : ∀ r : CopyLabel 1, ∀ A∈highestFourOccupations 1,
    kernelHighestEntry 1 r A = highestLookup fourHighestCache_1 r.val.val A := by
  rw [fourOccupations_1]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_1 (r s : CopyLabel 1) :
    integerFourGram 1 r s = fourZData_1 r s := by
  rw [integerFourGram_cached 1 fourHighestCache_1 fourHighestChecked_1]
  have h : ∀ r s : CopyLabel 1, cachedFourGram 1 fourHighestCache_1 r s = fourZData_1 r s := by
    simp only [cachedFourGram, fourOccupations_1]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_1 :
    ((integerCompression 1).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 1 = 0 := by
    rw [show integerFourGram 1 = fourZData_1 from Matrix.ext fourZChecked_1]
    have h : ∀ r s : CopyLabel 1, fourZData_1 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate02
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate02. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_2 : highestFourOccupations 2 = ∅ := by
  decide +kernel

theorem fourHighestChecked_2 : ∀ r : CopyLabel 2, ∀ A∈highestFourOccupations 2,
    kernelHighestEntry 2 r A = highestLookup fourHighestCache_2 r.val.val A := by
  rw [fourOccupations_2]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_2 (r s : CopyLabel 2) :
    integerFourGram 2 r s = fourZData_2 r s := by
  rw [integerFourGram_cached 2 fourHighestCache_2 fourHighestChecked_2]
  have h : ∀ r s : CopyLabel 2, cachedFourGram 2 fourHighestCache_2 r s = fourZData_2 r s := by
    simp only [cachedFourGram, fourOccupations_2]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_2 :
    ((integerCompression 2).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 2 = 0 := by
    rw [show integerFourGram 2 = fourZData_2 from Matrix.ext fourZChecked_2]
    have h : ∀ r s : CopyLabel 2, fourZData_2 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate03
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate03. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_3 : highestFourOccupations 3 = ∅ := by
  decide +kernel

theorem fourHighestChecked_3 : ∀ r : CopyLabel 3, ∀ A∈highestFourOccupations 3,
    kernelHighestEntry 3 r A = highestLookup fourHighestCache_3 r.val.val A := by
  rw [fourOccupations_3]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_3 (r s : CopyLabel 3) :
    integerFourGram 3 r s = fourZData_3 r s := by
  rw [integerFourGram_cached 3 fourHighestCache_3 fourHighestChecked_3]
  have h : ∀ r s : CopyLabel 3, cachedFourGram 3 fourHighestCache_3 r s = fourZData_3 r s := by
    simp only [cachedFourGram, fourOccupations_3]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_3 :
    ((integerCompression 3).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 3 = 0 := by
    rw [show integerFourGram 3 = fourZData_3 from Matrix.ext fourZChecked_3]
    have h : ∀ r s : CopyLabel 3, fourZData_3 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate04
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate04. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_4 : highestFourOccupations 4 = ∅ := by
  decide +kernel

theorem fourHighestChecked_4 : ∀ r : CopyLabel 4, ∀ A∈highestFourOccupations 4,
    kernelHighestEntry 4 r A = highestLookup fourHighestCache_4 r.val.val A := by
  rw [fourOccupations_4]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_4 (r s : CopyLabel 4) :
    integerFourGram 4 r s = fourZData_4 r s := by
  rw [integerFourGram_cached 4 fourHighestCache_4 fourHighestChecked_4]
  have h : ∀ r s : CopyLabel 4, cachedFourGram 4 fourHighestCache_4 r s = fourZData_4 r s := by
    simp only [cachedFourGram, fourOccupations_4]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_4 :
    ((integerCompression 4).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 4 = 0 := by
    rw [show integerFourGram 4 = fourZData_4 from Matrix.ext fourZChecked_4]
    have h : ∀ r s : CopyLabel 4, fourZData_4 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate05Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate05 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_5 : highestFourOccupations 5 = {{0,1,2,3}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate05
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate05. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestChecked_5 : ∀ r : CopyLabel 5, ∀ A∈highestFourOccupations 5,
    kernelHighestEntry 5 r A = highestLookup fourHighestCache_5 r.val.val A := by
  rw [fourOccupations_5]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_5 (r s : CopyLabel 5) :
    integerFourGram 5 r s = fourZData_5 r s := by
  rw [integerFourGram_cached 5 fourHighestCache_5 fourHighestChecked_5]
  have h : ∀ r s : CopyLabel 5, cachedFourGram 5 fourHighestCache_5 r s = fourZData_5 r s := by
    simp only [cachedFourGram, fourOccupations_5]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_5 :
    fourZData_5 * (Matrix.diagonal (fun r : CopyLabel 5 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 5 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val) *
        fourYData_5 * Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val)) *
      fourZData_5 = fourLData_5 * Matrix.diagonal fourPivotData_5 * (fourLData_5)ᵀ := by
  have h : ∀ r s : CopyLabel 5,
      (fourZData_5 * (Matrix.diagonal (fun r : CopyLabel 5 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 5 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val) *
          fourYData_5 * Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val)) *
        fourZData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ) r s =
      (fourLData_5 * Matrix.diagonal fourPivotData_5 * (fourLData_5)ᵀ : Matrix (CopyLabel 5) (CopyLabel 5) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_5 : ∀ r, 0 ≤ fourPivotData_5 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_5, copyDiagonalData]

theorem integer_certificate_5 :
    ((integerCompression 5).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_5) (fourPivotData_5) _ fourPivotChecked_5
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 5 = fourYData_5 from Matrix.ext fourYChecked_5,
    show integerFourGram 5 = fourZData_5 from Matrix.ext fourZChecked_5]
  exact fourLDLChecked_5

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate06
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate06. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_6 : highestFourOccupations 6 = {{0,1,2,4}} := by
  decide +kernel

theorem fourHighestChecked_6 : ∀ r : CopyLabel 6, ∀ A∈highestFourOccupations 6,
    kernelHighestEntry 6 r A = highestLookup fourHighestCache_6 r.val.val A := by
  rw [fourOccupations_6]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_6 (r s : CopyLabel 6) :
    integerFourGram 6 r s = fourZData_6 r s := by
  rw [integerFourGram_cached 6 fourHighestCache_6 fourHighestChecked_6]
  have h : ∀ r s : CopyLabel 6, cachedFourGram 6 fourHighestCache_6 r s = fourZData_6 r s := by
    simp only [cachedFourGram, fourOccupations_6]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_6 :
    ((integerCompression 6).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 6 = 0 := by
    rw [show integerFourGram 6 = fourZData_6 from Matrix.ext fourZChecked_6]
    have h : ∀ r s : CopyLabel 6, fourZData_6 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_7 : highestFourOccupations 7 = {{0,1,2,5}, {0,1,3,4}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestChecked_7 : ∀ r : CopyLabel 7, ∀ A∈highestFourOccupations 7,
    kernelHighestEntry 7 r A = highestLookup fourHighestCache_7 r.val.val A := by
  rw [fourOccupations_7]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_7 (r s : CopyLabel 7) :
    integerFourGram 7 r s = fourZData_7 r s := by
  rw [integerFourGram_cached 7 fourHighestCache_7 fourHighestChecked_7]
  have h : ∀ r s : CopyLabel 7, cachedFourGram 7 fourHighestCache_7 r s = fourZData_7 r s := by
    simp only [cachedFourGram, fourOccupations_7]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_7 :
    fourZData_7 * (Matrix.diagonal (fun r : CopyLabel 7 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 7 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val) *
        fourYData_7 * Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val)) *
      fourZData_7 = fourLData_7 * Matrix.diagonal fourPivotData_7 * (fourLData_7)ᵀ := by
  have h : ∀ r s : CopyLabel 7,
      (fourZData_7 * (Matrix.diagonal (fun r : CopyLabel 7 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 7 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val) *
          fourYData_7 * Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val)) *
        fourZData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ) r s =
      (fourLData_7 * Matrix.diagonal fourPivotData_7 * (fourLData_7)ᵀ : Matrix (CopyLabel 7) (CopyLabel 7) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_7 : ∀ r, 0 ≤ fourPivotData_7 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_7, copyDiagonalData]

theorem integer_certificate_7 :
    ((integerCompression 7).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_7) (fourPivotData_7) _ fourPivotChecked_7
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 7 = fourYData_7 from Matrix.ext fourYChecked_7,
    show integerFourGram 7 = fourZData_7 from Matrix.ext fourZChecked_7]
  exact fourLDLChecked_7

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerCompression
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem planar_certificate_of_integer (D : ℕ)
    (h : ((integerCompression D).map (algebraMap ℚ ℂ)).PosSemidef) :
    (planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D).PosSemidef := by
  classical
  let d : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
    Matrix.diagonal (fun r => (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ))
  let G := (integerFourGram D).map (algebraMap ℚ ℂ)
  let Y := (integerRowsFourTrace D).map (algebraMap ℚ ℂ)
  let u : CopyLabel D → ℂ := fun r => (rationalCopyDiagonal D r.val.val : ℂ)
  let c : CopyLabel D → ℂ := fun r => (if r.val.val=1 then 2 else 0)+3/10^6
  have hd : dᴴ = d := by
    ext r s
    by_cases hrs : r=s <;> simp [d, Matrix.conjTranspose_apply, hrs, eq_comm]
  have hDD : d*d=Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    have hu : 0 ≤ (rationalCopyDiagonal D r.val.val : ℝ) := by
      exact_mod_cast (rationalCopyDiagonal_pos D r.val.val).le
    change (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ)*
      (Real.sqrt (rationalCopyDiagonal D r.val.val : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
    simp [u]
  have hc : d*Matrix.diagonal c*d = Matrix.diagonal (fun r => c r*u r) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    have hv := congrFun (congrFun hDD r) r
    simp only [d, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at hv
    rw [mul_right_comm, hv]
    exact mul_comm _ _
  have hG : planarFourGram D = d*G*d := by
    ext r s
    rw [planarFourGram_rational, rationalFourGram_integer]
    simp [d,G,Matrix.diagonal_mul,Matrix.mul_diagonal, Complex.ofReal_mul]
  have hE : (Matrix.of (fun r s => ((∑ t : Fin 8,
      planarRowFourTrace D (certificateRows t).t.val (certificateRows t).alpha r s : ℝ) : ℂ))) =
      d*Y*d := by
    ext r s
    simp only [Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, d,Y,
      Matrix.map_apply, integerRowsFourTrace, Matrix.sum_apply, map_sum, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    change ((planarRowFourTrace D t.val (rationalComparisonRow t (certificateEll t)
      (certificateAlpha t)).alpha r s : ℝ) : ℂ) = _
    rw [planarRowFourTrace_rational D t (certificateEll t) (certificateAlpha t),
      rationalFourTrace_integer]
    simp
  have hC : planarFourComparison certificateRows (3/10^6) D = Matrix.diagonal c - d*Y*d := by
    rw [planarFourComparison, hE]
    have hct : (2:ℂ) • targetCopy D + ((3/10^6:ℝ):ℂ) • (1:Matrix (CopyLabel D) (CopyLabel D) ℂ) =
        Matrix.diagonal c := by
      ext r s
      by_cases he : r=s
      · subst s
        simp [targetCopy, c, Matrix.smul_apply]
      · have hf : ¬ (r.val.val=1 ∧ s.val.val=1) := by
          intro hh
          apply he
          apply Subtype.ext
          apply Fin.ext
          omega
        simp [targetCopy, c, Matrix.smul_apply, he, hf]
    rw [← hct]
    abel
  have hM : (integerFourMiddle D).map (algebraMap ℚ ℂ) =
      Matrix.diagonal (fun r => c r*u r) - Matrix.diagonal u*Y*Matrix.diagonal u := by
    ext r s
    simp only [integerFourMiddle, Matrix.map_apply, Matrix.sub_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hrs : r=s
    · subst s
      simp only [Matrix.diagonal_apply_eq]
      dsimp [c,u,Y]
      split_ifs <;> simp
    · simp [hrs, c,u,Y]
  have hfull : planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D = d*((integerCompression D).map (algebraMap ℚ ℂ))*d := by
    rw [hG, hC, integerCompression, Matrix.map_mul, Matrix.map_mul, hM]
    calc
      _ = d*(G*(d*Matrix.diagonal c*d-(d*d)*Y*(d*d))*G)*d := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by rw [hDD, hc]
  rw [hfull]
  simpa only [hd] using h.mul_mul_conjTranspose_same d

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem certificate_four_oai (D : ℕ) (hD : 1 ≤ D) (hD' : D ≤ 23) :
    (planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D).PosSemidef := by
  apply planar_certificate_of_integer D
  interval_cases D
  · exact integer_certificate_1
  · exact integer_certificate_2
  · exact integer_certificate_3
  · exact integer_certificate_4
  · exact integer_certificate_5
  · exact integer_certificate_6
  · exact integer_certificate_7
  · exact integer_certificate_8
  · exact integer_certificate_9
  · exact integer_certificate_10
  · exact integer_certificate_11
  · exact integer_certificate_12
  · exact integer_certificate_13
  · exact integer_certificate_14
  · exact integer_certificate_15
  · exact integer_certificate_16
  · exact integer_certificate_17
  · exact integer_certificate_18
  · exact integer_certificate_19
  · exact integer_certificate_20
  · exact integer_certificate_21
  · exact integer_certificate_22
  · exact integer_certificate_23



end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.certificate_four_oai := @OAI.LaughlinFock.certificate_four_oai
