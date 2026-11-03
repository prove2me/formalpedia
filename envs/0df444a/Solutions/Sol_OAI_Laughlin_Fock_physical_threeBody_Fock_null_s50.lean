-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:25:40.590482+00:00
-- url     : https://prove2.me/submissions/03316705-784c-42d8-8cb9-2b626f45dd9c

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_sourceThreeVector_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_threeWedge_zero_of_gram_zero_s50
import Theorems.Thm_OAI_Laughlin_Spin_normalizedCoupledDescendant_eigen_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_FamilyCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem occupationInner_basis_left (Q : ℕ) (A : Finset (Fin (Q+1))) (x : Space Q) :
    occupationInner Q (occupationBasis Q A) x = (occupationBasis Q).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_ext_right (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q z x = occupationInner Q z y) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  simpa only [occupationInner_basis_left] using h (occupationBasis Q A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourcePairCreateEnd_mul (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = sourcePairVector Q p*x := by
  simp only [sourcePairCreateEnd,pairCreateEnd,sourcePairVector,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,Finset.sum_mul,smul_mul_assoc,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*x) =
    (ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*1))*x
  simp only [mul_one,mul_assoc]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledBasis_eigen (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeGram Q-1)*coupledBasisMatrix Q hQ =
      coupledBasisMatrix Q hQ * Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) := by
  ext i s
  rw [Matrix.mul_apply,Matrix.mul_diagonal]
  have he := congrFun (normalizedCoupledDescendant_eigen_s50 Q s.1.val s.2.val hQ (by omega)) i
  simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,coupledBasisMatrix,mul_comm] using he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledSelector_eigen (Q : ℕ) (z : Fin (Q+1)) :
    Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) *
      coupledSelector Q z = gramEigenvalueFormula Q z.val • coupledSelector Q z := by
  unfold coupledSelector
  rw [Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases hst : s=t
  · subst t
    simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
    by_cases h : s.1=z
    · simp [h]
    · simp [h]
  · simp [hst]

theorem threeSpinProjector_sub_one_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeGram Q-1)*threeSpinProjector Q hQ z =
      gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z := by
  unfold threeSpinProjector
  calc
    _ = ((threeGram Q-1)*coupledBasisMatrix Q hQ)*coupledSelector Q z*(coupledBasisMatrix Q hQ)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = coupledBasisMatrix Q hQ *
      (Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val)*coupledSelector Q z)*
      (coupledBasisMatrix Q hQ)ᵀ := by rw [coupledBasis_eigen]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [coupledSelector_eigen]; simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem threeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    threeGram Q*threeSpinProjector Q hQ z =
      (1+gramEigenvalueFormula Q z.val) • threeSpinProjector Q hQ z := by
  have he := threeSpinProjector_sub_one_eigen Q hQ z
  rw [Matrix.sub_mul,Matrix.one_mul] at he
  calc
    _ = (threeGram Q*threeSpinProjector Q hQ z-threeSpinProjector Q hQ z)+threeSpinProjector Q hQ z := by abel
    _ = gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z+threeSpinProjector Q hQ z := by rw [he]
    _ = _ := by ext i j; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_NullFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem gramEigenvalueFormula_zero (Q : ℕ) : gramEigenvalueFormula Q 0 = -1 := by
  simp [gramEigenvalueFormula,fallingRatio]

theorem gramEigenvalueFormula_one (Q : ℕ) (hQ : 2 ≤ Q) : gramEigenvalueFormula Q 1 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hd : (2*(Q : ℝ)-2) ≠ 0 := by
    have h : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hq1 : -1+(Q : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  norm_num [gramEigenvalueFormula,fallingRatio,Nat.descFactorial]
  rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring_nf
  field_simp [hq1]
  ring

theorem descFactorial_three_real (n : ℕ) (hn : 2 ≤ n) :
    (n.descFactorial 3 : ℝ) = (n : ℝ)*(n-1)*(n-2) := by
  norm_num [Nat.descFactorial]
  rw [Nat.cast_sub hn,Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem gramEigenvalueFormula_three (Q : ℕ) (hQ : 3 ≤ Q) : gramEigenvalueFormula Q 3 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have h : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd₀ : (2*(Q : ℝ)-2) ≠ 0 := by linarith
  have hd₁ : (2*(Q : ℝ)-2-1) ≠ 0 := by linarith
  have hd₂ : (2*(Q : ℝ)-2-2) ≠ 0 := by linarith
  have hpoly : -6+(Q : ℝ)*13-(Q : ℝ)^2*9+(Q : ℝ)^3*2 ≠ 0 := by
    have hp : 0 < ((Q : ℝ)-1)*((Q : ℝ)-2)*(2*(Q : ℝ)-3) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    nlinarith
  unfold gramEigenvalueFormula fallingRatio
  rw [descFactorial_three_real Q (by omega),descFactorial_three_real (2*Q-2) (by omega),
    Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  norm_num
  field_simp
  ring_nf
  field_simp [hpoly]
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_NullSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem complexThreeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    complexThreeGram Q * complexThreeSpinProjector Q hQ z =
      ((1+gramEigenvalueFormula Q z.val : ℝ) : ℂ) • complexThreeSpinProjector Q hQ z := by
  ext a b
  have he := congrArg (fun M : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ =>
    (M a b : ℂ)) (Spin.threeSpinProjector_eigen Q hQ z)
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul] at he ⊢
  push_cast at he
  simpa only [complexThreeGram,complexThreeSpinProjector,Complex.ofReal_add,Complex.ofReal_one] using he

theorem source_threeBody_null_sectors (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (u : Spin.PairOrbitalIndex Q → ℂ) :
    threeWedge Q (complexThreeSpinProjector Q hQ z *ᵥ u) = 0 := by
  have hval : gramEigenvalueFormula Q z.val = -1 := by
    rcases hz with hz | hz | hz
    · rw [hz,gramEigenvalueFormula_zero]
    · rw [hz,gramEigenvalueFormula_one Q hQ]
    · rw [hz,gramEigenvalueFormula_three Q (by omega)]
  apply threeWedge_zero_of_gram_zero_s50 Q hQ
  rw [Matrix.mulVec_mulVec,complexThreeSpinProjector_eigen,hval]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix

theorem threeBodyColumn_sourceThreeVector (Q : ℕ) (i : PairOrbitalIndex Q) :
    threeBodyColumn Q i.1.val i.2 = sourceThreeVector Q i := by
  rw [threeBodyColumn,sourcePairCreateEnd_mul]
  rfl

theorem threeWedge_contraction_zero (Q : ℕ) (v : PairOrbitalIndex Q → ℂ)
    (hv : threeWedge Q v=0) (x : Space Q) :
    (∑ i, star (v i) • sourceThreeEnd Q i x)=0 := by
  apply occupationInner_ext_right Q
  intro y
  have h : occupationInner Q (threeWedge Q v*y) x =
      occupationInner Q y (∑ i, star (v i) • sourceThreeEnd Q i x) := by
    simp only [threeWedge,Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
      occupationInner_smul_left,threeBodyColumn_sourceThreeVector,sourceThreeVector_adjoint_s50,
      occupationInner_sum_right,occupationInner_smul_right]
  rw [← h,hv,zero_mul]
  simp [occupationInner]

theorem physical_threeBody_Fock_null_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x = 0 := by
  let R := (threeSpinProjector Q hQ z).map Complex.ofReal
  have hc (j : PairOrbitalIndex Q) : (∑ i, star (R i j) • sourceThreeEnd Q i x)=0 := by
    apply threeWedge_contraction_zero
    have h := source_threeBody_null_sectors Q hQ z hz (Pi.single j 1)
    have he : complexThreeSpinProjector Q hQ z *ᵥ Pi.single j 1 = (fun i => R i j) := by
      funext i
      simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexThreeSpinProjector,R]
    rw [he] at h
    exact h
  have he : contractionForm Q (sourceThreeEnd Q) R x =
      ∑ j, occupationInner Q (∑ i, star (R i j) • sourceThreeEnd Q i x) (sourceThreeEnd Q j x) := by
    simp only [contractionForm,occupationInner_sum_left,occupationInner_smul_left,star_star]
    rw [Finset.sum_comm]
  change contractionForm Q (sourceThreeEnd Q) R x=0
  rw [he]
  simp only [hc]
  simp [occupationInner]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50_oai := @OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50_oai
