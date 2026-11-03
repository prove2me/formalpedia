-- Prove2me | solution 1 for OAI.Laughlin.Fock.fourPairEmbedding_contract_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:45:31.675436+00:00
-- url     : https://prove2.me/submissions/49d15f7f-0f31-4bda-8a6c-6300d35707b5

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L022
import Theorems.Thm_OAI_Laughlin_Spin_pairCoefficient_tensor_lowering_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j) x) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Orthonormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero (A B z : ℕ) :
    highestRaw A B z 0 = 1 / Real.sqrt (B.choose z : ℝ) := by
  simp [highestRaw]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_exterior_sum (Q : ℕ) (f : SpinIndex Q Q → Space Q)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (a : SpinIndex Q Q → ℂ) :
    (∑ i, a i • f i) = ∑ i : WedgePairIndex Q, (a i.val-a i.val.swap) • f i.val := by
  apply (occupationBasis Q).repr.injective
  ext A
  have h := antisymmetric_ordered_sum Q
    (fun i => (occupationBasis Q).repr (f i) A) a (by
      intro i j; rw [hf,map_neg]; rfl)
  simpa only [map_sum,map_smul,Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,mul_comm] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem highestUnit_one_zero (Q : ℕ) (hQ : 1 ≤ Q) :
    highestUnit Q Q 1 0 = 1 / Real.sqrt 2 := by
  have hn := highestUnit_norm Q Q 1 hQ hQ
  have hr := highestUnit_reverse Q 1 0 (by omega)
  norm_num at hr
  simp only [show 1+1=2 by omega,Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at hn
  rw [hr] at hn
  have hp : 0 < highestUnit Q Q 1 0 := by
    rw [highestUnit,highestRaw_zero]
    have hqr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    simp only [Nat.choose_one_right]
    exact div_pos (by positivity) (highestNorm_pos Q Q 1 hQ hQ)
  have ht : 0 < (1 : ℝ)/Real.sqrt 2 := by positivity
  have hs : ((1 : ℝ)/Real.sqrt 2)^2 = 1/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith only [hn,hp,ht,hs]

theorem pairCoupledTensor_one_zero (Q : ℕ) (hQ : 1 ≤ Q) (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ 0 i = pairCoefficient Q 0 i.1 i.2 := by
  rw [pairCoupledTensor,genericUnitDescendant_zero]
  simp only [pow_one,Pi.smul_apply,smul_eq_mul,neg_one_mul]
  by_cases hi : i.1.val+i.2.val=1
  · let p : Fin 2 := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex Q Q 1 hQ hQ p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    have hv : genericHighest Q Q 1 hQ hQ i = highestUnit Q Q 1 i.1.val := by
      change extendWeightSlice Q Q 1 hQ hQ _ i = _
      rw [he,extendWeightSlice_at]; rfl
    rw [hv]
    have hqr : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    rcases (show i.1.val=0 ∨ i.1.val=1 by omega) with h0 | h1
    · have hj : i.2.val=1 := by omega
      simp [pairCoefficient,h0,hj,highestUnit_one_zero Q hQ,hqr,div_eq_mul_inv]
    · have hj : i.2.val=0 := by omega
      have hr := highestUnit_reverse Q 1 0 (by omega)
      norm_num at hr
      rw [h1,hr,highestUnit_one_zero Q hQ]
      simp [pairCoefficient,h1,hj,hqr]
  · have hv : genericHighest Q Q 1 hQ hQ i = 0 :=
      extendWeightSlice_off Q Q 1 hQ hQ _ i hi
    simp [hv,pairCoefficient,hi]

theorem pairCoupledTensor_lowering (Q r n : ℕ) (hr : r ≤ Q)
    (hn : n < genericCoupledWeight Q Q r) :
    (totalRaise Q Q)ᵀ *ᵥ pairCoupledTensor Q r hr n =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q r : ℝ)-n)) •
        pairCoupledTensor Q r hr (n+1) := by
  rw [pairCoupledTensor,Matrix.mulVec_smul,genericUnitDescendant_lowering Q Q r n hr hr hn]
  exact smul_comm _ _ _

theorem pairCoupledTensor_one (Q n : ℕ) (hQ : 1 ≤ Q) (hn : n ≤ 2*Q-2)
    (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ n i = pairCoefficient Q n i.1 i.2 := by
  induction n generalizing i with
  | zero => exact pairCoupledTensor_one_zero Q hQ i
  | succ n ih =>
    have hcw : genericCoupledWeight Q Q 1 = 2*Q-2 := by unfold genericCoupledWeight; omega
    have hlt : n < genericCoupledWeight Q Q 1 := by rw [hcw]; omega
    have hreal : (n : ℝ) < genericCoupledWeight Q Q 1 := by exact_mod_cast hlt
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (pairCoupledTensor_lowering Q 1 n hQ hlt) i
    have hf : pairCoupledTensor Q 1 hQ n = fun j => pairCoefficient Q n j.1 j.2 := by
      funext j; exact ih (by omega) j
    rw [hf] at he
    change (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n))*
        pairCoupledTensor Q 1 hQ (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have hc := pairCoefficient_tensor_lowering_s50 Q n (by omega) (by omega) i.1 i.2
    have hl : pairTensorLower Q n i.1 i.2 =
        (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) := by
      rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      unfold pairTensorLower; split_ifs <;> ring
    rw [hcw] at he hd
    have hw : ladder (2*Q-2) n = Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n)) := by
      unfold ladder
      rw [Nat.cast_sub (by omega : n ≤ 2*Q-2)]
    rw [hw] at hc
    have he' : pairTensorLower Q n i.1 i.2 =
      Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n))*pairCoupledTensor Q 1 hQ (n+1) i := by
      rw [hl,totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      exact he
    exact (mul_left_cancel₀ hd) (he'.symm.trans hc)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PairTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix Kronecker

theorem pairCoupledOne_contract (Q : ℕ) (hQ : 1 ≤ Q)
    (n : Fin (genericCoupledWeight Q Q 1+1)) (x : Space Q) :
    (∑ i : WedgePairIndex Q, (pairCoupledInclusion Q 1 hQ i n : ℂ) •
      annihilate i.val.2 (annihilate i.val.1 x)) = sourcePairEnd Q n.val x := by
  have hf (i j : Fin (Q+1)) : annihilate i (annihilate j x) =
      -annihilate j (annihilate i x) := by
    have h := LinearMap.congr_fun (annihilate_anticommute i j) x
    exact eq_neg_of_add_eq_zero_left h
  have he := antisymmetric_exterior_sum Q
    (fun i => annihilate i.2 (annihilate i.1 x)) hf
    (fun i => ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ))
  have hn : n.val ≤ 2*Q-2 := by have := n.isLt; unfold genericCoupledWeight at this; omega
  have hc (i : WedgePairIndex Q) :
      ((pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 : ℝ) : ℂ) -
        ((pairCoefficient Q n.val i.val.2 i.val.1 / Real.sqrt 2 : ℝ) : ℂ) =
      (pairCoupledInclusion Q 1 hQ i n : ℂ) := by
    rw [pairCoefficient_swap Q n.val i.val.1 i.val.2]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hreal : pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 -
        -pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 =
      Real.sqrt 2*pairCoefficient Q n.val i.val.1 i.val.2 := by
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [← Complex.ofReal_sub,hreal]
    simp only [pairCoupledInclusion,pairCoupledWedge,tensorToWedgePair,pairCoupledTensor_one Q n.val hQ hn]
  have he' := he.trans (Finset.sum_congr rfl (fun i hi =>
    congrArg (fun c : ℂ => c • annihilate i.val.2 (annihilate i.val.1 x)) (hc i)))
  calc
    _ = ∑ i : SpinIndex Q Q, ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ) •
        annihilate i.2 (annihilate i.1 x) := he'.symm
    _ = _ := by
      simp only [sourcePairEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,
        Module.End.mul_apply,Fintype.sum_prod_type]

theorem fourPairEmbedding_contract_s50_oai (Q : ℕ) (hQ : 1 ≤ Q)
    (j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1)) (x : Space Q) :
    (∑ i : FourWedgeIndex Q, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x) =
      sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x) := by
  simp only [fourPairEmbedding,Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,
    Matrix.map_apply,apply_ite,star_zero,Complex.star_def,Complex.conj_ofReal,
    ite_mul,one_mul,zero_mul,ite_smul,zero_smul,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact pairCoupledOne_contract Q hQ j.2 (sourcePairEnd Q j.1.val x)

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.fourPairEmbedding_contract_s50_oai := @OAI.Laughlin.Fock.fourPairEmbedding_contract_s50_oai
