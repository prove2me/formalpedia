-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourcePairCreate_inner_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:57:52.16218+00:00
-- url     : https://prove2.me/submissions/6fc1e0b5-d3ec-4376-bb0c-d5c61cf9d37e

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L011
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_create_inner_s50
import Theorems.Thm_OAI_Laughlin_Fock_pairCreate_pair_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_pairEnd_create_create_s50
import Theorems.Thm_OAI_Laughlin_pairCoefficient_unit_norm_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_PositiveFockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

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

theorem pairCoefficient_orthogonal (Q p q : ℕ) (hpq : p ≠ q) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hp : x.val+y.val = p+1
  · have hq : x.val+y.val ≠ q+1 := by omega
    simp [pairCoefficient, hq]
  · simp [pairCoefficient, hp]

theorem pairCoefficient_gram (Q p q : ℕ) (hQ : 2 ≤ Q)
    (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    simpa only [pow_two] using pairCoefficient_unit_norm_s50 Q p hQ hp
  · rw [ite_eq_right h]
    exact pairCoefficient_orthogonal Q p q h

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PairAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pair_weight_difference (Q p : ℕ) (i j : Fin (Q+1)) :
    pairCoefficient Q p i j / Real.sqrt 2 - pairCoefficient Q p j i / Real.sqrt 2 =
      Real.sqrt 2 * pairCoefficient Q p i j := by
  rw [pairCoefficient_swap Q p i j]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  calc
    _ = 2*pairCoefficient Q p i j / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2*Real.sqrt 2)*pairCoefficient Q p i j / Real.sqrt 2 := by
      rw [Real.mul_self_sqrt (by norm_num)]
    _ = _ := by field_simp

theorem pair_weight_product (Q p q : ℕ) (i j k l : Fin (Q+1)) :
    ((pairCoefficient Q q i j / Real.sqrt 2 : ℝ) : ℂ) *
      (((pairCoefficient Q p k l / Real.sqrt 2 : ℝ) : ℂ) -
       ((pairCoefficient Q p l k / Real.sqrt 2 : ℝ) : ℂ)) =
      (pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p k l : ℂ) := by
  rw [← Complex.ofReal_sub,pair_weight_difference]
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_sub_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y-z) = occupationInner Q x y-occupationInner Q x z := by
  simp [occupationInner,mul_sub,Finset.sum_sub_distrib]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem swapCompression_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    swapCompression Q a b = ∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  have he (i : TripleIndex Q) :
      ((tripleInclusion Q)ᵀ * swap23Matrix Q) a i = tripleInclusion Q (swap23 i) a := by
    have hi (k : TripleIndex Q) : swap23 k=i ↔ k=swap23 i := by
      constructor
      · intro h; simpa using congrArg swap23 h
      · intro h; rw [h,swap23_involutive]
    simp [Matrix.mul_apply,swap23Matrix,hi,Matrix.transpose_apply]
  unfold swapCompression
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [tripleInclusion,pairInclusion,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,swap23]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairCoefficient_swap Q a.1.val t b.2,pairCoefficient_swap Q b.1.val t a.2]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_PairNormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourcePair_normal_order (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    sourcePairEnd Q p * sourcePairCreateEnd Q q =
      (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) -
      (2 : ℂ) • (∑ i, ∑ j, ∑ t,
        ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
          (create i * annihilate j)) +
      sourcePairCreateEnd Q q * sourcePairEnd Q p := by
  let F : Module.End ℂ (Space Q) := ∑ i, ∑ j,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • 1
  let U : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ)) • (create j * annihilate b)
  let V : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j b : ℂ)) • (create i * annihilate b)
  have hexp : sourcePairEnd Q p * sourcePairCreateEnd Q q =
      F-U+V+sourcePairCreateEnd Q q * sourcePairEnd Q p := by
    simp only [sourcePairCreateEnd,pairCreateEnd,Complex.star_def,Complex.conj_ofReal,
      Finset.mul_sum,mul_smul_comm,← mul_assoc,sourcePairEnd,pairEnd_create_create_s50,
      smul_add,smul_sub,Finset.smul_sum,smul_smul,pair_weight_product,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_mul,smul_mul_assoc,F,U,V]
  have hF : F = (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg Complex.ofReal (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    congr 1
    by_cases he : p=q <;> simpa [he,mul_comm] using hg
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro b hb
    rw [pairCoefficient_swap Q q i j]
    simp only [Complex.ofReal_neg,neg_mul]
    apply LinearMap.ext
    intro x
    exact neg_smul ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ))
      ((create j * annihilate b) x)
  have hU : U = ∑ i, ∑ j, ∑ t,
      ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
        (create i * annihilate j) := by
    dsimp [U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro t ht
    rw [pairCoefficient_swap Q q t i,pairCoefficient_swap Q p t j]
    simp [mul_comm]
  rw [hexp,hF,hV,hU]
  module

theorem complexThreeGram_sub_one_entry (Q : ℕ) (a b : Spin.PairOrbitalIndex Q) :
    (complexThreeGram Q-1) a b = -2 * ∑ t,
      (pairCoefficient Q a.1.val b.2 t : ℂ)*(pairCoefficient Q b.1.val a.2 t : ℂ) := by
  simp only [complexThreeGram,Spin.threeGram,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Spin.swapCompression_entry,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_sum]
  have h : ((1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ) a b : ℂ) =
      (1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ) a b := by
    classical
    by_cases hab : a=b <;> simp [hab,Matrix.one_apply]
  rw [h]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_NormalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem pair_annihilate_create_inner (Q p : ℕ) (x y : Space Q) :
    occupationInner Q x (sourcePairCreateEnd Q p y) =
      occupationInner Q (sourcePairEnd Q p x) y := by
  have h := congrArg star (pairCreate_pair_adjoint_s50 Q
    (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) y x)
  simpa only [occupationInner_star,sourcePairCreateEnd,sourcePairEnd] using h

theorem sourcePairCreate_inner_s50_oai (Q : ℕ) (hQ : 2 ≤ Q)
    (p q : Fin (2*Q-2+1)) (y z : Space Q) :
    occupationInner Q (sourcePairCreateEnd Q p.val y) (sourcePairCreateEnd Q q.val z) =
      (if p=q then (1 : ℂ) else 0) * occupationInner Q y z +
      (∑ i, ∑ j, (complexThreeGram Q-1) (p,i) (q,j) *
        occupationInner Q (annihilate i y) (annihilate j z)) +
      occupationInner Q (sourcePairEnd Q q.val y) (sourcePairEnd Q p.val z) := by
  rw [sourcePairCreateEnd,pairCreate_pair_adjoint_s50]
  change occupationInner Q y ((sourcePairEnd Q p.val * sourcePairCreateEnd Q q.val) z) = _
  rw [sourcePair_normal_order Q p.val q.val hQ (by omega)]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_add_right,occupationInner_sub_right,occupationInner_smul_right,
    occupationInner_sum_right,annihilate_create_inner_s50,pair_annihilate_create_inner,
    complexThreeGram_sub_one_entry,Finset.sum_mul,Finset.mul_sum]
  have he : p.val=q.val ↔ p=q := Fin.val_inj
  simp only [he]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourcePairCreate_inner_s50_oai := @OAI.Laughlin.Fock.sourcePairCreate_inner_s50_oai
