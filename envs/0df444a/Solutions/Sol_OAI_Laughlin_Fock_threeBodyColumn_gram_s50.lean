-- Prove2me | solution 1 for OAI.Laughlin.Fock.threeBodyColumn_gram_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:59:21.077607+00:00
-- url     : https://prove2.me/submissions/ccf205f3-7102-4ae9-9e67-4694757daf52

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_pairCreate_pair_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_pairEnd_three_create_s50
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

theorem sourcePairCreate_apply (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = ∑ i, ∑ j,
      ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) • create i (create j x) := by
  simp [sourcePairCreateEnd,pairCreateEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]

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

theorem sourcePair_threeBodyColumn (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (k : Fin (Q+1)) :
    sourcePairEnd Q p (threeBodyColumn Q q k) =
      (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) -
      (2 : ℂ) • (∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p i k : ℂ)) •
        create j (1 : Space Q)) := by
  let F : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • create k (1 : Space Q)
  let U : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i k : ℂ)) • create j (1 : Space Q)
  let V : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j k : ℂ)) • create i (1 : Space Q)
  have hexp : sourcePairEnd Q p (threeBodyColumn Q q k) = F-U+V := by
    rw [threeBodyColumn,sourcePairCreate_apply]
    simp only [map_sum,map_smul,sourcePairEnd,pairEnd_three_create_s50,
      smul_add,smul_sub,smul_smul,pair_weight_product]
    simp only [F,U,V,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hF : F = (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    rw [show (∑ i, ∑ j, (pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) =
      (if p = q then 1 else 0) by by_cases he : p = q <;> simpa [he,mul_comm] using hg]
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [pairCoefficient_swap Q q i j]
    simp
  rw [hexp,hF,hV]
  change _ = _ - (2 : ℂ) • U
  module

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

theorem occupationInner_oneMode (Q : ℕ) (i j : Fin (Q+1)) :
    occupationInner Q (create i (1 : Space Q)) (create j (1 : Space Q)) =
      if i = j then 1 else 0 := by
  have h (k : Fin (Q+1)) : create k (1 : Space Q) = occupationBasis Q {k} := by
    rw [occupation_singleton]
    simp [create]
  rw [h i,h j]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem threeBodyColumn_gram_s50_oai (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    occupationInner Q (threeBodyColumn Q p i) (threeBodyColumn Q q j) =
      (if p = q then (1 : ℂ) else 0)*(if i = j then (1 : ℂ) else 0) -
      2 * ∑ t, (pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ) := by
  rw [threeBodyColumn,sourcePairCreateEnd,pairCreate_pair_adjoint_s50]
  change occupationInner Q (create i (1 : Space Q))
    (sourcePairEnd Q p (threeBodyColumn Q q j)) = _
  rw [sourcePair_threeBodyColumn Q p q hQ hp j,occupationInner_sub_right,
    occupationInner_smul_right,occupationInner_smul_right]
  simp only [occupationInner_sum_right,occupationInner_smul_right,occupationInner_oneMode]
  simp only [mul_ite,mul_one,mul_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [pairCoefficient_swap Q q i t,pairCoefficient_swap Q p j t]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.threeBodyColumn_gram_s50_oai := @OAI.Laughlin.Fock.threeBodyColumn_gram_s50_oai
