-- Prove2me | solution 1 for OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:33:01.862836+00:00
-- url     : https://prove2.me/submissions/7c9b1df1-3008-4845-83e4-1e47c6a03f4c

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_threeBodyColumn_gram_s50

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

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

theorem occupationNormSq_eq_zero (Q : ℕ) (x : Space Q) :
    occupationNormSq Q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hc : ∀ A, (occupationBasis Q).repr x A = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun A (_ : A ∈ Finset.univ) => sq_nonneg ‖(occupationBasis Q).repr x A‖)).mp h
      intro A
      have ha := hs A (Finset.mem_univ A)
      simpa using ha
    apply (occupationBasis Q).repr.injective
    ext A
    simp [hc]
  · intro h
    simp [h,occupationNormSq]

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

theorem threeGram_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    threeGram Q a b = (if a=b then 1 else 0) - 2*∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  simp only [threeGram,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    swapCompression_entry]

theorem threeGram_physical (Q : ℕ) (hQ : 2 ≤ Q) (a b : PairOrbitalIndex Q) :
    (threeGram Q a b : ℂ) =
      Fock.occupationInner Q (Fock.threeBodyColumn Q a.1.val a.2)
        (Fock.threeBodyColumn Q b.1.val b.2) := by
  rw [threeGram_entry,Fock.threeBodyColumn_gram_s50 Q a.1.val b.1.val hQ (by omega)]
  push_cast
  congr 1
  by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;>
    simp [Prod.ext_iff,ha,hb]
  simp_all [Fin.ext_iff]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem threeWedge_inner (Q : ℕ) (hQ : 2 ≤ Q) (u v : Spin.PairOrbitalIndex Q → ℂ) :
    occupationInner Q (threeWedge Q u) (threeWedge Q v) =
      ∑ a, star (u a)*(complexThreeGram Q *ᵥ v) a := by
  unfold threeWedge
  rw [occupationInner_sum_left]
  simp_rw [occupationInner_smul_left,occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,complexThreeGram]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Spin.threeGram_physical Q hQ a b]
  ring

theorem threeWedge_zero_of_gram_zero_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (u : Spin.PairOrbitalIndex Q → ℂ)
    (hu : complexThreeGram Q *ᵥ u=0) : threeWedge Q u=0 := by
  apply (occupationNormSq_eq_zero Q _).mp
  apply Complex.ofReal_injective
  rw [← occupationInner_self,threeWedge_inner Q hQ,hu]
  simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50_oai := @OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50_oai
