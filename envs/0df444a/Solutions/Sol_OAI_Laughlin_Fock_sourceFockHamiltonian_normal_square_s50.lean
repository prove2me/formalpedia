-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:27:54.18954+00:00
-- url     : https://prove2.me/submissions/7c96e7e5-00a2-43e8-bf2a-6d49544a0841

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_sourcePairCreate_inner_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_EnergyRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourceFockEnergy_eq_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockEnergy Q x = ∑ p : Fin (2*Q-2+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  unfold sourceFockEnergy
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem sourceFockHamiltonian_apply_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairVector Q p.val * sourcePairEnd Q p.val x := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,sourcePairCreateEnd_mul]
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_annihilate_commute (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i : Fin (Q+1)) : pairEnd Q c * annihilate i = annihilate i * pairEnd Q c := by
  have h (a b : Fin (Q+1)) : annihilate b * annihilate a * annihilate i =
      annihilate i * (annihilate b * annihilate a) := by
    calc
      _ = annihilate b * (annihilate a * annihilate i) := mul_assoc _ _ _
      _ = annihilate b * -(annihilate i * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute a i)]
      _ = -(annihilate b * (annihilate i * annihilate a)) := by
        apply LinearMap.ext
        intro x
        exact map_neg (annihilate b) ((annihilate i * annihilate a) x)
      _ = -((annihilate b * annihilate i) * annihilate a) := by rw [mul_assoc]
      _ = -(-(annihilate i * annihilate b) * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute b i)]
      _ = _ := by
        apply LinearMap.ext
        intro x
        change -(-(annihilate i (annihilate b (annihilate a x)))) = _
        exact neg_neg _
  simp only [pairEnd,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,h]

theorem pairEnd_commute (Q : ℕ) (c d : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q c * pairEnd Q d = pairEnd Q d * pairEnd Q c := by
  conv_lhs => arg 2; unfold pairEnd
  conv_rhs => arg 1; unfold pairEnd
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ← mul_assoc,pairEnd_annihilate_commute]
  simp only [mul_assoc,pairEnd_annihilate_commute]

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

theorem sourceFockHamiltonian_normal_square_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  have hc (p q : Fin (2*Q-2+1)) :
      sourcePairEnd Q p.val (sourcePairEnd Q q.val x) =
        sourcePairEnd Q q.val (sourcePairEnd Q p.val x) :=
    LinearMap.congr_fun (pairEnd_commute Q _ _) x
  have hH : sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairCreateEnd Q p.val (sourcePairEnd Q p.val x) := by
    rw [sourceFockHamiltonian_apply_fin Q (by omega)]
    simp only [sourcePairCreateEnd_mul]
  have he : (occupationNormSq Q (sourceFockHamiltonian Q x) : ℂ) =
      (sourceFockEnergy Q x : ℂ) +
      contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
    rw [← occupationInner_self,hH,occupationInner_sum_left]
    simp_rw [occupationInner_sum_right,sourcePairCreate_inner_s50 Q hQ]
    have hl (p q : Fin (2*Q-2+1)) : occupationInner Q
        (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))
        (sourcePairEnd Q p.val (sourcePairEnd Q q.val x)) =
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
      rw [hc p q,occupationInner_self]
    simp only [Finset.sum_add_distrib,hl]
    congr 1
    · congr 1
      · rw [sourceFockEnergy_eq_fin Q (by omega),Complex.ofReal_sum]
        simp [occupationInner_self]
      · simp only [contractionForm,Fintype.sum_prod_type,sourceThreeEnd,Module.End.mul_apply]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
  have hr := congrArg Complex.re he
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.re_sum] using hr

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50_oai := @OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50_oai
