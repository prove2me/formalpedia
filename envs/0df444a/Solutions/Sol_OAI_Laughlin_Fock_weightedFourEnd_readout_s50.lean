-- Prove2me | solution 1 for OAI.Laughlin.Fock.weightedFourEnd_readout_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:41:08.883813+00:00
-- url     : https://prove2.me/submissions/0b38af65-0809-4a70-bc18-a1fd286aa710

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L013
import Theorems.Thm_OAI_Laughlin_Fock_limitPairEnd_four_create_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

theorem normal_order_two_inner {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (annihilate b * create d) -
      delta b c • (annihilate a * create d) +
      create c * annihilate b * annihilate a * create d := by
  calc
    _ = annihilate b * (annihilate a * create c) * create d := by noncomm_ring
    _ = delta a c • (annihilate b * create d) -
        (annihilate b * create c) * annihilate a * create d := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b c]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_NormalOrderFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem normal_order_two_one {Q : ℕ} (a b d : Fin (Q+1)) :
    annihilate b * annihilate a * create d =
      delta a d • annihilate b - delta b d • annihilate a +
        create d * annihilate b * annihilate a := by
  calc
    _ = annihilate b * (annihilate a * create d) := by noncomm_ring
    _ = delta a d • annihilate b - (annihilate b * create d) * annihilate a := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b d]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

theorem normal_order_four {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (delta b d • (1 : Module.End ℂ (Space Q))) -
      delta b c • (delta a d • (1 : Module.End ℂ (Space Q))) -
      delta a c • (create d * annihilate b) +
      delta b c • (create d * annihilate a) +
      delta a d • (create c * annihilate b) -
      delta b d • (create c * annihilate a) +
      create c * create d * annihilate b * annihilate a := by
  rw [normal_order_two_inner, annihilate_create b d, annihilate_create a d]
  have h : create c * annihilate b * annihilate a * create d =
      create c * (annihilate b * annihilate a * create d) := by noncomm_ring
  rw [h, normal_order_two_one]
  simp only [smul_sub, mul_add, mul_sub, mul_smul_comm]
  noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_PairNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_vacuum {Q : ℕ} (i : Fin (Q+1)) : annihilate i (1 : Space Q) = 0 := by
  simp [annihilate]

theorem two_annihilate_two_create {Q : ℕ} (a b i j : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (1 : Space Q)))) =
      (delta a i*delta b j-delta b i*delta a j) • (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (1 : Space Q)
  simpa [Module.End.mul_apply, annihilate_vacuum, smul_smul, sub_smul] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_LimitCARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem limitFourEnd_four_create (Q p : ℕ) (j k a b c d : Fin (Q+1)) :
    limitFourEnd Q p j k (create a (create b (create c (create d (1 : Space Q))))) =
      (((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) * wedgeDelta Q j k c d -
       ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) * wedgeDelta Q j k b d +
       ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) * wedgeDelta Q j k b c +
       ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) * wedgeDelta Q j k a d -
       ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a c +
       ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a b) • (1 : Space Q) := by
  simp only [limitFourEnd,Module.End.mul_apply,limitPairEnd_four_create_s50,map_sub,map_add,map_smul,
    two_annihilate_two_create,smul_smul,wedgeDelta,sub_smul,add_smul,smul_sub,mul_sub]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_WeightedReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_weighted_wedgeDelta (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) = (S a b : ℂ) := by
  simp only [wedgeDelta,delta,mul_sub,mul_ite,mul_one,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hS a b]
  push_cast
  ring

theorem sum_weighted_wedgeDelta_factor (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (c : ℂ) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*(c*wedgeDelta Q j k a b)) = c*(S a b : ℂ) := by
  calc
    _ = c*(∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk; ring
    _ = _ := by rw [sum_weighted_wedgeDelta Q S hS a b]

theorem weightedFourEnd_readout_s50_oai (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b c d : Fin (Q+1)) :
    weightedFourEnd Q p S (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val*S c d -
        Real.sqrt 2*pairLimitCoefficient p a.val c.val*S b d +
        Real.sqrt 2*pairLimitCoefficient p a.val d.val*S b c +
        Real.sqrt 2*pairLimitCoefficient p b.val c.val*S a d -
        Real.sqrt 2*pairLimitCoefficient p b.val d.val*S a c +
        Real.sqrt 2*pairLimitCoefficient p c.val d.val*S a b : ℝ) : ℂ) • (1 : Space Q) := by
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply,limitFourEnd_four_create,
    smul_smul,← Finset.sum_smul]
  congr 1
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    sum_weighted_wedgeDelta_factor Q S hS]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.weightedFourEnd_readout_s50_oai := @OAI.Laughlin.Fock.weightedFourEnd_readout_s50_oai
