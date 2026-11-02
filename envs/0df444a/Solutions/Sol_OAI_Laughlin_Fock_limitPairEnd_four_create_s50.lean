-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitPairEnd_four_create_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:37:51.87864+00:00
-- url     : https://prove2.me/submissions/8f7f85e9-438c-4a5f-a481-5c4484c22539

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_apply (Q : ℕ) (a b : Fin (Q+1)) (x : Space Q) :
    annihilate a (create b x) = delta a b • x - create b (annihilate a x) := by
  have h := LinearMap.congr_fun (annihilate_create a b) x
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using h

theorem annihilate_three_create (Q : ℕ) (a x y z : Fin (Q+1)) :
    annihilate a (create x (create y (create z (1 : Space Q)))) =
      delta a x • create y (create z (1 : Space Q)) -
      delta a y • create x (create z (1 : Space Q)) +
      delta a z • create x (create y (1 : Space Q)) := by
  simp only [annihilate_create_apply,annihilate_vacuum,map_zero,sub_zero,map_sub,map_smul]
  abel

theorem annihilate_four_create (Q : ℕ) (a x y z w : Fin (Q+1)) :
    annihilate a (create x (create y (create z (create w (1 : Space Q))))) =
      delta a x • create y (create z (create w (1 : Space Q))) -
      delta a y • create x (create z (create w (1 : Space Q))) +
      delta a z • create x (create y (create w (1 : Space Q))) -
      delta a w • create x (create y (create z (1 : Space Q))) := by
  rw [annihilate_create_apply,annihilate_three_create]
  simp only [map_sub,map_add,map_smul]
  abel

theorem pairEnd_four_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y z w : Fin (Q+1)) :
    pairEnd Q c (create x (create y (create z (create w (1 : Space Q))))) =
      (c x y-c y x) • create z (create w (1 : Space Q)) -
      (c x z-c z x) • create y (create w (1 : Space Q)) +
      (c x w-c w x) • create y (create z (1 : Space Q)) +
      (c y z-c z y) • create x (create w (1 : Space Q)) -
      (c y w-c w y) • create x (create z (1 : Space Q)) +
      (c z w-c w z) • create x (create y (1 : Space Q)) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    annihilate_four_create,map_sub,map_add,map_smul,annihilate_three_create,
    smul_sub,smul_add,smul_smul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [delta,mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [sub_smul]
  abel

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

namespace Laughlin

theorem pairLimitCoefficient_swap (p x y : ℕ) :
    pairLimitCoefficient p y x = -pairLimitCoefficient p x y := by
  unfold pairLimitCoefficient
  rw [Nat.add_comm y x]
  split_ifs
  · rw [show ((2 : ℕ) : ℝ)^p * y.factorial*x.factorial =
      ((2 : ℕ) : ℝ)^p*x.factorial*y.factorial by ring]
    ring
  · simp

theorem pairLimitCoefficient_difference (p x y : ℕ) :
    pairLimitCoefficient p x y / Real.sqrt 2 - pairLimitCoefficient p y x / Real.sqrt 2 =
      Real.sqrt 2 * pairLimitCoefficient p x y := by
  rw [pairLimitCoefficient_swap p x y]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = 2 * pairLimitCoefficient p x y / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2 * Real.sqrt 2) * pairLimitCoefficient p x y / Real.sqrt 2 := by rw [h]
    _ = _ := by field_simp

end Laughlin

namespace Laughlin.Fock
open scoped BigOperators

theorem limitPairEnd_four_create_s50_oai (Q p : ℕ) (a b c d : Fin (Q+1)) :
    limitPairEnd Q p (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) • create c (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) • create b (create d (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) • create b (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) • create a (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) • create a (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) • create a (create b (1 : Space Q)) := by
  unfold limitPairEnd
  rw [pairEnd_four_create]
  have he (x y : ℕ) : ((pairLimitCoefficient p x y / Real.sqrt 2 : ℝ) : ℂ) -
      ((pairLimitCoefficient p y x / Real.sqrt 2 : ℝ) : ℂ) =
      ((Real.sqrt 2 * pairLimitCoefficient p x y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub,pairLimitCoefficient_difference]
  simp only [he]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitPairEnd_four_create_s50_oai := @OAI.Laughlin.Fock.limitPairEnd_four_create_s50_oai
