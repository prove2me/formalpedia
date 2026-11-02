-- Prove2me | solution 1 for OAI.Laughlin.Fock.pairEnd_three_create_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:39:31.847596+00:00
-- url     : https://prove2.me/submissions/e2d9bbe6-9c37-4c0c-aa70-e1e0348564d7

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_vacuum {Q : ℕ} (a i : Fin (Q+1)) :
    annihilate a (create i (1 : Space Q)) = delta a i • (1 : Space Q) := by
  have h := LinearMap.congr_fun (mixed_car a i) (1 : Space Q)
  by_cases ha : a = i <;> simpa [Module.End.mul_apply,annihilate_vacuum,delta,ha] using h

theorem two_annihilate_three_create {Q : ℕ} (a b i j k : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (create k (1 : Space Q))))) =
      (delta a i*delta b j-delta b i*delta a j) • create k (1 : Space Q) -
      (delta a i*delta b k-delta b i*delta a k) • create j (1 : Space Q) +
      (delta a j*delta b k-delta b j*delta a k) • create i (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (create k (1 : Space Q))
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,Module.End.one_apply,annihilate_create_vacuum,map_smul,
    annihilate_vacuum,smul_zero,map_zero,add_zero,smul_smul] at h
  rw [h]
  module

theorem pairEnd_three_create_s50_oai (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j k : Fin (Q+1)) :
    pairEnd Q c (create i (create j (create k (1 : Space Q)))) =
      (c i j-c j i) • create k (1 : Space Q) -
      (c i k-c k i) • create j (1 : Space Q) +
      (c j k-c k j) • create i (1 : Space Q) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    two_annihilate_three_create,smul_add,smul_sub,smul_smul]
  simp [delta,mul_sub,sub_smul,mul_ite,ite_smul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.pairEnd_three_create_s50_oai := @OAI.Laughlin.Fock.pairEnd_three_create_s50_oai
