-- Prove2me | solution 1 for HopfAlgebra.natCard_algHom_eq_finrank_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e087cfda-3d42-5db7-ad6b-8f395bb1a748

import Mathlib
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero

open TensorProduct

universe u v w

theorem solution (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H]
    (K : Type w) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] :
    Nat.card (H →ₐ[R] K) = Module.finrank R H := by
  haveI : Module.Finite K (K ⊗[R] H) := inferInstance
  haveI hEt : Algebra.Etale K (K ⊗[R] H) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero K (K ⊗[R] H)
  have hcount : Nat.card ((K ⊗[R] H) →ₐ[K] K) = Module.finrank K (K ⊗[R] H) :=
    Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed K (K ⊗[R] H)
  have hLHS : Nat.card (H →ₐ[R] K) = Nat.card ((K ⊗[R] H) →ₐ[K] K) := by
    refine Nat.card_congr ⟨?toFun, ?invFun, ?li, ?ri⟩
    case toFun =>
      refine fun f => ⟨(Algebra.TensorProduct.lift (AlgHom.id R K) f (fun _ _ => mul_comm _ _)).toRingHom, ?_⟩
      intro a
      show (Algebra.TensorProduct.lift (AlgHom.id R K) f (fun _ _ => mul_comm _ _))
          (algebraMap K (K ⊗[R] H) a) = algebraMap K K a
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_id, id_eq, map_one, mul_one]
    case invFun =>
      exact fun g => (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    case li =>
      intro f; ext h
      show (Algebra.TensorProduct.lift (AlgHom.id R K) f (fun _ _ => mul_comm _ _)) ((1 : K) ⊗ₜ[R] h) = f h
      rw [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, one_mul]
    case ri =>
      intro g
      apply AlgHom.ext
      intro x
      show (Algebra.TensorProduct.lift (AlgHom.id R K)
        ((g.restrictScalars R).comp Algebra.TensorProduct.includeRight) (fun _ _ => mul_comm _ _)) x = g x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a h =>
          have hinc : ((g.restrictScalars R).comp Algebra.TensorProduct.includeRight) h
              = g ((1 : K) ⊗ₜ[R] h) := rfl
          rw [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, hinc]
          calc a * g (1 ⊗ₜ[R] h)
              = a • g ((1 : K) ⊗ₜ[R] h) := (smul_eq_mul a _).symm
            _ = g (a • ((1 : K) ⊗ₜ[R] h)) := (map_smul g a _).symm
            _ = g (a ⊗ₜ[R] h) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hRHS : Module.finrank K (K ⊗[R] H) = Module.finrank R H := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  rw [hLHS, hcount, hRHS]

end S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero (solution)
