-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflStep.refl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:36.768581+00:00
-- url     : https://prove2.me/submissions/4cee7151-b2df-451e-893b-a7d3c30ea6c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflStep
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.UnRep.ReflStep
theorem _root_.solution (x v : Fin n → E) (u : E) :
    refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x := by
  have hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x := by
    simp only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring
end GlobalTheory.UnRep.ReflStep
