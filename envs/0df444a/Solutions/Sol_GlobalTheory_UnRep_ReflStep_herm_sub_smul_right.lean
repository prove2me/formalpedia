-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflStep.herm_sub_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:36.498946+00:00
-- url     : https://prove2.me/submissions/d1af8e6a-29e1-45bf-ad2f-14143e4487d9

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
theorem _root_.solution (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.UnRep.ReflStep
