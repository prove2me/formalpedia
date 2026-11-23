-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflStep.herm_sub_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:36.440979+00:00
-- url     : https://prove2.me/submissions/549c2b57-43de-4d84-a6d0-a79216ec6c3f

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
    hermE c G (z - e • x) w = hermE c G z w - e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.UnRep.ReflStep
