-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflLaws.hermE_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:36.159116+00:00
-- url     : https://prove2.me/submissions/ec8a3b36-d7f5-4d6c-b029-2c4d06309326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws

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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflLaws
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.UnRep.ReflLaws
namespace _root_.GlobalTheory.UnRep.ReflLaws
theorem _root_.solution (v x : Fin n → E) :
    _root_.GlobalTheory.UnRep.hermE c G v x = (G *ᵥ fun b => c (x b)) ⬝ᵥ v := by
  unfold _root_.GlobalTheory.UnRep.hermE
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end _root_.GlobalTheory.UnRep.ReflLaws
end GlobalTheory.UnRep.ReflLaws
