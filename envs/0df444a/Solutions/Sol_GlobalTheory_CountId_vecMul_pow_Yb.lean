-- Prove2me | solution 1 for GlobalTheory.CountId.vecMul_pow_Yb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:27.928326+00:00
-- url     : https://prove2.me/submissions/040a8b7f-8a01-4944-869b-8e23f5e16703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (l : V →ₗ[E] E) (i : ℕ) (j : Fin n) :
    ((fun j => l (e j)) ᵥ* (LinearMap.toMatrix e e T) ^ i) j = l ((T ^ i) (e j)) := by
  rw [LinearMap.toMatrix_pow]
  simp only [Matrix.vecMul, dotProduct, LinearMap.toMatrix_apply]
  conv_rhs => rw [← e.sum_repr ((T ^ i) (e j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
end GlobalTheory.CountId
