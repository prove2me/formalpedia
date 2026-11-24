-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.contract_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:21.086085+00:00
-- url     : https://prove2.me/submissions/711d1c17-d8c6-45f9-b207-a8c5e2dca1c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_induction_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (x : M) :
    contract hf l (a • x) = contract hf (l ∘ₗ LinearMap.mulLeft K a) x := by
  refine induction_smul hf (p := fun x =>
    contract hf l (a • x) = contract hf (l ∘ₗ LinearMap.mulLeft K a) x) x (by simp) ?_ ?_
  · intro c v
    rw [smul_smul, contract_smul, contract_smul]
    rfl
  · intro x y hx hy
    rw [smul_add, map_add, map_add, hx, hy]
end GlobalTheory.GaloisDescent
