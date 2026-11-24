-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.contract_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:20.340717+00:00
-- url     : https://prove2.me/submissions/fbec57f2-79da-48bd-8a62-a32cec1f4479

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
variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) (l : L →ₗ[K] K) (x : M) :
    contract hf' l (F x) = p (contract hf l x) := by
  refine induction_smul hf (p := fun x => contract hf' l (F x) = p (contract hf l x)) x
    (by simp) ?_ ?_
  · intro a v
    rw [map_smul, hF, contract_smul, contract_smul, map_smul]
  · intro x y hx hy
    simp only [map_add, hx, hy]
end GlobalTheory.GaloisDescent
