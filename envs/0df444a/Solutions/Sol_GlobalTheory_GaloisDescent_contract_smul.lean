-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.contract_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:52.321298+00:00
-- url     : https://prove2.me/submissions/f1c0d0b6-7f76-491f-81fc-2a5b617055e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (v : V) :
    contract hf l (a • f v) = l a • v := by
  simp [contract, hf.equiv_symm_apply, smul_tmul']
end GlobalTheory.GaloisDescent
