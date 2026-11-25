-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.fixedAlgEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:55:41.148377+00:00
-- url     : https://prove2.me/submissions/f586e0db-8865-4fd2-90b1-8c54b9c80977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange



set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L G A : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [Ring A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction G A] [SMulDistribClass G L A] [SMulCommClass G K A]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution [Finite G] [IsGaloisGroup G K L] (l : L)
    (a : FixedPoints.subalgebra K A G) : fixedAlgEquiv K L G A (l ⊗ₜ a) = l • (a : A) := by
  simp [fixedAlgEquiv]
end GlobalTheory.GaloisDescent
