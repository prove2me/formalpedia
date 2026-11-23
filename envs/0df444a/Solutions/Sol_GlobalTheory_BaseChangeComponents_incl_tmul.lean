-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.incl_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:45.352925+00:00
-- url     : https://prove2.me/submissions/17129d67-2deb-4f70-b47f-88c12311d12f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution (R : Subalgebra K Ω) (a : F) (r : R) :
    incl F R (a ⊗ₜ r) = a ⊗ₜ (r : Ω) := rfl
end GlobalTheory.BaseChangeComponents
