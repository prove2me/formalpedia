-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.incl_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:20.258492+00:00
-- url     : https://prove2.me/submissions/3b1e1a4b-2bbc-4a27-ab64-060e99f48761

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
theorem _root_.solution (R : Subalgebra K Ω) : Function.Injective (incl F R) :=
  by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := F)
      R.val.toLinearMap Subtype.val_injective hxy
end GlobalTheory.BaseChangeComponents
