-- Prove2me | solution 2 for GlobalTheory.monoVal_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:42.7438+00:00
-- url     : https://prove2.me/submissions/f83bfee5-f5cb-4ea8-bb2b-253dc83c77e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} {ι : Type*}
namespace GlobalTheory
theorem _root_.solution [CommMonoid R] [Fintype ι] (f : ι → R) (α : ι →₀ ℕ) :
    monoVal f α = ∏ i, f i ^ α i :=
  Finsupp.prod_fintype _ _ (by simp)
end GlobalTheory
