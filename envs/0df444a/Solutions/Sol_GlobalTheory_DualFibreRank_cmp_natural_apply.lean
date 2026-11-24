-- Prove2me | solution 1 for GlobalTheory.DualFibreRank.cmp_natural_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:55.524032+00:00
-- url     : https://prove2.me/submissions/8df7b7e8-c452-4d80-834c-68506e25ff0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Theorems.Thm_GlobalTheory_DualFibreRank_cmp_natural

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]
variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
namespace GlobalTheory.DualFibreRank
theorem _root_.solution (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) :=
  LinearMap.congr_fun (cmp_natural A f) x
end GlobalTheory.DualFibreRank
