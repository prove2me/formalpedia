-- Prove2me | solution 1 for GlobalTheory.DualFibreRank.cmp_natural
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:16.369509+00:00
-- url     : https://prove2.me/submissions/f98f6eba-9577-48da-8be5-b76c02b2101d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange

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
theorem _root_.solution (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by
  ext g x
  simp [cmp]
end GlobalTheory.DualFibreRank
