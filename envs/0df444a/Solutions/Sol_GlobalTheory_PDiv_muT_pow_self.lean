-- Prove2me | solution 1 for GlobalTheory.PDiv.muT_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:30.842846+00:00
-- url     : https://prove2.me/submissions/4d5a5da7-c851-49a4-b1a8-6a3664d3f2cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable (R : Type*) [CommRing R] (m : ℕ)
namespace GlobalTheory.PDiv
theorem _root_.solution : muT R m ^ m = 1 := by
  rw [muT_pow, ZMod.natCast_self]; rfl
end GlobalTheory.PDiv
