-- Prove2me | solution 1 for GlobalTheory.PDiv.kerIdeal_comp_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:00.474155+00:00
-- url     : https://prove2.me/submissions/559ebb11-5f22-4f37-b2b5-579476c252c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_of_surjective
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp

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
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution (g : A →ₐc[R] B) {f : C →ₐc[R] A}
    (hf : Function.Surjective f) : kerIdeal (g.comp f) = kerIdeal g := by
  rw [kerIdeal_comp, kerIdeal_of_surjective hf]
end GlobalTheory.PDiv
