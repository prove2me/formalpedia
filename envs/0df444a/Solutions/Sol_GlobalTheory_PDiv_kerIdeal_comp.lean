-- Prove2me | solution 1 for GlobalTheory.PDiv.kerIdeal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:50.258292+00:00
-- url     : https://prove2.me/submissions/04a5d9e8-a969-4d18-8e7d-31c6809d309b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_IsBicharacter_map


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
theorem _root_.solution (g : A →ₐc[R] B) (f : C →ₐc[R] A) :
    kerIdeal (g.comp f) = Ideal.map (g : A →ₐ[R] B) (kerIdeal f) :=
  (Ideal.map_mapₐ (f : C →ₐ[R] A) (g : A →ₐ[R] B)).symm
end GlobalTheory.PDiv
