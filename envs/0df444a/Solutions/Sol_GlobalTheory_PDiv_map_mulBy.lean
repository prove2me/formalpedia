-- Prove2me | solution 1 for GlobalTheory.PDiv.map_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:13.645369+00:00
-- url     : https://prove2.me/submissions/1bf785dd-029d-4092-a7c7-42604bd571b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy
import Theorems.Thm_GlobalTheory_PDiv_mulBy_comp

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
theorem _root_.solution [IsCocomm R C] [IsCocomm R A] (f : C →ₐc[R] A) (n : ℕ) (c : C) :
    f (mulBy R C n c) = mulBy R A n (f c) :=
  DFunLike.congr_fun ((comp_mulBy f n).trans (mulBy_comp f n).symm) c
end GlobalTheory.PDiv
