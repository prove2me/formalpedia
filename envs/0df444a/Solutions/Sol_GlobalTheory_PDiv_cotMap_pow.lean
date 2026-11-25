-- Prove2me | solution 1 for GlobalTheory.PDiv.cotMap_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:42.522903+00:00
-- url     : https://prove2.me/submissions/e83bc1e6-830e-4d83-b22c-c9af2961a897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_cotMap_one
import Theorems.Thm_GlobalTheory_PDiv_cotMap_mul

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
theorem _root_.solution [IsCocomm R C] (f : WithConv (C →ₐc[R] A)) (n : ℕ) :
    cotMap (f ^ n).ofConv = n • cotMap f.ofConv := by
  induction n with
  | zero => rw [pow_zero, cotMap_one, zero_smul]
  | succ n ih => rw [pow_succ, cotMap_mul, ih, succ_nsmul]
end GlobalTheory.PDiv
