-- Prove2me | solution 1 for GlobalTheory.PDiv.mulBy_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:19.009353+00:00
-- url     : https://prove2.me/submissions/f651c2f2-6422-4b23-ad8a-f6cdd4f907f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy

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
theorem _root_.solution [IsCocomm R A] (m n : ℕ) (a : A) :
    mulBy R A m (mulBy R A n a) = mulBy R A (m * n) a := by
  have h := comp_mulBy (mulBy R A m) n
  rw [mulBy, toConv_ofConv, ← pow_mul] at h
  exact DFunLike.congr_fun h a
end GlobalTheory.PDiv
