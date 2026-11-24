-- Prove2me | solution 1 for GlobalTheory.PDiv.comp_mulBy_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:53.242212+00:00
-- url     : https://prove2.me/submissions/8c94a163-1f17-4b5e-b208-8e557d1a6195

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
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm R A] {E : Type*} [CommRing E] [Algebra R E] (x : A →ₐ[R] E)
    (n : ℕ) : x.comp (mulBy R A n : A →ₐ[R] A) = (toConv x ^ n).ofConv := by
  have h := map_pow ((ptsPush A x).comp toPts) (toConv (BialgHom.id R A)) n
  exact congrArg ofConv h
end GlobalTheory.PDiv
