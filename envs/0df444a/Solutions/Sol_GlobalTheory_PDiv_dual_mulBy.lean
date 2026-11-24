-- Prove2me | solution 1 for GlobalTheory.PDiv.dual_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:31.597799+00:00
-- url     : https://prove2.me/submissions/1cde3fe3-0da7-4b17-93cc-5cd055953c81

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
variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R C] [Module.Projective R C]
  [IsCocomm R A] [IsCocomm R C]
namespace GlobalTheory.PDiv
theorem _root_.solution (n : ℕ) : CartierDual.map (mulBy R A n) = mulBy R (CartierDual R A) n :=
  congrArg ofConv (map_pow (dualMonoidHom R A A) (toConv (BialgHom.id R A)) n)
end GlobalTheory.PDiv
