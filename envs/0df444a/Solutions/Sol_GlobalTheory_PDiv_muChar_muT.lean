-- Prove2me | solution 1 for GlobalTheory.PDiv.muChar_muT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:13.472806+00:00
-- url     : https://prove2.me/submissions/2b0e5ca5-6aef-4df4-9e01-0f39884bbe91

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
variable {R m} [NeZero m] {B : Type*} [CommRing B] [Algebra R B]
namespace GlobalTheory.PDiv
theorem _root_.solution {A : Type*} [CommRing A] [Bialgebra R A] (u : A)
    (hg : IsGroupLikeElem R u) (hu : u ^ m = 1) : muChar u hg hu (muT R m) = u :=
  muPoint_muT u hu
end GlobalTheory.PDiv
