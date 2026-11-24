-- Prove2me | solution 1 for GlobalTheory.PDiv.mu_bialgHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:55.225066+00:00
-- url     : https://prove2.me/submissions/74e5ed51-9aad-49a4-bd21-b5a565f8e333

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
theorem _root_.solution {A : Type*} [CommRing A] [Bialgebra R A]
    {x y : AddMonoidAlgebra R (ZMod m) →ₐc[R] A} (h : x (muT R m) = y (muT R m)) : x = y :=
  BialgHom.coe_toAlgHom_injective (mu_algHom_ext h)
end GlobalTheory.PDiv
