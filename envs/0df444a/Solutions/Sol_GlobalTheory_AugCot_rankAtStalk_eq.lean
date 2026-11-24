-- Prove2me | solution 1 for GlobalTheory.AugCot.rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:34.667819+00:00
-- url     : https://prove2.me/submissions/b55be921-9ea6-44cb-b930-6c9494ea7659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
namespace GlobalTheory.AugCot
theorem _root_.solution [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]] (p : PrimeSpectrum R) :
    Module.rankAtStalk (AugCot ε) p = Module.rankAtStalk Ω[A⁄R] (p.comap (ε : A →+* R)) := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  rw [Module.rankAtStalk_eq_of_equiv (kaehlerEquiv ε (fun _ => rfl)),
    Module.rankAtStalk_baseChange]
  rfl
end GlobalTheory.AugCot
