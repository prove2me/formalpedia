-- Prove2me | solution 1 for GlobalTheory.HopfQuot.ev_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:43.859619+00:00
-- url     : https://prove2.me/submissions/7e9f3fb3-25fa-41d7-afa5-3b4559d5a484

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] [Module R Λ]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (B : Type*) [CommRing B] [Algebra R B] (f : Λ →ₗ[R] R) (b : B) (x : Λ) :
    ev B f (b ⊗ₜ x) = f x • b := by
  simp [ev]
end GlobalTheory.HopfQuot
