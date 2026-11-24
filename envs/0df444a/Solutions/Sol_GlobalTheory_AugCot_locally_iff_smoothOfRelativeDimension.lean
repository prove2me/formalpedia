-- Prove2me | solution 1 for GlobalTheory.AugCot.locally_iff_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:47.309195+00:00
-- url     : https://prove2.me/submissions/98801e6b-f93e-4c7f-8c80-0ffca84ff467

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
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}
open AlgebraicGeometry
namespace GlobalTheory.AugCot
theorem _root_.solution :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A) ↔
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := CommRingCat.ofHom (algebraMap R A))).symm
end GlobalTheory.AugCot
