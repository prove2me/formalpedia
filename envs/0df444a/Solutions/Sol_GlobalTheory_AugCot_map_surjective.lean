-- Prove2me | solution 1 for GlobalTheory.AugCot.map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:17.14514+00:00
-- url     : https://prove2.me/submissions/a997af5f-be9f-44b2-bfc6-b41f10e9374d

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
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}
namespace GlobalTheory.AugCot
theorem _root_.solution (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Surjective (map φ h) := by
  intro x
  obtain ⟨b, rfl⟩ := d_surjective εB x
  obtain ⟨a, rfl⟩ := hφ b
  exact ⟨d εA a, map_d φ h a⟩
end GlobalTheory.AugCot
