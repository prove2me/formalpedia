-- Prove2me | solution 1 for GlobalTheory.AugCot.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:11.442677+00:00
-- url     : https://prove2.me/submissions/527e1686-1a31-4fd7-93cc-42570aa8ad34

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
theorem _root_.solution (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (h : εB.comp φ = εA) (h' : εC.comp ψ = εB)
    (h'' : εC.comp (ψ.comp φ) = εA := by rw [← AlgHom.comp_assoc, h', h]) :
    map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h :=
  hom_ext fun a => by simp
end GlobalTheory.AugCot
