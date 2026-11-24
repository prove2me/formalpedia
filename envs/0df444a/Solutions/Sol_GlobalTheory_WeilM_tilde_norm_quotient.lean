-- Prove2me | solution 1 for GlobalTheory.WeilM.tilde_norm_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:47.25307+00:00
-- url     : https://prove2.me/submissions/e2f0f4f0-c238-480e-91e9-e6bf0d5f9da9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
namespace GlobalTheory.WeilM
theorem _root_.solution (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) (z : Eˣ) :
    tilde c χ hχ ⟨h90 c z, z, rfl⟩ = χ z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z
end GlobalTheory.WeilM
