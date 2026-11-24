-- Prove2me | solution 1 for GlobalTheory.WeilM.isTilde_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:02.03281+00:00
-- url     : https://prove2.me/submissions/3562e586-ba38-4808-95b5-40349280c07c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_hilbertNinetyQuotientHom_eq_iff
import Theorems.Thm_GlobalTheory_WeilM_tilde_norm_quotient

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
theorem _root_.solution (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) (u : Eˣ) (t : Circle) :
    IsTilde c χ u t ↔ ∃ hu : u ∈ (h90 c).range, t = tilde c χ hχ ⟨u, hu⟩ := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain rfl := hilbertNinetyQuotientHom_eq_iff.mpr hz
    exact ⟨⟨z, rfl⟩, (tilde_norm_quotient χ hχ z).symm⟩
  · rintro ⟨⟨z, rfl⟩, rfl⟩
    exact ⟨z, hilbertNinetyQuotientHom_eq_iff.mp rfl, tilde_norm_quotient χ hχ z⟩
end GlobalTheory.WeilM
