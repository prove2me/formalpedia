-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.triv_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:13.302707+00:00
-- url     : https://prove2.me/submissions/a94d98ba-22e0-4fe9-9729-4e9d8edae5df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_unit_of_fixed

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
open GlobalTheory.WeilM.IsQuad
variable {ξ : E} (h : IsQuad c ξ)
include h
variable [Invertible (2 : R)]
namespace GlobalTheory.WeilM.IsQuad
theorem _root_.solution {χ : Eˣ →* Circle} (hχ : ∀ a : Rˣ, χ (Units.map (algebraMap R E : R →* E) a) = 1) (z : Eˣ)
    (hz : c z = z) : χ z = 1 := by
  obtain ⟨a, rfl⟩ := h.exists_unit_of_fixed hz
  exact hχ a
end GlobalTheory.WeilM.IsQuad
