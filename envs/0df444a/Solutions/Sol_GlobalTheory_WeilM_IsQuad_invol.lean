-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.invol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:08.010062+00:00
-- url     : https://prove2.me/submissions/4e294159-6c84-4e21-9dc0-9a59a4cc6afd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_eq

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
namespace GlobalTheory.WeilM.IsQuad
theorem _root_.solution (z : E) : c (c z) = z := by
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  simp [h.anti]
end GlobalTheory.WeilM.IsQuad
