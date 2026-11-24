-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_iff_hasQExpansion_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:41:31.38935+00:00
-- url     : https://prove2.me/submissions/947adb4e-06d9-4f77-a51c-14afd5d04e36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a) := by
  rw [hasQ_iff]
  simp only [GlobalTheory.HasQExpansion, Function.Periodic.qParam, PowerSeries.coeff_mk,
    Complex.ofReal_natCast]
end GlobalTheory.QFam
