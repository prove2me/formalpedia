-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:20.151796+00:00
-- url     : https://prove2.me/submissions/abfe0d21-4438-4ac1-ae50-83dd51208487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
import Theorems.Thm_GlobalTheory_Published_Metaplectic_coe_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Published.Metaplectic
theorem _root_.solution (p q : ι → ℝ) (φ : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) :
    rho (p, q) φ x = cexp (2 * π * ((x ⬝ᵥ q + p ⬝ᵥ q / 2 : ℝ) : ℂ) * I) * φ (x + p) := by
  rw [coe_rho]
  simp only [GlobalTheory.WeilM.schr, eChar_apply, invOf_eq_inv]
  congr 2
  push_cast
  ring
end GlobalTheory.Published.Metaplectic
