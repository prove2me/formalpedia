-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:51.713304+00:00
-- url     : https://prove2.me/submissions/f0a295d1-e9d5-4bbf-ab81-ea22baf46e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_add
import Theorems.Thm_GlobalTheory_RealWeil_dRho_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (w : l ⊕ l → ℝ) : dRho w = ∑ a, (w a : ℂ) • dRho (Pi.single a 1) := by
  let L : (l ⊕ l → ℝ) →+ (Sch l →L[ℂ] Sch l) := AddMonoidHom.mk' dRho dRho_add
  have : w = ∑ a, w a • (Pi.single a 1 : l ⊕ l → ℝ) := by
    ext b
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  exact (map_sum L _ _).trans (Finset.sum_congr rfl fun a _ => dRho_smul _ _)
end GlobalTheory.RealWeil
