-- Prove2me | solution 1 for GlobalTheory.Doubling.continuous_npow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.003796+00:00
-- url     : https://prove2.me/submissions/45763181-87cf-4850-941e-6d637d8c65c2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_npow_eq_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
namespace GlobalTheory.Doubling
theorem _root_.solution {X : Type} [TopologicalSpace X] {f : X → ℝ≥0} (hf : Continuous f) (h : ∀ x, 0 < f x) (t : ℂ) :
    Continuous fun x => npow (f x) t := by
  simp only [npow_eq_exp (h _)]
  exact ((Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp hf).log fun x => (NNReal.coe_pos.2 (h x)).ne')).mul continuous_const).cexp
end GlobalTheory.Doubling
