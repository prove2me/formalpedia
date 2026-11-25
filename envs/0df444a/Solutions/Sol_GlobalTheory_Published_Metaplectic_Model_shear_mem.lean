-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.Model.shear_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:25.51449+00:00
-- url     : https://prove2.me/submissions/603c5fc6-636d-45d0-9642-0e94d381b9ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear

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
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Published.Metaplectic.Model
theorem _root_.solution (C : Matrix ι ι ℝ) (hC : Cᵀ = C) : fromBlocks 1 0 C 1 ∈ symplecticGroup ι ℝ := by
  rw [SymplecticGroup.mem_iff]
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hC]
end GlobalTheory.Published.Metaplectic.Model
