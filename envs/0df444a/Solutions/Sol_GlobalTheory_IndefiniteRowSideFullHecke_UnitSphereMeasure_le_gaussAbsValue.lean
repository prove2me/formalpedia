-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.le_gaussAbsValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:13.621591+00:00
-- url     : https://prove2.me/submissions/1a3d4e8b-df6d-484e-9235-94bd252ce4ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
theorem _root_.solution {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) (d : ι →₀ ℕ) :
    w (coeff d ω) ≤ gaussAbsValue w ω := by
  by_cases h : d ∈ ω.support
  · have := Finset.le_sup (f := fun d => Real.toNNReal (w (coeff d ω))) h
    exact Real.toNNReal_le_iff_le_coe.1 this
  · rw [notMem_support_iff.1 h]
    simp [gaussAbsValue]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
