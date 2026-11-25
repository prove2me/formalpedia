-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finite_support_log_gaussAbsValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:18.861925+00:00
-- url     : https://prove2.me/submissions/3f383fde-5ed3-4435-8b67-fa730dafe4dd

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
theorem _root_.solution {ι : Type} {ω : MvPolynomial ι K} (h : ω ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbsValue w ω)).Finite := by
  have hf : (⋃ d ∈ ω.support, Function.mulSupport fun w : FinitePlace K => w (coeff d ω)).Finite :=
    ω.support.finite_toSet.biUnion fun d hd =>
      FinitePlace.hasFiniteMulSupport (mem_support_iff.1 hd)
  refine hf.subset fun w hw => ?_
  obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w h
  refine Set.mem_biUnion hd fun h1 => hw ?_
  simp only at h1
  simp [e, h1]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
