-- Prove2me | solution 1 for GlobalTheory.DoublingLength.hasSum_of_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:24:52.843698+00:00
-- url     : https://prove2.me/submissions/dffcc6d3-ac1c-4622-a869-3c0345f3185d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution {β : Type} {P : β → Prop} (f : β → ℂ) {g : β → ℂ} {a b : ℂ} (c : ℂ)
    (h : HasSum (fun x : {x // P x} => f x.1) a) (h1 : ∀ x, P x → g x = f x * c) (h0 : ∀ x, ¬ P x → g x = 0)
    (hb : b = a * c) : HasSum g b := by
  have h2 : HasSum (fun x => Set.indicator {x | P x} f x * c) (a * c) :=
    ((hasSum_subtype_iff_indicator (s := {x | P x}) (f := f)).1 h).mul_right c
  have h3 : g = fun x => Set.indicator {x | P x} f x * c := funext fun x => by
    by_cases hx : P x
    · rw [h1 x hx, Set.indicator_of_mem (by exact hx)]
    · rw [h0 x hx, Set.indicator_of_notMem (by exact hx), zero_mul]
  rw [h3, hb]
  exact h2
end GlobalTheory.DoublingLength
