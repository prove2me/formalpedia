-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.measurePreserving_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:10.00739+00:00
-- url     : https://prove2.me/submissions/dd25fb61-1d46-488b-b903-b3abe14fa79a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution (X : Type) [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (n : ℕ) : MeasurePreserving
      (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) volume volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm
  have e : (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  rw [e]
  exact h
end GlobalTheory.GLFirstColumn
