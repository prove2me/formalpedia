-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.isCompact_finset_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:21.279698+00:00
-- url     : https://prove2.me/submissions/34227d37-aabe-4b0b-942a-ef54f4201b9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_isCompact_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (t : Finset ι) (H : ι → AddSubgroup V) (hH : ∀ i, IsCompact (H i : Set V)) :
    IsCompact ((t.sup H : AddSubgroup V) : Set V) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sup_insert]; exact isCompact_sup _ _ (hH a) ih
end GlobalTheory.JR.WeilQuad.Fnf
