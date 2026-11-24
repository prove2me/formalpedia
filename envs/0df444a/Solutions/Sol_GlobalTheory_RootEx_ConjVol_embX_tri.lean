-- Prove2me | solution 1 for GlobalTheory.RootEx.ConjVol.embX_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:48.524236+00:00
-- url     : https://prove2.me/submissions/329b0d6c-a83c-43f1-9d51-c060e735fb94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ConjVol
theorem _root_.solution (p : ℕ) (x : GL n k) : (embX c x).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · simp [VolN.val_embX]
  · simp [VolN.val_embX]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [VolN.val_embX, this]
end GlobalTheory.RootEx.ConjVol
