-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.det_eq_one_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:19.865804+00:00
-- url     : https://prove2.me/submissions/eb8588c7-8de1-4cb0-a568-61e7963db28e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hb : M.BlockTriangular f := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock f a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM _ _ (by rw [i.2, j.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]
end GlobalTheory.RootEx.TargetUnip
