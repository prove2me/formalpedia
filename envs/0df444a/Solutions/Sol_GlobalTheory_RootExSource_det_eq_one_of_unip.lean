-- Prove2me | solution 1 for GlobalTheory.RootExSource.det_eq_one_of_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:04:59.894119+00:00
-- url     : https://prove2.me/submissions/6afeff0f-d6c6-4b3e-a34c-5ea26c8e4422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal

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
open GlobalTheory GlobalTheory.RootExSource
namespace GlobalTheory.RootExSource
theorem _root_.solution {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (b : ι → ℕ)
    (M : Matrix ι ι k) (h : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hT : M.BlockTriangular b := fun r s hrs => by
    rw [h r s hrs.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hrs
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext r s
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ (by rw [r.2, s.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_one]
end GlobalTheory.RootExSource
