-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_unitri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:06.833831+00:00
-- url     : https://prove2.me/submissions/de76701b-8293-4fed-ac89-e77347ca3f21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have ht : M.BlockTriangular b := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl; exact lt_irrefl _ h
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, hM r s (by omega), Matrix.one_apply]
  rw [this, det_one]
end GlobalTheory.RootEx.VolN
