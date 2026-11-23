-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_lm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:27.225321+00:00
-- url     : https://prove2.me/submissions/b35addee-ab44-4c66-91d5-e1bbdbcd3e47

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
theorem _root_.solution (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    [DecidableEq {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k) :
    (lm P h).det = ∏ s, (h.toSquareBlockProp fun r => P r s).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ht : (lm P h).BlockTriangular (fun a => a.1.2) := by
    intro a b hab
    simp only [lm, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab).symm]
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  let E : {r // P r s} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.2 = s} :=
    { toFun := fun r => ⟨⟨(r.1, s), r.2⟩, rfl⟩
      invFun := fun a => ⟨a.1.1.1, by have h1 := a.1.2; have h2 : a.1.1.2 = s := a.2; rwa [h2] at h1⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self E]
  congr 1
  ext i j
  simp [toSquareBlock_def, toSquareBlockProp_def, lm, E]
end GlobalTheory.RootEx.VolN
