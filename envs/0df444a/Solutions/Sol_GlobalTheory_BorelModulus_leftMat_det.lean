-- Prove2me | solution 1 for GlobalTheory.BorelModulus.leftMat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:40.481219+00:00
-- url     : https://prove2.me/submissions/16d6ac23-16fc-4af7-8a31-4e747f74174f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelModulus
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.BorelModulus
theorem _root_.solution (u : (borelGL k (Fin n)).U) : (leftMat u.1.val).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
  have hb : (leftMat u.1.val).BlockTriangular (fun p => p.1.1) := fun p q h => by
    simp [leftMat, h1 _ _ h]
  rw [hb.det_fintype]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (leftMat u.1.val).toSquareBlock (fun p => p.1.1) a = 1 := by
    ext ⟨⟨⟨i, j⟩, hp⟩, rfl⟩ ⟨⟨⟨i', j'⟩, hq⟩, e⟩
    obtain rfl : i' = i := e
    simp [toSquareBlock_def, leftMat, h2, Matrix.one_apply, eq_comm]
  rw [this, det_one]
end GlobalTheory.BorelModulus
