-- Prove2me | solution 1 for GlobalTheory.BorelModulus.coord_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:37.775705+00:00
-- url     : https://prove2.me/submissions/24317c71-4664-47f1-81b7-b391de86eb95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
import Theorems.Thm_GlobalTheory_BorelModulus_coord_apply
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
theorem _root_.solution (t : Fin n → kˣ) (ht) (x : (borelGL k (Fin n)).U) :
    coord k n (conjAut _ ⟨(borelGL k (Fin n)).s t, ht⟩ x) =
      (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec (coord k n x) := by
  funext p
  rw [mulVec_diagonal, coord_apply, conjAut_coe, coord_apply]
  show ((diagHom k (Fin n) t) * x.1 * (diagHom k (Fin n) t)⁻¹).val _ _ = _
  rw [← map_inv, Units.val_mul, Units.val_mul, diagHom_val, diagHom_val, mul_diagonal, diagonal_mul]
  simp only [Pi.inv_apply, Units.val_mul]
  ring
end GlobalTheory.BorelModulus
