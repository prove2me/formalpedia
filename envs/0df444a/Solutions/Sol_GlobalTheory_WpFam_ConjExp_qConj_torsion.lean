-- Prove2me | solution 1 for GlobalTheory.WpFam.ConjExp.qConj_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:10.240298+00:00
-- url     : https://prove2.me/submissions/9e994a23-2884-4400-b3c2-74c29cd64eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexAutomorphismWeierstrassTorsionQCoeffs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QConjTorsion
import Theorems.Thm_GlobalTheory_WpFam_Act_rightActions
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main
import Theorems.Thm_GlobalTheory_WpFam_CoeffConj_main
import Theorems.Thm_GlobalTheory_WpFam_DerivExpansion_main
import Theorems.Thm_GlobalTheory_WpFam_ExpP_main
import Theorems.Thm_GlobalTheory_WpFam_ExpansionB_main
import Theorems.Thm_GlobalTheory_WpFam_RowsSummed_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.ConjExp
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam.ConjExp
namespace _root_.GlobalTheory.WpFam.ConjExp
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by
  intro N _ g a hg x
  have hc := _root_.GlobalTheory.WpFam.CoeffConj.main N g a hg x
  refine ⟨⟨_, _root_.GlobalTheory.WpFam.ExpP.main N x, ?_⟩,
    ⟨_, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, ?_⟩, fun hx => ⟨_,
      _root_.GlobalTheory.WpFam.ExpansionB.main N x hx, ?_⟩⟩
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cP N x n)) = _root_.GlobalTheory.WpFam.cP N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.2.2]
    exact _root_.GlobalTheory.WpFam.ExpP.main N _
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cD N x n)) = _root_.GlobalTheory.WpFam.cD N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.1]
    exact _root_.GlobalTheory.WpFam.DerivExpansion.main N _
  · have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
    rw [show (fun n => g (_root_.GlobalTheory.WpFam.cB N x n)) = _root_.GlobalTheory.WpFam.cB N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).1]
    exact _root_.GlobalTheory.WpFam.ExpansionB.main N _ fun h => hx (hzero.1 h)
end _root_.GlobalTheory.WpFam.ConjExp
end GlobalTheory.WpFam.ConjExp
