-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isSemisimple_tensorMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:49.490619+00:00
-- url     : https://prove2.me/submissions/e4158cb4-e182-428e-93b7-16fd558b1717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_map
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) := by
  have h1 : End.IsSemisimple (f.rTensor V' : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.rTensorAlgHom ℂ V V') hf
  have h2 : End.IsSemisimple (g.lTensor V : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.lTensorAlgHom ℂ V' V) hg
  have e : (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) = f.rTensor V' * g.lTensor V := by
    ext; simp
  rw [e]
  refine End.IsSemisimple.mul_of_commute ?_ h1 h2
  show _ = _
  ext; simp
end GlobalTheory.WeilDeligne
