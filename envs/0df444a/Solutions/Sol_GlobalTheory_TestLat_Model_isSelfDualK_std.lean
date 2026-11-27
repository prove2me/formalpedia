-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.isSelfDualK_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:43.987838+00:00
-- url     : https://prove2.me/submissions/c067e836-0d4d-46a6-8d1d-99701b401f03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_GlobalTheory_TestLat_Model_isLattice_stdLat
import Theorems.Thm_GlobalTheory_TestLat_Model_isSelfDualE_std
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
namespace GlobalTheory.TestLat.Model
theorem _root_.solution [StarRing K] : IsSelfDualK (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by
  refine ⟨isLattice_stdLat, ?_⟩
  ext y
  rw [(isSelfDualE_std (starRingEnd K)).2 y]
  change (∀ x ∈ stdLat K n, _) ↔ _
  refine forall₂_congr fun x _ => ?_
  simp [Formalism.UG.hform, Matrix.one_apply, dotProduct, Submodule.mem_one, starRingEnd_apply]
end GlobalTheory.TestLat.Model
