-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.isSelfDualE_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:08.634044+00:00
-- url     : https://prove2.me/submissions/4d6af054-90b0-40a6-a9bb-fe889701ea2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_GlobalTheory_TestLat_Model_mem_stdLat
import Theorems.Thm_GlobalTheory_TestLat_Model_isLattice_stdLat
import Theorems.Thm_GlobalTheory_TestLat_Model_map_mem_range
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
theorem _root_.solution (σ : K →+* K) : IsSelfDualE σ (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by
  refine ⟨isLattice_stdLat, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [mem_stdLat] at hx hy
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
    refine Subring.mul_mem _ (Subring.mul_mem _ (map_mem_range σ (hx i)) ?_) (hy j)
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [mem_stdLat]
    intro a
    have := h (Pi.single a 1) (by
      rw [mem_stdLat]; intro b; rw [Pi.single_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _)
    simpa [Formalism.UG.hform, Matrix.one_apply, Pi.single_apply, apply_ite σ] using this
end GlobalTheory.TestLat.Model
