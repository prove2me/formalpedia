-- Prove2me | solution 1 for GlobalTheory.UnitLemma.BaseChange.herm_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:22.002691+00:00
-- url     : https://prove2.me/submissions/416d45f7-ecc4-47fd-a7bc-fe8da98491fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OrthonormalIffUnitary
import Theorems.Thm_GlobalTheory_UnitLemma_BaseChange_herm_sum_left
import Theorems.Thm_GlobalTheory_UnitLemma_BaseChange_herm_sum_right
import Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_smul_left
import Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.BaseChange
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.BaseChange
theorem _root_.solution (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by
  have hi := e.sum_toMatrix_smul_self e' i
  have hj := e.sum_toMatrix_smul_self e' j
  rw [← hi, ← hj, herm_sum_left]
  simp_rw [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]
  simp [mul_ite, Finset.sum_ite_eq]
end GlobalTheory.UnitLemma.BaseChange
