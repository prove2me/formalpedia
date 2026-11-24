-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.map_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:12.996325+00:00
-- url     : https://prove2.me/submissions/0c779dbc-f7a2-443c-84c3-b8e588569445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_smul
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_sum
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_map_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd GlobalTheory.JR.WeilProd.TensorTest
variable {X : Type} [TopologicalSpace X]
namespace GlobalTheory.JR.WeilProd.TensorTest
theorem _root_.solution {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_
  intro a s ha ih hf
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have hs : IsTest (∑ j ∈ s, c j • f j) :=
    isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))
  rw [hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs,
    ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]
end GlobalTheory.JR.WeilProd.TensorTest
