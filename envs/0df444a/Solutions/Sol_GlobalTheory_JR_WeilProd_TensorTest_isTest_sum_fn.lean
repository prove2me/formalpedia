-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_sum_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:51.869196+00:00
-- url     : https://prove2.me/submissions/9c5310ce-4758-45fb-b36e-a1311c0c45a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_sum

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
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.JR.WeilProd.TensorTest
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by
  have := isTest_sum s F hF
  rwa [Finset.sum_fn] at this
end GlobalTheory.JR.WeilProd.TensorTest
