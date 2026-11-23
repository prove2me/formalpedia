-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:50.055427+00:00
-- url     : https://prove2.me/submissions/3de6f3a4-792c-451f-986b-cef182d53153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct

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
theorem _root_.solution (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.comp (c * ·), hf.2.smul_left⟩
end GlobalTheory.JR.WeilProd.TensorTest
