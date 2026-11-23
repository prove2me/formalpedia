-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:50.286633+00:00
-- url     : https://prove2.me/submissions/f0bfa8ad-4f41-4958-ad4d-d1f418c67988

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
theorem _root_.solution : IsTest (0 : X → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
end GlobalTheory.JR.WeilProd.TensorTest
