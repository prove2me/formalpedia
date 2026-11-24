-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:12.029141+00:00
-- url     : https://prove2.me/submissions/9c504208-5667-494e-bf32-d0daa0c63d1e

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
theorem _root_.solution {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') :=
  ⟨hf.1.add hf'.1, hf.2.add hf'.2⟩
end GlobalTheory.JR.WeilProd.TensorTest
