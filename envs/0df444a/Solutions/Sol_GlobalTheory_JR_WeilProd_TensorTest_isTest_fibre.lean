-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:27.991921+00:00
-- url     : https://prove2.me/submissions/30e31a0b-98e8-48a9-b3f0-e16bb7f3dce8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_of_lc

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
theorem _root_.solution {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by
  refine isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_
  intro v hv
  exact ⟨(u, v), subset_tsupport _ hv, rfl⟩
end GlobalTheory.JR.WeilProd.TensorTest
