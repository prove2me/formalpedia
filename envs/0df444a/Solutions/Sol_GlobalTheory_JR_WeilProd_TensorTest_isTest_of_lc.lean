-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.isTest_of_lc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:43.55992+00:00
-- url     : https://prove2.me/submissions/23036feb-384b-4c57-a635-fad12dcb7f43

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
theorem _root_.solution {g : X → ℂ} (hg : IsLocallyConstant g) {K : Set X} (hK : IsCompact K)
    (hs : Function.support g ⊆ K) : IsTest g := by
  refine ⟨hg, ?_⟩
  have hcl : IsClosed (Function.support g) := by
    show IsClosed {x | g x ≠ 0}
    exact (hg.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hs
end GlobalTheory.JR.WeilProd.TensorTest
