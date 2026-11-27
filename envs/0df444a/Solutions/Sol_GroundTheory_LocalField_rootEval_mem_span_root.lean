-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_mem_span_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:52.404463+00:00
-- url     : https://prove2.me/submissions/d1843d90-a6cc-42e7-a8d3-b3b8bed04d4e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_rootEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.rootEval_X

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)
namespace GroundTheory.LocalField
theorem _root_.solution {G : B⟦X⟧} (hG : constantCoeff G = 0) :
    rootEval hP G ∈ Ideal.span {AdjoinRoot.root P} := by
  obtain ⟨H, rfl⟩ := PowerSeries.X_dvd_iff.mpr hG
  rw [map_mul, rootEval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end GroundTheory.LocalField
