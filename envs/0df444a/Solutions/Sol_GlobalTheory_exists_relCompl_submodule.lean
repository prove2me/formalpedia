-- Prove2me | solution 1 for GlobalTheory.exists_relCompl_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:00.567681+00:00
-- url     : https://prove2.me/submissions/90096ec8-bab5-4c63-9509-8883333766a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (h : U ≤ W) : ∃ C : Submodule K V, Disjoint U C ∧ U ⊔ C = W := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  refine ⟨C ⊓ W, hC.disjoint.mono_right inf_le_left, ?_⟩
  rw [← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]
end GlobalTheory
