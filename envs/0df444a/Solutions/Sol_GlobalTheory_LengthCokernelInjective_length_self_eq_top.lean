-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.length_self_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:49.483897+00:00
-- url     : https://prove2.me/submissions/96d9574d-c55f-4d90-adec-c66b8f6093a4

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthCokernelInjective
theorem _root_.solution : Module.length R R = ⊤ := by
  have h : Ring.ord R (0 : R) = ⊤ := by rw [Ring.ord_eq_addVal]; simp
  have h2 : Ring.ord R (0 : R) ≤ Module.length R R :=
    Module.length_le_of_surjective (Ideal.span {(0 : R)}).mkQ (Submodule.mkQ_surjective _)
  rw [h] at h2
  exact top_le_iff.mp h2
end GlobalTheory.LengthCokernelInjective
