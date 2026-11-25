-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.equivRayGroup_rcl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:49.904847+00:00
-- url     : https://prove2.me/submissions/c22d338c-3a86-4d45-831f-7b7255c4de70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI' : I ≠ ⊥) :
    D.equivRayGroup (RayCl.rcl M I) = D.cls I := by
  rw [RayCl.rcl_of (show I ∈ RayCl.primeTo K M from ⟨hI, hI'⟩)]
  rfl
end GlobalTheory.Mem.RayData
