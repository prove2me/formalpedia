-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:50.150297+00:00
-- url     : https://prove2.me/submissions/65cbf897-c0e9-4cef-b8bf-a375ebefd5a4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {H K K' : Subgroup G} (hKK' : K ≤ K') (hH : H.relIndex K ≠ 0)
    (hK : K.relIndex K' ≠ 0) : H.relIndex K' ≠ 0 := by
  have h1 : (H ⊓ K).relIndex K' = (H ⊓ K).relIndex K * K.relIndex K' :=
    (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right hKK').symm
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 : (H ⊓ K).relIndex K' ≠ 0 := by
    rw [h1]
    exact mul_ne_zero hH hK
  intro h0
  apply h2
  have := Subgroup.relIndex_dvd_of_le_left K' (inf_le_left : H ⊓ K ≤ H)
  rw [h0] at this
  exact Nat.eq_zero_of_zero_dvd this
end GroundTheory.Automorphic.Parabolic
