-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.apply_out_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:21.900886+00:00
-- url     : https://prove2.me/submissions/e080ee19-e867-4f46-80f0-f7a202cc9865

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums

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
open Function
open scoped Pointwise
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
variable {H}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hΦ g h h.2]
end GroundTheory.Automorphic.Parabolic
