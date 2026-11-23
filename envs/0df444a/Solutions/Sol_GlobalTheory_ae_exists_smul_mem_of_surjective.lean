-- Prove2me | solution 1 for GlobalTheory.ae_exists_smul_mem_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:53.717217+00:00
-- url     : https://prove2.me/submissions/5f009b1d-bf57-46dc-b8cb-8cf0ab4e2cc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}
namespace GlobalTheory
theorem _root_.solution (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ) :
    ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D := by
  filter_upwards [hD.ae_covers] with x ⟨h, hh⟩
  obtain ⟨g, rfl⟩ := hφ h
  exact ⟨g, hφs g x ▸ hh⟩
end GlobalTheory
