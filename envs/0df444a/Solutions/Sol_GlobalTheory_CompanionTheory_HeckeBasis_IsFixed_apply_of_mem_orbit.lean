-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.IsFixed.apply_of_mem_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:40.190336+00:00
-- url     : https://prove2.me/submissions/52f05600-d536-4680-8296-73b5361e7834

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}
namespace GlobalTheory.CompanionTheory.HeckeBasis
namespace IsFixed
theorem _root_.solution {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by
  obtain ⟨k, rfl⟩ := hz
  have h := lam_apply_smul K (k : G) u x
  rw [hu _ k.2] at h
  exact h
end IsFixed
end GlobalTheory.CompanionTheory.HeckeBasis
