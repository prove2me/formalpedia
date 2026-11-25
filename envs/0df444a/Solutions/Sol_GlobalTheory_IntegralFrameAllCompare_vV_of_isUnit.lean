-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.vV_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:16.320653+00:00
-- url     : https://prove2.me/submissions/a6da68bf-e2c3-47f2-90be-6891d789732e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_mem_range_iff
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_vV_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution {v : V} (h : IsUnit v) : vV V (algebraMap V K v) = 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 := (mem_range_iff (V := V) (algebraMap V K (u : V))).1 ⟨_, rfl⟩
  have h2 := (mem_range_iff (V := V) (algebraMap V K ((u⁻¹ : Vˣ) : V))).1 ⟨_, rfl⟩
  rw [map_units_inv, ← zpow_neg_one, vV_zpow] at h2
  omega
end GlobalTheory.IntegralFrameAllCompare
