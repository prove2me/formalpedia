-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.op_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:07.137713+00:00
-- url     : https://prove2.me/submissions/a4dc7247-460b-4bf0-ac76-e29b62ce4888

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_lam_one

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
theorem _root_.solution {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u (delta K) = u := by
  rw [delta, op_single hu, lam_one, one_smul]
end GlobalTheory.CompanionTheory.HeckeBasis
