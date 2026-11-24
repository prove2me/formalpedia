-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.heckeOp_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:10:52.70099+00:00
-- url     : https://prove2.me/submissions/982974a5-0696-40aa-b8c8-fa63de16d3cf

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_op_delta

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
theorem _root_.solution (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g :=
  op_delta (orbitVec_fixed hK g)
end GlobalTheory.CompanionTheory.HeckeBasis
