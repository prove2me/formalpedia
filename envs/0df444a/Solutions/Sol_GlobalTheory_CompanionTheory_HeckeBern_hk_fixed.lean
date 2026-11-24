-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.hk_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:09.611705+00:00
-- url     : https://prove2.me/submissions/6f217bf6-9a38-4488-9fae-95be92250b2e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_hk_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_lam_dd

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution (A : Hk K) {k : G} (hk : k ∈ K) : lam K k (A.1 (dd K)) = A.1 (dd K) := by
  rw [← hk_comm, lam_dd hk]
end GlobalTheory.CompanionTheory.HeckeBern
