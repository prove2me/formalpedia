-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.lam_out_dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:58.938389+00:00
-- url     : https://prove2.me/submissions/6841ed46-6c23-4de7-8732-55f81d92fee6

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_smul_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_lam_single

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
theorem _root_.solution (y : G ⧸ K) : lam K (Quotient.out y) (dd K) = Finsupp.single y 1 := by
  rw [dd, lam_single, smul_mk, mul_one, QuotientGroup.out_eq']
end GlobalTheory.CompanionTheory.HeckeBern
