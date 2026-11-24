-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.lam_dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:58.266028+00:00
-- url     : https://prove2.me/submissions/28741c11-039c-4f42-9ca5-2eb88f86f8bd

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_smul_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_lam_single
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution {k : G} (hk : k ∈ K) : lam K k (dd K) = dd K := by
  rw [dd, lam_single, smul_mk, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
end GlobalTheory.CompanionTheory.HeckeBern
