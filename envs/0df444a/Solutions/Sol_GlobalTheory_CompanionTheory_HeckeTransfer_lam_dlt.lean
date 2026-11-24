-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.lam_dlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:37:05.01516+00:00
-- url     : https://prove2.me/submissions/7c368eb8-101f-41c8-8ad3-8ccf0e3f8f48

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_lam_single
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
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution {k : G} (hk : k ∈ K) : lam K k (dlt K) = dlt K := by
  simp only [dlt]
  rw [lam_single, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
end GlobalTheory.CompanionTheory.HeckeTransfer
