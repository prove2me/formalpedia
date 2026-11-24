-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.phi_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:13.845513+00:00
-- url     : https://prove2.me/submissions/15baa1b1-fe30-409e-9db4-a9e7ec29e04e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_lam
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_lam_dlt
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_hk_comm
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
theorem _root_.solution (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) :
    ∀ k ∈ K, σ k (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  intro k hk
  rw [← phi_lam hv, hk_comm, lam_dlt hk]
end GlobalTheory.CompanionTheory.HeckeTransfer
