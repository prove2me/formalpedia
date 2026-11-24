-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.phi_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:29.543159+00:00
-- url     : https://prove2.me/submissions/fe4dae5d-f2ad-4295-852e-9ef8ce25c5b1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_lam_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_lam
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_hk_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_fixed
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
theorem _root_.solution (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) f =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hd : lam K x (dlt K) = Finsupp.single (x : G ⧸ K) 1 := by
      simp only [dlt]
      rw [lam_single, mul_one]
    rw [phi_single (phi_fixed hv h), ← phi_lam hv, hk_comm, hd,
      ← Finsupp.smul_single_one (x : G ⧸ K) c, LinearMap.map_smul, LinearMap.map_smul]
end GlobalTheory.CompanionTheory.HeckeTransfer
