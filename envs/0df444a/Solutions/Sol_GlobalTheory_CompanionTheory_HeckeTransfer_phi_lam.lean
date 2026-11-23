-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.phi_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:12.136503+00:00
-- url     : https://prove2.me/submissions/49cad0e6-d9a5-4917-b059-025ace6e7e76

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_single
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
theorem _root_.solution (hv : ∀ k ∈ K, σ k v = v) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ v (lam K g f) = σ g (phi K σ v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [lam_single, phi_single hv, phi_single hv, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.map_smul]
end GlobalTheory.CompanionTheory.HeckeTransfer
