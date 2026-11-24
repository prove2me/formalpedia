-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.delta_fixed_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:41.250094+00:00
-- url     : https://prove2.me/submissions/3cfe5488-2af4-49f3-9a2c-ec81e5d937fb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_lam_delta
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
variable {K}
variable (K)
variable {K}
variable (K)
namespace GlobalTheory.CompanionTheory.HeckeBasis
theorem _root_.solution (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by
  intro k hk
  have hc : lam K k * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K k :=
    (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨k, rfl⟩
  have hd : lam K k (delta K) = delta K := by
    have hk1 : (k : G ⧸ K) = ((1 : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
    rw [lam_delta, delta, hk1]
  have := LinearMap.congr_fun hc (delta K)
  simp only [Module.End.mul_apply] at this
  rw [this, hd]
end GlobalTheory.CompanionTheory.HeckeBasis
