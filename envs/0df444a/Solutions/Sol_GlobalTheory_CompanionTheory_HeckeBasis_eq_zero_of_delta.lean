-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.eq_zero_of_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:42.490859+00:00
-- url     : https://prove2.me/submissions/50c66d02-42df-4731-a7ef-194078a4cc62

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
variable {K}
namespace GlobalTheory.CompanionTheory.HeckeBasis
theorem _root_.solution (h : Hk K)
    (h0 : (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = 0) : h = 0 := by
  apply Subtype.ext
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hc : lam K x * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K x :=
      (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hc (delta K)
    simp only [Module.End.mul_apply] at this
    rw [h0, map_zero, lam_delta] at this
    simpa using this.symm
end GlobalTheory.CompanionTheory.HeckeBasis
