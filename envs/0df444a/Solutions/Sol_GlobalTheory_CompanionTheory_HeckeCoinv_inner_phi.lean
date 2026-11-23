-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.inner_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:20.42301+00:00
-- url     : https://prove2.me/submissions/4ef352ce-7499-4b0a-86f7-6df7c8996f10

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
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
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution {N : ℕ} (Γ : Subgroup G) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (x : G ⧸ K) (f : (G ⧸ K) →₀ ℂ) :
    ⟪φ (Finsupp.single x 1), φ f⟫_ℂ = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, inner_add_right, ha, hb, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single z c =>
    have hs : Finsupp.single z c = c • Finsupp.single z (1 : ℂ) := by simp
    rw [Finsupp.sum_single_index (by simp), hs, map_smul, inner_smul_right, hφ]
end GlobalTheory.CompanionTheory.HeckeCoinv
