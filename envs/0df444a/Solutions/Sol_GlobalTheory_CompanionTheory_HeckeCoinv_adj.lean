-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:00.197624+00:00
-- url     : https://prove2.me/submissions/3c99c4e9-0df0-4a9c-ab69-19eee179c146

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_adj_single
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
theorem _root_.solution {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (h : Hk K) (u v : (G ⧸ K) →₀ ℂ) :
    ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
  | single y c =>
    have hs : Finsupp.single y c = c • Finsupp.single y (1 : ℂ) := by simp
    rw [hs]
    simp only [map_smul, inner_smul_right]
    congr 1
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
    | single x d =>
      have hs' : Finsupp.single x d = d • Finsupp.single x (1 : ℂ) := by simp
      rw [hs']
      simp only [map_smul, inner_smul_left]
      rw [adj_single Γ hp h φ hφ]
end GlobalTheory.CompanionTheory.HeckeCoinv
