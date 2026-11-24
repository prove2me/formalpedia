-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.exists_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:37:01.25945+00:00
-- url     : https://prove2.me/submissions/723b4b2a-4646-4e42-9c02-3e1d28d5e713

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
theorem _root_.solution {N : ℕ} (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hs : Function.Surjective φ)
    (hadj : ∀ (h : Hk K) u v, ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ) :
    ∃ ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)),
      StarClosed ρ ∧ ∀ h u, ρ h (φ u) = φ (h.1 u) := by
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hσ' : ∀ v, φ (σ v) = v := fun v => LinearMap.congr_fun hσ v
  have hker : ∀ (h : Hk K) u, φ u = 0 → φ (h.1 u) = 0 := by
    intro h u hu
    have := hadj h (h.1 u) u
    rw [hu, inner_zero_right] at this
    exact (inner_self_eq_zero (𝕜 := ℂ)).1 this
  have hdesc : ∀ (h : Hk K) u, φ (h.1 (σ (φ u))) = φ (h.1 u) := by
    intro h u
    have h1 : φ (σ (φ u) - u) = 0 := by rw [map_sub, hσ', sub_self]
    have h2 := hker h _ h1
    rwa [map_sub, map_sub, sub_eq_zero] at h2
  let L : Hk K →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) :=
    { toFun := fun h => φ ∘ₗ h.1 ∘ₗ σ
      map_add' := fun a b => by
        ext1 v
        simp
      map_smul' := fun c a => by
        ext1 v
        simp }
  have hL : ∀ h u, L h (φ u) = φ (h.1 u) := fun h u => hdesc h u
  let ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) := AlgHom.ofLinearMap L
    (by
      ext1 v
      show φ (σ v) = v
      exact hσ' v)
    (fun a b => by
      ext1 v
      obtain ⟨u, rfl⟩ := hs v
      show L (a * b) (φ u) = L a (L b (φ u))
      rw [hL, hL, hL]
      rfl)
  have hρ : ∀ h u, ρ h (φ u) = φ (h.1 u) := hL
  refine ⟨ρ, fun h => ⟨starH hp h, fun a b => ?_⟩, hρ⟩
  obtain ⟨u, rfl⟩ := hs a
  obtain ⟨v, rfl⟩ := hs b
  rw [hρ, hρ, ← inner_conj_symm, hadj h v u, inner_conj_symm]
end GlobalTheory.CompanionTheory.HeckeCoinv
