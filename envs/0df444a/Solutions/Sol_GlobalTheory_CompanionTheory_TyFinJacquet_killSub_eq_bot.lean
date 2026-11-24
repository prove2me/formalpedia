-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.killSub_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:11.794539+00:00
-- url     : https://prove2.me/submissions/c3eb232a-b2f0-440f-87fa-dd2220f84c0a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_leviHom_dGL
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_equivariant_tprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
variable {τ : FDRep ℂ (GL ι K)} {b : ι → Fin s} {lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)}
  {Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ}
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution (hΦ : Φ ≠ 0) (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (c : Fin s)
    (hirr : IsIrr (lam c).ρ) : killSub Φ c = ⊥ := by
  have hinv : ∀ g, ∀ x ∈ killSub Φ c, (lam c).ρ g x ∈ killSub Φ c := by
    intro g x hx f
    let gh : ∀ c', GL {i // b i = c'} K := Function.update 1 c g
    let p : parab K b := ⟨dGL b gh, dGL_mem b gh⟩
    have hl : ∀ c', levi K b c' p = gh c' := fun c' => congrFun (leviHom_dGL b gh) c'
    have h1 := equivariant_tprod heq p (Function.update f c x)
    have h2 : (fun c' => (lam c').ρ (levi K b c' p) (Function.update f c x c')) =
        Function.update f c ((lam c).ρ g x) := by
      funext c'
      rw [hl]
      by_cases e : c' = c
      · subst e
        simp [gh]
      · simp [gh, e]
    rw [h2] at h1
    rw [h1, hx f, map_zero]
  rcases hirr.2 (killSub Φ c) hinv with h | h
  · exact h
  · exfalso
    apply hΦ
    apply PiTensorProduct.ext
    ext f
    have h1 : f c ∈ killSub Φ c := by rw [h]; trivial
    have h2 := h1 f
    rw [Function.update_eq_self] at h2
    simpa using h2
end GlobalTheory.CompanionTheory.TyFinJacquet
