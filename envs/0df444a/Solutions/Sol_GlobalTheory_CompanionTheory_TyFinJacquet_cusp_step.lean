-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.cusp_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:49.501539+00:00
-- url     : https://prove2.me/submissions/5249c4c5-c9d9-4348-9484-caffbbb5fa76

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_parts
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_equivariant_tprod
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_killSub_eq_bot

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
theorem _root_.solution (hb : Function.Surjective b) (hΦ : Φ ≠ 0)
    (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (c : Fin s) (hirr : IsIrr (lam c).ρ)
    {t : ℕ} (ht : 1 ≤ t) (b₁ : {i // b i = c} → Fin t) (hb₁ : Function.Surjective b₁)
    (v : lam c) (hv : v ≠ 0) (hfix : ∀ u ∈ unip K b₁, (lam c).ρ u v = v) : HasFixed τ (s + t - 1) := by
  have hnot : v ∉ killSub Φ c := by
    rw [killSub_eq_bot hΦ heq c hirr]
    simpa using hv
  have hex : ∃ f : ∀ c, (lam c : Type), Φ (PiTensorProduct.tprod ℂ (Function.update f c v)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  refine ⟨refine b c b₁ ht, refine_surjective b c b₁ ht hb hb₁, _, hf, fun u hu => ?_⟩
  obtain ⟨hp, h1, h2⟩ := refine_parts b c b₁ ht hu
  have h3 := equivariant_tprod heq ⟨u, hp⟩ (Function.update f c v)
  have h4 : (fun c' => (lam c').ρ (levi K b c' ⟨u, hp⟩) (Function.update f c v c')) = Function.update f c v := by
    funext c'
    by_cases e : c' = c
    · subst e
      simpa using hfix _ h2
    · rw [h1 c' e]
      simp
  rw [h4] at h3
  exact h3.symm
end GlobalTheory.CompanionTheory.TyFinJacquet
