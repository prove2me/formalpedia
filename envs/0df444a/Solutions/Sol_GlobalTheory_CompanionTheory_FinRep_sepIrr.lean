-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinRep.sepIrr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:53.47274+00:00
-- url     : https://prove2.me/submissions/daecf376-94ae-4961-b71d-3ea9ba460537

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_asAlgebraHom_leftRep
import Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_isIrr_leftRep
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinRep
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.FinRep
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  intro Γ _ _ x hx
  have hsimple : ∀ N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) N → ∀ n ∈ N, x * n = 0 := by
    intro N hN n hn
    have hS : Simple (FDRep.of (leftRep N)) :=
      (GlobalTheory.T.simple_iff_irreducible.1 Γ (FDRep.of (leftRep N))).2 (by
        simpa using isIrr_leftRep N)
    have h0 := hx _ hS
    have h1 : Representation.asAlgebraHom (leftRep N) x = 0 := by
      simpa using h0
    have h2 := asAlgebraHom_leftRep N x ⟨n, hn⟩
    rw [h1] at h2
    have h3 := congrArg Subtype.val h2
    simpa using h3.symm
  let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
    { carrier := {n | ∀ a, x * (a * n) = 0}
      add_mem' := fun {u v} hu hv a => by
        rw [mul_add, mul_add, hu a, hv a, add_zero]
      zero_mem' := fun a => by simp
      smul_mem' := fun c n hn a => by
        simpa [mul_assoc] using hn (a * c) }
  have hJ : (⊤ : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) ≤ J := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra ℂ Γ)]
    refine sSup_le fun N hN n hn a => ?_
    exact hsimple N hN _ (by simpa using N.smul_mem a hn)
  have h1 : (1 : MonoidAlgebra ℂ Γ) ∈ J := hJ Submodule.mem_top
  simpa using h1 1
end GlobalTheory.CompanionTheory.FinRep
