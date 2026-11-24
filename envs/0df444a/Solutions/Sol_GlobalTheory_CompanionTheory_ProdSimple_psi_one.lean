-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:38.412683+00:00
-- url     : https://prove2.me/submissions/ba2b2405-f184-4e52-a138-ff37ffe973c5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    psi ρ v (fun _ => 1) = v := by
  classical
  rw [psi_apply, Finset.sum_eq_single (1 : ∀ c, L c)]
  · simp [MonoidAlgebra.one_def]
  · intro g _ hg
    obtain ⟨c, hc⟩ : ∃ c, g c ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hg (funext hall)
    rw [Finset.prod_eq_zero (Finset.mem_univ c), zero_smul]
    simp [MonoidAlgebra.one_def, Finsupp.single_apply, hc.symm]
  · simp
end GlobalTheory.CompanionTheory.ProdSimple
