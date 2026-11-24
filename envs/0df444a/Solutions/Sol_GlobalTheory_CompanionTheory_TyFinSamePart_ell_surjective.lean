-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.ell_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:50.402184+00:00
-- url     : https://prove2.me/submissions/8450f0ba-537d-4141-8476-952411725f57

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_dGL_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    Function.Surjective (ell (K := K) b π) := by
  intro L
  have h1 : dGL b L ∈ parab K b := dGL_mem b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) L
  have h2 : dGL b L ∈ parab K (π ∘ b) :=
    dGL_mem b (π ∘ b) (fun i j h e => by simp only [Function.comp, e] at h; exact lt_irrefl _ h) L
  refine ⟨⟨dGL b L, h1, h2⟩, ?_⟩
  funext c
  apply Units.ext
  exact bd_blk b (fun c => (L c).1) c
end GlobalTheory.CompanionTheory.TyFinSamePart
