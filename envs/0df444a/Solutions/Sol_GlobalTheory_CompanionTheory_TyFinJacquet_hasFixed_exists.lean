-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.hasFixed_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:17.182437+00:00
-- url     : https://prove2.me/submissions/e8f582a0-8786-4987-9516-1b79cf3f9059

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_unip_trivial

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
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution (τ : FDRep ℂ (GL ι K)) [Nontrivial τ] : ∃ s, HasFixed τ s := by
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  rcases isEmpty_or_nonempty ι with h | h
  · refine ⟨0, fun i => isEmptyElim i, fun c => c.elim0, v, hv, fun u hu => ?_⟩
    rw [unip_trivial _ (fun i => isEmptyElim i) hu]
    simp
  · obtain ⟨i₀⟩ := h
    refine ⟨1, fun _ => 0, fun c => ⟨i₀, Subsingleton.elim _ _⟩, v, hv, fun u hu => ?_⟩
    rw [unip_trivial _ (fun _ _ => rfl) hu]
    simp
end GlobalTheory.CompanionTheory.TyFinJacquet
