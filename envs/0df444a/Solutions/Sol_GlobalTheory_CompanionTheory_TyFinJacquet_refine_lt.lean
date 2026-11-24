-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.refine_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:13.258003+00:00
-- url     : https://prove2.me/submissions/13a4a182-7cae-4673-b20c-f09581753b02

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_cases

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
variable (b : ι → Fin s) (c : Fin s) {t : ℕ} (b₁ : {i // b i = c} → Fin t) (ht : 1 ≤ t)
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution {i j : ι} (h : b j < b i) : refine b c b₁ ht j < refine b c b₁ ht i := by
  have h' : (b j : ℕ) < b i := h
  rw [Fin.lt_def]
  rcases refine_cases b c b₁ ht i with h1 | h1 | h1 <;> rcases refine_cases b c b₁ ht j with h2 | h2 | h2 <;> omega
end GlobalTheory.CompanionTheory.TyFinJacquet
