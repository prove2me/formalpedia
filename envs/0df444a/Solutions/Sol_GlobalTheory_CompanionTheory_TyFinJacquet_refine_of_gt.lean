-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.refine_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:38.180498+00:00
-- url     : https://prove2.me/submissions/1ef6e0db-655a-4772-9769-1472efa13e95

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll

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
theorem _root_.solution {i : ι} (h : (c : ℕ) < b i) : (refine b c b₁ ht i : ℕ) = b i + t - 1 := by
  have h' : b i ≠ c := fun e => by rw [e] at h; exact lt_irrefl _ h
  have h2 : ¬ (b i : ℕ) < c := by omega
  simp [refine, h2, h']
end GlobalTheory.CompanionTheory.TyFinJacquet
