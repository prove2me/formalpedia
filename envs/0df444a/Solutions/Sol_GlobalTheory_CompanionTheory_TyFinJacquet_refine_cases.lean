-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.refine_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:00.422823+00:00
-- url     : https://prove2.me/submissions/fb901e9c-95dc-448e-837c-596cb69e5411

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_of_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_of_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_of_gt

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
theorem _root_.solution (i : ι) :
    ((b i : ℕ) < c ∧ (refine b c b₁ ht i : ℕ) = b i) ∨
    ((b i : ℕ) = c ∧ (c : ℕ) ≤ refine b c b₁ ht i ∧ (refine b c b₁ ht i : ℕ) < c + t) ∨
    ((c : ℕ) < b i ∧ (refine b c b₁ ht i : ℕ) = b i + t - 1) := by
  rcases lt_trichotomy (b i : ℕ) c with h | h | h
  · exact Or.inl ⟨h, refine_of_lt b c b₁ ht h⟩
  · have h' : b i = c := Fin.ext h
    have := refine_of_eq b c b₁ ht h'
    have := (b₁ ⟨i, h'⟩).2
    exact Or.inr (Or.inl ⟨h, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨h, refine_of_gt b c b₁ ht h⟩)
end GlobalTheory.CompanionTheory.TyFinJacquet
