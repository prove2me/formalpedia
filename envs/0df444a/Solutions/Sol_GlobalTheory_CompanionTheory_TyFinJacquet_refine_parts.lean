-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.refine_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:30.79911+00:00
-- url     : https://prove2.me/submissions/138dfe8b-0ac8-4999-9a90-e64d6c52f63e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_of_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_refine_eq_of_ne

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
theorem _root_.solution {u : GL ι K} (hu : u ∈ unip K (refine b c b₁ ht)) :
    ∃ hp : u ∈ parab K b, (∀ c', c' ≠ c → levi K b c' ⟨u, hp⟩ = 1) ∧ levi K b c ⟨u, hp⟩ ∈ unip K b₁ := by
  have hp : u ∈ parab K b :=
    ⟨fun i j h => hu.1.1 i j (refine_lt b c b₁ ht h), fun i j h => hu.1.2 i j (refine_lt b c b₁ ht h)⟩
  refine ⟨hp, fun c' hc' => ?_, ⟨?_, ?_⟩, ?_⟩
  · apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h1 := hu.2 i j (refine_eq_of_ne b c b₁ ht (hi.trans hj.symm) (by rw [hi]; exact hc'))
    show (u : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩
    rw [h1, Matrix.one_apply]
    simp
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    refine hu.1.1 i j ?_
    have h' : (b₁ ⟨j, hj⟩ : ℕ) < b₁ ⟨i, hi⟩ := h
    rw [Fin.lt_def, refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj]
    omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    refine hu.1.2 i j ?_
    have h' : (b₁ ⟨j, hj⟩ : ℕ) < b₁ ⟨i, hi⟩ := h
    rw [Fin.lt_def, refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj]
    omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have h1 : refine b c b₁ ht i = refine b c b₁ ht j := by
      apply Fin.ext
      rw [refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj, h]
    have h2 := hu.2 i j h1
    show (u : Matrix ι ι K) i j = _
    rw [h2]
    simp
end GlobalTheory.CompanionTheory.TyFinJacquet
