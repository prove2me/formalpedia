-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.refine_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:14.297117+00:00
-- url     : https://prove2.me/submissions/e2eb188e-f34a-489d-9582-fb0e863e7b9e

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
theorem _root_.solution (hb : Function.Surjective b) (hb₁ : Function.Surjective b₁) :
    Function.Surjective (refine b c b₁ ht) := by
  intro k
  have hk := k.2
  have hcs := c.2
  by_cases h1 : (k : ℕ) < c
  · obtain ⟨i, hi⟩ := hb ⟨k, by omega⟩
    have hi' : (b i : ℕ) = k := by rw [hi]
    refine ⟨i, Fin.ext ?_⟩
    rw [refine_of_lt b c b₁ ht (by omega), hi']
  · by_cases h2 : (k : ℕ) < c + t
    · obtain ⟨x, hx⟩ := hb₁ ⟨k - c, by omega⟩
      have hx' : (b₁ x : ℕ) = k - c := by rw [hx]
      refine ⟨x.1, Fin.ext ?_⟩
      rw [refine_of_eq b c b₁ ht x.2]
      have : b₁ ⟨x.1, x.2⟩ = b₁ x := rfl
      rw [this, hx']
      omega
    · obtain ⟨i, hi⟩ := hb ⟨k + 1 - t, by omega⟩
      have hi' : (b i : ℕ) = k + 1 - t := by rw [hi]
      refine ⟨i, Fin.ext ?_⟩
      rw [refine_of_gt b c b₁ ht (by omega), hi']
      omega
end GlobalTheory.CompanionTheory.TyFinJacquet
