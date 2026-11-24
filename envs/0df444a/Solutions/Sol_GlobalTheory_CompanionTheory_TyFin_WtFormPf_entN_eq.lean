-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.WtFormPf.entN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:36.979128+00:00
-- url     : https://prove2.me/submissions/dc71acdd-3213-4983-846c-0e76be70685b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatementStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardJPat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.WtFormPf
open ReciprocityTheory.Ty.Fin.Lq
namespace GlobalTheory.CompanionTheory.TyFin.WtFormPf
theorem _root_.solution {A : Type} [Semiring A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (x y : ℕ) :
    entN M x y = ∑ i : Fin N, ∑ j : Fin N, (if (i : ℕ) = x ∧ (j : ℕ) = y then (1 : A) else 0) * M i j := by
  unfold entN
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨x, h.1⟩ : Fin N), Finset.sum_eq_single (⟨y, h.2⟩ : Fin N)]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ y := fun e => hj (Fin.ext e)
      simp [this]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ x := fun e => hi (Fin.ext e)
      simp [this]
    · simp
  · symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : ¬ ((i : ℕ) = x ∧ (j : ℕ) = y) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨i.2, j.2⟩
    simp [this]
end GlobalTheory.CompanionTheory.TyFin.WtFormPf
