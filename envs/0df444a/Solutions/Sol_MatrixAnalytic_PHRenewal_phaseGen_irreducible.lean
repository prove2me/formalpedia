-- Prove2me | solution 1 for MatrixAnalytic.PHRenewal.phaseGen_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:49:12.423759+00:00
-- url     : https://prove2.me/submissions/eca6c333-d13f-4c41-8880-a4d1a998425a

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix
open MatrixAnalytic.PHRenewal
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    IsIrreducibleGen (phaseGen τ T) := by
  have hle : ∀ a b, T a b ≤ phaseGen τ T a b := by
    intro a b
    simp only [phaseGen, Matrix.add_apply, vecMulVec_apply]
    have := mul_nonneg (hrep.exit_nonneg a) (hrep.tau_nonneg b)
    linarith
  have hmono : ∀ a b, Relation.ReflTransGen (PosRate T) a b →
      Relation.ReflTransGen (PosRate (phaseGen τ T)) a b := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hxy ih => exact ih.tail ⟨hxy.1, lt_of_lt_of_le hxy.2 (hle _ _)⟩
  intro i j
  obtain ⟨k, hik, hk⟩ := hirr.1 i
  obtain ⟨i', hτ, hi'j⟩ := hirr.2 j
  refine (hmono _ _ hik).trans (Relation.ReflTransGen.trans ?_ (hmono _ _ hi'j))
  by_cases hki : k = i'
  · subst hki; exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ⟨hki, ?_⟩
    simp only [phaseGen, Matrix.add_apply, vecMulVec_apply]
    have := hrep.offDiag_nonneg k i' hki
    have := mul_pos hk hτ
    linarith

