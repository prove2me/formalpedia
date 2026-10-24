-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_pos_of_height_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:05:11.353901+00:00
-- url     : https://prove2.me/submissions/928ca224-57ea-4680-9890-99e87abb3c80

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib

section

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

namespace PiL11

theorem indep_cols {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {K : Type*} [Field K] (A : Matrix α β K)
    (h : Function.Surjective A.mulVecLin) :
    ∃ selection : α → β,
      Function.Injective selection ∧
        LinearIndependent K (fun j : α => fun i : α => A i (selection j)) := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  have htop : Submodule.span K (Set.range (A.col ∘ a)) = ⊤ := by
    rw [hsp, ← Matrix.range_mulVecLin, LinearMap.range_eq_top.2 h]
  have : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  let b := Module.Basis.mk hli htop.ge
  have hc : Fintype.card κ = Fintype.card α := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  obtain ⟨e⟩ := Fintype.card_eq.1 hc.symm
  exact ⟨a ∘ e, ha.comp e.injective, hli.comp e e.injective⟩

theorem minor {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (M : Matrix alpha beta Complex) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : alpha → beta, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by
  obtain ⟨f, hf, hli⟩ := indep_cols M hM
  refine ⟨f, hf, ?_⟩
  have : IsUnit (M.submatrix id f) := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  exact (Matrix.isUnit_iff_isUnit_det _).1 this |>.ne_zero

theorem rowcount (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  unfold actualRowCount
  apply Fintype.card_pos_iff.2
  refine ⟨⟨⟨0, d.K_pos⟩, ⟨0, ?_⟩⟩⟩
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  simp [hH, hH.le]

end PiL11

end

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < actualRowCount d H := by
  apply PiL11.rowcount <;> assumption
