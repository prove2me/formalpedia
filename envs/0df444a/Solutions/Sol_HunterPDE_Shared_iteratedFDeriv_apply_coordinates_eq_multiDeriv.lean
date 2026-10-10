-- Prove2me | solution 1 for HunterPDE.Shared.iteratedFDeriv_apply_coordinates_eq_multiDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:26:36.294146+00:00
-- url     : https://prove2.me/submissions/7704e096-4e99-4e8b-ac6e-bcf99bd868ef

import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Theorems.Thm_HunterPDE_Shared_iteratedFDeriv_apply_coordinate_list
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem list_count_perm {n : ℕ} (l : List (Fin n)) :
    l.Perm (multiIndexList (fun i => l.count i)) := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  rw [multiIndexList, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem solution {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) (a : Fin k → Fin n) :
    iteratedFDeriv ℝ k u x (fun j => EuclideanSpace.single (a j) 1) =
      multiDeriv u (fun i => (List.ofFn a).count i) x := by
  have h : iteratedFDeriv ℝ k u x (fun j => EuclideanSpace.single (a j) 1) =
      iteratedPartial u (List.ofFn a) x := by
    have hc (m : ℕ) (hm : m = k) :
        iteratedFDeriv ℝ m u x (fun j => EuclideanSpace.single (a (Fin.cast hm j)) 1) =
          iteratedFDeriv ℝ k u x (fun j => EuclideanSpace.single (a j) 1) := by
      subst m
      rfl
    have he := HunterPDE.Shared.iteratedFDeriv_apply_coordinate_list hs hu (List.ofFn a) hx
    simp only [List.get_ofFn] at he
    rw [hc _ (List.length_ofFn)] at he
    exact he
  have hp := HunterPDE.Shared.iteratedPartial_eq_of_perm hs hu (list_count_perm (List.ofFn a)) hx
  simpa [multiDeriv] using h.trans hp
