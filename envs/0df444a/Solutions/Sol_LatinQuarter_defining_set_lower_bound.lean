-- Prove2me | solution 1 for LatinQuarter.defining_set_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:45.473327+00:00
-- url     : https://prove2.me/submissions/ac7c4dec-21a3-41f9-9112-17bc885dc432

module
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Theorems.Thm_LatinQuarter_small_clue_coefficient_zero
public import Theorems.Thm_LatinQuarter_defining_coefficient_one


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) : n * n / 4 ≤ P.card := by
  classical
  by_contra! hP
  let e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  have hc0 := small_clue_coefficient_zero P L e hP
  have hc1 := defining_coefficient_one P L h (fun p => markedConstant e p.1 p.2)
  exact zero_ne_one (hc0.symm.trans hc1)
end LatinQuarter
