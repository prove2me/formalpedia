-- Prove2me | solution 1 for Nock.NPR.listPoly_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:58.982512+00:00
-- url     : https://prove2.me/submissions/6ba483f9-434a-4993-b9eb-5a0ad144c7b3

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_cpoly_ne_zero_of_coeff

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) (hne : l₁ ≠ l₂) :
    listPoly l₁ - listPoly l₂ ≠ 0 := by
  -- find a position where they differ
  have hex : ∃ j, j < l₁.length ∧ l₁.getD j 0 ≠ l₂.getD j 0 := by
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    apply hne
    apply List.ext_getElem hlen
    intro j hj hj2
    have hjeq := h j hj
    rwa [List.getD_eq_getElem l₁ 0 hj, List.getD_eq_getElem l₂ 0 (hlen ▸ hj)] at hjeq
  obtain ⟨j, hj, hval⟩ := hex
  unfold listPoly
  rw [hlen]
  exact cpoly_ne_zero_of_coeff (hlen ▸ hj) hval
end Nock.NPR
