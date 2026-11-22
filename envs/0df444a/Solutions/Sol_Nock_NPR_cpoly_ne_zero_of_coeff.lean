-- Prove2me | solution 1 for Nock.NPR.cpoly_ne_zero_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:23.427233+00:00
-- url     : https://prove2.me/submissions/a8a791b3-cd8e-46b8-a502-ed712a63e5d3

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_cpoly_coeff
public import Theorems.Thm_Nock_NPR_cpoly_sub

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution {f g : ℕ → K} {n j : ℕ} (hj : j < n) (h : f j ≠ g j) :
    cpoly f n - cpoly g n ≠ 0 := by
  rw [cpoly_sub]
  intro hzero
  apply h
  have hc : (cpoly (fun i => f i - g i) n).coeff j = f j - g j := by
    rw [cpoly_coeff]; simp [hj]
  rw [hzero, coeff_zero] at hc
  exact sub_eq_zero.mp hc.symm
end Nock.NPR
