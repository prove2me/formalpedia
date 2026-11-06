-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaRational_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:24.00767+00:00
-- url     : https://prove2.me/submissions/347b83a3-48d4-4b53-96f1-7b8c6b537e3e

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_quadratic_phase
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_quadratic_character_sum
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) : quadraticGammaRational m hm = 1 := by
  let : NeZero m := ⟨hm⟩
  let : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  let : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  have hsum : (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) = (m : ℂ) := by
    have hreindex := ((rationalCoordEquiv m hm).sum_comp
      (fun x : O ⧸ Ideal.span {(m : O)} => ψ (x ^ 2))).symm
    rw [hreindex, Fintype.sum_prod_type]
    calc
      (∑ x : ZMod m, ∑ y : ZMod m,
        ψ ((rationalCoordEquiv m hm) (x, y) ^ 2)) =
        ∑ x : ZMod m, ∑ y : ZMod m,
          ZMod.stdAddChar (2*x*y-y^2) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact rational_quadratic_phase m hm x y
      _ = (m : ℂ) := rational_quadratic_character_sum m hodd
  have hnorm : ‖eisEmbedding (m : O)‖ = m := by simp
  unfold quadraticGammaRational
  change (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ) = 1
  rw [hsum, hnorm]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact div_self hmC
end OAI.ActualEisensteinCubic
