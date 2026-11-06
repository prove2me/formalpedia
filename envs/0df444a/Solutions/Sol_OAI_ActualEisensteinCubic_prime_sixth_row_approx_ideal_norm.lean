-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.prime_sixth_row_approx_ideal_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:28:09.8772+00:00
-- url     : https://prove2.me/submissions/49f26b58-65c5-47a2-bfc5-0f700aefa9ef

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_sixth_row_approx_maximal
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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns,
      Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / Ideal.absNorm (Ideal.span {p}) + 1) : ℕ) := by
  have hcol : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D := by
    intro n hn
    rw [qNat_eq_absNorm_span]
    exact hcolnorm n hn
  simpa only [qNat_eq_absNorm_span] using
    (prime_sixth_row_approx_maximal P hgood columns support weight p hp
      hprime D hsupport hcol hweight)
end OAI.ActualEisensteinCubic
