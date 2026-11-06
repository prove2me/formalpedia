-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.prime_sixth_row_approx_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:29.19554+00:00
-- url     : https://prove2.me/submissions/2235d373-ef97-4552-8cd3-ea0e37648cce

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_sixth_row_approx

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
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / ShortDraftLatticeCount.qNat p + 1) : ℕ) := by
  apply prime_sixth_row_approx P hgood columns support weight p hp D
    ?_ hcolnorm hweight
  intro n hn ⟨i, hi, hpi⟩
  have hle : (Ideal.span {p} : Ideal O) ≤ P i :=
    (Ideal.span_singleton_le_iff_mem (P i)).mpr hpi
  have hne : P i ≠ ⊤ := (inferInstance : (P i).IsMaximal).ne_top
  have heq : (Ideal.span {p} : Ideal O) = P i := hprime.eq_of_le hne hle
  have hnP : n ∈ Ideal.span {p} := by
    rw [heq]
    exact hsupport n hn i hi
  exact Ideal.mem_span_singleton.mp hnP
end OAI.ActualEisensteinCubic
