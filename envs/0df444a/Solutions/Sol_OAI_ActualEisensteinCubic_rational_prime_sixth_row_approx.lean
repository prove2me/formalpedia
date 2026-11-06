-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_prime_sixth_row_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:52:55.711288+00:00
-- url     : https://prove2.me/submissions/a588e0aa-ac1b-4e6e-a277-1044c9336992

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_sixth_row_approx_two_factors
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_prime_ideal_cover

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
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r : ℕ) (hr : r.Prime) (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤
      (128 * (D / r + 1) : ℕ) := by
  obtain ⟨a, b, ha0, hb0, hra, hrb, hcover⟩ :=
    rational_prime_ideal_cover r hr
  have hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, (r : O) ∈ P i) → a ∣ n ∨ b ∣ n := by
    intro n hn ⟨i, hi, hri⟩
    rcases hcover (P i) (inferInstance) hri with hPa | hPb
    · have hmem : n ∈ (Ideal.span {a} : Ideal O) := by
        rw [← hPa]
        exact hsupport n hn i hi
      exact Or.inl (Ideal.mem_span_singleton.mp hmem)
    · have hmem : n ∈ (Ideal.span {b} : Ideal O) := by
        rw [← hPb]
        exact hsupport n hn i hi
      exact Or.inr (Ideal.mem_span_singleton.mp hmem)
  have hrow := rational_sixth_row_approx_two_factors
    P hgood columns support weight (r : O) a b ha0 hb0 D
    hfactor hcolnorm hweight
  have hAdiv : D / ShortDraftLatticeCount.qNat a ≤ D / r :=
    Nat.div_le_div_left hra hr.pos
  have hBdiv : D / ShortDraftLatticeCount.qNat b ≤ D / r :=
    Nat.div_le_div_left hrb hr.pos
  have hnat :
      64 * (D / ShortDraftLatticeCount.qNat a + 1) +
      64 * (D / ShortDraftLatticeCount.qNat b + 1) ≤
      128 * (D / r + 1) := by omega
  exact hrow.trans (by exact_mod_cast hnat)
end OAI.ActualEisensteinCubic
