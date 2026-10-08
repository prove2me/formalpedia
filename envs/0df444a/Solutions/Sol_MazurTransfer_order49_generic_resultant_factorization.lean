-- Prove2me | solution 1 for MazurTransfer.order49_generic_resultant_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:48:30.18699+00:00
-- url     : https://prove2.me/submissions/a4c3aea7-a8d0-43a4-b553-0663360631b5

import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_1
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence_5
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_expanded
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0 := MazurTransfer.order49_resultant_recurrence_0
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1 := MazurTransfer.order49_resultant_recurrence_1
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2 := MazurTransfer.order49_resultant_recurrence_2
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence3_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence3 := MazurTransfer.order49_resultant_recurrence_3
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence4 := MazurTransfer.order49_resultant_recurrence_4
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence5_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence5 := MazurTransfer.order49_resultant_recurrence_5
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6 := by
  have hr : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder8 = (-1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate) := by
    norm_num [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder8, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder8Coefficient0, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder8Coefficient0Block0, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder8Coefficient0Chunk0, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.coefficientTerm]
  simpa only [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient6, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional6, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit6, hr] using MazurTransfer.order49_resultant_recurrence6_expanded


/- Source module: MazurTorsion.Foundations.Polynomial.BoundedResultant. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Bounded polynomial resultants

This file collects bridges used by exact-arithmetic polynomial certificates.
The first transports a pseudo-remainder identity to bounded resultants.  The
remaining results turn a nonzero bounded resultant against a monic polynomial
into the usual resultant, coprimality, and no-common-root conclusions, without
requiring the left polynomial to retain its generic degree after specialization.
-/

open Polynomial

namespace MazurTorsion.PolynomialResultant

variable {R : Type*} [CommRing R]

/-- A pseudo-remainder identity, with all degree padding explicit, induces
the corresponding identity between bounded resultants. -/
theorem bounded_resultant_pseudoRemainder
    (a b q r : R[X]) (l c : R) (m n k delta : ℕ)
    (hb : b.natDegree ≤ n)
    (hr : r.natDegree ≤ k) (hq : q.natDegree + n ≤ m)
    (hkm : k ≤ m) (hbl : b.coeff n = l)
    (hid : Polynomial.C (l ^ delta) * a =
      Polynomial.C c * r + b * q) :
    l ^ (delta * n) * a.resultant b m n =
      (-1 : R) ^ (n * (m - k)) * l ^ (m - k) * c ^ n *
        r.resultant b k n := by
  rw [pow_mul, ← resultant_C_mul_left, hid]
  rw [resultant_add_mul_left _ _ _ _ _ hq hb]
  rw [show m = k + (m - k) by omega]
  have hcr : (Polynomial.C c * r).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le c r).trans hr
  rw [resultant_add_left_deg _ _ _ _ _ hcr, hbl]
  rw [resultant_C_mul_left]
  simp only [Nat.add_sub_cancel_left]
  ring

section Telescope

variable [IsDomain R]

private theorem resultant_telescope_step
    {A B r s t e f : R} (hr : A * r = e * s)
    (hs : B * s = A * f * t) (hA : A ≠ 0) :
    B * r = e * f * t := by
  apply mul_left_cancel₀ hA
  calc
    A * (B * r) = B * (A * r) := by ring
    _ = B * (e * s) := by rw [hr]
    _ = e * (B * s) := by ring
    _ = e * (A * f * t) := by rw [hs]
    _ = A * (e * f * t) := by ring

/-- Telescope for the bounded-resultant degree pattern `33, 7, 6, ..., 0`.

The principal coefficients are cancelled in the coefficient domain, before
the parameter is specialized.  This is the algebraic cancellation used by
the order-seven backtracking resultant certificate. -/
theorem resultant_telescope_33_7
    (R0 R1 R2 R3 R4 R5 R6 : R)
    (L2 L3 L4 L5 L6 E0 E1 E2 E3 E4 E5 E6 U : R)
    (hL2 : L2 ≠ 0) (hL3 : L3 ≠ 0) (hL4 : L4 ≠ 0)
    (hL5 : L5 ≠ 0) (hL6 : L6 ≠ 0)
    (h0 : R0 = -E0 ^ 7 * R1)
    (h1 : L2 ^ 10 * R1 = E1 ^ 6 * R2)
    (h2 : L3 ^ 8 * R2 = L2 ^ 10 * E2 ^ 5 * R3)
    (h3 : L4 ^ 6 * R3 = L3 ^ 8 * E3 ^ 4 * R4)
    (h4 : L5 ^ 4 * R4 = L4 ^ 6 * E4 ^ 3 * R5)
    (h5 : L6 ^ 2 * R5 = L5 ^ 4 * E5 ^ 2 * R6)
    (h6 : R6 = L6 ^ 2 * E6 * U) :
    R0 = -E0 ^ 7 * E1 ^ 6 * E2 ^ 5 * E3 ^ 4 * E4 ^ 3 *
      E5 ^ 2 * E6 * U := by
  have h12 : L3 ^ 8 * R1 = E1 ^ 6 * E2 ^ 5 * R3 :=
    resultant_telescope_step h1 h2 (pow_ne_zero 10 hL2)
  have h123 : L4 ^ 6 * R1 =
      (E1 ^ 6 * E2 ^ 5) * E3 ^ 4 * R4 :=
    resultant_telescope_step h12 h3 (pow_ne_zero 8 hL3)
  have h1234 : L5 ^ 4 * R1 =
      ((E1 ^ 6 * E2 ^ 5) * E3 ^ 4) * E4 ^ 3 * R5 :=
    resultant_telescope_step h123 h4 (pow_ne_zero 6 hL4)
  have h12345 : L6 ^ 2 * R1 =
      (((E1 ^ 6 * E2 ^ 5) * E3 ^ 4) * E4 ^ 3) * E5 ^ 2 * R6 :=
    resultant_telescope_step h1234 h5 (pow_ne_zero 4 hL5)
  have hR1 : R1 =
      E1 ^ 6 * E2 ^ 5 * E3 ^ 4 * E4 ^ 3 * E5 ^ 2 * E6 * U := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hL6)
    rw [h12345, h6]
    ring
  rw [h0, hR1]
  ring

end Telescope

section DegreeTelescope

variable [IsDomain R]

/-- The normalized bounded-resultant telescope for the degree pattern
`33, 7, 6, 5, 4, 3, 2, 1, 0`.

The recurrence hypotheses retain the generated leading coefficients, so an
exact pseudo-remainder certificate can be passed without reshaping.  All
principal-coefficient cancellation happens over the coefficient domain. -/
theorem bounded_resultant_telescope_33_7
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 : R[X])
    (q0 q1 q2 q3 q4 q5 q6 : R[X])
    (L2 L3 L4 L5 L6 L7 E0 E1 E2 E3 E4 E5 E6 U : R)
    (hr1 : r1.natDegree ≤ 7)
    (hr2 : r2.natDegree ≤ 6)
    (hr3 : r3.natDegree ≤ 5)
    (hr4 : r4.natDegree ≤ 4)
    (hr5 : r5.natDegree ≤ 3)
    (hr6 : r6.natDegree ≤ 2)
    (hr7 : r7.natDegree ≤ 1)
    (hr8 : r8.natDegree ≤ 0)
    (hq0 : q0.natDegree + 7 ≤ 33)
    (hq1 : q1.natDegree + 6 ≤ 7)
    (hq2 : q2.natDegree + 5 ≤ 6)
    (hq3 : q3.natDegree + 4 ≤ 5)
    (hq4 : q4.natDegree + 3 ≤ 4)
    (hq5 : q5.natDegree + 2 ≤ 3)
    (hq6 : q6.natDegree + 1 ≤ 2)
    (hlead1 : r1.coeff 7 = 1)
    (hlead2 : r2.coeff 6 = L2)
    (hlead3 : r3.coeff 5 = L3)
    (hlead4 : r4.coeff 4 = L4)
    (hlead5 : r5.coeff 3 = L5)
    (hlead6 : r6.coeff 2 = L6)
    (hlead7 : r7.coeff 1 = L7)
    (hL2 : L2 ≠ 0)
    (hL3 : L3 ≠ 0)
    (hL4 : L4 ≠ 0)
    (hL5 : L5 ≠ 0)
    (hL6 : L6 ≠ 0)
    (hL7 : L7 ≠ 0)
    (hrec0 :
      Polynomial.C ((r1.coeff 7) ^ 27) * r0 =
        r1 * q0 + Polynomial.C E0 * r2)
    (hrec1 :
      Polynomial.C ((r2.coeff 6) ^ 2) * r1 =
        r2 * q1 +
          Polynomial.C ((r1.coeff 7) ^ 2 * E1) * r3)
    (hrec2 :
      Polynomial.C ((r3.coeff 5) ^ 2) * r2 =
        r3 * q2 +
          Polynomial.C ((r2.coeff 6) ^ 2 * E2) * r4)
    (hrec3 :
      Polynomial.C ((r4.coeff 4) ^ 2) * r3 =
        r4 * q3 +
          Polynomial.C ((r3.coeff 5) ^ 2 * E3) * r5)
    (hrec4 :
      Polynomial.C ((r5.coeff 3) ^ 2) * r4 =
        r5 * q4 +
          Polynomial.C ((r4.coeff 4) ^ 2 * E4) * r6)
    (hrec5 :
      Polynomial.C ((r6.coeff 2) ^ 2) * r5 =
        r6 * q5 +
          Polynomial.C ((r5.coeff 3) ^ 2 * E5) * r7)
    (hrec6 :
      Polynomial.C ((r7.coeff 1) ^ 2) * r6 =
        r7 * q6 +
          Polynomial.C ((r6.coeff 2) ^ 2 * E6) * r8)
    (hr8C : r8 = Polynomial.C U) :
    r0.resultant r1 33 7 =
      -E0 ^ 7 * E1 ^ 6 * E2 ^ 5 * E3 ^ 4 *
        E4 ^ 3 * E5 ^ 2 * E6 * U := by
  have hs0 :
      r0.resultant r1 33 7 =
        -E0 ^ 7 * r1.resultant r2 7 6 := by
    have h := bounded_resultant_pseudoRemainder
      r0 r1 q0 r2 1 E0 33 7 6 27
      hr1 hr2 hq0 (by omega) hlead1
      (by simpa [hlead1, add_comm] using hrec0)
    rw [resultant_comm r2 r1 6 7] at h
    norm_num at h ⊢
    simpa using h
  have hs1 :
      L2 ^ 10 * r1.resultant r2 7 6 =
        E1 ^ 6 * r2.resultant r3 6 5 := by
    have h := bounded_resultant_pseudoRemainder
      r1 r2 q1 r3 L2 E1 7 6 5 2
      hr2 hr3 hq1 (by omega) hlead2
      (by simpa [hlead1, hlead2, add_comm] using hrec1)
    rw [resultant_comm r3 r2 5 6] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL2)
    calc
      L2 ^ 2 * (L2 ^ 10 * r1.resultant r2 7 6) =
          L2 ^ 12 * r1.resultant r2 7 6 := by ring
      _ = L2 ^ 2 * E1 ^ 6 * r2.resultant r3 6 5 := h
      _ = L2 ^ 2 *
          (E1 ^ 6 * r2.resultant r3 6 5) := by ring
  have hs2 :
      L3 ^ 8 * r2.resultant r3 6 5 =
        L2 ^ 10 * E2 ^ 5 * r3.resultant r4 5 4 := by
    have h := bounded_resultant_pseudoRemainder
      r2 r3 q2 r4 L3 (L2 ^ 2 * E2) 6 5 4 2
      hr3 hr4 hq2 (by omega) hlead3
      (by simpa [hlead2, hlead3, add_comm] using hrec2)
    rw [resultant_comm r4 r3 4 5] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL3)
    calc
      L3 ^ 2 * (L3 ^ 8 * r2.resultant r3 6 5) =
          L3 ^ 10 * r2.resultant r3 6 5 := by ring
      _ = L3 ^ 2 * (L2 ^ 2 * E2) ^ 5 *
          r3.resultant r4 5 4 := h
      _ = L3 ^ 2 *
          (L2 ^ 10 * E2 ^ 5 * r3.resultant r4 5 4) := by ring
  have hs3 :
      L4 ^ 6 * r3.resultant r4 5 4 =
        L3 ^ 8 * E3 ^ 4 * r4.resultant r5 4 3 := by
    have h := bounded_resultant_pseudoRemainder
      r3 r4 q3 r5 L4 (L3 ^ 2 * E3) 5 4 3 2
      hr4 hr5 hq3 (by omega) hlead4
      (by simpa [hlead3, hlead4, add_comm] using hrec3)
    rw [resultant_comm r5 r4 3 4] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL4)
    calc
      L4 ^ 2 * (L4 ^ 6 * r3.resultant r4 5 4) =
          L4 ^ 8 * r3.resultant r4 5 4 := by ring
      _ = L4 ^ 2 * (L3 ^ 2 * E3) ^ 4 *
          r4.resultant r5 4 3 := h
      _ = L4 ^ 2 *
          (L3 ^ 8 * E3 ^ 4 * r4.resultant r5 4 3) := by ring
  have hs4 :
      L5 ^ 4 * r4.resultant r5 4 3 =
        L4 ^ 6 * E4 ^ 3 * r5.resultant r6 3 2 := by
    have h := bounded_resultant_pseudoRemainder
      r4 r5 q4 r6 L5 (L4 ^ 2 * E4) 4 3 2 2
      hr5 hr6 hq4 (by omega) hlead5
      (by simpa [hlead4, hlead5, add_comm] using hrec4)
    rw [resultant_comm r6 r5 2 3] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL5)
    calc
      L5 ^ 2 * (L5 ^ 4 * r4.resultant r5 4 3) =
          L5 ^ 6 * r4.resultant r5 4 3 := by ring
      _ = L5 ^ 2 * (L4 ^ 2 * E4) ^ 3 *
          r5.resultant r6 3 2 := h
      _ = L5 ^ 2 *
          (L4 ^ 6 * E4 ^ 3 * r5.resultant r6 3 2) := by ring
  have hs5 :
      L6 ^ 2 * r5.resultant r6 3 2 =
        L5 ^ 4 * E5 ^ 2 * r6.resultant r7 2 1 := by
    have h := bounded_resultant_pseudoRemainder
      r5 r6 q5 r7 L6 (L5 ^ 2 * E5) 3 2 1 2
      hr6 hr7 hq5 (by omega) hlead6
      (by simpa [hlead5, hlead6, add_comm] using hrec5)
    rw [resultant_comm r7 r6 1 2] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL6)
    calc
      L6 ^ 2 * (L6 ^ 2 * r5.resultant r6 3 2) =
          L6 ^ 4 * r5.resultant r6 3 2 := by ring
      _ = L6 ^ 2 * (L5 ^ 2 * E5) ^ 2 *
          r6.resultant r7 2 1 := h
      _ = L6 ^ 2 *
          (L5 ^ 4 * E5 ^ 2 * r6.resultant r7 2 1) := by ring
  have hs6 :
      r6.resultant r7 2 1 = L6 ^ 2 * E6 * U := by
    have h := bounded_resultant_pseudoRemainder
      r6 r7 q6 r8 L7 (L6 ^ 2 * E6) 2 1 0 2
      hr7 hr8 hq6 (by omega) hlead7
      (by simpa [hlead6, hlead7, add_comm] using hrec6)
    rw [resultant_comm r8 r7 0 1, hr8C] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL7)
    calc
      L7 ^ 2 * r6.resultant r7 2 1 =
          L7 ^ 2 * (L6 ^ 2 * E6) * U := h
      _ = L7 ^ 2 * (L6 ^ 2 * E6 * U) := by ring
  exact resultant_telescope_33_7
    (r0.resultant r1 33 7) (r1.resultant r2 7 6)
    (r2.resultant r3 6 5) (r3.resultant r4 5 4)
    (r4.resultant r5 4 3) (r5.resultant r6 3 2)
    (r6.resultant r7 2 1)
    L2 L3 L4 L5 L6 E0 E1 E2 E3 E4 E5 E6 U
    hL2 hL3 hL4 hL5 hL6 hs0 hs1 hs2 hs3 hs4 hs5 hs6

end DegreeTelescope









end MazurTorsion.PolynomialResultant

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingCertificateData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Polynomial data for the order-seven backtracking certificates

This file stores the degree-33 selection cofactor and the three canonical
degree-seven quotient cofactors as nested polynomials in `ℚ[D][X]`.  The
pointwise `ℚ[X]` factors are obtained only by specializing the inner parameter
variable, so the large coefficient tables have a single source of truth.

The quotient factors are ordered by constant-term `D`-valuation `3`, `2`, and
`1`; this is the canonical order used by the FLINT resultant computation.

## Computational provenance

The coefficient tables were generated with SymPy polynomial arithmetic over
`ℚ[x,d]`.  The computation expanded the order-seven Tate and selection
formulas, formed the selection numerator and the quotient seventh division
polynomial, divided each exactly by the displayed dual-kernel cubic, factored
the quotient cofactor, and sorted its three factors by constant-term
`d`-valuation `3`, `2`, and `1`.  SymPy specialization at the integer
abscissas emitted the Horner expressions in the evaluation shards.  The Lean
`ring` proofs in those shards and the interpolation argument in the final
certificate check the emitted data; they do not trust the generating script.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal





end Internal









lemma divisionCofactorData0_degree :
    divisionCofactorData0.natDegree ≤ 7 := by
  unfold divisionCofactorData0
  compute_degree











@[simp] theorem divisionCofactorData0_coeff_seven :
    divisionCofactorData0.coeff 7 = 1 := by
  simp [divisionCofactorData0, Internal.divisionCofactor0Coefficient7,
    Internal.divisionCofactor0Coefficient7Chunk0]



































namespace Internal






















































end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Generic resultant certificate for order-seven backtracking

This file checks the degree and leading-coefficient side conditions
for the primitive pseudo-remainder sequence and telescopes its seven
recurrences to the factored generic resultant. The recurrence proofs
are separate exact-arithmetic certificate shards.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant

namespace Internal.ResultantCertificate

private lemma remainder1_degree : remainder1.natDegree ≤ 7 := by
  simpa [remainder1] using divisionCofactorData0_degree

private lemma remainder2_degree :
    remainder2.natDegree ≤ 6 := by
  unfold remainder2 outerTerm
  compute_degree

private lemma remainder3_degree :
    remainder3.natDegree ≤ 5 := by
  unfold remainder3 outerTerm
  compute_degree

private lemma remainder4_degree :
    remainder4.natDegree ≤ 4 := by
  unfold remainder4 outerTerm
  compute_degree

private lemma remainder5_degree :
    remainder5.natDegree ≤ 3 := by
  unfold remainder5 outerTerm
  compute_degree

private lemma remainder6_degree :
    remainder6.natDegree ≤ 2 := by
  unfold remainder6 outerTerm
  compute_degree

private lemma remainder7_degree :
    remainder7.natDegree ≤ 1 := by
  unfold remainder7 outerTerm
  compute_degree

private lemma remainder8_degree :
    remainder8.natDegree ≤ 0 := by
  unfold remainder8 outerTerm
  compute_degree

private lemma quotient0_degree :
    quotient0.natDegree ≤ 26 := by
  unfold quotient0 outerTerm
  compute_degree

private lemma quotient1_degree :
    quotient1.natDegree ≤ 1 := by
  unfold quotient1 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient2_degree :
    quotient2.natDegree ≤ 1 := by
  unfold quotient2 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient3_degree :
    quotient3.natDegree ≤ 1 := by
  unfold quotient3 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient4_degree :
    quotient4.natDegree ≤ 1 := by
  unfold quotient4 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient5_degree :
    quotient5.natDegree ≤ 1 := by
  unfold quotient5 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient6_degree :
    quotient6.natDegree ≤ 1 := by
  unfold quotient6 linearPseudoQuotient outerTerm
  compute_degree

private lemma remainder1_coeff_seven : remainder1.coeff 7 = 1 := by
  simp [remainder1]

private lemma remainder2Coefficient6Block0_topCoefficient :
    (remainder2Coefficient6Block0.coeff 95) =
      (-((1 : ℚ))) := by
  norm_num [remainder2Coefficient6Block0, remainder2Coefficient6Chunk0,
    remainder2Coefficient6Chunk1, remainder2Coefficient6Chunk2,
    remainder2Coefficient6Chunk3, remainder2Coefficient6Chunk4,
    remainder2Coefficient6Chunk5, remainder2Coefficient6Chunk6,
    remainder2Coefficient6Chunk7, remainder2Coefficient6Chunk8,
    remainder2Coefficient6Chunk9, remainder2Coefficient6Chunk10,
    remainder2Coefficient6Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder2Coefficient6_topCoefficient :
    (remainder2Coefficient6.coeff 95) =
      (-((1 : ℚ))) := by
  simp [remainder2Coefficient6,
    remainder2Coefficient6Block0_topCoefficient]

private lemma remainder2_leadingCoeff_ne_zero :
    remainder2.coeff 6 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder2Coefficient6 = 0 := by
    simpa [remainder2, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 95)
    hcoefficient
  rw [remainder2Coefficient6_topCoefficient] at htop
  norm_num at htop

private lemma remainder3Coefficient5Block0_topCoefficient :
    (remainder3Coefficient5Block0.coeff 134) =
      (-((9250229 : ℚ))) := by
  norm_num [remainder3Coefficient5Block0, remainder3Coefficient5Chunk0,
    remainder3Coefficient5Chunk1, remainder3Coefficient5Chunk2,
    remainder3Coefficient5Chunk3, remainder3Coefficient5Chunk4,
    remainder3Coefficient5Chunk5, remainder3Coefficient5Chunk6,
    remainder3Coefficient5Chunk7, remainder3Coefficient5Chunk8,
    remainder3Coefficient5Chunk9, remainder3Coefficient5Chunk10,
    remainder3Coefficient5Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder3Coefficient5Block1_topCoefficient :
    (remainder3Coefficient5Block1.coeff 134) =
      (0 : ℚ) := by
  norm_num [remainder3Coefficient5Block1, remainder3Coefficient5Chunk12,
    remainder3Coefficient5Chunk13, remainder3Coefficient5Chunk14,
    remainder3Coefficient5Chunk15, remainder3Coefficient5Chunk16,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder3Coefficient5_topCoefficient :
    (remainder3Coefficient5.coeff 134) =
      (-((9250229 : ℚ))) := by
  simp [remainder3Coefficient5,
    remainder3Coefficient5Block0_topCoefficient,
    remainder3Coefficient5Block1_topCoefficient]

private lemma remainder3_leadingCoeff_ne_zero :
    remainder3.coeff 5 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder3Coefficient5 = 0 := by
    simpa [remainder3, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 134)
    hcoefficient
  rw [remainder3Coefficient5_topCoefficient] at htop
  norm_num at htop

private lemma remainder4Coefficient4Block0_topCoefficient :
    (remainder4Coefficient4Block0.coeff 178) =
      (-((152365481437 : ℚ))) := by
  norm_num [remainder4Coefficient4Block0, remainder4Coefficient4Chunk0,
    remainder4Coefficient4Chunk1, remainder4Coefficient4Chunk2,
    remainder4Coefficient4Chunk3, remainder4Coefficient4Chunk4,
    remainder4Coefficient4Chunk5, remainder4Coefficient4Chunk6,
    remainder4Coefficient4Chunk7, remainder4Coefficient4Chunk8,
    remainder4Coefficient4Chunk9, remainder4Coefficient4Chunk10,
    remainder4Coefficient4Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder4Coefficient4Block1_topCoefficient :
    (remainder4Coefficient4Block1.coeff 178) =
      (0 : ℚ) := by
  norm_num [remainder4Coefficient4Block1, remainder4Coefficient4Chunk12,
    remainder4Coefficient4Chunk13, remainder4Coefficient4Chunk14,
    remainder4Coefficient4Chunk15, remainder4Coefficient4Chunk16,
    remainder4Coefficient4Chunk17, remainder4Coefficient4Chunk18,
    remainder4Coefficient4Chunk19, remainder4Coefficient4Chunk20,
    remainder4Coefficient4Chunk21, remainder4Coefficient4Chunk22,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder4Coefficient4_topCoefficient :
    (remainder4Coefficient4.coeff 178) =
      (-((152365481437 : ℚ))) := by
  simp [remainder4Coefficient4,
    remainder4Coefficient4Block0_topCoefficient,
    remainder4Coefficient4Block1_topCoefficient]

private lemma remainder4_leadingCoeff_ne_zero :
    remainder4.coeff 4 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder4Coefficient4 = 0 := by
    simpa [remainder4, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 178)
    hcoefficient
  rw [remainder4Coefficient4_topCoefficient] at htop
  norm_num at htop

private lemma remainder5Coefficient3Block0_topCoefficient :
    (remainder5Coefficient3Block0.coeff 164) =
      (-((447151549834258283177195510 : ℚ))) := by
  norm_num [remainder5Coefficient3Block0, remainder5Coefficient3Chunk0,
    remainder5Coefficient3Chunk1, remainder5Coefficient3Chunk2,
    remainder5Coefficient3Chunk3, remainder5Coefficient3Chunk4,
    remainder5Coefficient3Chunk5, remainder5Coefficient3Chunk6,
    remainder5Coefficient3Chunk7, remainder5Coefficient3Chunk8,
    remainder5Coefficient3Chunk9, remainder5Coefficient3Chunk10,
    remainder5Coefficient3Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder5Coefficient3Block1_topCoefficient :
    (remainder5Coefficient3Block1.coeff 164) =
      (0 : ℚ) := by
  norm_num [remainder5Coefficient3Block1, remainder5Coefficient3Chunk12,
    remainder5Coefficient3Chunk13, remainder5Coefficient3Chunk14,
    remainder5Coefficient3Chunk15, remainder5Coefficient3Chunk16,
    remainder5Coefficient3Chunk17, remainder5Coefficient3Chunk18,
    remainder5Coefficient3Chunk19, remainder5Coefficient3Chunk20,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder5Coefficient3_topCoefficient :
    (remainder5Coefficient3.coeff 164) =
      (-((447151549834258283177195510 : ℚ))) := by
  simp [remainder5Coefficient3,
    remainder5Coefficient3Block0_topCoefficient,
    remainder5Coefficient3Block1_topCoefficient]

private lemma remainder5_leadingCoeff_ne_zero :
    remainder5.coeff 3 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder5Coefficient3 = 0 := by
    simpa [remainder5, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 164)
    hcoefficient
  rw [remainder5Coefficient3_topCoefficient] at htop
  norm_num at htop

private lemma remainder6Coefficient2Block0_topCoefficient :
    (remainder6Coefficient2Block0.coeff 145) =
      (-(((53701746906274322922389292 : ℚ) * 10 ^ 36 +
        413329009090012362832185396756764943))) := by
  norm_num [remainder6Coefficient2Block0, remainder6Coefficient2Chunk0,
    remainder6Coefficient2Chunk1, remainder6Coefficient2Chunk2,
    remainder6Coefficient2Chunk3, remainder6Coefficient2Chunk4,
    remainder6Coefficient2Chunk5, remainder6Coefficient2Chunk6,
    remainder6Coefficient2Chunk7, remainder6Coefficient2Chunk8,
    remainder6Coefficient2Chunk9, remainder6Coefficient2Chunk10,
    remainder6Coefficient2Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder6Coefficient2Block1_topCoefficient :
    (remainder6Coefficient2Block1.coeff 145) =
      (0 : ℚ) := by
  norm_num [remainder6Coefficient2Block1, remainder6Coefficient2Chunk12,
    remainder6Coefficient2Chunk13, remainder6Coefficient2Chunk14,
    remainder6Coefficient2Chunk15, remainder6Coefficient2Chunk16,
    remainder6Coefficient2Chunk17, remainder6Coefficient2Chunk18,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder6Coefficient2_topCoefficient :
    (remainder6Coefficient2.coeff 145) =
      (-(((53701746906274322922389292 : ℚ) * 10 ^ 36 +
        413329009090012362832185396756764943))) := by
  simp [remainder6Coefficient2,
    remainder6Coefficient2Block0_topCoefficient,
    remainder6Coefficient2Block1_topCoefficient]

private lemma remainder6_leadingCoeff_ne_zero :
    remainder6.coeff 2 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder6Coefficient2 = 0 := by
    simpa [remainder6, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 145)
    hcoefficient
  rw [remainder6Coefficient2_topCoefficient] at htop
  norm_num at htop

private lemma remainder7Coefficient1Block0_topCoefficient :
    (remainder7Coefficient1Block0.coeff 84) =
      (-((((((1557 : ℚ) * 10 ^ 36 +
        411197222661268025367413836777879542) * 10 ^ 36 +
        082863389056330876674739520938317083) * 10 ^ 36 +
        162921568205678358405098446864079426) * 10 ^ 36 +
        408781113703694420237088677512308100))) := by
  norm_num [remainder7Coefficient1Block0, remainder7Coefficient1Chunk0,
    remainder7Coefficient1Chunk1, remainder7Coefficient1Chunk2,
    remainder7Coefficient1Chunk3, remainder7Coefficient1Chunk4,
    remainder7Coefficient1Chunk5, remainder7Coefficient1Chunk6,
    remainder7Coefficient1Chunk7, remainder7Coefficient1Chunk8,
    remainder7Coefficient1Chunk9, remainder7Coefficient1Chunk10,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder7Coefficient1_topCoefficient :
    (remainder7Coefficient1.coeff 84) =
      (-((((((1557 : ℚ) * 10 ^ 36 +
        411197222661268025367413836777879542) * 10 ^ 36 +
        082863389056330876674739520938317083) * 10 ^ 36 +
        162921568205678358405098446864079426) * 10 ^ 36 +
        408781113703694420237088677512308100))) := by
  simp [remainder7Coefficient1,
    remainder7Coefficient1Block0_topCoefficient]

private lemma remainder7_leadingCoeff_ne_zero :
    remainder7.coeff 1 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder7Coefficient1 = 0 := by
    simpa [remainder7, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 84)
    hcoefficient
  rw [remainder7Coefficient1_topCoefficient] at htop
  norm_num at htop

private lemma remainder8_eq : remainder8 = C (-1) := by
  norm_num [remainder8, remainder8Coefficient0,
    remainder8Coefficient0Block0, remainder8Coefficient0Chunk0,
    outerTerm, coefficientTerm]

private theorem cmSix_eq_resultantFactorSix :
    cmSix = resultantFactorSix.map (Int.castRingHom ℚ) := by
  simp [cmSix, resultantFactorSix, parameter]

private theorem cmTwelve_eq_resultantFactorTwelve :
    cmTwelve = resultantFactorTwelve.map (Int.castRingHom ℚ) := by
  simp [cmTwelve, resultantFactorTwelve, parameter]

private theorem exceptional_monomial_identity
    {M : Type} [CommMonoid M]
    (a b q c6 c12 u3 u4 u5 u6 : M)
    (hunit : u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6 = 1) :
    ((b ^ 6 * a ^ 7) ^ 7) * (q ^ 21) ^ 6 *
      (b * a ^ 2) ^ 5 * (u3 * q ^ 22) ^ 4 *
      (u4 * b * q ^ 4) ^ 3 * (u5 * a ^ 2 * q ^ 14 * c6) ^ 2 *
      (u6 * b * q ^ 6 * c12) =
        a ^ 63 * b ^ 51 * q ^ 260 * c6 ^ 2 * c12 := by
  have ha : a ^ 63 = a ^ 49 * a ^ 10 * a ^ 4 := by
    rw [show 63 = 49 + 10 + 4 by omega, pow_add, pow_add]
  have hb : b ^ 51 = b ^ 42 * b ^ 5 * b ^ 3 * b := by
    rw [show 51 = 42 + 5 + 3 + 1 by omega,
      pow_add, pow_add, pow_add, pow_one]
  have hq : q ^ 260 = q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 *
      q ^ 6 := by
    rw [show 260 = 126 + 88 + 12 + 28 + 6 by omega,
      pow_add, pow_add, pow_add, pow_add]
  calc
    _ = (u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6) *
        (a ^ 49 * a ^ 10 * a ^ 4) *
        (b ^ 42 * b ^ 5 * b ^ 3 * b) *
        (q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 * q ^ 6) *
        c6 ^ 2 * c12 := by
      simp only [mul_pow]
      repeat rw [← pow_mul]
      norm_num
      ac_rfl
    _ = _ := by rw [hunit, ha, hb, hq]; ac_rfl

private theorem factored_expression_eq_resultantFactorData :
    parameter ^ 63 * (parameter - 1) ^ 51 *
      discriminantFactor ^ 260 * cmSix ^ 2 * cmTwelve =
      resultantFactorData := by
  have hp : parameter = X := rfl
  have h8 : (8 : Coefficient) = C 8 := rfl
  have h5 : (5 : Coefficient) = C 5 := rfl
  have hd : discriminantFactor =
      X ^ 3 - C 8 * X ^ 2 + C 5 * X + 1 := by
    rw [discriminantFactor, hp, h8, h5]
  unfold resultantFactorData
  rw [← cmSix_eq_resultantFactorSix,
    ← cmTwelve_eq_resultantFactorTwelve, hp, hd]

private theorem exceptional_product_eq_resultantFactorData :
    exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
      exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
      exceptional6 = resultantFactorData := by
  have hunit : exceptionalUnit3 ^ 4 * exceptionalUnit4 ^ 3 *
      exceptionalUnit5 ^ 2 * exceptionalUnit6 = 1 := by
    unfold exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
      exceptionalUnit6
    rw [← map_pow, ← map_pow, ← map_pow,
      ← map_mul, ← map_mul, ← map_mul]
    norm_num
  have hmonomial := exceptional_monomial_identity
    parameter (parameter - 1) discriminantFactor cmSix cmTwelve
    exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
    exceptionalUnit6 hunit
  rw [← factored_expression_eq_resultantFactorData, ← hmonomial]
  unfold exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6
  simp only [exceptionalUnit0, exceptionalUnit1, exceptionalUnit2,
    map_one, one_mul, pow_one]

end Internal.ResultantCertificate

open Internal.ResultantCertificate

/-- The seven checked pseudo-remainder recurrences imply the exact
factorization of the first bounded resultant over `ℚ[D]`. -/
theorem generic_resultant_eq_resultantFactorData :
    resultant selectionCofactorData divisionCofactorData0 33 7 =
      resultantFactorData := by
  have h := bounded_resultant_telescope_33_7
    remainder0 remainder1 remainder2 remainder3 remainder4
    remainder5 remainder6 remainder7 remainder8
    quotient0 quotient1 quotient2 quotient3 quotient4 quotient5 quotient6
    (remainder2.coeff 6) (remainder3.coeff 5)
    (remainder4.coeff 4) (remainder5.coeff 3)
    (remainder6.coeff 2) (remainder7.coeff 1)
    exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6 (-1)
    remainder1_degree remainder2_degree remainder3_degree
    remainder4_degree remainder5_degree remainder6_degree
    remainder7_degree remainder8_degree
    (by have := quotient0_degree; omega)
    (by have := quotient1_degree; omega)
    (by have := quotient2_degree; omega)
    (by have := quotient3_degree; omega)
    (by have := quotient4_degree; omega)
    (by have := quotient5_degree; omega)
    (by have := quotient6_degree; omega)
    remainder1_coeff_seven rfl rfl rfl rfl rfl rfl
    remainder2_leadingCoeff_ne_zero
    remainder3_leadingCoeff_ne_zero
    remainder4_leadingCoeff_ne_zero
    remainder5_leadingCoeff_ne_zero
    remainder6_leadingCoeff_ne_zero
    remainder7_leadingCoeff_ne_zero
    (by simpa only [recurrence0] using recurrence0_checked)
    (by simpa only [recurrence1] using recurrence1_checked)
    (by simpa only [recurrence2] using recurrence2_checked)
    (by simpa only [recurrence3] using recurrence3_checked)
    (by simpa only [recurrence4] using recurrence4_checked)
    (by simpa only [recurrence5] using recurrence5_checked)
    (by simpa only [recurrence6] using recurrence6_checked)
    remainder8_eq
  calc
    resultant selectionCofactorData divisionCofactorData0 33 7 =
        exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
          exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
          exceptional6 := by
      rw [← remainder0, ← remainder1]
      calc
        resultant remainder0 remainder1 33 7 =
            -exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 * (-1) := h
        _ = exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 := by ring
    _ = resultantFactorData := exceptional_product_eq_resultantFactorData





end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

theorem solution : Polynomial.resultant MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0 33 7 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.generic_resultant_eq_resultantFactorData
#print axioms solution
