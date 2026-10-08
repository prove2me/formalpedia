-- Prove2me | solution 1 for MazurTransfer.order49_all_bounded_resultants_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:17:31.482595+00:00
-- url     : https://prove2.me/submissions/f55304ad-f2ba-492f-a864-0f84d1a223de

import Theorems.Thm_MazurTransfer_order49_first_bounded_resultant_nonzero
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_0
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_1
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_2
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_3
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_4
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_5
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_6
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_7
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_8
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_9
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_10
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_11
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_12
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_13
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_14
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_15
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_16
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_17
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_18
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_19
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_20
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_21
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_22
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_23
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_24
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_25
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_26
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_27
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_28
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_29
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_30
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_31
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_32
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_33
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_34
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_35
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_36
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_divisionCofactor0_resultant_ne_zero (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) : Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 := MazurTransfer.order49_first_bounded_resultant_nonzero d hd0 hd1 hcubic
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt0 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 0 := MazurTransfer.order49_selection_evaluation_0 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt1 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 1 := MazurTransfer.order49_selection_evaluation_1 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt2 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 2 := MazurTransfer.order49_selection_evaluation_2 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt3 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 3 := MazurTransfer.order49_selection_evaluation_3 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt4 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 4 := MazurTransfer.order49_selection_evaluation_4 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt5 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 5 := MazurTransfer.order49_selection_evaluation_5 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt6 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 6 := MazurTransfer.order49_selection_evaluation_6 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt7 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 7 := MazurTransfer.order49_selection_evaluation_7 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt8 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 8 := MazurTransfer.order49_selection_evaluation_8 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt9 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 9 := MazurTransfer.order49_selection_evaluation_9 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt10 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 10 := MazurTransfer.order49_selection_evaluation_10 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt11 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 11 := MazurTransfer.order49_selection_evaluation_11 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt12 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 12 := MazurTransfer.order49_selection_evaluation_12 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt13 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 13 := MazurTransfer.order49_selection_evaluation_13 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt14 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 14 := MazurTransfer.order49_selection_evaluation_14 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt15 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 15 := MazurTransfer.order49_selection_evaluation_15 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt16 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 16 := MazurTransfer.order49_selection_evaluation_16 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt17 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 17 := MazurTransfer.order49_selection_evaluation_17 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt18 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 18 := MazurTransfer.order49_selection_evaluation_18 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt19 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 19 := MazurTransfer.order49_selection_evaluation_19 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt20 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 20 := MazurTransfer.order49_selection_evaluation_20 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt21 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 21 := MazurTransfer.order49_selection_evaluation_21 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt22 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 22 := MazurTransfer.order49_selection_evaluation_22 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt23 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 23 := MazurTransfer.order49_selection_evaluation_23 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt24 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 24 := MazurTransfer.order49_selection_evaluation_24 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt25 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 25 := MazurTransfer.order49_selection_evaluation_25 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt26 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 26 := MazurTransfer.order49_selection_evaluation_26 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt27 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 27 := MazurTransfer.order49_selection_evaluation_27 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt28 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 28 := MazurTransfer.order49_selection_evaluation_28 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt29 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 29 := MazurTransfer.order49_selection_evaluation_29 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt30 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 30 := MazurTransfer.order49_selection_evaluation_30 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt31 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 31 := MazurTransfer.order49_selection_evaluation_31 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt32 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 32 := MazurTransfer.order49_selection_evaluation_32 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt33 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 33 := MazurTransfer.order49_selection_evaluation_33 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt34 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 34 := MazurTransfer.order49_selection_evaluation_34 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt35 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 35 := MazurTransfer.order49_selection_evaluation_35 d
theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt36 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 36 := MazurTransfer.order49_selection_evaluation_36 d


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



section Telescope

variable [IsDomain R]





end Telescope

section DegreeTelescope

variable [IsDomain R]



end DegreeTelescope

/-- A nonzero bounded resultant against a monic polynomial is already a
nonzero ordinary resultant.  Only a degree bound is needed on the left
polynomial, so this remains useful when specialization drops its degree. -/
theorem resultant_ne_zero_of_bounded_resultant_ne_zero
    {f g : R[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) :
    resultant f g ≠ 0 := by
  have hcoeff : g.coeff n = 1 := by
    rw [← hg]
    exact hmonic
  intro hzero
  apply hres
  have hm : m = f.natDegree + (m - f.natDegree) := by omega
  rw [hm, resultant_add_left_deg _ _ _ _ _ le_rfl, hcoeff]
  simp only [one_pow, mul_one]
  rw [← hg]
  exact mul_eq_zero_of_right _ hzero

/-- A nonzero bounded resultant against a monic polynomial over a field
makes the two polynomials coprime. -/
theorem isCoprime_of_bounded_resultant_ne_zero
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) :
    IsCoprime f g := by
  have hraw : resultant f g ≠ 0 :=
    resultant_ne_zero_of_bounded_resultant_ne_zero hf hg hmonic hres
  by_contra hnot
  apply hraw
  exact resultant_eq_zero_iff.mpr ⟨Or.inr hmonic.ne_zero, hnot⟩

/-- Coprime polynomials have nonzero bounded resultant when the right
polynomial is monic and the degree padding is explicit.  The left polynomial
may lose degree after specialization. -/
theorem bounded_resultant_ne_zero_of_isCoprime
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic) (hcop : IsCoprime f g) :
    resultant f g m n ≠ 0 := by
  have hraw : resultant f g ≠ 0 :=
    Polynomial.resultant_ne_zero f g hcop
  have hcoeff : g.coeff n = 1 := by
    rw [← hg]
    exact hmonic.coeff_natDegree
  have hm : m = f.natDegree + (m - f.natDegree) := by omega
  rw [hm, resultant_add_left_deg _ _ _ _ _ le_rfl, hcoeff]
  simp only [one_pow, mul_one]
  rw [← hg]
  exact mul_ne_zero (by simp) hraw



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

/-- Internal datum. -/ noncomputable def dualKernelPolynomial (d : ℚ) : ℚ[X] :=
  C 7 * X ^ 3 +
    C (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) * X ^ 2 +
    C (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 - 203 * d ^ 4 +
      49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) * X +
    C (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 - 767 * d ^ 8 +
      2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 - 295 * d ^ 4 -
      116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1)

@[simp] theorem dualKernelPolynomial_eval (d x : ℚ) :
    (dualKernelPolynomial d).eval x = orderSevenDualKernelPolynomial d x := by
  simp [dualKernelPolynomial, orderSevenDualKernelPolynomial]

end Internal

lemma selectionCofactorData_degree :
    selectionCofactorData.natDegree ≤ 33 := by
  unfold selectionCofactorData
  compute_degree





lemma selectionCofactor_degree (d : ℚ) :
    (selectionCofactor d).natDegree ≤ 33 := by
  exact natDegree_map_le.trans selectionCofactorData_degree

lemma divisionCofactorData0_degree :
    divisionCofactorData0.natDegree ≤ 7 := by
  unfold divisionCofactorData0
  compute_degree

lemma divisionCofactorData1_degree :
    divisionCofactorData1.natDegree ≤ 7 := by
  unfold divisionCofactorData1
  compute_degree

lemma divisionCofactorData2_degree :
    divisionCofactorData2.natDegree ≤ 7 := by
  unfold divisionCofactorData2
  compute_degree

lemma divisionCofactor0_degree (d : ℚ) :
    (divisionCofactor0 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans divisionCofactorData0_degree

lemma divisionCofactor1_degree (d : ℚ) :
    (divisionCofactor1 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans divisionCofactorData1_degree

lemma divisionCofactor2_degree (d : ℚ) :
    (divisionCofactor2 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans divisionCofactorData2_degree



















@[simp] theorem divisionCofactor0_coeff_seven (d : ℚ) :
    (divisionCofactor0 d).coeff 7 = 1 := by
  simp [divisionCofactor0, divisionCofactorData0,
    Internal.divisionCofactor0Coefficient7,
    Internal.divisionCofactor0Coefficient7Chunk0]

@[simp] theorem divisionCofactor1_coeff_seven (d : ℚ) :
    (divisionCofactor1 d).coeff 7 = 1 := by
  simp [divisionCofactor1, divisionCofactorData1,
    Internal.divisionCofactor1Coefficient7,
    Internal.divisionCofactor1Coefficient7Chunk0]

@[simp] theorem divisionCofactor2_coeff_seven (d : ℚ) :
    (divisionCofactor2 d).coeff 7 = 1 := by
  simp [divisionCofactor2, divisionCofactorData2,
    Internal.divisionCofactor2Coefficient7,
    Internal.divisionCofactor2Coefficient7Chunk0]

theorem divisionCofactor0_natDegree (d : ℚ) :
    (divisionCofactor0 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (divisionCofactor0_degree d) (by simp)

theorem divisionCofactor1_natDegree (d : ℚ) :
    (divisionCofactor1 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (divisionCofactor1_degree d) (by simp)

theorem divisionCofactor2_natDegree (d : ℚ) :
    (divisionCofactor2 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (divisionCofactor2_degree d) (by simp)

theorem divisionCofactor0_monic (d : ℚ) :
    (divisionCofactor0 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (divisionCofactor0_degree d) (divisionCofactor0_coeff_seven d)

theorem divisionCofactor1_monic (d : ℚ) :
    (divisionCofactor1 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (divisionCofactor1_degree d) (divisionCofactor1_coeff_seven d)

theorem divisionCofactor2_monic (d : ℚ) :
    (divisionCofactor2 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (divisionCofactor2_degree d) (divisionCofactor2_coeff_seven d)

namespace Internal

/-- Internal datum. -/ noncomputable def completedCubicPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

/-- Internal datum. -/ noncomputable def completedTangentPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- Internal datum. -/ noncomputable def tateAlphaPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  (C 12 * X + C W.b₂) * completedCubicPolynomial W -
    completedTangentPolynomial W ^ 2

/-- Internal datum. -/ noncomputable def tateGammaPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * completedCubicPolynomial W ^ 2 -
    tateAlphaPolynomial W * completedTangentPolynomial W

/-- Internal datum. -/ noncomputable def tateParameterNumeratorPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  -tateAlphaPolynomial W ^ 3

/-- Internal datum. -/ noncomputable def tateParameterDenominatorPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 16 * tateGammaPolynomial W * completedCubicPolynomial W ^ 2

/-- Internal datum. -/ noncomputable def parameterCubicPolynomial (A B : ℚ[X]) : ℚ[X] :=
  A ^ 3 - C 8 * A ^ 2 * B + C 5 * A * B ^ 2 + B ^ 3

/-- Internal datum. -/ noncomputable def parameterHauptmodulNumeratorPolynomial
    (A B : ℚ[X]) : ℚ[X] :=
  C 49 * A * (A - B) * B

/-- Internal datum. -/ noncomputable def selectionPolynomialData (d : ℚ) : ℚ[X] :=
  let W := orderSevenQuotient d
  let A := tateParameterNumeratorPolynomial W
  let B := tateParameterDenominatorPolynomial W
  C (d * (d - 1)) * parameterHauptmodulNumeratorPolynomial A B -
    C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) * parameterCubicPolynomial A B

@[simp] theorem selectionPolynomialData_eval (d x : ℚ) :
    (selectionPolynomialData d).eval x = orderSevenSelectionPolynomial d x := by
  simp [selectionPolynomialData,
    parameterHauptmodulNumeratorPolynomial,
    parameterCubicPolynomial,
    tateParameterNumeratorPolynomial,
    tateParameterDenominatorPolynomial,
    tateAlphaPolynomial,
    tateGammaPolynomial,
    completedTangentPolynomial,
    completedCubicPolynomial,
    orderSevenSelectionPolynomial,
    pointTateParameterUnivariateNumerator,
    pointTateParameterUnivariateDenominator,
    pointTateAlphaUnivariateCleared,
    pointTateGammaUnivariateCleared,
    pointTateCompletedTangentNumerator,
    orderSevenParameterHauptmodulNumerator,
    orderSevenParameterCubic,
    Doubling.completedCubic]

private lemma natDegree_mul_le_of_le {p q : ℚ[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private lemma natDegree_sub_le_of_le {p q : ℚ[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p - q).natDegree ≤ max m n :=
  natDegree_sub_le p q |>.trans (max_le_max hp hq)

private lemma natDegree_add_le_of_le {p q : ℚ[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ max m n :=
  natDegree_add_le p q |>.trans (max_le_max hp hq)

private lemma natDegree_pow_le_of_le {p : ℚ[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) :
    (p ^ n).natDegree ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left n hp)

private lemma completedCubicPolynomial_degree (W : WeierstrassCurve ℚ) :
    (completedCubicPolynomial W).natDegree ≤ 3 := by
  unfold completedCubicPolynomial
  compute_degree

private lemma completedTangentPolynomial_degree (W : WeierstrassCurve ℚ) :
    (completedTangentPolynomial W).natDegree ≤ 2 := by
  unfold completedTangentPolynomial
  compute_degree

private lemma tateAlphaPolynomial_degree (W : WeierstrassCurve ℚ) :
    (tateAlphaPolynomial W).natDegree ≤ 4 := by
  unfold tateAlphaPolynomial
  have ht2 : (completedTangentPolynomial W ^ 2).natDegree ≤ 4 := by
    simpa using natDegree_pow_le_of_le (n := 2)
      (completedTangentPolynomial_degree W)
  apply le_trans (natDegree_sub_le _ _)
  apply max_le
  · exact natDegree_mul_le_of_le (by compute_degree)
      (completedCubicPolynomial_degree W)
  · exact ht2

private lemma tateGammaPolynomial_degree (W : WeierstrassCurve ℚ) :
    (tateGammaPolynomial W).natDegree ≤ 6 := by
  unfold tateGammaPolynomial
  have hd2 : (completedCubicPolynomial W ^ 2).natDegree ≤ 6 := by
    simpa using natDegree_pow_le_of_le (n := 2)
      (completedCubicPolynomial_degree W)
  apply le_trans (natDegree_sub_le _ _)
  apply max_le
  · exact natDegree_mul_le_of_le (by compute_degree) hd2
  · exact natDegree_mul_le_of_le (tateAlphaPolynomial_degree W)
      (completedTangentPolynomial_degree W)

private lemma tateParameterNumeratorPolynomial_degree
    (W : WeierstrassCurve ℚ) :
    (tateParameterNumeratorPolynomial W).natDegree ≤ 12 := by
  unfold tateParameterNumeratorPolynomial
  simpa using natDegree_pow_le_of_le (n := 3)
    (tateAlphaPolynomial_degree W)

private lemma tateParameterDenominatorPolynomial_degree
    (W : WeierstrassCurve ℚ) :
    (tateParameterDenominatorPolynomial W).natDegree ≤ 12 := by
  unfold tateParameterDenominatorPolynomial
  have hd2 : (completedCubicPolynomial W ^ 2).natDegree ≤ 6 := by
    simpa using natDegree_pow_le_of_le (n := 2)
      (completedCubicPolynomial_degree W)
  exact natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by compute_degree)
      (tateGammaPolynomial_degree W))
    hd2

private lemma parameterHauptmodulNumeratorPolynomial_degree
    {A B : ℚ[X]} (hA : A.natDegree ≤ 12) (hB : B.natDegree ≤ 12) :
    (parameterHauptmodulNumeratorPolynomial A B).natDegree ≤ 36 := by
  unfold parameterHauptmodulNumeratorPolynomial
  have hc : (C (49 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hab : (A - B).natDegree ≤ 12 := by
    simpa using natDegree_sub_le_of_le hA hB
  exact natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le hc hA) hab) hB

private lemma parameterCubicPolynomial_degree
    {A B : ℚ[X]} (hA : A.natDegree ≤ 12) (hB : B.natDegree ≤ 12) :
    (parameterCubicPolynomial A B).natDegree ≤ 36 := by
  unfold parameterCubicPolynomial
  have hA3 : (A ^ 3).natDegree ≤ 36 := by
    simpa using natDegree_pow_le_of_le (n := 3) hA
  have hA2 : (A ^ 2).natDegree ≤ 24 := by
    simpa using natDegree_pow_le_of_le (n := 2) hA
  have hB2 : (B ^ 2).natDegree ≤ 24 := by
    simpa using natDegree_pow_le_of_le (n := 2) hB
  have hc8 : (C (8 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hc5 : (C (5 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hA2B : (C 8 * A ^ 2 * B).natDegree ≤ 36 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le hc8 hA2) hB
  have hAB2 : (C 5 * A * B ^ 2).natDegree ≤ 36 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le hc5 hA) hB2
  have hB3 : (B ^ 3).natDegree ≤ 36 := by
    simpa using natDegree_pow_le_of_le (n := 3) hB
  exact natDegree_add_le_of_le
    (natDegree_add_le_of_le (natDegree_sub_le_of_le hA3 hA2B) hAB2) hB3

lemma selectionPolynomialData_degree (d : ℚ) :
    (selectionPolynomialData d).natDegree ≤ 36 := by
  let W := orderSevenQuotient d
  let A := tateParameterNumeratorPolynomial W
  let B := tateParameterDenominatorPolynomial W
  change (C (d * (d - 1)) * parameterHauptmodulNumeratorPolynomial A B -
    C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      parameterCubicPolynomial A B).natDegree ≤ 36
  have hA : A.natDegree ≤ 12 := tateParameterNumeratorPolynomial_degree W
  have hB : B.natDegree ≤ 12 := tateParameterDenominatorPolynomial_degree W
  have hc0 : (C (d * (d - 1))).natDegree ≤ 0 := by compute_degree
  have hc1 : (C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)).natDegree ≤ 0 := by
    compute_degree
  exact natDegree_sub_le_of_le
    (natDegree_mul_le_of_le hc0
      (parameterHauptmodulNumeratorPolynomial_degree hA hB))
    (natDegree_mul_le_of_le hc1
      (parameterCubicPolynomial_degree hA hB))








end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingFactorCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Factor certificates for order-seven backtracking

The selection identity has degree at most `36` in the abscissa and is checked
at `37` rational values.  The quotient seventh division-polynomial identity
has degree at most `24` and is checked at `25` rational values.  Their
pointwise consequences expose only the canonical cofactors needed by the
backtracking obstruction.

Both evaluation families are serial import chains so an ordinary build does
not check several memory-heavy interpolation shards concurrently.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

private theorem selection_eval_fin (d : ℚ) (i : Fin 37) :
    Internal.SelectionEvalCertificate d (i : ℚ) := by
  fin_cases i
  · simpa using Internal.selectionEvalAt0 d
  · simpa using Internal.selectionEvalAt1 d
  · simpa using Internal.selectionEvalAt2 d
  · simpa using Internal.selectionEvalAt3 d
  · simpa using Internal.selectionEvalAt4 d
  · simpa using Internal.selectionEvalAt5 d
  · simpa using Internal.selectionEvalAt6 d
  · simpa using Internal.selectionEvalAt7 d
  · simpa using Internal.selectionEvalAt8 d
  · simpa using Internal.selectionEvalAt9 d
  · simpa using Internal.selectionEvalAt10 d
  · simpa using Internal.selectionEvalAt11 d
  · simpa using Internal.selectionEvalAt12 d
  · simpa using Internal.selectionEvalAt13 d
  · simpa using Internal.selectionEvalAt14 d
  · simpa using Internal.selectionEvalAt15 d
  · simpa using Internal.selectionEvalAt16 d
  · simpa using Internal.selectionEvalAt17 d
  · simpa using Internal.selectionEvalAt18 d
  · simpa using Internal.selectionEvalAt19 d
  · simpa using Internal.selectionEvalAt20 d
  · simpa using Internal.selectionEvalAt21 d
  · simpa using Internal.selectionEvalAt22 d
  · simpa using Internal.selectionEvalAt23 d
  · simpa using Internal.selectionEvalAt24 d
  · simpa using Internal.selectionEvalAt25 d
  · simpa using Internal.selectionEvalAt26 d
  · simpa using Internal.selectionEvalAt27 d
  · simpa using Internal.selectionEvalAt28 d
  · simpa using Internal.selectionEvalAt29 d
  · simpa using Internal.selectionEvalAt30 d
  · simpa using Internal.selectionEvalAt31 d
  · simpa using Internal.selectionEvalAt32 d
  · simpa using Internal.selectionEvalAt33 d
  · simpa using Internal.selectionEvalAt34 d
  · simpa using Internal.selectionEvalAt35 d
  · simpa using Internal.selectionEvalAt36 d

private lemma dualKernelPolynomial_degree (d : ℚ) :
    (Internal.dualKernelPolynomial d).natDegree ≤ 3 := by
  unfold Internal.dualKernelPolynomial
  compute_degree

private lemma selection_factor_product_degree (d : ℚ) :
    (C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
      selectionCofactor d).natDegree ≤ 36 := by
  have h0 : (C (64 ^ 3 : ℚ) *
      Internal.dualKernelPolynomial d).natDegree ≤ 3 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add (by compute_degree) (dualKernelPolynomial_degree d))
  exact le_trans natDegree_mul_le
    (Nat.add_le_add h0 (selectionCofactor_degree d))

private theorem selection_polynomial_factorization (d : ℚ) :
    Internal.selectionPolynomialData d =
      C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
        selectionCofactor d := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 37 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    simpa [Internal.SelectionEvalCertificate] using selection_eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := Internal.selectionPolynomialData_degree d
    have hr := selection_factor_product_degree d
    omega

/-- Pointwise factorization of the backtracking selection polynomial into the
dual-kernel cubic and its degree-33 cofactor. -/
theorem orderSevenSelectionPolynomial_eval_factorization (d x : ℚ) :
    orderSevenSelectionPolynomial d x =
      64 ^ 3 * orderSevenDualKernelPolynomial d x *
        (selectionCofactor d).eval x := by
  have h := congrArg (Polynomial.eval x)
    (selection_polynomial_factorization d)
  simpa [Internal.selectionPolynomialData_eval,
    Internal.dualKernelPolynomial_eval, mul_assoc] using h











end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSymmetry. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Order-three symmetry of the order-seven backtracking cofactors

The fractional-linear parameter transformation `d ↦ 1 / (1 - d)` cyclically permutes the
three canonical degree-seven division cofactors and preserves the selection cofactor up to scale.
The accompanying affine change of the polynomial variable is explicit, so a coprimality
certificate for one division cofactor can be transported to the other two.

The division identities check the stored coefficient tables directly.  The
selection identity instead transports the structural Tate and dual-kernel
factorizations, then cancels their certified common factor.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

/-- The order-three transformation of the order-seven Hauptmodul parameter. -/
def orderThreeParameter (d : ℚ) : ℚ :=
  (1 - d)⁻¹

/-- The affine polynomial-variable change accompanying `orderThreeParameter`. -/
def orderThreeAffine (d : ℚ) : ℚ[X] :=
  C ((d - 1)⁻¹ ^ 4) * X - C (d * (d - 1)⁻¹ ^ 3)

/-- The order-three transform stays away from zero when the original
parameter stays away from one. -/
theorem orderThreeParameter_ne_zero (d : ℚ) (hd : d ≠ 1) :
    orderThreeParameter d ≠ 0 := by
  unfold orderThreeParameter
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hd))

/-- The order-three transform stays away from one when the original
parameter stays away from zero. -/
theorem orderThreeParameter_ne_one (d : ℚ) (hd : d ≠ 0) :
    orderThreeParameter d ≠ 1 := by
  unfold orderThreeParameter
  rw [inv_ne_one]
  intro h
  apply hd
  linarith

/-- The cubic singular factor is preserved up to a nonzero cube by the
order-three parameter symmetry. -/
theorem discriminantFactor_orderThreeParameter (d : ℚ) (hd : d ≠ 1) :
    orderThreeParameter d ^ 3 -
        8 * orderThreeParameter d ^ 2 +
        5 * orderThreeParameter d + 1 =
      (d - 1)⁻¹ ^ 3 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simp only [orderThreeParameter]
  field_simp [sub_ne_zero.mpr hd]
  ring

/-- The order-three parameter symmetry sends the first division cofactor to the second. -/
theorem divisionCofactor0_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (divisionCofactor0 (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 28) * divisionCofactor1 d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_mul, eval_C]
  simp only [orderThreeAffine, inv_pow, map_mul, eval_sub, eval_mul, eval_C, eval_X,
    divisionCofactor0, orderThreeParameter, divisionCofactorData0,
    Internal.divisionCofactor0Coefficient0,
    Internal.divisionCofactor0Coefficient0Chunk0, zero_add,
    Internal.divisionCofactor0Coefficient0Chunk1, mul_neg,
    Internal.divisionCofactor0Coefficient0Chunk2, mul_one, map_add, map_one, map_neg, map_pow,
    Internal.divisionCofactor0Coefficient1,
    Internal.divisionCofactor0Coefficient1Chunk0,
    Internal.divisionCofactor0Coefficient1Chunk1,
    Internal.divisionCofactor0Coefficient2,
    Internal.divisionCofactor0Coefficient2Chunk0,
    Internal.divisionCofactor0Coefficient2Chunk1,
    Internal.divisionCofactor0Coefficient3,
    Internal.divisionCofactor0Coefficient3Chunk0,
    Internal.divisionCofactor0Coefficient3Chunk1,
    Internal.divisionCofactor0Coefficient4,
    Internal.divisionCofactor0Coefficient4Chunk0,
    Internal.divisionCofactor0Coefficient5, Internal.divisionCofactor0Coefficient5Chunk0,
    Internal.divisionCofactor0Coefficient6, Internal.divisionCofactor0Coefficient6Chunk0,
    Internal.divisionCofactor0Coefficient7, Internal.divisionCofactor0Coefficient7Chunk0,
    Polynomial.map_add, Polynomial.map_mul, map_C, coe_evalRingHom, Polynomial.map_one,
    Polynomial.map_neg, eval_ofNat, Polynomial.map_pow, map_X, eval_add, eval_one, eval_neg,
    eval_pow, divisionCofactor1, divisionCofactorData1,
    Internal.divisionCofactor1Coefficient0,
    Internal.divisionCofactor1Coefficient0Chunk0,
    Internal.divisionCofactor1Coefficient0Chunk1,
    Internal.divisionCofactor1Coefficient0Chunk2,
    Internal.divisionCofactor1Coefficient1,
    Internal.divisionCofactor1Coefficient1Chunk0,
    Internal.divisionCofactor1Coefficient1Chunk1,
    Internal.divisionCofactor1Coefficient2,
    Internal.divisionCofactor1Coefficient2Chunk0,
    Internal.divisionCofactor1Coefficient2Chunk1,
    Internal.divisionCofactor1Coefficient3,
    Internal.divisionCofactor1Coefficient3Chunk0,
    Internal.divisionCofactor1Coefficient3Chunk1,
    Internal.divisionCofactor1Coefficient4,
    Internal.divisionCofactor1Coefficient4Chunk0,
    Internal.divisionCofactor1Coefficient5, Internal.divisionCofactor1Coefficient5Chunk0,
    Internal.divisionCofactor1Coefficient6,
    Internal.divisionCofactor1Coefficient6Chunk0,
    Internal.divisionCofactor1Coefficient7,
    Internal.divisionCofactor1Coefficient7Chunk0]
  field_simp [sub_ne_zero.mpr hd]
  ring

/-- The order-three parameter symmetry sends the second division cofactor to the third. -/
theorem divisionCofactor1_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (divisionCofactor1 (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 28) * divisionCofactor2 d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_mul, eval_C]
  simp only [orderThreeAffine, inv_pow, map_mul, eval_sub, eval_mul, eval_C, eval_X,
    divisionCofactor1, orderThreeParameter, divisionCofactorData1,
    Internal.divisionCofactor1Coefficient0,
    Internal.divisionCofactor1Coefficient0Chunk0, zero_add,
    Internal.divisionCofactor1Coefficient0Chunk1, mul_neg,
    Internal.divisionCofactor1Coefficient0Chunk2, mul_one, map_add, map_neg, map_one, map_pow,
    Internal.divisionCofactor1Coefficient1,
    Internal.divisionCofactor1Coefficient1Chunk0,
    Internal.divisionCofactor1Coefficient1Chunk1,
    Internal.divisionCofactor1Coefficient2,
    Internal.divisionCofactor1Coefficient2Chunk0,
    Internal.divisionCofactor1Coefficient2Chunk1,
    Internal.divisionCofactor1Coefficient3,
    Internal.divisionCofactor1Coefficient3Chunk0,
    Internal.divisionCofactor1Coefficient3Chunk1,
    Internal.divisionCofactor1Coefficient4,
    Internal.divisionCofactor1Coefficient4Chunk0,
    Internal.divisionCofactor1Coefficient5,
    Internal.divisionCofactor1Coefficient5Chunk0,
    Internal.divisionCofactor1Coefficient6, Internal.divisionCofactor1Coefficient6Chunk0,
    Internal.divisionCofactor1Coefficient7, Internal.divisionCofactor1Coefficient7Chunk0,
    Polynomial.map_add, Polynomial.map_mul, map_C, coe_evalRingHom, Polynomial.map_neg,
    Polynomial.map_one, eval_ofNat, Polynomial.map_pow, map_X, eval_add, eval_neg, eval_one,
    eval_pow, divisionCofactor2, divisionCofactorData2,
    Internal.divisionCofactor2Coefficient0,
    Internal.divisionCofactor2Coefficient0Chunk0,
    Internal.divisionCofactor2Coefficient0Chunk1,
    Internal.divisionCofactor2Coefficient0Chunk2,
    Internal.divisionCofactor2Coefficient1,
    Internal.divisionCofactor2Coefficient1Chunk0,
    Internal.divisionCofactor2Coefficient1Chunk1,
    Internal.divisionCofactor2Coefficient2,
    Internal.divisionCofactor2Coefficient2Chunk0,
    Internal.divisionCofactor2Coefficient2Chunk1,
    Internal.divisionCofactor2Coefficient3,
    Internal.divisionCofactor2Coefficient3Chunk0,
    Internal.divisionCofactor2Coefficient3Chunk1,
    Internal.divisionCofactor2Coefficient4,
    Internal.divisionCofactor2Coefficient4Chunk0,
    Internal.divisionCofactor2Coefficient5, Internal.divisionCofactor2Coefficient5Chunk0,
    Internal.divisionCofactor2Coefficient6,
    Internal.divisionCofactor2Coefficient6Chunk0,
    Internal.divisionCofactor2Coefficient7,
    Internal.divisionCofactor2Coefficient7Chunk0]
  field_simp [sub_ne_zero.mpr hd]
  ring



private theorem completedCubic_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    Doubling.completedCubic (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 12 *
        Doubling.completedCubic (orderSevenQuotient d) x := by
  simp [Doubling.completedCubic, orderSevenQuotient,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    orderSevenB, orderSevenC, orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem completedTateLinear_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    12 * (orderThreeAffine d).eval x +
        (orderSevenQuotient (orderThreeParameter d)).b₂ =
      (d - 1)⁻¹ ^ 4 *
        (12 * x + (orderSevenQuotient d).b₂) := by
  simp [orderSevenQuotient, WeierstrassCurve.b₂,
    orderSevenB, orderSevenC, orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem completedTangent_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateCompletedTangentNumerator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 8 *
        pointTateCompletedTangentNumerator (orderSevenQuotient d) x := by
  simp [pointTateCompletedTangentNumerator, orderSevenQuotient,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, orderSevenB, orderSevenC,
    orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem tateAlpha_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateAlphaUnivariateCleared
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 16 *
        pointTateAlphaUnivariateCleared (orderSevenQuotient d) x := by
  rw [pointTateAlphaUnivariateCleared,
    completedTateLinear_orderThreeParameter d x hd,
    completedCubic_orderThreeParameter d x hd,
    completedTangent_orderThreeParameter d x hd,
    pointTateAlphaUnivariateCleared]
  ring

private theorem tateGamma_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateGammaUnivariateCleared
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 24 *
        pointTateGammaUnivariateCleared (orderSevenQuotient d) x := by
  rw [pointTateGammaUnivariateCleared,
    completedCubic_orderThreeParameter d x hd,
    tateAlpha_orderThreeParameter d x hd,
    completedTangent_orderThreeParameter d x hd,
    pointTateGammaUnivariateCleared]
  ring

private theorem tateParameterNumerator_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateParameterUnivariateNumerator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 48 *
        pointTateParameterUnivariateNumerator (orderSevenQuotient d) x := by
  rw [pointTateParameterUnivariateNumerator,
    tateAlpha_orderThreeParameter d x hd,
    pointTateParameterUnivariateNumerator]
  ring

private theorem tateParameterDenominator_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateParameterUnivariateDenominator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 48 *
        pointTateParameterUnivariateDenominator
          (orderSevenQuotient d) x := by
  rw [pointTateParameterUnivariateDenominator,
    tateGamma_orderThreeParameter d x hd,
    completedCubic_orderThreeParameter d x hd,
    pointTateParameterUnivariateDenominator]
  ring

private theorem selectionPolynomial_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    orderSevenSelectionPolynomial (orderThreeParameter d)
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 147 * orderSevenSelectionPolynomial d x := by
  rw [orderSevenSelectionPolynomial,
    tateParameterNumerator_orderThreeParameter d x hd,
    tateParameterDenominator_orderThreeParameter d x hd,
    orderSevenSelectionPolynomial]
  simp only [orderThreeParameter,
    orderSevenParameterHauptmodulNumerator,
    orderSevenParameterCubic]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem selectionPolynomialData_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1) :
    (Internal.selectionPolynomialData (orderThreeParameter d)).comp
        (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 147) *
        Internal.selectionPolynomialData d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, Internal.selectionPolynomialData_eval,
    eval_mul, eval_C]
  exact selectionPolynomial_orderThreeParameter d x hd

private theorem dualKernel_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    orderSevenDualKernelPolynomial (orderThreeParameter d)
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 12 *
        orderSevenDualKernelPolynomial d x := by
  simp [orderSevenDualKernelPolynomial,
    orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem dualKernelPolynomial_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1) :
    (Internal.dualKernelPolynomial (orderThreeParameter d)).comp
        (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 12) *
        Internal.dualKernelPolynomial d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, Internal.dualKernelPolynomial_eval,
    eval_mul, eval_C]
  exact dualKernel_orderThreeParameter d x hd

private theorem selectionPolynomial_factorization (d : ℚ) :
    Internal.selectionPolynomialData d =
      C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
        selectionCofactor d := by
  apply Polynomial.funext
  intro x
  simpa [Internal.selectionPolynomialData_eval,
    Internal.dualKernelPolynomial_eval, mul_assoc] using
      orderSevenSelectionPolynomial_eval_factorization d x

/-- The selection cofactor is preserved up to scale by the order-three parameter symmetry. -/
theorem selectionCofactor_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 135) * selectionCofactor d := by
  have hdual : Internal.dualKernelPolynomial d ≠ 0 := by
    have hdegree :
        (Internal.dualKernelPolynomial d).natDegree = 3 := by
      unfold Internal.dualKernelPolynomial
      compute_degree
      all_goals norm_num
    intro h
    rw [h] at hdegree
    norm_num at hdegree
  have hscale : (d - 1)⁻¹ ^ 12 ≠ 0 :=
    pow_ne_zero 12 (inv_ne_zero (sub_ne_zero.mpr hd))
  have hcommon :
      C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (C_ne_zero.mpr hscale)) hdual
  have hfactorTransformed :
      (Internal.selectionPolynomialData (orderThreeParameter d)).comp
          (orderThreeAffine d) =
        C (64 ^ 3 : ℚ) *
          (Internal.dualKernelPolynomial
            (orderThreeParameter d)).comp (orderThreeAffine d) *
          (selectionCofactor
            (orderThreeParameter d)).comp (orderThreeAffine d) := by
    have h := congrArg (Polynomial.compRingHom (orderThreeAffine d))
      (selectionPolynomial_factorization (orderThreeParameter d))
    simpa using h
  apply mul_left_cancel₀ hcommon
  calc
    (C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d) *
        (selectionCofactor (orderThreeParameter d)).comp
          (orderThreeAffine d) =
        (Internal.selectionPolynomialData
          (orderThreeParameter d)).comp (orderThreeAffine d) := by
      rw [hfactorTransformed,
        dualKernelPolynomial_orderThreeParameter d hd]
      ring
    _ = C ((d - 1)⁻¹ ^ 147) *
          Internal.selectionPolynomialData d :=
      selectionPolynomialData_orderThreeParameter d hd
    _ = (C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d) *
        (C ((d - 1)⁻¹ ^ 135) * selectionCofactor d) := by
      rw [selectionPolynomial_factorization,
        show 147 = 12 + 135 by norm_num, pow_add, map_mul]
      ring

/-- Coprimality with the first division cofactor at the transformed
parameter transports to coprimality with the second cofactor. -/
theorem isCoprime_selection_divisionCofactor1_of_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1)
    (hcop : IsCoprime
      (selectionCofactor (orderThreeParameter d))
      (divisionCofactor0 (orderThreeParameter d))) :
    IsCoprime (selectionCofactor d) (divisionCofactor1 d) := by
  have hmap := hcop.map (Polynomial.compRingHom (orderThreeAffine d))
  change IsCoprime
    ((selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d))
    ((divisionCofactor0 (orderThreeParameter d)).comp
      (orderThreeAffine d)) at hmap
  rw [selectionCofactor_orderThreeParameter_comp d hd,
    divisionCofactor0_orderThreeParameter_comp d hd] at hmap
  exact hmap.of_mul_left_right.symm.of_mul_left_right.symm

/-- Coprimality with the second division cofactor at the transformed
parameter transports to coprimality with the third cofactor. -/
theorem isCoprime_selection_divisionCofactor2_of_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1)
    (hcop : IsCoprime
      (selectionCofactor (orderThreeParameter d))
      (divisionCofactor1 (orderThreeParameter d))) :
    IsCoprime (selectionCofactor d) (divisionCofactor2 d) := by
  have hmap := hcop.map (Polynomial.compRingHom (orderThreeAffine d))
  change IsCoprime
    ((selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d))
    ((divisionCofactor1 (orderThreeParameter d)).comp
      (orderThreeAffine d)) at hmap
  rw [selectionCofactor_orderThreeParameter_comp d hd,
    divisionCofactor1_orderThreeParameter_comp d hd] at hmap
  exact hmap.of_mul_left_right.symm.of_mul_left_right.symm

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantSymmetry. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The order-three orbit of the order-seven resultant

The generic pseudo-remainder certificate computes the bounded resultant
against the first division cofactor. The order-three parameter symmetry
transports coprimality twice around its orbit, producing the other two
bounded resultants required by the stable obstruction consumer.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant
open Internal.ResultantCertificate

/-- The seven checked recurrences make all three bounded resultants nonzero at
every nonsingular order-seven Kubert parameter. -/
theorem bounded_resultants_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 ∧
      resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0 ∧
      resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0 := by
  let t := orderThreeParameter d
  let t2 := orderThreeParameter t
  have ht0 : t ≠ 0 := orderThreeParameter_ne_zero d hd1
  have ht1 : t ≠ 1 := orderThreeParameter_ne_one d hd0
  have htcubic : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0 := by
    rw [show t = orderThreeParameter d by rfl,
      discriminantFactor_orderThreeParameter d hd1]
    exact mul_ne_zero
      (pow_ne_zero 3 (inv_ne_zero (sub_ne_zero.mpr hd1)))
      hcubic
  have ht20 : t2 ≠ 0 := orderThreeParameter_ne_zero t ht1
  have ht21 : t2 ≠ 1 := orderThreeParameter_ne_one t ht0
  have ht2cubic : t2 ^ 3 - 8 * t2 ^ 2 + 5 * t2 + 1 ≠ 0 := by
    rw [show t2 = orderThreeParameter t by rfl,
      discriminantFactor_orderThreeParameter t ht1]
    exact mul_ne_zero
      (pow_ne_zero 3 (inv_ne_zero (sub_ne_zero.mpr ht1)))
      htcubic
  have hres0 :
      resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      d hd0 hd1 hcubic
  have hres0t :
      resultant (selectionCofactor t) (divisionCofactor0 t) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      t ht0 ht1 htcubic
  have hcop0t : IsCoprime
      (selectionCofactor t) (divisionCofactor0 t) :=
    isCoprime_of_bounded_resultant_ne_zero
      (selectionCofactor_degree t) (divisionCofactor0_natDegree t)
      (divisionCofactor0_monic t) hres0t
  have hcop1 : IsCoprime
      (selectionCofactor d) (divisionCofactor1 d) :=
    isCoprime_selection_divisionCofactor1_of_orderThreeParameter
      d hd1 hcop0t
  have hres1 :
      resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0 :=
    bounded_resultant_ne_zero_of_isCoprime
      (selectionCofactor_degree d) (divisionCofactor1_natDegree d)
      (divisionCofactor1_monic d) hcop1
  have hres0t2 :
      resultant (selectionCofactor t2) (divisionCofactor0 t2) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      t2 ht20 ht21 ht2cubic
  have hcop0t2 : IsCoprime
      (selectionCofactor t2) (divisionCofactor0 t2) :=
    isCoprime_of_bounded_resultant_ne_zero
      (selectionCofactor_degree t2) (divisionCofactor0_natDegree t2)
      (divisionCofactor0_monic t2) hres0t2
  have hcop1t : IsCoprime
      (selectionCofactor t) (divisionCofactor1 t) :=
    isCoprime_selection_divisionCofactor1_of_orderThreeParameter
      t ht1 hcop0t2
  have hcop2 : IsCoprime
      (selectionCofactor d) (divisionCofactor2 d) :=
    isCoprime_selection_divisionCofactor2_of_orderThreeParameter
      d hd1 hcop1t
  have hres2 :
      resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0 :=
    bounded_resultant_ne_zero_of_isCoprime
      (selectionCofactor_degree d) (divisionCofactor2_natDegree d)
      (divisionCofactor2_monic d) hcop2
  exact ⟨hres0, hres1, hres2⟩

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

theorem solution (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 ∧
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0 ∧
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0 := MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.bounded_resultants_ne_zero d hd0 hd1 hcubic
#print axioms solution
