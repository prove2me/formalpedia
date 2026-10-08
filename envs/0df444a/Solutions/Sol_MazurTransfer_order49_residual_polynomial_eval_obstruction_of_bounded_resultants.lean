-- Prove2me | solution 1 for MazurTransfer.order49_residual_polynomial_eval_obstruction_of_bounded_resultants
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:01:27.570986+00:00
-- url     : https://prove2.me/submissions/effc46be-4a04-4900-bacc-54e12d839f56

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
import Theorems.Thm_MazurTransfer_order49_quotient_prePsi_seven_polynomial_factorization
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_0
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_1
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
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_2
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
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_3
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_30
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_31
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_32
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_33
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_34
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_35
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_36
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_4
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_5
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_6
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_7
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_8
import Theorems.Thm_MazurTransfer_order49_selection_evaluation_9
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero map_zero
theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt0 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 0 := by
  apply MazurTransfer.order49_selection_evaluation_0 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt1 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 1 := by
  apply MazurTransfer.order49_selection_evaluation_1 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt10 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 10 := by
  apply MazurTransfer.order49_selection_evaluation_10 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt11 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 11 := by
  apply MazurTransfer.order49_selection_evaluation_11 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt12 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 12 := by
  apply MazurTransfer.order49_selection_evaluation_12 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt13 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 13 := by
  apply MazurTransfer.order49_selection_evaluation_13 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt14 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 14 := by
  apply MazurTransfer.order49_selection_evaluation_14 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt15 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 15 := by
  apply MazurTransfer.order49_selection_evaluation_15 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt16 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 16 := by
  apply MazurTransfer.order49_selection_evaluation_16 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt17 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 17 := by
  apply MazurTransfer.order49_selection_evaluation_17 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt18 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 18 := by
  apply MazurTransfer.order49_selection_evaluation_18 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt19 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 19 := by
  apply MazurTransfer.order49_selection_evaluation_19 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt2 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 2 := by
  apply MazurTransfer.order49_selection_evaluation_2 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt20 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 20 := by
  apply MazurTransfer.order49_selection_evaluation_20 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt21 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 21 := by
  apply MazurTransfer.order49_selection_evaluation_21 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt22 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 22 := by
  apply MazurTransfer.order49_selection_evaluation_22 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt23 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 23 := by
  apply MazurTransfer.order49_selection_evaluation_23 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt24 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 24 := by
  apply MazurTransfer.order49_selection_evaluation_24 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt25 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 25 := by
  apply MazurTransfer.order49_selection_evaluation_25 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt26 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 26 := by
  apply MazurTransfer.order49_selection_evaluation_26 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt27 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 27 := by
  apply MazurTransfer.order49_selection_evaluation_27 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt28 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 28 := by
  apply MazurTransfer.order49_selection_evaluation_28 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt29 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 29 := by
  apply MazurTransfer.order49_selection_evaluation_29 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt3 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 3 := by
  apply MazurTransfer.order49_selection_evaluation_3 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt30 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 30 := by
  apply MazurTransfer.order49_selection_evaluation_30 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt31 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 31 := by
  apply MazurTransfer.order49_selection_evaluation_31 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt32 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 32 := by
  apply MazurTransfer.order49_selection_evaluation_32 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt33 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 33 := by
  apply MazurTransfer.order49_selection_evaluation_33 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt34 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 34 := by
  apply MazurTransfer.order49_selection_evaluation_34 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt35 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 35 := by
  apply MazurTransfer.order49_selection_evaluation_35 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt36 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 36 := by
  apply MazurTransfer.order49_selection_evaluation_36 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt4 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 4 := by
  apply MazurTransfer.order49_selection_evaluation_4 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt5 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 5 := by
  apply MazurTransfer.order49_selection_evaluation_5 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt6 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 6 := by
  apply MazurTransfer.order49_selection_evaluation_6 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt7 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 7 := by
  apply MazurTransfer.order49_selection_evaluation_7 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt8 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 8 := by
  apply MazurTransfer.order49_selection_evaluation_8 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt9 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 9 := by
  apply MazurTransfer.order49_selection_evaluation_9 <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.quotient_prePsi_seven_polynomial_factorization (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d := by
  apply MazurTransfer.order49_quotient_prePsi_seven_polynomial_factorization <;> assumption
namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
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
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.PolynomialResultant.resultant_ne_zero_of_bounded_resultant_ne_zero hf hg hmonic hres
  by_contra hnot
  apply hraw
  exact resultant_eq_zero_iff.mpr ⟨Or.inr hmonic.ne_zero, hnot⟩



/-- A nonzero bounded resultant against a monic polynomial rules out a
common root after specialization. -/
theorem eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) (x : K) :
    f.eval x ≠ 0 ∨ g.eval x ≠ 0 := by
  have hcop : IsCoprime f g :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.PolynomialResultant.isCoprime_of_bounded_resultant_ne_zero hf hg hmonic hres
  simpa [aeval_def] using aeval_ne_zero_of_isCoprime hcop x

end MazurTorsion.PolynomialResultant

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal



@[simp] theorem dualKernelPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d).eval x = MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial, MazurTorsion.Kubert.orderSevenDualKernelPolynomial]

end Internal

lemma selectionCofactorData_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData.natDegree ≤ 33 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData
  compute_degree





lemma selectionCofactor_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).natDegree ≤ 33 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData_degree

lemma divisionCofactorData0_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0
  compute_degree

lemma divisionCofactorData1_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1
  compute_degree

lemma divisionCofactorData2_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2
  compute_degree

lemma divisionCofactor0_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0_degree

lemma divisionCofactor1_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1_degree

lemma divisionCofactor2_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2_degree



















@[simp] theorem divisionCofactor0_coeff_seven (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).coeff 7 = 1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7Chunk0]

@[simp] theorem divisionCofactor1_coeff_seven (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).coeff 7 = 1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient7Chunk0]

@[simp] theorem divisionCofactor2_coeff_seven (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).coeff 7 = 1 := by
  simp [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient7Chunk0]

theorem divisionCofactor0_natDegree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_degree d) (by simp)

theorem divisionCofactor1_natDegree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_degree d) (by simp)

theorem divisionCofactor2_natDegree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).natDegree = 7 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_degree d) (by simp)

theorem divisionCofactor0_monic (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_coeff_seven d)

theorem divisionCofactor1_monic (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_coeff_seven d)

theorem divisionCofactor2_monic (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 7
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_coeff_seven d)

namespace Internal

/-- Internal datum. -/ noncomputable def completedCubicPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

/-- Internal datum. -/ noncomputable def completedTangentPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- Internal datum. -/ noncomputable def tateAlphaPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  (C 12 * X + C W.b₂) * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W -
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial W ^ 2

/-- Internal datum. -/ noncomputable def tateGammaPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W ^ 2 -
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial W * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial W

/-- Internal datum. -/ noncomputable def tateParameterNumeratorPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  -MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial W ^ 3

/-- Internal datum. -/ noncomputable def tateParameterDenominatorPolynomial
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 16 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateGammaPolynomial W * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W ^ 2

/-- Internal datum. -/ noncomputable def parameterCubicPolynomial (A B : ℚ[X]) : ℚ[X] :=
  A ^ 3 - C 8 * A ^ 2 * B + C 5 * A * B ^ 2 + B ^ 3

/-- Internal datum. -/ noncomputable def parameterHauptmodulNumeratorPolynomial
    (A B : ℚ[X]) : ℚ[X] :=
  C 49 * A * (A - B) * B

/-- Internal datum. -/ noncomputable def selectionPolynomialData (d : ℚ) : ℚ[X] :=
  let W := MazurTorsion.Kubert.orderSevenQuotient d
  let A := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial W
  let B := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial W
  C (d * (d - 1)) * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial A B -
    C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial A B

@[simp] theorem selectionPolynomialData_eval (d x : ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData d).eval x = MazurTorsion.Kubert.orderSevenSelectionPolynomial d x := by
  simp [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateGammaPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial,
    MazurTorsion.Kubert.orderSevenSelectionPolynomial,
    MazurTorsion.Kubert.pointTateParameterUnivariateNumerator,
    MazurTorsion.Kubert.pointTateParameterUnivariateDenominator,
    MazurTorsion.Kubert.pointTateAlphaUnivariateCleared,
    MazurTorsion.Kubert.pointTateGammaUnivariateCleared,
    MazurTorsion.Kubert.pointTateCompletedTangentNumerator,
    MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator,
    MazurTorsion.Kubert.orderSevenParameterCubic,
    MazurTorsion.Doubling.completedCubic]

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
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W).natDegree ≤ 3 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial
  compute_degree

private lemma completedTangentPolynomial_degree (W : WeierstrassCurve ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial W).natDegree ≤ 2 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial
  compute_degree

private lemma tateAlphaPolynomial_degree (W : WeierstrassCurve ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial W).natDegree ≤ 4 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial
  have ht2 : (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial W ^ 2).natDegree ≤ 4 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 2)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial_degree W)
  apply le_trans (natDegree_sub_le _ _)
  apply max_le
  · exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (by compute_degree)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial_degree W)
  · exact ht2

private lemma tateGammaPolynomial_degree (W : WeierstrassCurve ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateGammaPolynomial W).natDegree ≤ 6 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateGammaPolynomial
  have hd2 : (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W ^ 2).natDegree ≤ 6 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 2)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial_degree W)
  apply le_trans (natDegree_sub_le _ _)
  apply max_le
  · exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (by compute_degree) hd2
  · exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial_degree W)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedTangentPolynomial_degree W)

private lemma tateParameterNumeratorPolynomial_degree
    (W : WeierstrassCurve ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial W).natDegree ≤ 12 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial
  simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 3)
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateAlphaPolynomial_degree W)

private lemma tateParameterDenominatorPolynomial_degree
    (W : WeierstrassCurve ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial W).natDegree ≤ 12 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial
  have hd2 : (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial W ^ 2).natDegree ≤ 6 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 2)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.completedCubicPolynomial_degree W)
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (by compute_degree)
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateGammaPolynomial_degree W))
    hd2

private lemma parameterHauptmodulNumeratorPolynomial_degree
    {A B : ℚ[X]} (hA : A.natDegree ≤ 12) (hB : B.natDegree ≤ 12) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial A B).natDegree ≤ 36 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial
  have hc : (C (49 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hab : (A - B).natDegree ≤ 12 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_sub_le_of_le hA hB
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le hc hA) hab) hB

private lemma parameterCubicPolynomial_degree
    {A B : ℚ[X]} (hA : A.natDegree ≤ 12) (hB : B.natDegree ≤ 12) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial A B).natDegree ≤ 36 := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial
  have hA3 : (A ^ 3).natDegree ≤ 36 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 3) hA
  have hA2 : (A ^ 2).natDegree ≤ 24 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 2) hA
  have hB2 : (B ^ 2).natDegree ≤ 24 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 2) hB
  have hc8 : (C (8 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hc5 : (C (5 : ℚ)).natDegree ≤ 0 := by compute_degree
  have hA2B : (C 8 * A ^ 2 * B).natDegree ≤ 36 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le hc8 hA2) hB
  have hAB2 : (C 5 * A * B ^ 2).natDegree ≤ 36 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le hc5 hA) hB2
  have hB3 : (B ^ 3).natDegree ≤ 36 := by
    simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_pow_le_of_le (n := 3) hB
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_add_le_of_le
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_add_le_of_le (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_sub_le_of_le hA3 hA2B) hAB2) hB3

lemma selectionPolynomialData_degree (d : ℚ) :
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData d).natDegree ≤ 36 := by
  let W := MazurTorsion.Kubert.orderSevenQuotient d
  let A := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial W
  let B := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial W
  change (C (d * (d - 1)) * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial A B -
    C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial A B).natDegree ≤ 36
  have hA : A.natDegree ≤ 12 := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterNumeratorPolynomial_degree W
  have hB : B.natDegree ≤ 12 := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.tateParameterDenominatorPolynomial_degree W
  have hc0 : (C (d * (d - 1))).natDegree ≤ 0 := by compute_degree
  have hc1 : (C (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)).natDegree ≤ 0 := by
    compute_degree
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_sub_le_of_le
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le hc0
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterHauptmodulNumeratorPolynomial_degree hA hB))
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.natDegree_mul_le_of_le hc1
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.parameterCubicPolynomial_degree hA hB))








end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
namespace MazurTorsion.Kubert

private noncomputable def sevenCyclotomicCubic : Polynomial ℤ :=
  Polynomial.X ^ 3 + Polynomial.X ^ 2 -
    Polynomial.C 2 * Polynomial.X - Polynomial.C 1

private lemma sevenCyclotomicCubic_monic :
    Polynomial.Monic MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic := by
  unfold MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic
  monicity!

private lemma sevenCyclotomicCubic_ne_zero (z : ℚ) :
    z ^ 3 + z ^ 2 - 2 * z - 1 ≠ 0 := by
  intro hz
  have hroot : Polynomial.aeval z MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic]
    linear_combination hz
  obtain ⟨m, hzm, hdiv⟩ :=
    exists_integer_of_is_root_of_monic MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic_monic hroot
  have hunit : IsUnit m := by
    rw [isUnit_iff_dvd_one]
    simpa [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic] using hdiv
  rcases Int.isUnit_iff.mp hunit with rfl | rfl
  · norm_num [hzm] at hz
  · norm_num [hzm] at hz



private def orderSevenDualKernelDiscriminantFactor (d : ℚ) : ℚ :=
  d ^ 3 - 8 * d ^ 2 + 5 * d + 1

private def orderSevenDualKernelCyclotomicNumerator (d x : ℚ) : ℚ :=
  9 * d ^ 9 - 13 * d ^ 8 - 230 * d ^ 7 + 742 * d ^ 6 - 966 * d ^ 5 +
    525 * d ^ 4 + 14 * d ^ 3 - 80 * d ^ 2 + 9 * d - 5 +
    7 * (5 * d ^ 5 - 20 * d ^ 4 + 25 * d ^ 3 - 7 * d ^ 2 + 2 * d - 2) * x +
    7 * (3 * d - 1) * x ^ 2

private def orderSevenDualKernelCyclotomicParameter (d x : ℚ) : ℚ :=
  MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicNumerator d x /
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor d ^ 3

private def orderSevenDualKernelCyclotomicCofactor (d x : ℚ) : ℚ :=
  49 * (3 * d - 1) ^ 3 * x ^ 3 +
    49 * (3 * d - 1) ^ 2 *
      (9 * d ^ 5 - 43 * d ^ 4 + 52 * d ^ 3 - 6 * d ^ 2 - 3 * d - 4) * x ^ 2 +
    49 * (3 * d - 1) *
      (24 * d ^ 10 - 205 * d ^ 9 + 621 * d ^ 8 - 835 * d ^ 7 +
        206 * d ^ 6 + 463 * d ^ 5 - 185 * d ^ 4 - 128 * d ^ 3 +
        34 * d ^ 2 + 7 * d + 5) * x +
    7 * (113 * d ^ 15 - 964 * d ^ 14 + 959 * d ^ 13 + 12621 * d ^ 12 -
      49413 * d ^ 11 + 81116 * d ^ 10 - 68761 * d ^ 9 + 19534 * d ^ 8 +
      16885 * d ^ 7 - 12397 * d ^ 6 - 2716 * d ^ 5 + 2954 * d ^ 4 +
      385 * d ^ 3 - 266 * d ^ 2 - 24 * d - 13)

private theorem orderSevenDualKernelCyclotomic_identity (d x : ℚ) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicNumerator d x ^ 3 +
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicNumerator d x ^ 2 *
          MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor d ^ 3 -
        2 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicNumerator d x *
          MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor d ^ 6 -
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor d ^ 9 =
      MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x *
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicCofactor d x := by
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicNumerator,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor, MazurTorsion.Kubert.orderSevenDualKernelPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicCofactor]
  ring

private theorem orderSevenDualKernelCyclotomicParameter_isRoot
    {d x : ℚ} (hK : MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelDiscriminantFactor d ≠ 0)
    (hdual : MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x = 0) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter d x ^ 3 +
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter d x ^ 2 -
        2 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter d x - 1 = 0 := by
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter]
  field_simp [hK]
  linear_combination
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomic_identity d x +
      MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicCofactor d x * hdual

/-- On a nonsingular order-seven Tate curve, the dual-kernel cubic has no
rational root. -/
theorem orderSevenDualKernelPolynomial_ne_zero
    (d x : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x ≠ 0 := by
  intro hdual
  apply MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.sevenCyclotomicCubic_ne_zero
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter d x)
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelCyclotomicParameter_isRoot
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d).2.2 hdual

end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

private theorem selection_eval_fin (d : ℚ) (i : Fin 37) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d (i : ℚ) := by
  fin_cases i
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt0 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt1 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt2 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt3 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt4 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt5 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt6 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt7 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt8 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt9 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt10 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt11 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt12 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt13 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt14 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt15 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt16 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt17 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt18 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt19 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt20 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt21 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt22 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt23 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt24 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt25 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt26 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt27 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt28 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt29 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt30 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt31 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt32 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt33 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt34 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt35 d
  · simpa using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt36 d

private lemma dualKernelPolynomial_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d).natDegree ≤ 3 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial
  compute_degree

private lemma selection_factor_product_degree (d : ℚ) :
    (C (64 ^ 3 : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).natDegree ≤ 36 := by
  have h0 : (C (64 ^ 3 : ℚ) *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d).natDegree ≤ 3 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add (by compute_degree) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.dualKernelPolynomial_degree d))
  exact le_trans natDegree_mul_le
    (Nat.add_le_add h0 (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor_degree d))

private theorem selection_polynomial_factorization (d : ℚ) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData d =
      C (64 ^ 3 : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 37 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    simpa [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate] using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData_degree d
    have hr := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_factor_product_degree d
    omega

/-- Pointwise factorization of the backtracking selection polynomial into the
dual-kernel cubic and its degree-33 cofactor. -/
theorem orderSevenSelectionPolynomial_eval_factorization (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d x =
      64 ^ 3 * MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x *
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval x := by
  have h := congrArg (Polynomial.eval x)
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_polynomial_factorization d)
  simpa [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionPolynomialData_eval,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial_eval, mul_assoc] using h









/-- Pointwise factorization of the quotient seventh division polynomial into
the dual-kernel cubic and the three canonical degree-seven cofactors. -/
theorem orderSevenQuotient_preΨ_seven_eval_factorization (d x : ℚ) :
    ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval x =
      MazurTorsion.Kubert.orderSevenDualKernelPolynomial d x *
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).eval x := by
  have h := congrArg (Polynomial.eval x)
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.quotient_prePsi_seven_polynomial_factorization d)
  simpa [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial_eval, mul_assoc] using h

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant
open _root_.Polynomial

/-- Nonzero bounded resultants against all three quotient cofactors rule out
their simultaneous vanishing with the selection cofactor at every rational
abscissa. -/
theorem cofactor_eval_obstruction_of_bounded_resultants
    (d : ℚ)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval z ≠ 0 ∨
      (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).eval z ≠ 0 := by
  by_cases hselection : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval z = 0
  · right
    simp only [eval_mul]
    have h0 : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).eval z ≠ 0 :=
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.PolynomialResultant.eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_natDegree d)
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_monic d) hres0 z).resolve_left
            (fun hne ↦ hne hselection)
    have h1 : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).eval z ≠ 0 :=
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.PolynomialResultant.eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_natDegree d)
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_monic d) hres1 z).resolve_left
            (fun hne ↦ hne hselection)
    have h2 : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).eval z ≠ 0 :=
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.PolynomialResultant.eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor_degree d) (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_natDegree d)
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_monic d) hres2 z).resolve_left
            (fun hne ↦ hne hselection)
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  · exact Or.inl hselection



/-- Nonzero bounded resultants lift through the certified factorizations to
show that the backtracking selection polynomial and quotient seventh division
polynomial cannot both vanish at a rational abscissa. -/
theorem polynomial_eval_obstruction_of_bounded_resultants
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d z ≠ 0 ∨
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval z ≠ 0 := by
  have hdual : MazurTorsion.Kubert.orderSevenDualKernelPolynomial d z ≠ 0 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenDualKernelPolynomial_ne_zero d z
  rcases MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.cofactor_eval_obstruction_of_bounded_resultants
      d hres0 hres1 hres2 z with hselection | hdivision
  · left
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.orderSevenSelectionPolynomial_eval_factorization]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hdual) hselection
  · right
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.orderSevenQuotient_preΨ_seven_eval_factorization]
    exact mul_ne_zero hdual hdivision

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

namespace MazurTorsion.Kubert

open OrderSevenBacktrackingCertificate





end MazurTorsion.Kubert

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

theorem solution (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d z ≠ 0 ∨
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval z ≠ 0 := by
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.polynomial_eval_obstruction_of_bounded_resultants d hres0 hres1 hres2 z
#print axioms solution
