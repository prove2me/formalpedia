-- Prove2me | solution 1 for MazurTransfer.order49_residual_cofactor_eval_obstruction_of_bounded_resultants
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:01:18.680059+00:00
-- url     : https://prove2.me/submissions/e67496dd-df66-4cbc-93f2-6103aec2d929

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Mathlib
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero map_zero
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





end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

namespace MazurTorsion.Kubert

open OrderSevenBacktrackingCertificate





end MazurTorsion.Kubert

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

theorem solution (d : ℚ)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval z ≠ 0 ∨
      (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).eval z ≠ 0 := by
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.cofactor_eval_obstruction_of_bounded_resultants d hres0 hres1 hres2 z
#print axioms solution
