-- Prove2me | solution 1 for OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:36:42.238204+00:00
-- url     : https://prove2.me/submissions/07b3fb86-1312-47b0-a368-e27a109a5b80

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/Compression.lean:L67-L86
-- (upload_full_project.md Phase 4): solution for node OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

-- ---- from OAI.RepresentationTheory.SpinAngle.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
open scoped BigOperators
namespace SpinAngle.Analytic

variable {A : Type*} [contextInstance35_21 : CStarAlgebra A] [contextInstance35_38 : PartialOrder A] [contextInstance35_55 : StarOrderedRing A]
  [contextInstance36_2 : NonnegSpectrumClass ℝ A]

lemma norm_mul_projection_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (a p : A) (hp : IsStarProjection p) :
    ‖a * p‖ ^ 2 = ‖a * p * star a‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star, star_mul, hp.isSelfAdjoint.star_eq]
  congr 1
  calc
    a * p * (p * star a) = a * (p * p) * star a := by simp only [mul_assoc]
    _ = a * p * star a := by rw [hp.isIdempotentElem.eq]

lemma norm_mul_projection_sq_le_sum {ι : Type*} [Fintype ι]
    (a p : A) (hp : IsStarProjection p) (w : ι → ℝ) (r : ι → A)
    (hw : ∀ i, 0 ≤ w i) (hdom : p ≤ ∑ i, w i • (r i * star (r i))) :
    ‖a * p‖ ^ 2 ≤ ∑ i, w i * ‖a * r i‖ ^ 2 := by
  rw [norm_mul_projection_sq a p hp]
  have hcomp := star_right_conjugate_le_conjugate hdom a
  have hpos : 0 ≤ a * p * star a :=
    star_right_conjugate_nonneg hp.nonneg a
  calc
    ‖a * p * star a‖ ≤ ‖a * (∑ i, w i • (r i * star (r i))) * star a‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hcomp hpos
    _ = ‖∑ i, w i • ((a * r i) * star (a * r i))‖ := by
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
        star_mul, mul_assoc]
    _ ≤ ∑ i, ‖w i • ((a * r i) * star (a * r i))‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖a * r i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_of_nonneg (hw i), CStarRing.norm_self_mul_star, sq]

end SpinAngle.Analytic

end
end

end OAI

-- ---- platform node ----
open OAI OAI.SpinAngle OAI.SpinAngle.Analytic
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum := @_root_.OAI.SpinAngle.Analytic.norm_mul_projection_sq_le_sum
