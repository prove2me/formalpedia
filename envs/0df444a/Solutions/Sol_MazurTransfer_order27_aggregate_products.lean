-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_products
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:12.183318+00:00
-- url     : https://prove2.me/submissions/b0ad2251-409a-44a2-b110-1c984713b28a

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_certificate_zlTD_s0_zlTNSq_s0
import Theorems.Thm_MazurTransfer_order27_certificate_zlTNSq_s1_zlTNSq_s2
import Theorems.Thm_MazurTransfer_order27_certificate_zlTNCb_s0_zlTNSqTD_s0
import Theorems.Thm_MazurTransfer_order27_certificate_zlTDSq_s0_zlTDCb_s0
import Theorems.Thm_MazurTransfer_order27_certificate_zlTDCb_s1
import Theorems.Thm_MazurTransfer_order27_certificate_zlTNTD_s0_zlTNTD_s1
import Theorems.Thm_MazurTransfer_order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1
import Theorems.Thm_MazurTransfer_order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesC. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Kernel-cubic-side staged products

Staged products of the kernel-cubic-side certificate chain: powers of the
third-leg numerator and denominator reduced against the kernel cubic.
-/



section

namespace MazurTorsion.Kubert

lemma zlTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlE0 f Z) * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z := by
  exact MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0.1 hM


lemma zlTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    zlE0 f Z * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z := by
  linear_combination
    (zlTD_s0 hM)

lemma zlTNSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      (zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z) := by
  exact MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0.2 hM


lemma zlTNSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2.1 hM


lemma zlTNSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2.2 hM


lemma zlTNSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) =
      (((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) +
        ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z))) +
        (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z)) +
        (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z)) := by
  linear_combination
    ((zlTNSq_s0 hM) + (zlTNSq_s1 hM)) + (zlTNSq_s2 hM)

lemma zlTNCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f := by
  exact MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0.1 hM


lemma zlTNCb_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f := by
  linear_combination
    (zlTNCb_s0 hM)

lemma zlTNSqTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)) := by
  exact MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0.2 hM


lemma zlTNSqTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)) := by
  linear_combination
    (zlTNSqTD_s0 hM)

end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.DenominatorPowers. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Third-leg denominator powers

The square and cube certificates for the third-leg denominator, reduced against the
kernel cubic.
-/



section

namespace MazurTorsion.Kubert

lemma zlTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0.1 hM


lemma zlTDSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f
      Z) =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z := by
  linear_combination
    (zlTDSq_s0 hM)

lemma zlTDCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0.2 hM


lemma zlTDCb_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z + zlTDSqP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTDCbP1c0 f Z + zlTDCbP1c1 f Z) + (zlTDCbP1c2 f Z + zlTDCbP1c3 f Z)) +
        (zlTDCbP1c4 f Z + zlTDCbP1c5 f Z) := by
  exact MazurTransfer.order27_certificate_zlTDCb_s1 hM


lemma zlTDCb_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4 f Z) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      (((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) +
        ((zlTDCbP0c4 f Z + zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) +
        ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) + zlTDCbP1c5 f Z) := by
  linear_combination
    (zlTDCb_s0 hM) + (zlTDCb_s1 hM)

end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.NumeratorDenominator. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Third-leg numerator-denominator product

The staged product of the third-leg numerator and denominator, reduced against the
kernel cubic.
-/



section

namespace MazurTorsion.Kubert

lemma zlTNTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1.1 hM


lemma zlTNTD_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z := by
  exact MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1.2 hM


lemma zlTNTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      (((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) +
        ((zlTNTDP0c4 f Z + zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) +
        (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) := by
  linear_combination
    (zlTNTD_s0 hM) + (zlTNTD_s1 hM)

end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.NumeratorDenominatorSquare. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Third-leg numerator times the denominator square

The staged product certificate for the third-leg numerator and the square of its
denominator.
-/



section

namespace MazurTorsion.Kubert

lemma zlTNTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        zlTNTDSqP0c4 f Z := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1.1 hM


lemma zlTNTDSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z + zlTNTDP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z) + (zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z)) +
        (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z) := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1.2 hM


lemma zlTNTDSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3.1 hM


lemma zlTNTDSq_s3 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z) := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3.2 hM


lemma zlTNTDSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + ((zlTNTDP0c4 f Z +
      zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) + (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
        (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
        ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z))))
        + (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z))
        + (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z)) := by
  linear_combination
    ((zlTNTDSq_s0 hM) + (zlTNTDSq_s1 hM)) + ((zlTNTDSq_s2 hM) + (zlTNTDSq_s3 hM))

end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
zlE0 f Z * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) =
      (((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) +
        ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z))) +
        (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z)) +
        (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      (((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) +
        ((zlTNTDP0c4 f Z + zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) +
        (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + ((zlTNTDP0c4 f Z +
      zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) + (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
        (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
        ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z))))
        + (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z))
        + (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f
      Z) =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4 f Z) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      (((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) +
        ((zlTDCbP0c4 f Z + zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) +
        ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) + zlTDCbP1c5 f Z))
 := by
  exact ⟨MazurTorsion.Kubert.zlTD_val, ⟨MazurTorsion.Kubert.zlTNSq_val, ⟨MazurTorsion.Kubert.zlTNCb_val, ⟨MazurTorsion.Kubert.zlTNSqTD_val, ⟨MazurTorsion.Kubert.zlTNTD_val, ⟨MazurTorsion.Kubert.zlTNTDSq_val, ⟨MazurTorsion.Kubert.zlTDSq_val, MazurTorsion.Kubert.zlTDCb_val⟩⟩⟩⟩⟩⟩⟩

#print axioms solution

end
