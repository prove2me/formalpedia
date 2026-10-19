-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute.spectralStep_same_target_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/d4364f24-d17e-4d47-9976-cf0c20378b01

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute
open MetricCodes.Spherical.HigherHarmonicYoung
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute
theorem _root_.solution
    {r n : ℕ}
    (A B C D R : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hCD : C * D = D * C)
    (hRA : R * A - A * R = C)
    (hRB : R * B - B * R = D)
    (hRC : R * C = C * R)
    (hRD : R * D = D * R)
    (hcross : (x - y) • (C * B - B * C) = A * D - B * C) :
    (x • C - A * R) * (y • D - B * R) =
      (y • D - B * R) * (x • C - A * R) := by
  have hRA' : R * A = A * R + C := by
    rw [← hRA]
    noncomm_ring
  have hRB' : R * B = B * R + D := by
    rw [← hRB]
    noncomm_ring
  have hjacobi : C * B + A * D = D * A + B * C := by
    calc
      C * B + A * D =
          (R * A - A * R) * B + A * (R * B - B * R) := by
            rw [hRA, hRB]
      _ = R * (A * B) - (A * B) * R := by
            simp only [mul_sub, sub_mul, mul_assoc]
            module
      _ = R * (B * A) - (B * A) * R := by rw [hAB]
      _ = (R * B - B * R) * A + B * (R * A - A * R) := by
            simp only [mul_sub, sub_mul, mul_assoc]
            module
      _ = D * A + B * C := by rw [hRB, hRA]
  have hcbr :
      C * (B * R) - (B * R) * C = (C * B - B * C) * R := by
    calc
      C * (B * R) - (B * R) * C =
          (C * B) * R - B * (R * C) := by noncomm_ring
      _ = (C * B - B * C) * R := by
            rw [hRC]
            simp only [sub_mul, mul_assoc]
  have hard :
      (A * R) * D - D * (A * R) = (A * D - D * A) * R := by
    calc
      (A * R) * D - D * (A * R) =
          A * (R * D) - (D * A) * R := by noncomm_ring
      _ = (A * D - D * A) * R := by
            rw [hRD]
            simp only [sub_mul, mul_assoc]
  have hroots :
      (A * R) * (B * R) - (B * R) * (A * R) =
        (A * D - B * C) * R := by
    calc
      (A * R) * (B * R) - (B * R) * (A * R) =
          (A * (R * B)) * R - (B * (R * A)) * R := by
            noncomm_ring
      _ = (A * (B * R + D)) * R -
            (B * (A * R + C)) * R := by rw [hRB', hRA']
      _ = ((A * B - B * A) * R + (A * D - B * C)) * R := by
            simp only [sub_mul, mul_add, add_mul, mul_assoc]
            module
      _ = (A * D - B * C) * R := by rw [hAB]; simp
  apply sub_eq_zero.mp
  calc
    (x • C - A * R) * (y • D - B * R) -
        (y • D - B * R) * (x • C - A * R) =
      (x * y) • (C * D - D * C) -
        x • (C * (B * R) - (B * R) * C) -
        y • ((A * R) * D - D * (A * R)) +
        ((A * R) * (B * R) - (B * R) * (A * R)) := by
          simp only [mul_sub, sub_mul, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm, smul_smul, smul_sub]
          module
    _ = -(x • ((C * B - B * C) * R)) -
          y • ((A * D - D * A) * R) +
          (A * D - B * C) * R := by
            rw [hCD, sub_self, smul_zero, zero_sub,
              hcbr, hard, hroots]
    _ = (-((x - y) • (C * B - B * C)) +
          (A * D - B * C)) * R := by
            have hrel : A * D - D * A = -(C * B - B * C) := by
              calc
                A * D - D * A =
                    (C * B + A * D) - (D * A + B * C) -
                      (C * B - B * C) := by module
                _ = -(C * B - B * C) := by rw [hjacobi]; module
            rw [hrel]
            apply LinearMap.ext
            intro p
            simp only [LinearMap.add_apply, LinearMap.sub_apply,
              LinearMap.neg_apply, LinearMap.smul_apply,
              Module.End.mul_apply]
            module
    _ = 0 := by rw [hcross]; simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute
