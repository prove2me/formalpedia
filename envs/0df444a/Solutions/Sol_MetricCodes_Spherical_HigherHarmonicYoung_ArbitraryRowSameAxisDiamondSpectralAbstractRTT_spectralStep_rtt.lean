-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT.spectralStep_rtt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/9ed2b86a-8ad1-4f9a-bc04-20d77c589f39

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
open MetricCodes.Spherical.HigherHarmonicYoung
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
theorem _root_.solution
    {r n : ℕ}
    (A B C D E F S T : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hSB : S * B - B * S = D)
    (hTA : T * A - A * T = E)
    (hTB : T * B - B * T = F)
    (hSF : S * F = F * S)
    (hTC : T * C = C * T)
    (hTD : T * D = D * T)
    (hST : S * T = T * S)
    (hcross : (x - y) • (C * F - F * C) = E * D - F * C)
    (hCB : (x - y) • (C * B - B * C) = A * D - B * C)
    (hAF : (x - y) • (A * F - F * A) = E * B - F * A)
    (hEB : (x - y) • (E * B - B * E) = A * F - B * E) :
    (x - y) •
        ((x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S)) =
      (x • E - A * T) * (y • D - B * S) -
        (y • F - B * T) * (x • C - A * S) := by
  have hSB' : S * B = B * S + D := by
    rw [← hSB]
    noncomm_ring
  have hTA' : T * A = A * T + E := by
    rw [← hTA]
    noncomm_ring
  have hTB' : T * B = B * T + F := by
    rw [← hTB]
    noncomm_ring
  have hCBT : C * (B * T) - (B * T) * C =
      (C * B - B * C) * T := by
    calc
      C * (B * T) - (B * T) * C =
          (C * B) * T - B * (T * C) := by noncomm_ring
      _ = (C * B - B * C) * T := by
            rw [hTC]
            simp only [mul_assoc, sub_mul]
  have hASF : (A * S) * F - F * (A * S) =
      (A * F - F * A) * S := by
    calc
      (A * S) * F - F * (A * S) =
          A * (S * F) - (F * A) * S := by noncomm_ring
      _ = (A * F - F * A) * S := by
            rw [hSF]
            simp only [mul_assoc, sub_mul]
  have hASBT :
      (A * S) * (B * T) - (B * T) * (A * S) =
        (A * D) * T - (B * E) * S := by
    calc
      (A * S) * (B * T) - (B * T) * (A * S) =
          (A * (S * B)) * T - (B * (T * A)) * S := by
            noncomm_ring
      _ = (A * (B * S + D)) * T -
            (B * (A * T + E)) * S := by rw [hSB', hTA']
      _ = (A * B) * (S * T) - (B * A) * (T * S) +
            (A * D) * T - (B * E) * S := by
              simp only [mul_assoc, mul_add, add_mul]
              module
      _ = (A * D) * T - (B * E) * S := by
            rw [hAB, hST]
            module
  have hATBS :
      (A * T) * (B * S) - (B * T) * (A * S) =
        (A * F - B * E) * S := by
    calc
      (A * T) * (B * S) - (B * T) * (A * S) =
          (A * (T * B)) * S - (B * (T * A)) * S := by
            noncomm_ring
      _ = (A * (B * T + F)) * S -
            (B * (A * T + E)) * S := by rw [hTB', hTA']
      _ = ((A * B - B * A) * T + A * F - B * E) * S := by
            simp only [mul_assoc, mul_add, add_mul, sub_mul]
            module
      _ = (A * F - B * E) * S := by simp [hAB]
  have hATD : (A * T) * D = (A * D) * T := by
    calc
      (A * T) * D = A * (T * D) := by noncomm_ring
      _ = (A * D) * T := by rw [hTD]; noncomm_ring
  have hBTC : (B * T) * C = (B * C) * T := by
    calc
      (B * T) * C = B * (T * C) := by noncomm_ring
      _ = (B * C) * T := by rw [hTC]; noncomm_ring
  have hleft :
      (x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (C * F - F * C) +
          (-x • (C * B - B * C) + A * D) * T +
          (-y • (A * F - F * A) - B * E) * S := by
    calc
      (x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (C * F - F * C) -
          x • (C * (B * T) - (B * T) * C) -
          y • ((A * S) * F - F * (A * S)) +
          ((A * S) * (B * T) - (B * T) * (A * S)) := by
            simp only [mul_sub, sub_mul,
              Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
              smul_smul, smul_sub]
            module
      _ = (x * y) • (C * F - F * C) +
          (-x • (C * B - B * C) + A * D) * T +
          (-y • (A * F - F * A) - B * E) * S := by
            rw [hCBT, hASF, hASBT]
            simp only [add_mul, sub_mul, Algebra.smul_mul_assoc]
            module
  have hright :
      (x • E - A * T) * (y • D - B * S) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (E * D - F * C) +
          (-x • (E * B) + y • (F * A) + A * F - B * E) * S +
          (-y • (A * D) + x • (B * C)) * T := by
    calc
      (x • E - A * T) * (y • D - B * S) -
          (y • F - B * T) * (x • C - A * S) =
        (x * y) • (E * D - F * C) -
          x • ((E * B) * S) - y • ((A * D) * T) +
          y • ((F * A) * S) + x • ((B * C) * T) +
          ((A * T) * (B * S) - (B * T) * (A * S)) := by
            simp only [mul_sub, sub_mul,
              Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
              smul_smul, smul_sub]
            rw [hATD, hBTC]
            module
      _ = (x * y) • (E * D - F * C) +
          (-x • (E * B) + y • (F * A) + A * F - B * E) * S +
          (-y • (A * D) + x • (B * C)) * T := by
            rw [hATBS]
            simp only [add_mul, sub_mul, Algebra.smul_mul_assoc]
            module
  rw [hleft, hright]
  have ht :
      (x - y) • (-x • (C * B - B * C) + A * D) =
        -y • (A * D) + x • (B * C) := by
    rw [smul_add, smul_smul]
    have hscaled := congrArg (fun Z => (-x) • Z) hCB
    simp only [smul_smul] at hscaled
    rw [mul_comm (x - y) (-x), hscaled]
    simp only [smul_sub]
    module
  have hs :
      (x - y) • (-y • (A * F - F * A) - B * E) =
        -x • (E * B) + y • (F * A) + A * F - B * E := by
    rw [smul_sub, smul_smul]
    have hscaled := congrArg (fun Z => (-y) • Z) hAF
    simp only [smul_smul] at hscaled
    rw [mul_comm (x - y) (-y), hscaled]
    calc
      -y • (E * B - F * A) - (x - y) • (B * E) =
          -x • (E * B) + y • (F * A) +
            (x - y) • (E * B - B * E) := by
              simp only [smul_sub]
              module
      _ = -x • (E * B) + y • (F * A) + A * F - B * E := by
            rw [hEB]
            module
  simp only [smul_add]
  rw [smul_comm (x - y) (x * y), hcross]
  rw [← Algebra.smul_mul_assoc, ← Algebra.smul_mul_assoc, ht, hs]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
