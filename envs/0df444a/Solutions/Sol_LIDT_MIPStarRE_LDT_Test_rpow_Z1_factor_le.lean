-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:40:46.127181+00:00
-- url     : https://prove2.me/submissions/257575d4-88d7-41b1-9bc6-0eea1ad5dd5b

-- Generated proof for MIPStarRE.LDT.Test.rpow_Z1_factor_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Mathlib

namespace LIDT

end LIDT

open LIDT
/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ}
    {Z1 k2 m4 E2048 r Crpow Erpow : _root_.LIDT.MIPStarRE.LDT.Error}
    (hZ1NN : 0 ≤ Z1)
    (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
    (hrNN : 0 ≤ r)
    (hk2NN : 0 ≤ k2)
    (hm4NN : 0 ≤ m4)
    (hE2048NN : 0 ≤ E2048)
    (hA : Real.rpow (20204 : _root_.LIDT.MIPStarRE.LDT.Error) r ≤ Crpow)
    (hB : Real.rpow k2 r ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    (hC : Real.rpow m4 r ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error))
    (hD : Real.rpow E2048 r ≤ Erpow) :
    Real.rpow Z1 r ≤ Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Erpow := by
  set A : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow (20204 : _root_.LIDT.MIPStarRE.LDT.Error) r
  set B : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow k2 r
  set C : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow m4 r
  set D : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow E2048 r
  have hAnn : 0 ≤ A := by
    simpa [A] using Real.rpow_nonneg (by norm_num : 0 ≤ (20204 : Error)) r
  have hBnn : 0 ≤ B := by
    simpa [B] using Real.rpow_nonneg hk2NN r
  have hCnn : 0 ≤ C := by
    simpa [C] using Real.rpow_nonneg hm4NN r
  have hDnn : 0 ≤ D := by
    simpa [D] using Real.rpow_nonneg hE2048NN r
  have hCrpowNN : 0 ≤ Crpow := le_trans hAnn hA
  have hkNN : 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := Nat.cast_nonneg _
  have hmNN : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := Nat.cast_nonneg _
  have hAB : A * B ≤ Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error) :=
    mul_le_mul hA hB hBnn hCrpowNN
  have hABC : A * B * C ≤ (Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact mul_le_mul hAB hC hCnn (mul_nonneg hCrpowNN hkNN)
  have hABCD : A * B * C * D ≤ ((Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * Erpow := by
    exact mul_le_mul hABC hD hDnn (mul_nonneg (mul_nonneg hCrpowNN hkNN) hmNN)
  have hsplit1 :
      Real.rpow (((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2) * (m4 * E2048)) r =
        Real.rpow ((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2) r * Real.rpow (m4 * E2048) r := by
    simpa using
      (Real.mul_rpow (x := ((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2)) (y := (m4 * E2048)) (z := r)
        (by positivity) (mul_nonneg hm4NN hE2048NN))
  have hsplit2a :
      Real.rpow ((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2) r =
        Real.rpow (20204 : _root_.LIDT.MIPStarRE.LDT.Error) r * Real.rpow k2 r := by
    simpa using
      (Real.mul_rpow (x := (20204 : _root_.LIDT.MIPStarRE.LDT.Error)) (y := k2) (z := r) (by positivity) hk2NN)
  have hsplit2b :
      Real.rpow (m4 * E2048) r = Real.rpow m4 r * Real.rpow E2048 r := by
    simpa using (Real.mul_rpow (x := m4) (y := E2048) (z := r) hm4NN hE2048NN)
  have hFactor : Real.rpow (20204 * k2 * m4 * E2048) r = A * B * C * D := by
    calc
      Real.rpow (20204 * k2 * m4 * E2048) r
          = Real.rpow (((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2) * (m4 * E2048)) r := by
              congr 1
              ring
      _ = Real.rpow ((20204 : _root_.LIDT.MIPStarRE.LDT.Error) * k2) r * Real.rpow (m4 * E2048) r := hsplit1
      _ = (Real.rpow (20204 : _root_.LIDT.MIPStarRE.LDT.Error) r * Real.rpow k2 r) *
            (Real.rpow m4 r * Real.rpow E2048 r) := by
            rw [hsplit2a, hsplit2b]
      _ = A * B * C * D := by simp [A, B, C, D, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.rpow Z1 r ≤ Real.rpow (20204 * k2 * m4 * E2048) r :=
      Real.rpow_le_rpow hZ1NN hZ1 hrNN
    _ = A * B * C * D := hFactor
    _ ≤ Crpow * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Erpow := by
      simpa [mul_assoc] using hABCD
