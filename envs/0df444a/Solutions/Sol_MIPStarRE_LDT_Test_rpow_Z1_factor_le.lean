-- Prove2me | solution 1 for MIPStarRE.LDT.Test.rpow_Z1_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:23.019987+00:00
-- url     : https://prove2.me/submissions/f4b96cf3-7136-4d1d-bec2-b71f8c56bf4d

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean (solution of MIPStarRE.LDT.Test.rpow_Z1_factor_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ}
    {Z1 k2 m4 E2048 r Crpow Erpow : Error}
    (hZ1NN : 0 ≤ Z1)
    (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
    (hrNN : 0 ≤ r)
    (hk2NN : 0 ≤ k2)
    (hm4NN : 0 ≤ m4)
    (hE2048NN : 0 ≤ E2048)
    (hA : Real.rpow (20204 : Error) r ≤ Crpow)
    (hB : Real.rpow k2 r ≤ (k : Error))
    (hC : Real.rpow m4 r ≤ (params.m : Error))
    (hD : Real.rpow E2048 r ≤ Erpow) :
    Real.rpow Z1 r ≤ Crpow * (k : Error) * (params.m : Error) * Erpow := by
  set A : Error := Real.rpow (20204 : Error) r
  set B : Error := Real.rpow k2 r
  set C : Error := Real.rpow m4 r
  set D : Error := Real.rpow E2048 r
  have hAnn : 0 ≤ A := by
    simpa [A] using Real.rpow_nonneg (by norm_num : 0 ≤ (20204 : Error)) r
  have hBnn : 0 ≤ B := by
    simpa [B] using Real.rpow_nonneg hk2NN r
  have hCnn : 0 ≤ C := by
    simpa [C] using Real.rpow_nonneg hm4NN r
  have hDnn : 0 ≤ D := by
    simpa [D] using Real.rpow_nonneg hE2048NN r
  have hCrpowNN : 0 ≤ Crpow := le_trans hAnn hA
  have hkNN : 0 ≤ (k : Error) := Nat.cast_nonneg _
  have hmNN : 0 ≤ (params.m : Error) := Nat.cast_nonneg _
  have hAB : A * B ≤ Crpow * (k : Error) :=
    mul_le_mul hA hB hBnn hCrpowNN
  have hABC : A * B * C ≤ (Crpow * (k : Error)) * (params.m : Error) := by
    exact mul_le_mul hAB hC hCnn (mul_nonneg hCrpowNN hkNN)
  have hABCD : A * B * C * D ≤ ((Crpow * (k : Error)) * (params.m : Error)) * Erpow := by
    exact mul_le_mul hABC hD hDnn (mul_nonneg (mul_nonneg hCrpowNN hkNN) hmNN)
  have hsplit1 :
      Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) r =
        Real.rpow ((20204 : Error) * k2) r * Real.rpow (m4 * E2048) r := by
    simpa using
      (Real.mul_rpow (x := ((20204 : Error) * k2)) (y := (m4 * E2048)) (z := r)
        (by positivity) (mul_nonneg hm4NN hE2048NN))
  have hsplit2a :
      Real.rpow ((20204 : Error) * k2) r =
        Real.rpow (20204 : Error) r * Real.rpow k2 r := by
    simpa using
      (Real.mul_rpow (x := (20204 : Error)) (y := k2) (z := r) (by positivity) hk2NN)
  have hsplit2b :
      Real.rpow (m4 * E2048) r = Real.rpow m4 r * Real.rpow E2048 r := by
    simpa using (Real.mul_rpow (x := m4) (y := E2048) (z := r) hm4NN hE2048NN)
  have hFactor : Real.rpow (20204 * k2 * m4 * E2048) r = A * B * C * D := by
    calc
      Real.rpow (20204 * k2 * m4 * E2048) r
          = Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) r := by
              congr 1
              ring
      _ = Real.rpow ((20204 : Error) * k2) r * Real.rpow (m4 * E2048) r := hsplit1
      _ = (Real.rpow (20204 : Error) r * Real.rpow k2 r) *
            (Real.rpow m4 r * Real.rpow E2048 r) := by
            rw [hsplit2a, hsplit2b]
      _ = A * B * C * D := by simp [A, B, C, D, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.rpow Z1 r ≤ Real.rpow (20204 * k2 * m4 * E2048) r :=
      Real.rpow_le_rpow hZ1NN hZ1 hrNN
    _ = A * B * C * D := hFactor
    _ ≤ Crpow * (k : Error) * (params.m : Error) * Erpow := by
      simpa [mul_assoc] using hABCD
end MIPStarRE.LDT.Test
