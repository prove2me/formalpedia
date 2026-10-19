-- Prove2me | solution 1 for MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:53.857752+00:00
-- url     : https://prove2.me/submissions/438238a5-7bd5-43a1-9d87-77339b056a68

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean (solution of MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le);
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
import Theorems.Thm_MIPStarRE_LDT_Test_sqrt_stepEnvelope_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le
end
end MIPStarRE.LDT.Test.CascadeHypotheses

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem stepEnvelope_le_sq_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} (hn : 0 < n) (hN : 0 < N) :
    stepEnvelope params k eps n N ≤
      (stepEnvelope params k eps (2 * n) (2 * N)) ^ (2 : ℕ) := by
  let F : Error := stepEnvelope params k eps (2 * n) (2 * N)
  have hsqrt := sqrt_stepEnvelope_le (h := h) (n := n) (N := N) hn hN
  have hnn : 0 ≤ stepEnvelope params k eps n N := stepEnvelope_nonneg (h := h) (n := n) (N := N)
  have hFnn : 0 ≤ F := by
    simpa [F] using stepEnvelope_nonneg (h := h) (n := 2 * n) (N := 2 * N)
  have hsq : (Real.sqrt (stepEnvelope params k eps n N)) ^ (2 : ℕ) ≤ F ^ (2 : ℕ) := by
    exact (sq_le_sq).2 (by
      simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hFnn, F] using hsqrt)
  simpa [F, Real.sq_sqrt hnn] using hsq
end
end MIPStarRE.LDT.Test

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ} {eps x C n N : Error}
    (h : CascadeHypotheses params k eps)
    (hC : 0 ≤ C)
    (hx : x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
      stepEnvelope params k eps n N)
    (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt x ≤
      Real.sqrt C * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
        stepEnvelope params k eps (2 * n) (2 * N) := by
  set E : Error := stepEnvelope params k eps (2 * n) (2 * N)
  have hE_sq : stepEnvelope params k eps n N ≤ E ^ (2 : ℕ) := by
    simpa [E] using stepEnvelope_le_sq_stepEnvelope (h := h) (n := n) (N := N) hn hN
  have hCoeffNN : 0 ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hENN : 0 ≤ E := by
    simpa [E] using stepEnvelope_nonneg (h := h) (n := 2 * n) (N := 2 * N)
  have hx' : x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) := by
    calc
      x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
            stepEnvelope params k eps n N := hx
      _ ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hE_sq hCoeffNN
  set u : Error := (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E
  have huNN : 0 ≤ u := by
    dsimp [u]
    positivity [hENN]
  have hsqrt := Real.sqrt_le_sqrt hx'
  calc
    Real.sqrt x ≤
        Real.sqrt (C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ)) :=
      hsqrt
    _ = Real.sqrt (C * (u ^ (2 : ℕ))) := by
      rw [show C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) =
          C * (u ^ (2 : ℕ)) by
        dsimp [u]
        ring]
    _ = Real.sqrt C * u := by
      rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg huNN]
    _ = Real.sqrt C * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
          stepEnvelope params k eps (2 * n) (2 * N) := by
      simp [u, E]
      ring
end MIPStarRE.LDT.Test
