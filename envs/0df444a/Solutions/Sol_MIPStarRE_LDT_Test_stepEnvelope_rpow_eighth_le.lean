-- Prove2me | solution 1 for MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:53.078394+00:00
-- url     : https://prove2.me/submissions/9961bcc3-70b8-41bc-96c7-b5f1bd05b472

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean (solution of MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le);
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
theorem rpow_one_four_eq_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (4 : Error)) = Real.sqrt (Real.sqrt x) := by
  calc
    Real.rpow x (1 / (4 : Error)) =
        Real.rpow x ((1 / (2 : Error)) * (1 / (2 : Error))) := by
      norm_num
    _ = Real.rpow (Real.rpow x (1 / (2 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (2 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      try rfl
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem rpow_one_eight_eq_sqrt_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (8 : Error)) = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  calc
    Real.rpow x (1 / (8 : Error)) =
        Real.rpow x ((1 / (4 : Error)) * (1 / (2 : Error))) := by
      norm_num
    _ = Real.rpow (Real.rpow x (1 / (4 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (4 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
      rw [Real.sqrt_eq_rpow, rpow_one_four_eq_sqrt_sqrt hx]
      try rfl
end
end MIPStarRE.LDT.Test

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error)) (1 / (8 : Error)) ≤
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  have h1 : Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)) ≤
      stepEnvelope params k eps (4096 : Error) (320000 : Error) := by
    simpa [show (2 : Error) * 2048 = 4096 by norm_num,
      show (2 : Error) * 160000 = 320000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (2048 : Error)) (N := (160000 : Error))
        (by norm_num) (by norm_num)
  have h2 : Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error)) ≤
      stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    simpa [show (2 : Error) * 4096 = 8192 by norm_num,
      show (2 : Error) * 320000 = 640000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (4096 : Error)) (N := (320000 : Error))
        (by norm_num) (by norm_num)
  have h3 : Real.sqrt (stepEnvelope params k eps (8192 : Error) (640000 : Error)) ≤
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
    simpa [show (2 : Error) * 8192 = 16384 by norm_num,
      show (2 : Error) * 640000 = 1280000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (8192 : Error)) (N := (640000 : Error))
        (by norm_num) (by norm_num)
  have hnn : 0 ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  calc
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error))
        (1 / (8 : Error))
      = Real.sqrt
          (Real.sqrt (Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)))) :=
        rpow_one_eight_eq_sqrt_sqrt_sqrt hnn
    _ ≤ Real.sqrt (Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error))) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    _ ≤ Real.sqrt (stepEnvelope params k eps (8192 : Error) (640000 : Error)) :=
      Real.sqrt_le_sqrt h2
    _ ≤ stepEnvelope params k eps (16384 : Error) (1280000 : Error) := h3
end MIPStarRE.LDT.Test
