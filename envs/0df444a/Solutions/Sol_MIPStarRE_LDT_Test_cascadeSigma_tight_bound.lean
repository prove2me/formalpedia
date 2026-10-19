-- Prove2me | solution 1 for MIPStarRE.LDT.Test.cascadeSigma_tight_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:19.999975+00:00
-- url     : https://prove2.me/submissions/6dbb8c55-1ec8-4321-8cbb-ad4bbfab8e22

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean (solution of MIPStarRE.LDT.Test.cascadeSigma_tight_bound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.Order.Group.Defs
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
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
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
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Init
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
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds

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
/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hk
end
end MIPStarRE.LDT.Test.CascadeHypotheses

namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- `m² ≤ m⁴`. -/
theorem m2_le_m4 : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  apply pow_le_pow_right₀ h.hm
  norm_num
end
end MIPStarRE.LDT.Test.CascadeHypotheses

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (1024 : Error) (80000 : Error) := by
  unfold cascadeSigma stepEnvelope
  set m2 : Error := (params.m : Error) ^ (2 : ℕ) with hm2_def
  set m4 : Error := (params.m : Error) ^ (4 : ℕ) with hm4_def
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  have hm2NN : 0 ≤ m2 := by positivity
  have hk2_ge_one : (1 : Error) ≤ k2 := h.k2_ge_one
  have hm2_le_m4 : m2 ≤ m4 := h.m2_le_m4
  have hm2_sq_m4 : m2 * m2 = m4 := by
    simp only [hm2_def, hm4_def]
    ring
  have hStep1 :
      m2 * ν ≤ 10000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
    have hreorder :
        m2 * (10000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) =
          10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
      ring
    calc
      m2 * ν
          ≤ m2 * (10000 * k2 * m2 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :=
            mul_le_mul_of_nonneg_left hν hm2NN
      _ = 10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := hreorder
      _ = 10000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := by
            rw [hm2_sq_m4]
  have hScaleGeOne : (1 : Error) ≤ 10000 * k2 := by
    nlinarith [hk2_ge_one]
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    calc
      m2 ≤ m4 := hm2_le_m4
      _ ≤ (10000 * k2) * m4 := by
        nlinarith [hScaleGeOne, show 0 ≤ m4 by positivity]
      _ = 10000 * k2 * m4 := by ring
  have hStep2 :
      m2 * Real.exp (-((k : Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
    have hExpNN : 0 ≤ Real.exp (-((k : Error) / (80000 * m2))) := Real.exp_nonneg _
    exact mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  have hExpand : m2 * (ν + Real.exp (-((k : Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2))) := by ring
  rw [hExpand]
  calc
    m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ 10000 * k2 * m4 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) +
            10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
          nlinarith [hStep1, hStep2]
    _ = 10000 * k2 * m4 *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
            Real.exp (-((k : Error) / (80000 * m2)))) := by ring
end MIPStarRE.LDT.Test
