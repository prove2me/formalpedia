-- Prove2me | solution 1 for MIPStarRE.LDT.Test.cascadeZeta2_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:39:59.982635+00:00
-- url     : https://prove2.me/submissions/481c8674-a411-4acc-a5a0-9a81bb751ed7

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta2Zeta3.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean
-/
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
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta2Zeta3.lean (solution of MIPStarRE.LDT.Test.cascadeZeta2_bound);
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
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeZeta1_bound_general
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeZeta1_bound_special
import Theorems.Thm_MIPStarRE_LDT_Test_rpow_Z1_factor_le
import Theorems.Thm_MIPStarRE_LDT_Test_stepEnvelope_rpow_eighth_le
import Theorems.Thm_MIPStarRE_LDT_Test_stepEnvelope_rpow_quarter_le

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

namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- `d/q ≤ 1` under the standing hypotheses. -/
theorem dqLeOne : (params.d : Error) / (params.q : Error) ≤ 1 :=
  (div_le_one h.hqPos).mpr h.hdq
end
end MIPStarRE.LDT.Test.CascadeHypotheses

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- For `x ∈ [0, 1]`, enlarging the denominator in `x^(1/n)` makes the
exponent smaller and therefore the value larger. -/
theorem rpow_le_of_denom_le {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n₁ n₂ : Error} (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) :
    Real.rpow x (1 / n₁) ≤ Real.rpow x (1 / n₂) := by
  have hn₂Pos : 0 < n₂ := lt_of_lt_of_le hn₁Pos hn
  have hdiv : 1 / n₂ ≤ 1 / n₁ := one_div_le_one_div_of_le hn₁Pos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n₂ by positivity) hdiv
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
/-- For `k ≥ 0`, `m > 0`, and `N₁ ≤ N₂`, the larger decay denominator gives
the weaker exponential bound `exp(-k/(N₁ m²)) ≤ exp(-k/(N₂ m²))`. -/
theorem exp_neg_le_of_denom_ge (k : ℕ) (m : Error) (hm : 0 < m)
    {N₁ N₂ : Error} (h₁ : 0 < N₁) (h₁₂ : N₁ ≤ N₂) :
    Real.exp (-((k : Error) / (N₁ * m ^ (2 : ℕ)))) ≤
      Real.exp (-((k : Error) / (N₂ * m ^ (2 : ℕ)))) := by
  have hm2 : 0 < m ^ (2 : ℕ) := by positivity
  have hN₁m : 0 < N₁ * m ^ 2 := mul_pos h₁ hm2
  have hknn : (0 : Error) ≤ (k : Error) := Nat.cast_nonneg _
  have hratio : (k : Error) / (N₂ * m ^ 2) ≤ (k : Error) / (N₁ * m ^ 2) := by
    apply div_le_div_of_nonneg_left hknn hN₁m
    exact mul_le_mul_of_nonneg_right h₁₂ hm2.le
  exact Real.exp_le_exp.mpr (neg_le_neg hratio)
end
end MIPStarRE.LDT.Test

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
theorem stepEnvelope_le_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n₁ n₂ N₁ N₂ : Error}
    (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) (hN₁Pos : 0 < N₁) (hN : N₁ ≤ N₂) :
    stepEnvelope params k eps n₁ N₁ ≤ stepEnvelope params k eps n₂ N₂ := by
  unfold stepEnvelope
  have hEps := rpow_le_of_denom_le h.hepsNN h.hepsOne hn₁Pos hn
  have hDq := rpow_le_of_denom_le h.dqNN h.dqLeOne hn₁Pos hn
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExp := exp_neg_le_of_denom_ge k (params.m : Error) hmPos hN₁Pos hN
  linarith
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem rpow20204_quarter_le_12 : Real.rpow (20204 : Error) (1 / (4 : Error)) ≤ 12 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (12 : Error) ^ (4 : ℕ)) (by positivity : 0 ≤ (1 / (4 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (4 : Error))
      ≤ Real.rpow ((12 : Error) ^ (4 : ℕ)) (1 / (4 : Error)) := hmono
    _ = Real.rpow (12 : Error) ((4 : Error) * (1 / (4 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (12 : Error)) 4 (1 / (4 : Error))
    _ = (12 : Error) := by norm_num [Real.rpow_one]
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem rpow20204_eighth_le_4 : Real.rpow (20204 : Error) (1 / (8 : Error)) ≤ 4 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (4 : Error) ^ (8 : ℕ)) (by positivity : 0 ≤ (1 / (8 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (8 : Error))
      ≤ Real.rpow ((4 : Error) ^ (8 : ℕ)) (1 / (8 : Error)) := hmono
    _ = Real.rpow (4 : Error) ((8 : Error) * (1 / (8 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : Error)) 8 (1 / (8 : Error))
    _ = (4 : Error) := by norm_num [Real.rpow_one]
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem k2_rpow_quarter_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (4 : Error)) ≤ (k : Error) := by
  calc
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (4 : Error))
      = Real.rpow (k : Error) ((2 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 (1 / (4 : Error))
    _ = Real.rpow (k : Error) (1 / (2 : Error)) := by norm_num
    _ ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk (by norm_num : (1 / (2 : Error)) ≤ 1)
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem m4_rpow_quarter_eq {params : Parameters} :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error)) = (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (4 : Error))
    _ = (params.m : Error) := by norm_num [Real.rpow_one]
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem k2_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error)) ≤ (k : Error) := by
  calc
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error))
      = Real.rpow (k : Error) ((2 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 (1 / (8 : Error))
    _ = Real.rpow (k : Error) (1 / (4 : Error)) := by norm_num
    _ ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk (by norm_num : (1 / (4 : Error)) ≤ 1)
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem m4_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error)) ≤ (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (8 : Error))
    _ = Real.rpow (params.m : Error) (1 / (2 : Error)) := by norm_num
    _ ≤ (params.m : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hm (by norm_num : (1 / (2 : Error)) ≤ 1)
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem cascadeSigma_nonneg {params : Parameters} {k : ℕ} {ν : Error}
    (hνNN : 0 ≤ ν) :
    0 ≤ cascadeSigma params k ν := by
  unfold cascadeSigma
  positivity
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem cascadeZeta1_nonneg {params : Parameters} {k : ℕ} {eps ν : Error}
    (h : CascadeHypotheses params k eps) (hνNN : 0 ≤ ν) :
    0 ≤ cascadeZeta1 params eps (cascadeSigma params k ν) := by
  have hσNN := cascadeSigma_nonneg (params := params) (k := k) (ν := ν) hνNN
  unfold cascadeZeta1
  positivity [hσNN, h.hepsNN, h.dqNN]
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem cascadeZeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  by_cases hkm1 : k = 1 ∧ params.m = 1
  · exact cascadeZeta1_bound_special (h := h) (ν := ν) hν hkm1
  · exact cascadeZeta1_bound_general (h := h) (ν := ν) hν hkm1
end
end MIPStarRE.LDT.Test

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)) ≤
      2568 * (k : Error) * (params.m : Error) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  set Z1 : Error := cascadeZeta1 params eps (cascadeSigma params k ν)
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E8192 : Error := stepEnvelope params k eps (8192 : Error) (640000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE8192 : E8192 ≤ E16384 := by
    simpa [E8192, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (8192 : Error)) (n₂ := (16384 : Error)) (N₁ := (640000 : Error))
      (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hQuarterRoot : Real.rpow Z1 (1 / (4 : Error)) ≤
      12 * (k : Error) * (params.m : Error) * E8192 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_quarter_le_12)
      (hB := by simpa [k2] using k2_rpow_quarter_le (h := h))
      (hC := by simpa [m4] using (m4_rpow_quarter_eq (params := params)).le)
      (hD := by simpa [E2048, E8192] using stepEnvelope_rpow_quarter_le (h := h))
  have hQuarterRoot' : Real.rpow Z1 (1 / (4 : Error)) ≤
      12 * (k : Error) * (params.m : Error) * E16384 := by
    calc
      Real.rpow Z1 (1 / (4 : Error)) ≤ 12 * (k : Error) * (params.m : Error) * E8192 := hQuarterRoot
      _ ≤ 12 * (k : Error) * (params.m : Error) * E16384 :=
        mul_le_mul_of_nonneg_left hE8192 (by positivity)
  have hEighthRoot : Real.rpow Z1 (1 / (8 : Error)) ≤
      4 * (k : Error) * (params.m : Error) * E16384 := by
    exact rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using rpow20204_eighth_le_4)
      (hB := by simpa [k2] using k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using stepEnvelope_rpow_eighth_le (h := h))
  unfold cascadeZeta2
  calc
    200 * Real.rpow Z1 (1 / (4 : Error)) + 42 * Real.rpow Z1 (1 / (8 : Error))
      ≤ 200 * (12 * (k : Error) * (params.m : Error) * E16384) +
          42 * (4 * (k : Error) * (params.m : Error) * E16384) := by
            nlinarith [hQuarterRoot', hEighthRoot]
    _ = 2568 * (k : Error) * (params.m : Error) * E16384 := by ring
end MIPStarRE.LDT.Test
