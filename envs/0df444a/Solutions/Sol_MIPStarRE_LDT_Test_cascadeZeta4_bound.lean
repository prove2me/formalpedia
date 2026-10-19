-- Prove2me | solution 1 for MIPStarRE.LDT.Test.cascadeZeta4_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:30.874992+00:00
-- url     : https://prove2.me/submissions/87165552-9958-4e59-b5a6-f20806b28736

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/SqrtBounds.lean
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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean (solution of MIPStarRE.LDT.Test.cascadeZeta4_bound);
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
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeSigma_tight_bound
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeZeta1_bound_general
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeZeta1_bound_special
import Theorems.Thm_MIPStarRE_LDT_Test_cascadeZeta3_bound
import Theorems.Thm_MIPStarRE_LDT_Test_sqrt_scaled_stepEnvelope_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT
section
set_option backward.isDefEq.respectTransparency false
/-- Subadditivity of the square root on nonnegative error terms. -/
theorem sqrt_add_le_add_sqrt {x y : Error} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  refine Real.sqrt_le_iff.mpr ?_
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]
end
end MIPStarRE.LDT

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

namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- `k ≤ k²`. -/
theorem k_le_k2 : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  have hk_nn : 0 ≤ (k : Error) := by linarith [h.hk]
  have : (k : Error) * 1 ≤ (k : Error) * (k : Error) :=
    mul_le_mul_of_nonneg_left h.hk hk_nn
  simpa [sq] using this
end
end MIPStarRE.LDT.Test.CascadeHypotheses

namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- `k m² ≤ k² m⁴`. -/
theorem km2_le_k2m4 : (k : Error) * ((params.m : Error) ^ (2 : ℕ)) ≤
    ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
  mul_le_mul h.k_le_k2 h.m2_le_m4 (by positivity) (by positivity)
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
theorem sqrt20204_le_143 : Real.sqrt (20204 : Error) ≤ 143 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem sqrt150000_le_388 : Real.sqrt (150000 : Error) ≤ 388 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num
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
    cascadeZeta4 (cascadeSigma params k ν)
        (cascadeZeta1 params eps (cascadeSigma params k ν))
        (cascadeZeta3
          (cascadeZeta1 params eps (cascadeSigma params k ν))
          (cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)))) ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (32768 : Error) (2560000 : Error) := by
  set σ : Error := cascadeSigma params k ν
  set Z1 : Error := cascadeZeta1 params eps σ
  set Z2 : Error := cascadeZeta2 Z1
  set Z3 : Error := cascadeZeta3 Z1 Z2
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E1024 : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E4096 : Error := stepEnvelope params k eps (4096 : Error) (320000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  set E32768 : Error := stepEnvelope params k eps (32768 : Error) (2560000 : Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE4096NN : 0 ≤ E4096 := by
    simpa [E4096] using stepEnvelope_nonneg (h := h) (n := (4096 : Error)) (N := (320000 : Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using
      stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using
      stepEnvelope_nonneg (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
  have hσ : σ ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ, k2, m4, E1024] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : Error)) (n₂ := (32768 : Error)) (N₁ := (80000 : Error))
            (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1_raw := cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ, Z1, k2, m4, E2048] using hZ1_raw
  have hZ3_raw := cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ, Z1, Z2, Z3, k2, m4, E16384] using hZ3_raw
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ, Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ2NN : 0 ≤ Z2 := by
    unfold Z2 cascadeZeta2
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
  have hZ3NN : 0 ≤ Z3 := by
    unfold Z3 cascadeZeta3
    exact add_nonneg (mul_nonneg (by norm_num) hZ1NN) (mul_nonneg (by norm_num) hZ2NN)
  have hX1NN : 0 ≤ 20204 * k2 * m4 * E2048 := by
    positivity [hE2048NN]
  have hsqrtZ1 : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048)
        ≤ Real.sqrt (20204 : Error) * (k : Error) * m2 * E4096 := by
          simpa [k2, m2, m4, E2048, E4096,
            show (2 : Error) * 2048 = 4096 by norm_num,
            show (2 : Error) * 160000 = 320000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 20204 * k2 * m4 * E2048) (C := (20204 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 143 * (k : Error) * m2 * E4096 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt20204_le_143
              (show 0 ≤ (k : Error) * m2 * E4096 by positivity [hE4096NN])
  have hE4096 : E4096 ≤ E32768 := by
    simpa [E4096, E32768] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (4096 : Error)) (n₂ := (32768 : Error)) (N₁ := (320000 : Error))
      (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hsqrtZ1' : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := hsqrtZ1
      _ ≤ 143 * (k : Error) * m2 * E32768 :=
        mul_le_mul_of_nonneg_left hE4096 (by positivity)
  have hX3NN : 0 ≤ 150000 * k2 * m4 * E16384 := by
    positivity [hE16384NN]
  have hsqrtZ3 : Real.sqrt (150000 * k2 * m4 * E16384) ≤ 388 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (150000 * k2 * m4 * E16384)
        ≤ Real.sqrt (150000 : Error) * (k : Error) * m2 * E32768 := by
          simpa [k2, m2, m4, E16384, E32768,
            show (2 : Error) * 16384 = 32768 by norm_num,
            show (2 : Error) * 1280000 = 2560000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 150000 * k2 * m4 * E16384) (C := (150000 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 388 * (k : Error) * m2 * E32768 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt150000_le_388
              (show 0 ≤ (k : Error) * m2 * E32768 by positivity [hE32768NN])
  have hsqrtTerm : 2 * Real.sqrt (Z1 + Z3 / 2) ≤ 1062 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3, hZ3NN]
    have hinside : Z1 + Z3 / 2 ≤ 20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384 := by
      linarith [hZ1, hZ3half]
    have hsqrtSplit : Real.sqrt (Z1 + Z3 / 2) ≤
        Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) := by
      calc
        Real.sqrt (Z1 + Z3 / 2)
          ≤ Real.sqrt (20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384) :=
            Real.sqrt_le_sqrt hinside
        _ ≤ Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) :=
            sqrt_add_le_add_sqrt (by positivity [hE2048NN]) (by positivity [hE16384NN])
    have hkm2 : (k : Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z1 : 143 * (k : Error) * m2 * E32768 ≤ 143 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 143 * E32768 by positivity [hE32768NN])
    have hkm2z3 : 388 * (k : Error) * m2 * E32768 ≤ 388 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 388 * E32768 by positivity [hE32768NN])
    nlinarith [hsqrtSplit, hsqrtZ1', hsqrtZ3, hkm2z1, hkm2z3]
  unfold cascadeZeta4
  calc
    2 * σ + 2 * Real.sqrt (Z1 + Z3 / 2)
      ≤ 20000 * k2 * m4 * E32768 + 1062 * k2 * m4 * E32768 := by
        nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
        nlinarith [show 0 ≤ k2 * m4 * E32768 by positivity]
end MIPStarRE.LDT.Test
