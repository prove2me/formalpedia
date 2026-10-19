-- Prove2me | solution 1 for MIPStarRE.LDT.Test.cascadeZeta1_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:00.638381+00:00
-- url     : https://prove2.me/submissions/c0bc910e-37ac-42c0-89d6-7b240770e286

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean (solution of MIPStarRE.LDT.Test.cascadeZeta1_bound_general);
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
import Theorems.Thm_MIPStarRE_LDT_Test_mdq_le_k2m4_stepEnvelope2048
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
/-- `1 ≤ m²`. -/
theorem m2_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hm
end
end MIPStarRE.LDT.Test.CascadeHypotheses

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
/-- `1 ≤ m⁴`. -/
theorem m4_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  simpa using one_le_pow₀ (n := (4 : ℕ)) h.hm
end
end MIPStarRE.LDT.Test.CascadeHypotheses

namespace MIPStarRE.LDT.Test.CascadeHypotheses
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)
include h
/-- `k² · m⁴ ≥ 1`. -/
theorem k2_m4_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) *
    ((params.m : Error) ^ (4 : ℕ)) := by
  nlinarith [h.k2_ge_one, h.m4_ge_one]
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
theorem four_mul_le_k2m4_mul {params : Parameters} {k : ℕ} {eps T : Error}
    (h : CascadeHypotheses params k eps) (hT : 0 ≤ T) :
    4 * T ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) * T := by
  have hscale : (4 : Error) ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) := by
    simpa using mul_le_mul_of_nonneg_left h.k2_m4_ge_one (by norm_num : (0 : Error) ≤ 4)
  exact mul_le_mul_of_nonneg_right hscale hT
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem sqrt_three_le_two : Real.sqrt (3 : Error) ≤ 2 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem sqrt20000_le_142 : Real.sqrt (20000 : Error) ≤ 142 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num
end
end MIPStarRE.LDT.Test

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hkm1 : ¬ (k = 1 ∧ params.m = 1)) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set S : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set T : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set σ : Error := cascadeSigma params k ν
  have hσtight : σ ≤ 10000 * k2 * m4 * S := by
    simpa [σ, k2, m4, S] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hST : S ≤ T := by
    simpa [S, T] using stepEnvelope_le_stepEnvelope (h := h) (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (N₁ := (80000 : Error)) (N₂ := (160000 : Error))
      (hn₁Pos := by norm_num) (hn := by norm_num) (hN₁Pos := by norm_num) (hN := by norm_num)
  have hσtoT : σ ≤ 10000 * k2 * m4 * T := by
    calc
      σ ≤ 10000 * k2 * m4 * S := hσtight
      _ ≤ 10000 * k2 * m4 * T := by
        exact mul_le_mul_of_nonneg_left hST (by positivity)
  have htwoσ : 2 * σ ≤ 20000 * k2 * m4 * T := by
    nlinarith [hσtoT]
  have hTNN : 0 ≤ T := by
    simpa [T] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hSNN : 0 ≤ S := by
    simpa [S] using stepEnvelope_nonneg (h := h) (n := (1024 : Error)) (N := (80000 : Error))
  have hEpsTerm : Real.rpow eps (1 / (2048 : Error)) ≤ T := by
    unfold T stepEnvelope
    have hdqNN' : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
      Real.rpow_nonneg h.dqNN _
    have hExpNN' :
        0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
      Real.exp_nonneg _
    nlinarith
  have hsqrt_eps : Real.sqrt eps ≤ Real.rpow eps (1 / (2048 : Error)) := by
    calc
      Real.sqrt eps = Real.rpow eps (1 / (2 : Error)) := by simpa using (Real.sqrt_eq_rpow eps)
      _ ≤ Real.rpow eps (1 / (2048 : Error)) :=
        rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (2 : Error)) (n₂ := (2048 : Error))
          (hn₁Pos := by norm_num) (hn := by norm_num)
  have hsqrt3eps : Real.sqrt (3 * eps) ≤ 2 * T := by
    calc
      Real.sqrt (3 * eps) = Real.sqrt (3 : Error) * Real.sqrt eps := by
        rw [Real.sqrt_mul (by norm_num)]
      _ ≤ 2 * Real.sqrt eps := by
        exact mul_le_mul_of_nonneg_right sqrt_three_le_two (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.rpow eps (1 / (2048 : Error)) :=
        mul_le_mul_of_nonneg_left hsqrt_eps (by norm_num)
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hEpsTerm (by norm_num)
  have hsqrtScaled : Real.sqrt (20000 * k2 * m4 * S) ≤
      Real.sqrt (20000 : Error) * (k : Error) * m2 * T := by
    simpa [k2, m2, m4, S, T,
      show (2 : Error) * 1024 = 2048 by norm_num,
      show (2 : Error) * 80000 = 160000 by norm_num] using
      sqrt_scaled_stepEnvelope_le (h := h)
        (x := 20000 * k2 * m4 * S) (C := (20000 : Error))
        (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
  have hsqrtScaled142 : Real.sqrt (20000 * k2 * m4 * S) ≤ 142 * (k : Error) * m2 * T := by
    calc
      Real.sqrt (20000 * k2 * m4 * S)
        ≤ Real.sqrt (20000 : Error) * (k : Error) * m2 * T := hsqrtScaled
      _ ≤ 142 * (k : Error) * m2 * T := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right sqrt20000_le_142
            (show 0 ≤ (k : Error) * m2 * T by positivity [hTNN])
  have hsqrtTmp : Real.sqrt (3 * eps + 2 * σ) ≤
      Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) := by
    have harg : 3 * eps + 2 * σ ≤ 3 * eps + 20000 * k2 * m4 * S := by
      nlinarith [hσtight, hSNN]
    calc
      Real.sqrt (3 * eps + 2 * σ)
        ≤ Real.sqrt (3 * eps + 20000 * k2 * m4 * S) := Real.sqrt_le_sqrt harg
      _ ≤ Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) :=
        sqrt_add_le_add_sqrt (by nlinarith [h.hepsNN]) (by positivity [hSNN])
  have hkm2_ge_two : (2 : Error) ≤ (k : Error) * m2 := by
    by_cases hk1 : k = 1
    · have hmNe : params.m ≠ 1 := by
        intro hmEq
        exact hkm1 ⟨hk1, hmEq⟩
      have hmNat2 : 2 ≤ params.m := by
        have hmNat1 : 1 ≤ params.m := by exact_mod_cast h.hm
        omega
      have hm_ge_two : (2 : Error) ≤ (params.m : Error) := by exact_mod_cast hmNat2
      have hm2_ge_two : (2 : Error) ≤ m2 := by
        dsimp [m2]
        nlinarith [hm_ge_two]
      simpa [hk1] using hm2_ge_two
    · have hkNat2 : 2 ≤ k := by
        have hkNat1 : 1 ≤ k := by exact_mod_cast h.hk
        omega
      have hk_ge_two : (2 : Error) ≤ (k : Error) := by exact_mod_cast hkNat2
      nlinarith [hk_ge_two, h.m2_ge_one]
  have hkm2NN : 0 ≤ (k : Error) * m2 := by positivity
  have hkm2_sq : (((k : Error) * m2) ^ (2 : ℕ)) = k2 * m4 := by
    dsimp [k2, m2, m4]
    ring
  have hCoeffDirect : (284 : Error) * ((k : Error) * m2) ≤ 199 * k2 * m4 := by
    have h284 : (284 : Error) ≤ 199 * ((k : Error) * m2) := by
      nlinarith [hkm2_ge_two]
    have hmul := mul_le_mul_of_nonneg_right h284 hkm2NN
    calc
      (284 : Error) * ((k : Error) * m2) ≤ (199 * ((k : Error) * m2)) * ((k : Error) * m2) := by
        simpa [mul_assoc] using hmul
      _ = 199 * (((k : Error) * m2) ^ (2 : ℕ)) := by ring
      _ = 199 * k2 * m4 := by rw [hkm2_sq]; ring
  have hsqrtBig : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 199 * k2 * m4 * T := by
    have htmp1' : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 2 * (142 * (k : Error) * m2 * T) :=
      mul_le_mul_of_nonneg_left hsqrtScaled142 (by norm_num : (0 : Error) ≤ 2)
    have htmp1b : 2 * (142 * (k : Error) * m2 * T) = (284 * ((k : Error) * m2)) * T := by
      ring
    have htmp1 : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ (284 * ((k : Error) * m2)) * T := by
      exact htmp1'.trans_eq htmp1b
    have htmp2 : (284 * ((k : Error) * m2)) * T ≤ (199 * k2 * m4) * T :=
      mul_le_mul_of_nonneg_right hCoeffDirect hTNN
    have htmp3 : (199 * k2 * m4) * T = 199 * k2 * m4 * T := by ring
    exact htmp1.trans <| htmp2.trans_eq htmp3
  have hsqrt3Term : 2 * Real.sqrt (3 * eps) ≤ 4 * T := by
    have htmp : 2 * Real.sqrt (3 * eps) ≤ 2 * (2 * T) :=
      mul_le_mul_of_nonneg_left hsqrt3eps (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 * (2 * T) = 4 * T := by ring
    exact htmp.trans_eq hEq
  have hsqrtTerm : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 4 * T + 199 * k2 * m4 * T := by
    have hsqrtTmp2' : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) :=
      mul_le_mul_of_nonneg_left hsqrtTmp (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) =
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by ring
    have hsqrtTmp2 : 2 * Real.sqrt (3 * eps + 2 * σ) ≤
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by
      exact hsqrtTmp2'.trans_eq hEq
    exact hsqrtTmp2.trans (add_le_add hsqrt3Term hsqrtBig)
  have hmdq_to_k2m4T :
      (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤ k2 * m4 * T := by
    dsimp [k2, m4, T]
    exact mdq_le_k2m4_stepEnvelope2048 (h := h)
  have hfourT : 4 * T ≤ 4 * (k2 * m4) * T := by
    dsimp [k2, m4]
    exact four_mul_le_k2m4_mul (h := h) hTNN
  rw [show cascadeZeta1 params eps σ =
      2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error) by rfl]
  have hmdq_to_k2m4T' :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤ k2 * m4 * T := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error)
        = (params.m : Error) * ((params.d : Error) / (params.q : Error)) := by ring
      _ ≤ k2 * m4 * T := hmdq_to_k2m4T
  calc
    2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error)
      ≤ (20000 * k2 * m4 * T + (4 * T + 199 * k2 * m4 * T)) + k2 * m4 * T :=
          add_le_add (add_le_add htwoσ hsqrtTerm) hmdq_to_k2m4T'
    _ = 20000 * k2 * m4 * T + 4 * T + 199 * k2 * m4 * T + k2 * m4 * T := by ring
    _ = (20000 * k2 * m4 * T + 4 * T) + (199 * k2 * m4 * T + k2 * m4 * T) := by ring
    _ ≤ (20000 * k2 * m4 * T + 4 * (k2 * m4) * T) +
          (199 * k2 * m4 * T + k2 * m4 * T) :=
        add_le_add (add_le_add le_rfl hfourT) le_rfl
    _ = 20204 * k2 * m4 * T := by ring
end MIPStarRE.LDT.Test
