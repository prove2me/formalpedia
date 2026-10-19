-- Prove2me | solution 1 for MIPStarRE.LDT.Test.cascadeZeta1_bound_special
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:20.69848+00:00
-- url     : https://prove2.me/submissions/21be6ae2-4a43-4671-98a9-a89624b07424

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
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean (solution of MIPStarRE.LDT.Test.cascadeZeta1_bound_special);
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
theorem self_le_rpow_one_div {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hn : 1 ≤ n) :
    x ≤ Real.rpow x (1 / n) := by
  have hnPos : 0 < n := by linarith
  have hdiv : 1 / n ≤ (1 : Error) := by
    field_simp [hnPos.ne']
    linarith
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n by positivity) hdiv)
end
end MIPStarRE.LDT.Test

namespace MIPStarRE.LDT.Test
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem two_sqrt40005_le_401 : 2 * Real.sqrt (40005 : Error) ≤ 401 := by
  have hsqrt : Real.sqrt (40005 : Error) ≤ 401 / 2 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor <;> norm_num
  nlinarith
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
    (hkm1 : k = 1 ∧ params.m = 1) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  rcases hkm1 with ⟨rfl, hm1⟩
  have hm_cast : (params.m : Error) = 1 := by exact_mod_cast hm1
  set a : Error := Real.rpow eps (1 / (2048 : Error))
  set b : Error := Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error))
  set c : Error := Real.exp (-(1 : Error) / (160000 : Error))
  have heps1024 : Real.rpow eps (1 / (1024 : Error)) ≤ a := by
    simpa [a] using rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hdq1024 : Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤ b := by
    simpa [b] using rpow_le_of_denom_le h.dqNN h.dqLeOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hνab : ν ≤ 10000 * (a + b) := by
    calc
      ν ≤ 10000 * (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
            simpa [hm_cast] using hν
      _ ≤ 10000 * (a + b) := by nlinarith [heps1024, hdq1024]
  have hExp80000_le_c :
      Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤ c := by
    calc
      Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
          = Real.exp (-(1 : Error) / (80000 : Error)) := by norm_num [hm_cast]
      _ ≤ Real.exp (-(1 : Error) / (160000 : Error)) := by
            exact Real.exp_le_exp.mpr (by norm_num)
      _ = c := by rfl
  have hσab : cascadeSigma params 1 ν ≤ 10000 * (a + b) + c := by
    have htmp : ν + Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        10000 * (a + b) + c := by
      nlinarith [hνab, hExp80000_le_c]
    simpa [cascadeSigma, hm_cast] using htmp
  have ha_le_one : a ≤ 1 := by
    unfold a
    exact Real.rpow_le_one h.hepsNN h.hepsOne (by positivity)
  have hb_le_one : b ≤ 1 := by
    unfold b
    exact Real.rpow_le_one h.dqNN h.dqLeOne (by positivity)
  have hc_le_one : c ≤ 1 := by
    unfold c
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hσ_le_20001 : cascadeSigma params 1 ν ≤ 20001 := by
    nlinarith [hσab, ha_le_one, hb_le_one, hc_le_one]
  have hsqrt_le_401 : 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ 401 := by
    have hinside : 3 * eps + 2 * cascadeSigma params 1 ν ≤ 40005 := by
      nlinarith [h.hepsOne, hσ_le_20001]
    have hsqrt : Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ Real.sqrt (40005 : Error) :=
      Real.sqrt_le_sqrt hinside
    nlinarith [hsqrt, two_sqrt40005_le_401]
  have hdq_le_b : (params.d : Error) / (params.q : Error) ≤ b := by
    exact self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)
  have hc_ge_quarter : (1 / 4 : Error) ≤ c := by
    have hexp_neg_one : Real.exp (- (1 : Error)) ≤ c := by
      unfold c
      exact Real.exp_le_exp.mpr (by norm_num)
    have hquarter_lt : (1 / 4 : Error) < Real.exp (- (1 : Error)) := by
      linarith [Real.exp_neg_one_gt_d9]
    exact hquarter_lt.le.trans hexp_neg_one
  have hconst : (401 : Error) ≤ 20202 * c := by
    nlinarith [hc_ge_quarter]
  have htarget :
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
        ≤ 20204 * (a + b + c) := by
    have htwoσ : 2 * cascadeSigma params 1 ν ≤ 20000 * (a + b) + 2 * c := by
      nlinarith [hσab]
    calc
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
          ≤ (20000 * (a + b) + 2 * c) + 401 + b := by
            nlinarith [htwoσ, hsqrt_le_401, hdq_le_b]
      _ ≤ 20204 * (a + b + c) := by
            nlinarith [hconst,
              show 0 ≤ a by
                unfold a
                exact Real.rpow_nonneg h.hepsNN _,
              show 0 ≤ b by
                unfold b
                exact Real.rpow_nonneg h.dqNN _]
  have hEnv : stepEnvelope params 1 eps (2048 : Error) (160000 : Error) = a + b + c := by
    unfold stepEnvelope a b c
    norm_num [hm_cast]
  simpa [cascadeZeta1, hm_cast, hEnv] using htarget
end MIPStarRE.LDT.Test
