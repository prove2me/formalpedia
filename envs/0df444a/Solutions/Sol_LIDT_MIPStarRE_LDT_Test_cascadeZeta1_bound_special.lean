-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound_special
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.923002+00:00
-- url     : https://prove2.me/submissions/cd10ed2c-9a44-4889-a6fe-07f594b3e253

-- Generated proof for MIPStarRE.LDT.Test.cascadeZeta1_bound_special.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean. -/
/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test



























namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h

/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le

/-- `d/q ≤ 1` under the standing hypotheses. -/
theorem dqLeOne : (params.d : Error) / (params.q : Error) ≤ 1 :=
  (div_le_one h.hqPos).mpr h.hdq



















end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean. -/
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

namespace MIPStarRE.LDT

namespace Test





/-- For `x ∈ [0, 1]`, enlarging the denominator in `x^(1/n)` makes the
exponent smaller and therefore the value larger. -/
theorem rpow_le_of_denom_le {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n₁ n₂ : Error} (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) :
    Real.rpow x (1 / n₁) ≤ Real.rpow x (1 / n₂) := by
  have hn₂Pos : 0 < n₂ := lt_of_lt_of_le hn₁Pos hn
  have hdiv : 1 / n₂ ≤ 1 / n₁ := one_div_le_one_div_of_le hn₁Pos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n₂ by positivity) hdiv

















theorem self_le_rpow_one_div {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hn : 1 ≤ n) :
    x ≤ Real.rpow x (1 / n) := by
  have hnPos : 0 < n := by linarith
  have hdiv : 1 / n ≤ (1 : Error) := by
    field_simp [hnPos.ne']
    linarith
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n by positivity) hdiv)





















theorem two_sqrt40005_le_401 : 2 * Real.sqrt (40005 : Error) ≤ 401 := by
  have hsqrt : Real.sqrt (40005 : Error) ≤ 401 / 2 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor <;> norm_num
  nlinarith

























end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — bounds for `σ` and `ζ₁`

This module proves the tight and absorbing bounds for the first two cascade
variables, `σ` and `ζ₁`.  The later variables `ζ₂`, `ζ₃`, and `ζ₄`, together
with the top-level consolidator `errorCascade_le_mainFormalError`, are in the
subsequent leaves of `Test.MainTheorem.ScalarBounds.CascadeBounds`.

The first cascade steps have three components:

* The **tight cascade bound** (`cascadeSigma_tight_bound`, `cascadeZeta1_bound`, …),
  deriving the native estimate directly from the cascade definition.
* The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …), coarsening the
  tight estimate to the final `mainFormalEnvelope` envelope.
* The corresponding nonnegativity lemmas (`cascadeSigma_nonneg`,
  `cascadeZeta1_nonneg`), used by the later cascade estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section


open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error}
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hkm1 : k = 1 ∧ params.m = 1) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν) ≤
      20204 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  rcases hkm1 with ⟨rfl, hm1⟩
  have hm_cast : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) = 1 := by exact_mod_cast hm1
  set a : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow eps (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error))
  set b : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (2048 : _root_.LIDT.MIPStarRE.LDT.Error))
  set c : _root_.LIDT.MIPStarRE.LDT.Error := Real.exp (-(1 : _root_.LIDT.MIPStarRE.LDT.Error) / (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have heps1024 : Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ a := by
    simpa [a] using _root_.LIDT.MIPStarRE.LDT.Test.rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
      (n₂ := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hdq1024 : Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ b := by
    simpa [b] using _root_.LIDT.MIPStarRE.LDT.Test.rpow_le_of_denom_le h.dqNN h.dqLeOne (n₁ := (1024 : _root_.LIDT.MIPStarRE.LDT.Error))
      (n₂ := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hνab : ν ≤ 10000 * (a + b) := by
    calc
      ν ≤ 10000 * (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
            simpa [hm_cast] using hν
      _ ≤ 10000 * (a + b) := by nlinarith [heps1024, hdq1024]
  have hExp80000_le_c :
      Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) ≤ c := by
    calc
      Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))
          = Real.exp (-(1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num [hm_cast]
      _ ≤ Real.exp (-(1 : _root_.LIDT.MIPStarRE.LDT.Error) / (160000 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            exact Real.exp_le_exp.mpr (by norm_num)
      _ = c := by rfl
  have hσab : _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν ≤ 10000 * (a + b) + c := by
    have htmp : ν + Real.exp (-((1 : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) ≤
        10000 * (a + b) + c := by
      nlinarith [hνab, hExp80000_le_c]
    simpa [_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma, hm_cast] using htmp
  have ha_le_one : a ≤ 1 := by
    unfold a
    exact Real.rpow_le_one h.hepsNN h.hepsOne (by positivity)
  have hb_le_one : b ≤ 1 := by
    unfold b
    exact Real.rpow_le_one h.dqNN h.dqLeOne (by positivity)
  have hc_le_one : c ≤ 1 := by
    unfold c
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hσ_le_20001 : _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν ≤ 20001 := by
    nlinarith [hσab, ha_le_one, hb_le_one, hc_le_one]
  have hsqrt_le_401 : 2 * Real.sqrt (3 * eps + 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν) ≤ 401 := by
    have hinside : 3 * eps + 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν ≤ 40005 := by
      nlinarith [h.hepsOne, hσ_le_20001]
    have hsqrt : Real.sqrt (3 * eps + 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν) ≤ Real.sqrt (40005 : _root_.LIDT.MIPStarRE.LDT.Error) :=
      Real.sqrt_le_sqrt hinside
    nlinarith [hsqrt, _root_.LIDT.MIPStarRE.LDT.Test.two_sqrt40005_le_401]
  have hdq_le_b : (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ b := by
    exact _root_.LIDT.MIPStarRE.LDT.Test.self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)
  have hc_ge_quarter : (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ c := by
    have hexp_neg_one : Real.exp (- (1 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ c := by
      unfold c
      exact Real.exp_le_exp.mpr (by norm_num)
    have hquarter_lt : (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) < Real.exp (- (1 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      linarith [Real.exp_neg_one_gt_d9]
    exact hquarter_lt.le.trans hexp_neg_one
  have hconst : (401 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 20202 * c := by
    nlinarith [hc_ge_quarter]
  have htarget :
      2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν) +
          (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
        ≤ 20204 * (a + b + c) := by
    have htwoσ : 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν ≤ 20000 * (a + b) + 2 * c := by
      nlinarith [hσab]
    calc
      2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params 1 ν) +
          (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
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
  have hEnv : _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params 1 eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) = a + b + c := by
    unfold _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope a b c
    norm_num [hm_cast]
  simpa [_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1, hm_cast, hEnv] using htarget
