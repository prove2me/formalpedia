-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.cascadeZeta2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:57:38.832278+00:00
-- url     : https://prove2.me/submissions/bcb487e0-eb53-4fa5-8a2d-a47b051e3ff5

-- Generated proof for MIPStarRE.LDT.Test.cascadeZeta2_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_general
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta1_bound_special
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_rpow_Z1_factor_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_stepEnvelope_rpow_eighth_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_stepEnvelope_rpow_quarter_le

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

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean. -/
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

namespace MIPStarRE.LDT

namespace Test





theorem cascadeSigma_nonneg {params : Parameters} {k : ℕ} {ν : Error}
    (hνNN : 0 ≤ ν) :
    0 ≤ cascadeSigma params k ν := by
  unfold cascadeSigma
  positivity

theorem cascadeZeta1_nonneg {params : Parameters} {k : ℕ} {eps ν : Error}
    (h : CascadeHypotheses params k eps) (hνNN : 0 ≤ ν) :
    0 ≤ cascadeZeta1 params eps (cascadeSigma params k ν) := by
  have hσNN := cascadeSigma_nonneg (params := params) (k := k) (ν := ν) hνNN
  unfold cascadeZeta1
  positivity [hσNN, h.hepsNN, h.dqNN]





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

theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _

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

theorem m4_rpow_quarter_eq {params : Parameters} :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error)) = (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (4 : Error))
    _ = (params.m : Error) := by norm_num [Real.rpow_one]

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













end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Error cascade — bounds for `ζ₂` and `ζ₃`

This module contains the middle cascade estimates used in Step 8 of the main
inductive step: the absorbing bounds for `ζ₂` and `ζ₃` obtained from the
`σ` and `ζ₁` estimates.

## References

* `references/ldt-paper/inductive_step.tex`, lines 205--217 and 230.
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)))) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 (_root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)) ≤
      2568 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  set Z1 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps (_root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
  set k2 : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)
  set m4 : _root_.LIDT.MIPStarRE.LDT.Error := (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)
  set E2048 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E8192 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (8192 : _root_.LIDT.MIPStarRE.LDT.Error) (640000 : _root_.LIDT.MIPStarRE.LDT.Error)
  set E16384 : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [Z1] using _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hE8192 : E8192 ≤ E16384 := by
    simpa [E8192, E16384] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (8192 : _root_.LIDT.MIPStarRE.LDT.Error)) (n₂ := (16384 : _root_.LIDT.MIPStarRE.LDT.Error)) (N₁ := (640000 : _root_.LIDT.MIPStarRE.LDT.Error))
      (N₂ := (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hQuarterRoot : Real.rpow Z1 (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      12 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E8192 := by
    exact _root_.LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using _root_.LIDT.MIPStarRE.LDT.Test.rpow20204_quarter_le_12)
      (hB := by simpa [k2] using _root_.LIDT.MIPStarRE.LDT.Test.k2_rpow_quarter_le (h := h))
      (hC := by simpa [m4] using (_root_.LIDT.MIPStarRE.LDT.Test.m4_rpow_quarter_eq (params := params)).le)
      (hD := by simpa [E2048, E8192] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_quarter_le (h := h))
  have hQuarterRoot' : Real.rpow Z1 (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      12 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384 := by
    calc
      Real.rpow Z1 (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 12 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E8192 := hQuarterRoot
      _ ≤ 12 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384 :=
        mul_le_mul_of_nonneg_left hE8192 (by positivity)
  have hEighthRoot : Real.rpow Z1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384 := by
    exact _root_.LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le (params := params) (k := k)
      (hZ1NN := hZ1NN) (hZ1 := hZ1) (hrNN := by positivity)
      (hk2NN := by positivity) (hm4NN := by positivity) (hE2048NN := hE2048NN)
      (hA := by simpa using _root_.LIDT.MIPStarRE.LDT.Test.rpow20204_eighth_le_4)
      (hB := by simpa [k2] using _root_.LIDT.MIPStarRE.LDT.Test.k2_rpow_eighth_le (h := h))
      (hC := by simpa [m4] using _root_.LIDT.MIPStarRE.LDT.Test.m4_rpow_eighth_le (h := h))
      (hD := by simpa [E2048, E16384] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le (h := h))
  unfold _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2
  calc
    200 * Real.rpow Z1 (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) + 42 * Real.rpow Z1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
      ≤ 200 * (12 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384) +
          42 * (4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384) := by
            nlinarith [hQuarterRoot', hEighthRoot]
    _ = 2568 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * E16384 := by ring
