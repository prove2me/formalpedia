-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.zeta3_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:12:25.127992+00:00
-- url     : https://prove2.me/submissions/6a0671b5-5354-48af-9638-ac3f3b20926b

-- Generated proof for MIPStarRE.LDT.Test.zeta3_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_cascadeZeta3_bound

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







/-- `mainFormalError` factors as `100000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem mainFormalError_eq_envelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalError params k eps =
      100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := rfl

/-- The envelope is nonnegative whenever `ε ≥ 0`. -/
theorem mainFormalEnvelope_nonneg (params : Parameters) (k : ℕ) (eps : Error)
    (heps : 0 ≤ eps) :
    0 ≤ mainFormalEnvelope params k eps := by
  unfold mainFormalEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg heps _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg (by positivity) _

















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

/-- The envelope is nonneg. -/
theorem envelope_nonneg : 0 ≤ mainFormalEnvelope params k eps :=
  mainFormalEnvelope_nonneg params k eps h.hepsNN

















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



theorem mainFormalEnvelope_eq_stepEnvelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalEnvelope params k eps =
      stepEnvelope params k eps (40000 : Error) (2560000 : Error) := rfl

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

/-- A paper-local envelope with exponent `1/n` and decay scale `N` is absorbed
by `mainFormalEnvelope` whenever `n ≤ 40000` and `N ≤ 2560000`. -/
theorem stepEnvelope_le_mainFormalEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error}
    (hnPos : 0 < n) (hn : n ≤ 40000) (hNPos : 0 < N) (hN : N ≤ 2560000) :
    stepEnvelope params k eps n N ≤ mainFormalEnvelope params k eps := by
  calc
    stepEnvelope params k eps n N ≤ stepEnvelope params k eps (40000 : Error) (2560000 : Error) :=
      stepEnvelope_le_stepEnvelope (h := h) (hn₁Pos := hnPos) (hn := hn)
        (hN₁Pos := hNPos) (hN := hN)
    _ = mainFormalEnvelope params k eps := by rw [mainFormalEnvelope_eq_stepEnvelope]

























































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
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ : _root_.LIDT.MIPStarRE.LDT.Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (1024 : _root_.LIDT.MIPStarRE.LDT.Error))))
    (hσEq : σ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta2 ζ₁) :
    _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3 ζ₁ ζ₂ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
  rw [hζ₂Eq, hζ₁Eq, hσEq, _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError_eq_envelope]
  have hζ₃ := _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error) ≤
        _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
    _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (1280000 : _root_.LIDT.MIPStarRE.LDT.Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 150000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₃.trans ?_
  calc
    150000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (16384 : _root_.LIDT.MIPStarRE.LDT.Error) (1280000 : _root_.LIDT.MIPStarRE.LDT.Error)
      ≤ 150000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (150000 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)))) *
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps := by ring
    _ ≤ (200000 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)))) *
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (150000 : Error) ≤ 200000) hk2m4NN) hENN
    _ = 2 *
          (100000 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
            _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps) := by ring
