-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:47:16.269809+00:00
-- url     : https://prove2.me/submissions/b07a2b75-f8f6-4e4e-8c8c-bef8cac6e084

-- Generated proof for MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_stepEnvelope_le

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









theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _











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

















































end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
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

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps x C n N : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps)
    (hC : 0 ≤ C)
    (hx : x ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N)
    (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt x ≤
      Real.sqrt C * (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
        _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by
  set E : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N)
  have hE_sq : _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N ≤ E ^ (2 : ℕ) := by
    simpa [E] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_le_sq_stepEnvelope (h := h) (n := n) (N := N) hn hN
  have hCoeffNN : 0 ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) := by positivity
  have hENN : 0 ≤ E := by
    simpa [E] using _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := 2 * n) (N := 2 * N)
  have hx' : x ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) := by
    calc
      x ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) *
            _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N := hx
      _ ≤ C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hE_sq hCoeffNN
  set u : _root_.LIDT.MIPStarRE.LDT.Error := (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * E
  have huNN : 0 ≤ u := by
    dsimp [u]
    positivity [hENN]
  have hsqrt := Real.sqrt_le_sqrt hx'
  calc
    Real.sqrt x ≤
        Real.sqrt (C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) * E ^ (2 : ℕ)) :=
      hsqrt
    _ = Real.sqrt (C * (u ^ (2 : ℕ))) := by
      rw [show C * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) =
          C * (u ^ (2 : ℕ)) by
        dsimp [u]
        ring]
    _ = Real.sqrt C * u := by
      rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg huNN]
    _ = Real.sqrt C * (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
          _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by
      simp [u, E]
      ring
