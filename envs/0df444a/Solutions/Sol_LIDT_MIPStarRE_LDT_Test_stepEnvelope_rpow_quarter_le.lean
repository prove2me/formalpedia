-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_quarter_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:47:16.044918+00:00
-- url     : https://prove2.me/submissions/0a7ed678-b7b1-46af-bdf3-90bc83d2fac4

-- Generated proof for MIPStarRE.LDT.Test.stepEnvelope_rpow_quarter_le.
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
      rfl











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

theorem solution {params : _root_.LIDT.MIPStarRE.LDT.Parameters} {k : ℕ} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) :
    Real.rpow (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (8192 : _root_.LIDT.MIPStarRE.LDT.Error) (640000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  have h1 : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (4096 : _root_.LIDT.MIPStarRE.LDT.Error) (320000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
    simpa [show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 2048 = 4096 by norm_num,
      show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 160000 = 320000 by norm_num] using
      _root_.LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
        (by norm_num) (by norm_num)
  have h2 : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (4096 : _root_.LIDT.MIPStarRE.LDT.Error) (320000 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
      _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (8192 : _root_.LIDT.MIPStarRE.LDT.Error) (640000 : _root_.LIDT.MIPStarRE.LDT.Error) := by
    simpa [show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 4096 = 8192 by norm_num,
      show (2 : _root_.LIDT.MIPStarRE.LDT.Error) * 320000 = 640000 by norm_num] using
      _root_.LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le (h := h) (n := (4096 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (320000 : _root_.LIDT.MIPStarRE.LDT.Error))
        (by norm_num) (by norm_num)
  have hnn : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error) :=
    _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope_nonneg (h := h) (n := (2048 : _root_.LIDT.MIPStarRE.LDT.Error)) (N := (160000 : _root_.LIDT.MIPStarRE.LDT.Error))
  calc
    Real.rpow (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))
      = Real.sqrt (Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2048 : _root_.LIDT.MIPStarRE.LDT.Error) (160000 : _root_.LIDT.MIPStarRE.LDT.Error))) :=
        _root_.LIDT.MIPStarRE.LDT.Test.rpow_one_four_eq_sqrt_sqrt hnn
    _ ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (4096 : _root_.LIDT.MIPStarRE.LDT.Error) (320000 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
      Real.sqrt_le_sqrt h1
    _ ≤ _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (8192 : _root_.LIDT.MIPStarRE.LDT.Error) (640000 : _root_.LIDT.MIPStarRE.LDT.Error) := h2
