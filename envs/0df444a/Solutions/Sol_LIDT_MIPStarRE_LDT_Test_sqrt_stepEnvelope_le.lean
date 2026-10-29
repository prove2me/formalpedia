-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:40:46.019796+00:00
-- url     : https://prove2.me/submissions/1398c4b6-a58c-4935-a527-17088185c6e8

-- Generated proof for MIPStarRE.LDT.Test.sqrt_stepEnvelope_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_rpow_one_div

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

















theorem sqrt_exp_neg_div (k : ℕ) (m N : Error) (hm : 0 < m) (hN : 0 < N) :
    Real.sqrt (Real.exp (-((k : Error) / (N * m ^ (2 : ℕ))))) =
      Real.exp (-((k : Error) / ((2 * N) * m ^ (2 : ℕ)))) := by
  rw [← Real.exp_half]
  congr 1
  field_simp [hm.ne', hN.ne']





















































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
    (h : _root_.LIDT.MIPStarRE.LDT.Test.CascadeHypotheses params k eps) {n N : _root_.LIDT.MIPStarRE.LDT.Error} (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps n N) ≤ _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by
  have hmPos : 0 < (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by linarith [h.hm]
  unfold _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope
  calc
    Real.sqrt
        (Real.rpow eps (1 / n) +
          Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / n) +
          Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (N * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))))
      ≤ Real.sqrt (Real.rpow eps (1 / n)) +
          Real.sqrt (Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / n)) +
          Real.sqrt (Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (N * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))) :=
        _root_.LIDT.MIPStarRE.LDT.sqrt_add3_le_add3_sqrt (Real.rpow_nonneg h.hepsNN _) (Real.rpow_nonneg h.dqNN _)
          (Real.exp_nonneg _)
    _ = _root_.LIDT.MIPStarRE.LDT.Test.stepEnvelope params k eps (2 * n) (2 * N) := by
      rw [_root_.LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div h.hepsNN hn, _root_.LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div h.dqNN hn,
        _root_.LIDT.MIPStarRE.LDT.Test.sqrt_exp_neg_div k (params.m : _root_.LIDT.MIPStarRE.LDT.Error) N hmPos hN]
      rfl
