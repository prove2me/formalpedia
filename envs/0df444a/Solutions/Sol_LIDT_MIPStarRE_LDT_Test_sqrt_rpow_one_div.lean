-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.427899+00:00
-- url     : https://prove2.me/submissions/1760fe38-170b-4df2-8e90-442341a48d3a

-- Generated proof for MIPStarRE.LDT.Test.sqrt_rpow_one_div.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Mathlib

namespace LIDT

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

theorem solution {x n : _root_.LIDT.MIPStarRE.LDT.Error} (hx : 0 ≤ x) (_hn : 0 < n) :
    Real.sqrt (Real.rpow x (1 / n)) = Real.rpow x (1 / (2 * n)) := by
  have hn0 : n ≠ 0 := by linarith
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x (1 / n)) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))
      = Real.rpow x ((1 / n) * (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
          simpa using (Real.rpow_mul hx (1 / n) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))).symm
    _ = Real.rpow x (1 / (2 * n)) := by
      field_simp [hn0]
