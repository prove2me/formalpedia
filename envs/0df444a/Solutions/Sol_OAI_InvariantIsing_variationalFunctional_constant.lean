-- Prove2me | solution 1 for OAI.InvariantIsing.variationalFunctional_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:28.049822+00:00
-- url     : https://prove2.me/submissions/42cdc56d-88a2-4b3c-b159-2cc81fa3695c

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_entropyFunctional_zero

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma spectralFunctional_constant (a : ℝ) (p : OverlapPath) :
    spectralFunctional (fun _ => a) p = a / 2 := by
  simp [spectralFunctional]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma variationalFunctional_constant_oai (a : ℝ) :
    variationalFunctional (fun _ => a) = ((a / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · have hi := iInf_le (fun p : OverlapPath =>
      entropyFunctional p + (spectralFunctional (fun _ => a) p : EReal))
      (constantPath 0 (by constructor <;> norm_num))
    simpa only [variationalFunctional, entropyFunctional_zero, spectralFunctional_constant,
      zero_add] using hi
  · apply le_iInf
    intro p
    rw [spectralFunctional_constant]
    simpa only [zero_add] using add_le_add (entropyFunctional_nonneg p)
      (le_rfl : ((a / 2 : ℝ) : EReal) ≤ ((a / 2 : ℝ) : EReal))

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.variationalFunctional_constant_oai := @OAI.InvariantIsing.variationalFunctional_constant_oai
