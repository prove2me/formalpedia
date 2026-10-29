-- Prove2me | solution 1 for LIDT.MIPStarRE.Quantum.Submeasurement.total_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:18:37.813881+00:00
-- url     : https://prove2.me/submissions/de4ad045-eb36-40d8-8b0f-9b66dccb6cb9

-- Generated proof for MIPStarRE.Quantum.Submeasurement.total_le_one.
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib

namespace LIDT

end LIDT

open LIDT
/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed submeasurements via answer relabeling.
* `Measurement.postprocess` — the paper's postprocessing proposition for complete POVMs.
* `inconsistency` — the off-diagonal mass `∑_{a ≠ b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## References

This file builds the project's finite-dimensional measurement layer on top of
the normalized-trace and positive-operator facts in `MIPStarRE.Quantum.FiniteMatrix`
for the quantum formalization in `references/ldt-paper/`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.Quantum

/-! ## Submeasurements and measurements -/





/-! ## Totals and postprocessing -/

open LIDT.MIPStarRE.Quantum.Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

theorem solution (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) :
    M.total ≤ 1 := by
  simpa [_root_.LIDT.MIPStarRE.Quantum.Submeasurement.total] using M.sum_le_one
