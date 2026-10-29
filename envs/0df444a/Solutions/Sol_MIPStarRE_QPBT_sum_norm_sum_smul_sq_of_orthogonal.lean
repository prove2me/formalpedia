-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_norm_sum_smul_sq_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.367603+00:00
-- url     : https://prove2.me/submissions/e03dfa6a-4513-4f8b-b332-51e1e8255c09

-- Generated proof for MIPStarRE.QPBT.sum_norm_sum_smul_sq_of_orthogonal.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries





/-! ## Parseval's identity for an orthogonal system of coefficients -/

theorem solution {I J E : Type*} [Fintype I]
    [DecidableEq I] [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : J → I → ℂ) (N : ℝ)
    (horth : ∀ i i', ∑ j, (starRingEnd ℂ) (c j i) * c j i' =
      if i = i' then (N : ℂ) else 0)
    (v : I → E) :
    ∑ j, ‖∑ i, c j i • v i‖ ^ 2 = N * ∑ i, ‖v i‖ ^ 2 := by
  have hnorm : ∀ x : E, ‖x‖ ^ 2 = (inner ℂ x x).re := fun x => by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have hj : ∀ j, ‖∑ i, c j i • v i‖ ^ 2 =
      (∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
        inner ℂ (v i) (v i')).re := by
    intro j
    rw [hnorm, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    ring
  have hsum : ∑ j, ∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
      inner ℂ (v i) (v i') = ∑ i, (N : ℂ) * inner ℂ (v i) (v i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    calc ∑ i', ∑ j, ((starRingEnd ℂ) (c j i) * c j i') * inner ℂ (v i) (v i')
        = ∑ i', (∑ j, (starRingEnd ℂ) (c j i) * c j i') *
            inner ℂ (v i) (v i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i', (if i = i' then (N : ℂ) else 0) * inner ℂ (v i) (v i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [horth]
      _ = (N : ℂ) * inner ℂ (v i) (v i) := by
          simp [ite_mul]
  calc ∑ j, ‖∑ i, c j i • v i‖ ^ 2
      = (∑ j, ∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') *
          inner ℂ (v i) (v i')).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun j _ => hj j
    _ = (∑ i, (N : ℂ) * inner ℂ (v i) (v i)).re := by rw [hsum]
    _ = N * ∑ i, ‖v i‖ ^ 2 := by
        rw [Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, ← hnorm]
