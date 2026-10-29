-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sum_norm_place_completedPair_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.612992+00:00
-- url     : https://prove2.me/submissions/f49db96e-3b4f-423e-8afb-3c7369bae924

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sum_norm_place_completedPair_sub_sq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_sum_option_prod_eq_of_none

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ZEvalDeficit.lean. -/
/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/



/-- The completed joint measurement has the joint effect on a pair of
evaluations. -/
theorem completedPair_effect_some {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (β × γ) d) (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) =
      Q.effect bc := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    show (Finset.univ.filter fun cd : β × γ =>
        (some cd.1, some cd.2) = (some bc.1, some bc.2)) = {bc} by
      ext cd; simp [Prod.ext_iff, eq_comm]]
  simp

/-- The completed joint measurement vanishes on outcomes outside the image of
the completion. -/
theorem completedPair_effect_eq_zero {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (β × γ) d) (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Finset.sum_eq_zero fun bc hbc =>
    absurd (Finset.mem_filter.mp hbc).2 (ho bc)





/-! ## The abstract one-point deficit -/



/-! ## The two placed deficits -/





/-! ## The two deficits over a product of restricted line-point laws -/











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}



/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) :
    S.place p (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place]

















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Completed point pairs -/









open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement)
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) (S.ExpandedLocalSpace p.side))
    (Gc : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P) →
      _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side))
    (G : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side))
    (hsome : ∀ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P, Gc (some ab.1, some ab.2) = G ab)
    (hnone1 : ∀ o2, Gc (none, o2) = 0) (hnone2 : ∀ o1, Gc (o1, none) = 0) :
    (∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place p ((Q.postprocess fun ab => (some ab.1, some ab.2)).effect o) -
            S.place p (Gc o)) S.psiHat‖ ^ 2) =
      ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (Q.effect ab) - S.place p (G ab))
          S.psiHat‖ ^ 2 := by
  refine Eq.trans (_root_.MIPStarRE.QPBT.sum_option_prod_eq_of_none _ ?_ ?_) ?_
  · intro o2
    rw [_root_.MIPStarRE.QPBT.completedPair_effect_eq_zero Q (none, o2) (fun ab => by simp), hnone1,
      _root_.MIPStarRE.QPBT.ProjectiveSetting.place_zero, sub_self]
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  · intro o1
    rw [_root_.MIPStarRE.QPBT.completedPair_effect_eq_zero Q (o1, none) (fun ab => by simp), hnone2,
      _root_.MIPStarRE.QPBT.ProjectiveSetting.place_zero, sub_self]
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  · refine Finset.sum_congr rfl fun ab _ => ?_
    rw [_root_.MIPStarRE.QPBT.completedPair_effect_some, hsome]
