-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_option_prod_eq_of_none
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:56.701171+00:00
-- url     : https://prove2.me/submissions/99669419-7af6-4639-b34d-587df1f24855

-- Generated proof for MIPStarRE.QPBT.sum_option_prod_eq_of_none.
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
import Mathlib.Analysis.MeanInequalitiesPow

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

theorem solution {β γ : Type*} [Fintype β] [Fintype γ]
    (F : Option β × Option γ → ℝ) (h1 : ∀ o2, F (none, o2) = 0)
    (h2 : ∀ o1, F (o1, none) = 0) :
    (∑ o, F o) = ∑ bc : β × γ, F (some bc.1, some bc.2) := by
  calc (∑ o : Option β × Option γ, F o)
      = ∑ o1 : Option β, ∑ o2 : Option γ, F (o1, o2) := Fintype.sum_prod_type (f := F)
    _ = (∑ o2 : Option γ, F (none, o2)) +
          ∑ b : β, ∑ o2 : Option γ, F (some b, o2) := Fintype.sum_option _
    _ = ∑ b : β, ∑ o2 : Option γ, F (some b, o2) := by
        rw [Finset.sum_eq_zero fun o2 _ => h1 o2, zero_add]
    _ = ∑ b : β, (F (some b, none) + ∑ c : γ, F (some b, some c)) :=
        Finset.sum_congr rfl fun b _ => Fintype.sum_option _
    _ = ∑ b : β, ∑ c : γ, F (some b, some c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [h2 (some b), zero_add]
    _ = ∑ bc : β × γ, F (some bc.1, some bc.2) :=
        (Fintype.sum_prod_type (f := fun bc : β × γ => F (some bc.1, some bc.2))).symm
