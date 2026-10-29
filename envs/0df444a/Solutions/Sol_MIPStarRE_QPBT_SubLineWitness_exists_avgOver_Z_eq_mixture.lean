-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.exists_avgOver_Z_eq_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:21.788057+00:00
-- url     : https://prove2.me/submissions/5996a387-9052-4750-8ca6-b64aa8d1a817

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.exists_avgOver_Z_eq_mixture.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_left
import Theorems.Thm_MIPStarRE_QPBT_avgOver_bind

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Regrouping the line answers by their evaluations -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P)
    (F : (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) ×
      (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) → ℝ) :
    ∃ components : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.SubLineComponent P), components.IsProbability ∧
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
            (fun t => F (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver components (fun c =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.1)
              (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.2))
            (fun w => F ((w.1.1, w.2.1), w.2.2))) := by
  obtain ⟨components, hcomp, -, hZ⟩ := sublines.source_mixture
  refine ⟨components, hcomp, ?_⟩
  have h1 : _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun t => F (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver ((_root_.MIPStarRE.QPBT.subLinePointDist P sublines.D).map _root_.MIPStarRE.QPBT.subLineZProjection) F := by
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.subLinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map,
      _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    rfl
  rw [h1, hZ, _root_.MIPStarRE.QPBT.avgOver_bind]
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun c => ?_
  rw [_root_.MIPStarRE.QPBT.subLineZComponentDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.Distribution.prod_map_left,
    _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
