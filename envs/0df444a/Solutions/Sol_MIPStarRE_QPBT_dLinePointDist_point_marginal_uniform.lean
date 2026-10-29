-- Prove2me | solution 1 for MIPStarRE.QPBT.dLinePointDist_point_marginal_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:45.897986+00:00
-- url     : https://prove2.me/submissions/682e7a2e-bffc-4671-8270-796d598c4ca7

-- Generated proof for MIPStarRE.QPBT.dLinePointDist_point_marginal_uniform.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_ldSeed

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/LowDegreeGameMeasurements.lean. -/
/-!
# Low-degree sampling and polynomial measurements

The low-degree question laws have uniform point and coordinate-index marginals,
and every sampled line is incident to its paired point.  Polynomial outcomes
are bounded multivariate polynomials. The soundness theorem using these
definitions is proved in `LowDegreeGameTheorems`.

## References

The principal definition and theorem are blueprint `def:ld-meas` and
`lem:ld-soundness`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/



/-- Formalization-only auxiliary lemma: the point block of a uniformly random
ambient vector is uniform. -/
private theorem map_uniformDistribution_point (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.point =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) := by
  have hsplit : (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map (_root_.MIPStarRE.QPBT.ldSpaceSplit L) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) :=
    _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.ldSpaceSplit L)
  calc
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.point
        = (((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map (_root_.MIPStarRE.QPBT.ldSpaceSplit L)).map
            Prod.fst).map Prod.fst := by
          rw [_root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
          rfl
    _ = ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))).map
            Prod.fst).map Prod.fst := by rw [hsplit]
    _ = (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L)).map Prod.fst := by
          rw [_root_.MIPStarRE.QPBT.uniformDistribution_map_fst]
    _ = _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) := _root_.MIPStarRE.QPBT.uniformDistribution_map_fst











































end

end MIPStarRE.QPBT

/-!
# Low-degree sampling and polynomial measurements

The low-degree question laws have uniform point and coordinate-index marginals,
and every sampled line is incident to its paired point.  Polynomial outcomes
are bounded multivariate polynomials. The soundness theorem using these
definitions is proved in `LowDegreeGameTheorems`.

## References

The principal definition and theorem are blueprint `def:ld-meas` and
`lem:ld-soundness`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.MIPStarRE.QPBT.dLinePointDist L).map Prod.snd =
        _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) ∧
      (_root_.MIPStarRE.QPBT.dLinePointDist L).map (fun sample => _root_.MIPStarRE.QPBT.chiIndex L sample.1.seed) =
        _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m) := by
  constructor
  · have hmap : (_root_.MIPStarRE.QPBT.dLinePointDist L).map Prod.snd
        = (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.point := by
      change ((((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
          fun z => (_root_.MIPStarRE.QPBT.ldDLineCL L z, _root_.MIPStarRE.QPBT.ldPointCL L z)).map
          fun s => (_root_.MIPStarRE.QPBT.dLineDescOf L s.1, _root_.MIPStarRE.QPBT.LdSpace.point s.2)).map Prod.snd) = _
      rw [_root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
      rfl
    rw [hmap, map_uniformDistribution_point]
  · have hmap : (_root_.MIPStarRE.QPBT.dLinePointDist L).map (fun sample => _root_.MIPStarRE.QPBT.chiIndex L sample.1.seed)
        = ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.seed).map (_root_.MIPStarRE.QPBT.chiIndex L) := by
      change ((((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
          fun z => (_root_.MIPStarRE.QPBT.ldDLineCL L z, _root_.MIPStarRE.QPBT.ldPointCL L z)).map
          fun s => (_root_.MIPStarRE.QPBT.dLineDescOf L s.1, _root_.MIPStarRE.QPBT.LdSpace.point s.2)).map
          fun sample => _root_.MIPStarRE.QPBT.chiIndex L sample.1.seed) = _
      rw [_root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
      rfl
    rw [hmap, _root_.MIPStarRE.QPBT.uniformDistribution_map_ldSeed, _root_.MIPStarRE.QPBT.uniformDistribution_map_chiIndex]
