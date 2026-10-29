-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.lowDegreeQuestionPMF_map
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:20.822034+00:00
-- url     : https://prove2.me/submissions/50e188a3-88e3-49eb-aecf-85b859ea1529

-- Generated proof for MIPStarRE.QPBT.Palomar.lowDegreeQuestionPMF_map.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_toPMF_map

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar

/-!
# Exact bridge for the compact low individual degree game

This module identifies the compact product-space game with the existing
low-degree game.  The bridge is by explicit equivalences of question
coordinates and answer summands.  It preserves the question PMF, every branch
of the Boolean verifier, and the value of every compact strategy exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/



open scoped BigOperators

open MIPStarRE.QPBT.Palomar

open LIDT.MIPStarRE.LDT

theorem solution (P : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionPMF (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)).map
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionPairEquiv P) =
      (_root_.MIPStarRE.QPBT.ldGame P).μ.toPMF (_root_.MIPStarRE.QPBT.ldGame P).μ_prob := by
  let compactMap := fun z :
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeType × _root_.MIPStarRE.QPBT.Palomar.LowDegreeType) ×
        _root_.MIPStarRE.QPBT.Palomar.LowDegreeSpace (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P) =>
    ((z.1.1, _root_.MIPStarRE.QPBT.Palomar.lowDegreeMap (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) z.1.1 z.2),
      (z.1.2, _root_.MIPStarRE.QPBT.Palomar.lowDegreeMap (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) z.1.2 z.2))
  let originalMap := fun z :
      (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) ×
        _root_.MIPStarRE.QPBT.LdSpace P =>
    ((z.1.1, _root_.MIPStarRE.QPBT.ldCL P z.1.1 z.2),
      (z.1.2, _root_.MIPStarRE.QPBT.ldCL P z.1.2 z.2))
  have hcomm : _root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionPairEquiv P ∘ compactMap =
      originalMap ∘ _root_.MIPStarRE.QPBT.Palomar.lowDegreeSourceEquiv P := by
    funext z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact _root_.MIPStarRE.QPBT.Palomar.lowDegreeMap_equiv P z.1.1 z.2
    · apply Prod.ext
      · rfl
      · exact _root_.MIPStarRE.QPBT.Palomar.lowDegreeMap_equiv P z.1.2 z.2
  rw [show _root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionPMF (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
      (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) =
        (PMF.uniformOfFintype _).map compactMap by rfl]
  rw [PMF.map_comp, hcomm, ← PMF.map_comp]
  rw [_root_.LIDT.PMF.uniformOfFintype_map_equiv (_root_.MIPStarRE.QPBT.Palomar.lowDegreeSourceEquiv P)]
  have hmap :=
    (_root_.LIDT.MIPStarRE.LDT.Distribution.toPMF_map
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) ×
          _root_.MIPStarRE.QPBT.LdSpace P))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability
        ((_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) ×
          _root_.MIPStarRE.QPBT.LdSpace P)) originalMap).symm
  rw [_root_.LIDT.MIPStarRE.LDT.uniformDistribution_toPMF] at hmap
  simpa only [_root_.MIPStarRE.QPBT.ldGame, _root_.MIPStarRE.QPBT.ldQuestionDistribution] using hmap
