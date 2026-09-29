-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/cb320005-adcf-5d47-8656-957dcad6d3a5

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ t : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      FiniteDimensional ↥(IntermediateField.adjoin (ResidueField A) ({t} : Set ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := by
  haveI : IsAlgClosed (ResidueField ↥A) := inferInstance
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex := inferInstance
  obtain ⟨x, -, -, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (translation_mem_GammaH (q ^ 2 * M') (levelH q M'))
  exact ⟨x, hfd⟩

end S_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH (solution)
