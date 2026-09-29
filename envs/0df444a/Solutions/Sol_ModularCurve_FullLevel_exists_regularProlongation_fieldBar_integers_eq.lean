-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6cb89603-3410-5616-87c3-47e14649bcc6

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ R : RegularProlongation A (fieldBar q M')
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))),
      R.integers = O ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  obtain ⟨R, hR1, hR2⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (AlgebraicClosure ℚ) A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) hT
  refine ⟨R, ?_, hR2⟩
  ext f
  exact (hR1 f).trans (hO f).symm

end S_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq (solution)
