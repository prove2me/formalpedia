-- Prove2me | solution 1 for NumberField.LevelArith.levelGal_surjective_and_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c0e37f62-a429-53e3-bed9-7004cd15dba6

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_levelGal_surjective_and_ker

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField.LevelArith
open scoped NumberField.LevelArith
theorem solution
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)] :
    Function.Surjective (levelGal L F hLF) ∧ (levelGal L F hLF).ker = F.fixingSubgroup.comap L.fixingSubgroup.subtype := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Normal (↥L) (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ (↥L) (AlgebraicClosure ℚ)
  refine ⟨(AlgEquiv.restrictNormalHom_surjective _).comp (IntermediateField.fixingSubgroupEquiv L).surjective, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := levelGal_apply_coe L F hLF g ⟨x, (IntermediateField.mem_extendScalars hLF).2 hx⟩
    rw [h] at this
    exact this.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [levelGal_apply_coe]
    exact h x ((IntermediateField.mem_extendScalars hLF).1 x.2)

end S_NumberField_LevelArith_levelGal_surjective_and_ker
end P2MW
export P2MW.S_NumberField_LevelArith_levelGal_surjective_and_ker (solution)
