-- Prove2me | solution 1 for IntermediateField.isUnramifiedOutside_normalClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d71a7a50-ec8b-57d6-ad54-4cc4dc2b2fa2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isUnramifiedOutside_normalClosure_1
set_option autoImplicit false

open IntermediateField in

theorem solution
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : F.IsUnramifiedOutside S) :
    F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ∧
    FiniteDimensional ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    IsGalois ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    ((normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ).IsUnramifiedOutside S := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  have hle : F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ := fun x hx =>
    (IntermediateField.mem_restrictScalars ℚ).2 (IntermediateField.le_normalClosure F hx)
  have hle' : (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ≤ normalClosure ℚ ↥F (AlgebraicClosure ℚ) :=
    fun x hx => (IntermediateField.mem_restrictScalars ℚ).1 hx
  exact ⟨hle, normalClosure.is_finiteDimensional ℚ ↥F (AlgebraicClosure ℚ), IsGalois.normalClosure ℚ ↥F (AlgebraicClosure ℚ),
    hF.normalClosure.of_le hle'⟩

end S_IntermediateField_isUnramifiedOutside_normalClosure_1
end P2MW
export P2MW.S_IntermediateField_isUnramifiedOutside_normalClosure_1 (solution)
