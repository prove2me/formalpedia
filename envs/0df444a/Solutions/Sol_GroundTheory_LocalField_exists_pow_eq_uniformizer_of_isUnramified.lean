-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_eq_uniformizer_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:12.976241+00:00
-- url     : https://prove2.me/submissions/9eaf4e9c-525e-44f0-b146-2f1b3fa0803f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
import Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_uniformizer_of_residueDegree_eq_one
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_tower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped IntermediateField
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution (T : IntermediateField K L) [IsUnramified K T]
    (hf : residueDegree T L = 1) (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ramificationIndex T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  have htow : ramificationIndex T L = ramificationIndex K L := by
    rw [ramificationIndex_tower K T L, IsUnramified.ramificationIndex_eq_one (K := K) (L := T), one_mul]
  have he' : Nat.Coprime (ramificationIndex T L) (ringChar 𝓀[T]) := by
    rw [htow, ← Algebra.ringChar_eq 𝓀[K] 𝓀[T]]
    exact he
  refine ⟨htow, ?_⟩
  rw [← htow]
  exact exists_pow_eq_uniformizer_of_residueDegree_eq_one T L hf he'
end GroundTheory.LocalField
