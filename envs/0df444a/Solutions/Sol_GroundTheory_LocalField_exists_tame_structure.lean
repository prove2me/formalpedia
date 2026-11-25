-- Prove2me | solution 1 for GroundTheory.LocalField.exists_tame_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:57:04.123962+00:00
-- url     : https://prove2.me/submissions/9caa0d92-951e-4aed-b4bb-5a7c02d11d35

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_uniformizer_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_exists_unramified_adjoin
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree


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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ T : IntermediateField K L, IsUnramified K T ∧
      Module.finrank K T = residueDegree K L ∧ residueDegree T L = 1 ∧
      ramificationIndex T L = ramificationIndex K L ∧
      Module.finrank T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  obtain ⟨β, -, -, -, -, hun, hdeg, hres⟩ := exists_unramified_adjoin K L
  set T := K⟮(β : L)⟯
  obtain ⟨htow, hrest⟩ := exists_pow_eq_uniformizer_of_isUnramified T hres he
  have hfin : Module.finrank T L = ramificationIndex K L := by
    have := ramificationIndex_mul_residueDegree T L
    rw [hres, mul_one, htow] at this
    exact this.symm
  exact ⟨T, hun, hdeg, hres, htow, hfin, hrest⟩
end GroundTheory.LocalField
