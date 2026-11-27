-- Prove2me | solution 1 for GroundTheory.Global.Artin.character_ind_restrictScalarsHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:35.101546+00:00
-- url     : https://prove2.me/submissions/7347d829-bafc-48d1-9c10-e74a28e8a2f6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_IsProjEigenspaceNegOneOfMulSelfEqOne
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_GammaInduction
import Theorems.Thm_GroundTheory_Global_Artin_indFun_mulEquiv
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_character_ind
import Theorems.Thm_GroundTheory_LocalField_indFun_indFun
import Theorems.Thm_GroundTheory_LocalField_isCharacter_character


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField NumberField.InfinitePlace IntermediateField Module GroundTheory.LocalField _root_.Complex
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)
omit [IsGalois K L]
open Classical
namespace GroundTheory.Global.Artin
theorem _root_.solution :
    (ρ.ind (AlgEquiv.restrictScalarsHom K)).character = indFun H.subtype (charOnSubgroup H ρ) := by
  rw [character_ind]
  have hφ : (AlgEquiv.restrictScalarsHom K : Gal(L/fixedField H) →* Gal(L/K)) =
      H.subtype.comp (fixedFieldMulEquiv H).symm.toMonoidHom := MonoidHom.ext fun _ ↦ rfl
  rw [hφ, ← indFun_indFun, indFun_mulEquiv (fixedFieldMulEquiv H).symm
    (isCharacter_character ρ).isClassFun]
  rfl
end GroundTheory.Global.Artin
