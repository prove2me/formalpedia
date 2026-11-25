-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tateZero_integerUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:04.124021+00:00
-- url     : https://prove2.me/submissions/fcaf9c9a-07de-4526-bb5e-b0756512740b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Theorems.Thm_GroundTheory_LocalField_coe_tateNorm_integerUnits
import Theorems.Thm_GroundTheory_LocalField_exists_eq_of_forall_smul_eq
import Theorems.Thm_GroundTheory_LocalField_coe_norm_integer
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateZero_iff


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
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]
end GroundTheory.LocalField
