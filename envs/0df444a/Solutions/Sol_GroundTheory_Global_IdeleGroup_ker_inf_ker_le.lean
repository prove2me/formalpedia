-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.ker_inf_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:52.590257+00:00
-- url     : https://prove2.me/submissions/f9736b24-ea5f-4bc6-9033-03bcb9bbe707

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ofFinite_mul_ofInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (𝔪 : Ideal (𝓞 K)) :
    (standardOpenInfiniteHom (K := K)).ker ⊓ (standardOpenFiniteHom 𝔪).ker ≤
      ((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
        (standardOpenSubgroup K) := by
  intro u hu
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
  rw [MonoidHom.mem_ker, standardOpenInfiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [MonoidHom.mem_ker, standardOpenFiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  rw [Subgroup.mem_subgroupOf, ← ofFinite_mul_ofInfinite (u : IdeleGroup K)]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, h2, rfl⟩) (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)
end GroundTheory.Global.IdeleGroup
