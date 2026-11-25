-- Prove2me | solution 1 for GroundTheory.Global.RayClassGroup.finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:27.103353+00:00
-- url     : https://prove2.me/submissions/02b75a3f-e820-44cd-905e-7b4590588900

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Theorems.Thm_GroundTheory_Global_IdeleGroup_rayGroup_le
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finite_quotient_idealLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ker_inf_ker_le

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
open IdeleGroup
namespace GroundTheory.Global
namespace RayClassGroup
theorem _root_.solution {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (RayClassGroup K 𝔪) := by
  set R := rayGroup K 𝔪
  set U := standardOpenSubgroup K
  set M := (diagonal K).range ⊔ U

  have hM : M.FiniteIndex := by
    rw [show M = (IdeleGroup.toClassGroup (K := K)).ker from (ker_toClassGroup).symm]
    exact Subgroup.finiteIndex_ker _

  have : Finite ((InfiniteAdeleRing K)ˣ ⧸ infinitePositive K) :=
    Subgroup.finite_quotient_of_finiteIndex
  have : Finite (finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0)) :=
    finite_quotient_idealLevel h𝔪
  have : Finite (standardOpenInfiniteHom (K := K)).range :=
    Finite.of_injective _ Subtype.val_injective
  have : Finite (standardOpenFiniteHom (K := K) 𝔪).range :=
    Finite.of_injective _ Subtype.val_injective
  have : (standardOpenInfiniteHom (K := K)).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have : (standardOpenFiniteHom (K := K) 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : (((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
      U).FiniteIndex := Subgroup.finiteIndex_of_le (ker_inf_ker_le 𝔪)
  have hWP : (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤ R :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h3 : (R.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le fun x hx ↦ Subgroup.mem_subgroupOf.2 (hWP (Subgroup.mem_subgroupOf.1 hx))

  have hUR : U ⊔ R = M :=
    le_antisymm (sup_le le_sup_right (rayGroup_le 𝔪))
      (sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left)
  have hRM : R.relIndex M ≠ 0 := by
    rw [← hUR, Subgroup.relIndex_sup_right]
    exact h3.index_ne_zero
  have hR : R.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (rayGroup_le 𝔪)]
    exact mul_ne_zero hRM hM.index_ne_zero
  exact Subgroup.index_ne_zero_iff_finite.1 hR
end RayClassGroup
end GroundTheory.Global
