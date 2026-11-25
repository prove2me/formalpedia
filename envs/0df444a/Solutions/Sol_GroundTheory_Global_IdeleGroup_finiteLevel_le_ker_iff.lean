-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteLevel_le_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:35.626228+00:00
-- url     : https://prove2.me/submissions/440f7ba8-9f75-4e35-a286-2b7d01032c56

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsSingle_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_finiteLevel_le_ker
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_unitsLevel_antitone
import Theorems.Thm_GroundTheory_Global_unitsLevel_le_ker_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle

set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
variable {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ χ.ker ↔ ∀ v, conductorExponentAt χ v ≤ n v := by
  have hloc : ∀ v, Continuous (χ.comp (finiteUnitsSingle v)) := fun v ↦
    hχ.comp (continuous_finiteUnitsSingle v)
  constructor
  · intro h v
    rw [conductorExponentAt, ← unitsLevel_le_ker_iff v hH _ (hloc v)]
    intro x hx
    exact h (finiteUnitsSingle_mem_finiteLevel hx)
  · intro h x hx
    classical
    obtain ⟨S, n₀, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
    set p := ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v x) with hp
    have hcomp : ∀ w, finiteComponent w p = if w ∈ S then finiteComponent w x else 1 := by
      intro w
      rw [hp, map_prod]
      split_ifs with hw
      · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (Ne.symm hv) _,
          finiteComponent_finiteUnitsSingle]
      · exact Finset.prod_eq_one fun v hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (fun h ↦ hw (by rw [h]; exact hv)) _
    have hy : x * p⁻¹ ∈ finiteLevel n₀ := by
      refine mem_finiteLevel.2 fun w ↦ ?_
      rw [map_mul, map_inv, hcomp]
      split_ifs with hw
      · rw [mul_inv_cancel]
        exact one_mem _
      · rw [inv_one, mul_one, h0 w hw]
        exact unitsLevel_antitone w (Nat.zero_le _) (mem_finiteLevel.1 hx w)
    have hpk : p ∈ χ.ker := Subgroup.prod_mem _ fun v _ ↦
      (unitsLevel_le_ker_iff v hH _ (hloc v)).2 (h v) (mem_finiteLevel.1 hx v)
    have hxp : x = x * p⁻¹ * p := by rw [inv_mul_cancel_right]
    rw [hxp]
    exact mul_mem (hker hy) hpk
end GroundTheory.Global.IdeleGroup
