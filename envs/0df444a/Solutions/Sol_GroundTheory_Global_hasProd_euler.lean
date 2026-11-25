-- Prove2me | solution 1 for GroundTheory.Global.hasProd_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:05.156457+00:00
-- url     : https://prove2.me/submissions/6e977b3c-8171-4dfa-8ef8-9987beea0def

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_eventually_mem_factoredIdeals
import Theorems.Thm_GroundTheory_Global_hasSum_indicator_factoredIdeals
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)
namespace GroundTheory.Global
theorem _root_.solution (hsum : Summable fun I ↦ ‖g I‖) (h0 : g ⊥ = 0) :
    HasProd (fun v : HeightOneSpectrum R ↦ (1 - g v.asIdeal)⁻¹) (∑' I, g I) := by
  have key : (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) =
      fun S ↦ ∑' I, (factoredIdeals S).indicator g I :=
    funext fun S ↦ (hasSum_indicator_factoredIdeals g hsum S).tsum_eq.symm
  show Tendsto (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) atTop
    (𝓝 (∑' I, g I))
  rw [key]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I ↦ ?_)
    (Eventually.of_forall fun S I ↦ norm_indicator_le_norm_self g I)
  by_cases hI : I = ⊥
  · subst hI
    have : ∀ S : Finset (HeightOneSpectrum R), (factoredIdeals S).indicator g ⊥ = g ⊥ :=
      fun S ↦ by rw [Set.indicator_of_notMem (fun h ↦ h.1 rfl), h0]
    simp only [this]
    exact tendsto_const_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_factoredIdeals hI] with S hS
    rw [Set.indicator_of_mem hS]
end GroundTheory.Global
