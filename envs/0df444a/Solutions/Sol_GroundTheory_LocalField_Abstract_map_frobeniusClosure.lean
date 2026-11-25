-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.map_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:31.842283+00:00
-- url     : https://prove2.me/submissions/612ddee0-79f4-4646-8325-608f5b417dcd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_denseRange_intCast
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_zpowers_sup_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_deg_zpow_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_frobeniusClosure_self
import Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ}
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    (frobeniusClosure d L σ).map d = AddSubgroup.toSubgroup (multiples N) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hcl : IsClosed (d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂))) :=
      (isClosed_multiples N).preimage (continuous_toAdd.comp hd)
    have hsub : ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) ⊆
        d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂)) := by
      intro h hh
      obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hh
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [deg_zpow_mul hdσ k hj, mem_multiples]
      exact ⟨(k : ℤ̂), by push_cast; rw [nsmul_eq_mul]; ring⟩
    have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hx
    exact closure_minimal hsub hcl hx'
  · intro y hy
    have hy' : Multiplicative.toAdd y ∈ multiples N := hy
    obtain ⟨w, hw⟩ := mem_multiples.1 hy'
    set S : Set (Multiplicative ℤ̂) := d '' (frobeniusClosure d L σ : Set G) with hSdef
    have hS : IsClosed S := (isClosed_frobeniusClosure.isCompact.image hd).isClosed
    have key : ∀ w : ℤ̂, Multiplicative.ofAdd ((N : ℤ̂) * w) ∈ S := by
      intro w
      refine denseRange_intCast.induction_on w
        (hS.preimage (continuous_ofAdd.comp (continuous_const.mul continuous_id))) fun k => ?_
      refine ⟨σ ^ k, Subgroup.zpow_mem _ mem_frobeniusClosure_self k, ?_⟩
      rw [map_zpow, hdσ, ← ofAdd_zsmul, zsmul_eq_mul, mul_comm]
    obtain ⟨x, hx, hxy⟩ := key w
    refine ⟨x, hx, ?_⟩
    rw [hxy, ← nsmul_eq_mul, ← hw]
    rfl
end GroundTheory.LocalField.Abstract
