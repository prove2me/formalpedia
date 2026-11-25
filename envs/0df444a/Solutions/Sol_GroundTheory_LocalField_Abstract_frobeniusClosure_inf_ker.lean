-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.frobeniusClosure_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:00.981122+00:00
-- url     : https://prove2.me/submissions/57490811-a96d-4fcb-a0cf-fc0c6b331e17

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_isOpen_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_zpowers_sup_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_deg_zpow_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_intCast_mem_multiples_iff
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
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    frobeniusClosure d L σ ⊓ d.ker = L ⊓ d.ker := by
  refine le_antisymm ?_ (le_inf le_frobeniusClosure inf_le_right)
  intro x hx0
  obtain ⟨hx, hxk⟩ := Subgroup.mem_inf.1 hx0
  rw [MonoidHom.mem_ker] at hxk
  obtain ⟨U0, hU0⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hL L.one_mem
  have : Finite (G ⧸ U0.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U0.isOpen'
  set t := orderOf (σ : G ⧸ U0.toSubgroup) with htdef
  have ht : 0 < t := orderOf_pos _
  set M : ℕ+ := ⟨t * N, Nat.mul_pos ht (Nat.pos_of_ne_zero hN)⟩ with hMdef
  set V : Set G := (U0 : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
  have hV : IsOpen V :=
    U0.isOpen'.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
  have hO : IsOpen ((fun y => x⁻¹ * y) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
  have hxO : x ∈ (fun y => x⁻¹ * y) ⁻¹' V := by
    simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
    exact ⟨U0.one_mem', (multiples M).zero_mem⟩
  have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨h, hhO, hhH⟩ := mem_closure_iff.1 hx' _ hO hxO
  obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhH
  obtain ⟨hU, hWm⟩ := hhO
  have hdk : Multiplicative.toAdd (d (x⁻¹ * (σ ^ k * j))) = ((k * N : ℤ) : ℤ̂) := by
    rw [map_mul, map_inv, hxk, inv_one, one_mul]
    exact deg_zpow_mul hdσ k hj
  have hdiv : ((M : ℕ) : ℤ) ∣ k * N := by
    have hmem : ((k * N : ℤ) : ℤ̂) ∈ multiples M := by
      rw [← hdk]
      exact hWm
    exact (intCast_mem_multiples_iff M.pos).1 hmem
  have htk : (t : ℤ) ∣ k := by
    have h2 : (t : ℤ) * N ∣ k * N := by simpa [hMdef] using hdiv
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hN)).1 h2
  have hσk : σ ^ k ∈ U0.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_zpow, ← orderOf_dvd_iff_zpow_eq_one]
    exact htk
  refine ⟨?_, (MonoidHom.mem_ker).2 hxk⟩
  have hx_eq : x = σ ^ k * j * (x⁻¹ * (σ ^ k * j))⁻¹ := by group
  rw [hx_eq]
  exact L.mul_mem (L.mul_mem (hU0 hσk) hj.1) (L.inv_mem (hU0 hU))
end GroundTheory.LocalField.Abstract
