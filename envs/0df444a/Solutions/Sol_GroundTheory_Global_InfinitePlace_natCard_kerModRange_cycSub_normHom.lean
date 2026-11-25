-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.natCard_kerModRange_cycSub_normHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:36.3288+00:00
-- url     : https://prove2.me/submissions/f387be85-fff3-4c08-bbac-27f4d9beda45

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_InfinitePlace_cycSub_unitsRep_toMul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_re_pos_of_mem_range_normHom
import Theorems.Thm_GroundTheory_Global_InfinitePlace_mem_range_normHom
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]
variable (v)
variable {v w}
variable (v w)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (cycSub (unitsRep v w) (completionConj hv))
      (normHom (unitsRep v w))) = 2 := by
  set c := completionConj (w := w) hv
  have hker : ∀ x : Additive w.Completionˣ,
      x ∈ (cycSub (unitsRep v w) c).ker ↔ c (x.toMul : w.Completion) = x.toMul := by
    intro x
    rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, cycSub_unitsRep_toMul,
      div_eq_one_iff_eq (Units.ne_zero _)]
  set m : Additive w.Completionˣ := Additive.ofMul (-1)
  have hm : m ∈ (cycSub (unitsRep v w) c).ker := by
    rw [hker]
    simp [m]
  have hme : extensionEmbedding w (m.toMul : w.Completion) = -1 := by simp [m]
  rw [Nat.card_eq_two_iff]
  refine ⟨QuotientAddGroup.mk ⟨0, zero_mem _⟩, QuotientAddGroup.mk ⟨m, hm⟩, ?_, ?_⟩
  · rw [Ne, KerModRange.mk_eq_mk_iff]
    intro h
    have := re_pos_of_mem_range_normHom hv hw h
    rw [AddSubgroup.coe_mk, zero_sub, toMul_neg, Units.val_inv_eq_inv_val, map_inv₀, hme] at this
    norm_num at this
  · rw [Set.eq_univ_iff_forall]
    intro q
    induction q using QuotientAddGroup.induction_on with | H z =>
    obtain ⟨x, hx⟩ := z
    have hc := (hker x).1 hx
    have hreal : extensionEmbedding w (x.toMul : w.Completion) =
        ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
      have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
      rw [hc] at h
      exact (Complex.conj_eq_iff_re.1 h.symm).symm
    have hne : (extensionEmbedding w (x.toMul : w.Completion)).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, map_eq_zero] at hreal
      exact Units.ne_zero _ hreal
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      rw [KerModRange.mk_eq_mk_iff]
      apply mem_range_normHom hv hw
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hc,
          (hker m).1 hm]
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀,
          hme, div_neg, div_one, Complex.neg_re]
        linarith
    · left
      rw [KerModRange.mk_eq_mk_iff, AddSubgroup.coe_mk, AddSubgroup.coe_mk, sub_zero]
      exact mem_range_normHom hv hw x hc hpos
end GroundTheory.Global.InfinitePlace
