-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.exists_independent_torsion_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:53.907101+00:00
-- url     : https://prove2.me/submissions/5b476307-37db-4958-97d0-4ac8470a5c57

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_nonempty_torsionBy_addEquiv
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
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
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (hℓF : (ℓ : F) ≠ 0) :
    ∃ P Q : W.toAffine.Point, ℓ • P = 0 ∧ ℓ • Q = 0 ∧
      ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv W hℓF
  refine ⟨(e.symm (1, 0) : W.toAffine.Point), (e.symm (0, 1) : W.toAffine.Point),
    torsionBy.nsmul_iff.mp (e.symm (1, 0)).2, torsionBy.nsmul_iff.mp (e.symm (0, 1)).2,
    fun a b h => ?_⟩
  have hab : ((a : ZMod ℓ), (b : ZMod ℓ)) =
      a • ((1 : ZMod ℓ), (0 : ZMod ℓ)) + b • ((0 : ZMod ℓ), (1 : ZMod ℓ)) := by
    ext <;> simp
  have h' : e.symm ((a : ZMod ℓ), (b : ZMod ℓ)) = 0 := by
    apply Subtype.ext
    rw [hab, map_add, map_nsmul, map_nsmul]
    simpa using h
  have h'' := congrArg e h'
  rw [AddEquiv.apply_symm_apply, map_zero] at h''
  exact ⟨(ZMod.natCast_eq_zero_iff a ℓ).mp (congrArg Prod.fst h''),
    (ZMod.natCast_eq_zero_iff b ℓ).mp (congrArg Prod.snd h'')⟩
end GroundTheory.Arith.Abelian
