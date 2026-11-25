-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:01.019027+00:00
-- url     : https://prove2.me/submissions/f244a2be-5a39-4587-aecb-60184b927760

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adele_ext
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicGL_ext
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_eventually_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_mul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_mul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (g : AdelicGLn.AdelicGL K n) :
    ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact, g = b * k := by
  classical

  choose pw hpw using fun w : InfinitePlace K => exists_upper_mul_archCompact' w (infAt w g)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ p : GL (Fin n) (v.adicCompletion K) ×
      GL (Fin n) (v.adicCompletion K), p.1 ∈ Iwasawa.borel (v.adicCompletion K) n ∧
      p.2 ∈ GLnLocal.integralGL (v.adicCompletion K) n ∧ finAt v g = p.1 * p.2 ∧
      (finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n → p.1 = 1) := by
    intro v
    by_cases hv : finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n
    · exact ⟨(1, finAt v g), one_mem _, hv, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨b, hb, k, hk, he⟩ := Iwasawa.exists_borel_mul_integralGL _ n (finAt v g)
      exact ⟨(b, k), hb, hk, he, fun h => absurd h hv⟩
  choose pv hpv using hloc

  let bX : (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
    (fun w => (pw w).1, ⟨fun v => (pv v).1, by
      filter_upwards [AdelicGLn.eventually_mem_integralGL K n g] with v hv
      rw [(hpv v).2.2.2 hv]
      exact one_mem _⟩)
  let kX : (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
    (fun w => (pw w).2, ⟨fun v => (pv v).2, Filter.Eventually.of_forall fun v => (hpv v).2.1⟩)
  set b := (AdelicGLn.restrictedProductEquiv K n).symm bX with hb
  set k := (AdelicGLn.restrictedProductEquiv K n).symm kX with hk
  have hbw : ∀ w, infAt w b = (pw w).1 := fun w => by
    simp [infAt, hb, bX]
  have hbv : ∀ v, finAt v b = (pv v).1 := fun v => by
    simp only [finAt, hb, ContinuousMulEquiv.apply_symm_apply, bX]
    rfl
  have hkw : ∀ w, infAt w k = (pw w).2 := fun w => by
    simp [infAt, hk, kX]
  have hkv : ∀ v, finAt v k = (pv v).2 := fun v => by
    simp only [finAt, hk, ContinuousMulEquiv.apply_symm_apply, kX]
    rfl
  refine ⟨b, ?_, k, ⟨fun w => hkw w ▸ (hpw w).2.1, fun v => hkv v ▸ (hpv v).2.1⟩, ?_⟩
  · intro i j hij
    refine adele_ext (fun w => ?_) (fun v => ?_)
    · have h := (hpw w).1 hij
      rw [← hbw w] at h
      exact h
    · have h := (Iwasawa.mem_borel _ n).1 (hpv v).1 hij
      rw [← hbv v] at h
      exact h
  · refine adelicGL_ext (fun w => ?_) (fun v => ?_)
    · rw [infAt_mul, hbw, hkw]
      exact (hpw w).2.2
    · rw [finAt_mul, hbv, hkv]
      exact (hpv v).2.2.1
end GroundTheory.Automorphic.Reduction
