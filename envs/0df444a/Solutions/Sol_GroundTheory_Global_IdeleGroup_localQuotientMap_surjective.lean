-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.localQuotientMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:44:02.608848+00:00
-- url     : https://prove2.me/submissions/0c8bac52-e183-42bf-afb1-96cc8cc05e95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteEmbedding_mem_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroup_le_sIdeles
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
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
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_finiteEmbedding

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localQuotientMap T H H' S) := by
  classical
  rintro ⟨a, b⟩
  choose α hα using fun v : S ↦ QuotientGroup.mk_surjective (a v)
  choose β hβ using fun w ↦ QuotientGroup.mk_surjective (b w)
  let x : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hx : x ∈ sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) := by
    refine mul_mem (prod_mem fun v _ ↦ ?_) (prod_mem fun w _ ↦ ?_)
    · intro u hu
      exact ord_finiteEmbedding_of_ne (fun h ↦ hu (Or.inl (by rw [h]; exact Finset.mem_coe.2 v.2))) _
    · exact standardOpenSubgroup_le_sIdeles _ (infiniteEmbedding_mem_standardOpenSubgroup w _)
  have hfin : ∀ v : S, finiteProj v.1 x = α v := by
    intro v
    simp only [x, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hinf : ∀ w : InfinitePlace K, infiniteProj w x = β w := by
    intro w
    simp only [x, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  refine ⟨⟨x, hx⟩, Prod.ext (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · exact (congrArg (QuotientGroup.mk (s := H v.1)) (hfin v)).trans (hα v)
  · exact (congrArg (QuotientGroup.mk (s := H' w)) (hinf w)).trans (hβ w)
end GroundTheory.Global.IdeleGroup
