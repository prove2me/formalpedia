-- Prove2me | solution 1 for GroundTheory.Global.hasSum_integral_ideleMeasure_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:31.826097+00:00
-- url     : https://prove2.me/submissions/0d50e21c-73bf-495d-a207-0224a8fbe8e4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Theorems.Thm_GroundTheory_Global_countable_quotient_of_isOpen
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_integral_ideleMeasure
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) {F : IdeleGroup K → E} (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ W, F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W ↦ (finiteIdeleMeasure K W).toReal •
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by
  have hc : Countable ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := countable_quotient_of_isOpen hWo
  set μ := (infiniteIdeleMeasure K).prod (finiteIdeleMeasure K)
  set G : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ → E :=
    fun p ↦ F ((IdeleGroup.prodEquiv K).symm p)
  have hG : Integrable G μ :=
    (integrable_map_equiv (IdeleGroup.prodEquiv K).symm.toHomeomorph.toMeasurableEquiv F).1 hFi

  set S : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W → Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    fun c ↦ QuotientGroup.mk ⁻¹' {c}
  have : DiscreteTopology ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := QuotientGroup.discreteTopology hWo
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    (isOpen_discrete ({c} : Set ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W))).preimage
      QuotientGroup.continuous_mk |>.measurableSet
  have hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    intro c
    ext b
    simp only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq]
  have hmeasS : ∀ c, finiteIdeleMeasure K (S c) = finiteIdeleMeasure K W := fun c ↦ by
    rw [hSW c, measure_preimage_mul]
  have hGS : ∀ c, ∀ a, ∀ b ∈ S c, G (a, b) = G (a, c.out) := by
    intro c a b hb
    rw [hSW c] at hb
    have hw : c.out⁻¹ * b ∈ W := hb
    have : (a, b) = (a, c.out) * (1, c.out⁻¹ * b) := by simp
    simp only [G]
    rw [this, map_mul, hF _ _ hw]
  have hT : ∀ c, MeasurableSet ((Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := fun c ↦
    MeasurableSet.univ.prod (hSm c)
  have hTd : Pairwise (Function.onFun Disjoint
      fun c ↦ (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun p hp hq ↦ hcd ?_
    exact hp.2.symm.trans hq.2
  have hTu : ⋃ c, (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p.2 : _ ⧸ W), trivial, rfl⟩
  have h := hasSum_integral_iUnion hT hTd hG.integrableOn
  rw [hTu, Measure.restrict_univ] at h
  rw [integral_ideleMeasure]
  convert h using 1
  funext c
  symm
  have e : μ.restrict (Set.univ ×ˢ S c) =
      (infiniteIdeleMeasure K).prod ((finiteIdeleMeasure K).restrict (S c)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e, integral_prod _ (by rw [← e]; exact hG.integrableOn), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
  simp only
  rw [setIntegral_congr_fun (hSm c) fun b hb ↦ hGS c a b hb, setIntegral_const, Measure.real,
    hmeasS c]
end GroundTheory.Global
