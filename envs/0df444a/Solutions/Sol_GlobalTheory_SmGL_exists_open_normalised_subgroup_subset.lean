-- Prove2me | solution 1 for GlobalTheory.SmGL.exists_open_normalised_subgroup_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:52.918349+00:00
-- url     : https://prove2.me/submissions/3b5d04eb-ae54-4c7c-91cd-c819e430bd13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL
namespace GlobalTheory.SmGL
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∀ U ∈ 𝓝 (1 : GL n k), ∃ J : Subgroup (GL n k), IsOpen (J : Set (GL n k)) ∧
      (J : Set (GL n k)) ⊆ U ∧ J ≤ KO k n ∧ ∀ x ∈ KO k n, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix n n k) :=
    inferInstanceAs (TotallyDisconnectedSpace (n → n → k))
  have : TotallyDisconnectedSpace (GL n k) :=
    ⟨(SplitFlip.isEmbedding_val_GL (k := k) (n := n)).isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace (KO k n) :=
    isCompact_iff_compactSpace.1 (SplitFlip.isCompact_KO (k := k) (n := n))
  have hV : IsOpen ((fun x : KO k n => (x : GL n k)) ⁻¹' interior U) :=
    isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : KO k n) ∈ (fun x : KO k n => (x : GL n k)) ⁻¹' interior U :=
    mem_interior_iff_mem_nhds.2 hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨H.toSubgroup.map (KO k n).subtype, ?_, ?_, ?_, ?_⟩
  · exact (SplitFlip.isOpen_KO (k := k) (n := n)).isOpenMap_subtype_val _ H.isOpen
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hH hy)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro x hx _ ⟨y, hy, rfl⟩
    have hc : (⟨x, hx⟩ : KO k n) * y * (⟨x, hx⟩ : KO k n)⁻¹ ∈ H.toSubgroup :=
      H.isNormal'.conj_mem y hy (⟨x, hx⟩ : KO k n)
    exact Subgroup.mem_map_of_mem (KO k n).subtype hc
end GlobalTheory.SmGL
