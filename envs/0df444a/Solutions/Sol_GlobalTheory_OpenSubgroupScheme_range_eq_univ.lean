-- Prove2me | solution 1 for GlobalTheory.OpenSubgroupScheme.range_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:49:06.87682+00:00
-- url     : https://prove2.me/submissions/a47b3262-e96c-4ca9-9b49-efd066ddd831

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Theorems.Thm_GlobalTheory_OpenSubgroupScheme_mem_range_iff_factors
import Theorems.Thm_GlobalTheory_OpenSubgroupScheme_exists_point
import Theorems.Thm_GlobalTheory_OpenSubgroupScheme_mulRight_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.OpenSubgroupScheme
theorem _root_.solution [IsAlgClosed K] [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    [IsOpenImmersion p.left] [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Set.range p.left = Set.univ := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range p.left with hU
  have hUo : IsOpen U := p.left.isOpenEmbedding.isOpen_range
  let V : Set G.left := ⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g},
    (GrpObj.mulRight g.1).hom.left ⁻¹' U
  have hVo : IsOpen V := isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)
  have hdisj : U ∩ V = ∅ := by
    by_contra hne
    obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      (hUo.inter hVo).isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hyV
    rw [Set.mem_preimage, mulRight_apply] at hg
    obtain ⟨a, ha⟩ := (mem_range_iff_factors p x).mp hyU
    obtain ⟨b, hb⟩ := (mem_range_iff_factors p _).mp hg
    refine g.2 ⟨a⁻¹ * b, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U :=
    (mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩
  have hcov : U ∪ V = Set.univ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (hUo.union hVo).isClosed_compl.isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hy
    refine hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)
    · rintro ⟨a, ha⟩
      refine hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)
      rw [GrpObj.inv_comp, ha, inv_inv]
    · rw [Set.mem_preimage, mulRight_apply, mul_inv_cancel]
      exact hone
  have hc : Uᶜ = V := by
    ext y
    constructor
    · intro hy
      exact ((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy
    · intro hy hyU
      exact (hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))
  have hcl : IsClopen U := ⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩
  exact hcl.eq_univ ⟨_, hone⟩
end GlobalTheory.OpenSubgroupScheme
