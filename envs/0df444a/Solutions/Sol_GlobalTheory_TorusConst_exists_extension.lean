-- Prove2me | solution 1 for GlobalTheory.TorusConst.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:29.315056+00:00
-- url     : https://prove2.me/submissions/40e2df18-b3f8-479c-9cdc-6e73ce372ee8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.TorusConst
theorem _root_.solution {W Z Y S : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ x : Z, ValuationRing (Z.presheaf.stalk x)) (w : W ⟶ Z) [IsOpenImmersion w] [Nonempty W]
    (sZ : Z ⟶ S) (sY : Y ⟶ S) [IsProper sY] [Y.IsSeparated] [S.IsSeparated] (u : W ⟶ Y)
    (hu : u ≫ sY = w ≫ sZ) : ∃ g : Z ⟶ Y, w ≫ g = u ∧ g ≫ sY = sZ := by
  have hd : Dense (w.opensRange : Set Z) :=
    w.opensRange.2.dense (Set.range_nonempty _)
  let f : Z.PartialMap Y := ⟨w.opensRange, hd, w.isoOpensRange.inv ≫ u⟩
  have hspec : ∀ (p : Z.PartialMap Y) (x : Z) (hx : x ∈ p.domain),
      Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk x) Z.functionField)) ≫
        p.fromSpecStalkOfMem hx = p.fromFunctionField := by
    intro p x hx
    simp only [Scheme.PartialMap.fromSpecStalkOfMem]
    rw [← Category.assoc]
    congr 1
    rw [← cancel_mono p.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
  have hf : f.fromFunctionField ≫ sY = Z.fromSpecStalk _ ≫ sZ := by
    simp only [Scheme.PartialMap.fromSpecStalkOfMem, f, Category.assoc, hu]
    rw [Scheme.Hom.isoOpensRange_inv_comp_assoc, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have hE : ValuativeCriterion.Existence sY := by
    have h : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have htop : f.toRationalMap.domain = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have := hZ x
    let Q : ValuativeCommSq sY :=
      { R := Z.presheaf.stalk x, K := Z.functionField, i₁ := f.fromFunctionField,
        i₂ := Z.fromSpecStalk x ≫ sZ,
        commSq := ⟨by
          rw [hf, ← Category.assoc]
          congr 1
          exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
            ((genericPoint_spec Z).specializes trivial)).symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    refine Scheme.RationalMap.mem_domain.2 ⟨Scheme.PartialMap.ofFromSpecStalk (x := x) sZ sY l h2,
      Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := x) sZ sY l h2, ?_⟩
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      ← hspec _ x (Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := x) sZ sY l h2),
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact h1
  let k : Z ⟶ f.toRationalMap.domain.toScheme := IsOpenImmersion.lift f.toRationalMap.domain.ι (𝟙 Z)
    (by rw [Scheme.Opens.range_ι, htop]; simp)
  have hk : k ≫ f.toRationalMap.domain.ι = 𝟙 Z := IsOpenImmersion.lift_fac _ _ _
  have key : w ≫ k ≫ f.toRationalMap.toPartialMap.hom = u := by
    have h1 := f.toPartialMap_toRationalMap_restrict
    have h2 : w ≫ k = w.isoOpensRange.hom ≫ Z.homOfLE f.le_domain_toRationalMap := by
      rw [← cancel_mono f.toRationalMap.domain.ι, Category.assoc, hk, Category.assoc,
        Scheme.homOfLE_ι, Category.comp_id]
      exact (Scheme.Hom.isoOpensRange_hom_ι w).symm
    rw [← Category.assoc, h2, Category.assoc]
    exact (congrArg (w.isoOpensRange.hom ≫ ·) h1).trans (Iso.hom_inv_id_assoc _ _)
  refine ⟨k ≫ f.toRationalMap.toPartialMap.hom, key, ?_⟩
  have : IsDominant w := ⟨hd⟩
  exact ext_of_isDominant w (by rw [← Category.assoc, key, hu])
end GlobalTheory.TorusConst
