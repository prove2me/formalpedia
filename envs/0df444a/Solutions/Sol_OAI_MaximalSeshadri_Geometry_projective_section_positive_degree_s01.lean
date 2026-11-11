-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:37.351333+00:00
-- url     : https://prove2.me/submissions/d731443d-1155-4e63-9e30-b7edbe263230

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_RestrictionComparison
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleMayerVietoris.tripleG_epi _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end
end MaximalSeshadri.ModuleMayerVietoris


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_CurveFiniteMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Set

lemma curve_nonclosed_generic {X : Type*} [TopologicalSpace X] [T0Space X]
    [IrreducibleSpace X] (hd : topologicalKrullDim X ≤ 1) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) : IsGenericPoint x Set.univ := by
  by_contra h
  have hp : closure ({x} : Set X) ≠ Set.univ := h
  have hs := proper_irreducible_closed_subsingleton hd isClosed_closure
    isIrreducible_singleton.closure hp
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hs hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact hx (he ▸ isClosed_closure)

theorem proper_curve_nonconstant_isFinite {X Y : Scheme}
    [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (hn : ∃ a b : X, f a ≠ f b) : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (by
    intro y
    by_cases hy : IsClosed ({y} : Set Y)
    · apply proper_closed_finite_of_dimension_one hd (hy.preimage f.continuous)
      intro he
      obtain ⟨a,b,hab⟩ := hn
      have ha : a ∈ f ⁻¹' ({y} : Set Y) := he ▸ Set.mem_univ a
      have hb : b ∈ f ⁻¹' ({y} : Set Y) := he ▸ Set.mem_univ b
      exact hab (ha.trans hb.symm)
    · apply Set.Subsingleton.finite
      intro a ha b hb
      apply (curve_nonclosed_generic hd a ?_).eq (curve_nonclosed_generic hd b ?_)
      · intro hc
        have hi := f.isClosedMap _ hc
        rw [Set.image_singleton, ha] at hi
        exact hy hi
      · intro hc
        have hi := f.isClosedMap _ hc
        rw [Set.image_singleton, hb] at hi
        exact hy hi)
  exact .of_isProper_of_locallyQuasiFinite f

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

end

end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_HyperplaneAvoidance
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ ι : Type} [Field K] [Infinite K] [Fintype σ] [Finite ι]

omit [Infinite K] in
lemma linearEquation_single_one [DecidableEq σ] (i : σ) :
    linearEquation (Pi.single i (1 : K)) = X i := by
  classical
  simp [linearEquation, Pi.single_apply, apply_ite, ite_mul]

theorem exists_hyperplane_avoiding (x : ι → Proj (PolyGrade K σ)) :
    ∃ v : σ → K, ∀ i, x i ∈ Proj.basicOpen (PolyGrade K σ) (linearEquation v) := by
  classical
  let p (i : ι) : Submodule K (σ → K) :=
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars K).comap (linearEquationLinear (K := K) (σ := σ))
  have hp (i : ι) : p i ≠ ⊤ := by
    intro h
    have hx : x i ∈ ⨆ j : σ, Proj.basicOpen (PolyGrade K σ) (X j) := by
      rw [projective_coordinate_cover]
      trivial
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
    have hj' : Pi.single j (1 : K) ∈ p i := h ▸ Submodule.mem_top
    change linearEquation (Pi.single j (1 : K)) ∈ (x i).asHomogeneousIdeal at hj'
    rw [linearEquation_single_one] at hj'
    exact hj hj'
  obtain ⟨v,hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨v, hv⟩

theorem exists_section_avoiding {Y : Scheme} {M : Y.Modules}
    (k : K →+* Γ(Y,⊤)) (s : σ → (MaximalSeshadri.Frames.O Y ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (x : ι → Y) :
    ∃ v : σ → K, ∀ i, x i ∈ SectionOpens.isoOpen (sectionCombination k s v) := by
  obtain ⟨v,hv⟩ := exists_hyperplane_avoiding (fun i => sectionsMorphism k s hs (x i))
  refine ⟨v, fun i => ?_⟩
  rw [← sectionsMorphism_hyperplane k s hs]
  exact hv i

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_CurvePencil
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

theorem curve_exists_finite_pencil [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : σ) (hne : (SectionOpens.isoOpen (s i) : Set X).Nonempty)
    (hproper : SectionOpens.isoOpen (s i) ≠ ⊤) :
    ∃ t : Bool → (O X ⟶ M), ∃ ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤,
      t false = s i ∧ IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U := SectionOpens.isoOpen (s i)
  let Z : Set X := (U : Set X)ᶜ
  have hz : Z.Finite := proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl (by
    intro he
    obtain ⟨x,hx⟩ := hne
    have : x ∈ Z := he ▸ Set.mem_univ x
    exact this hx)
  let : Finite Z := hz.to_subtype
  obtain ⟨v,hv⟩ := exists_section_avoiding k s hs ((↑) : Z → X)
  let t : Bool → (O X ⟶ M) := fun b => if b then sectionCombination k s v else s i
  have ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤ := by
    apply top_unique
    intro x hx
    by_cases h : x ∈ U
    · apply Opens.mem_iSup.mpr
      exact ⟨false, h⟩
    · apply Opens.mem_iSup.mpr
      exact ⟨true, hv ⟨x,h⟩⟩
  let f := sectionsMorphism k t ht
  have hf : IsFinite f := by
    let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
      dsimp only [k]
      rw [toSpec_scalarMap]
      infer_instance
    let : IsProper f := sectionsMorphism_proper k t ht
    apply proper_curve_nonconstant_isFinite f hd
    obtain ⟨a,ha⟩ := hne
    obtain ⟨b,hb⟩ : ∃ b : X, b ∉ U := by
      by_contra h
      apply hproper
      apply top_unique
      intro x hx
      exact Classical.not_not.mp (fun hx => h ⟨x,hx⟩)
    refine ⟨a,b,fun he => ?_⟩
    have hp : f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false) = U :=
      sectionsMorphism_preimage k t ht false
    have ha' : a ∈ f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false) := by
      rw [hp]
      exact ha
    have hb' : b ∈ U := by
      rw [← hp]
      change f b ∈ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false)
      rw [← he]
      exact ha'
    exact hb hb'
  exact ⟨t,ht,rfl,hf⟩

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_CurveProjection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

omit [Infinite K] in
lemma proper_affine_dimension_zero [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] : topologicalKrullDim X ≤ 0 := by
  let : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,inferInstance⟩
  let y : Spec (CommRingCat.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have he : p ⁻¹' ({y} : Set (Spec (CommRingCat.of K))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton y
  rw [he] at h
  let : DiscreteTopology X := isDiscrete_univ_iff.mp h
  exact topologicalKrullDim_zero_of_discreteTopology X

theorem projective_curve_finite_pencil [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ t : Bool → (O X ⟶ M), ∃ ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤,
      IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  have hne : (SectionOpens.isoOpen (s i) : Set X).Nonempty := ⟨x,hi⟩
  have hproper : SectionOpens.isoOpen (s i) ≠ ⊤ := by
    intro he
    have hA := (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i)
      (by decide)).preimage (sectionsMorphism k s hs)
    rw [sectionsMorphism_preimage, he] at hA
    let : IsAffine (⊤ : X.Opens).toScheme := hA
    let : IsAffine X := .of_isIso X.topIso.inv
    have hdim := proper_affine_dimension_zero p
    rw [hd] at hdim
    norm_num at hdim
  obtain ⟨t,ht,_,hf⟩ := curve_exists_finite_pencil p hd.le s hs i hne hproper
  exact ⟨t,ht,hf⟩
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveCohomology
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian
open MaximalSeshadri.Projective MaximalSeshadri.ModuleFlasque
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsNoetherian X]

local instance instHasExtModules_solutions : HasExt.{1} X.Modules := schemeHasExt

lemma two_affine_ext_zero (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : cohomology M (n+2)) : x = 0 := by
  let e : FiniteCoverCohomology.freeOpenModule (X := X) ⊤ ≅
      structureSheaf X := FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule ⊤) M (n+2), z = 0 := by
    rw [← hcover]
    exact ModuleMayerVietoris.union_ext_zero X.ringCatSheaf U V M (n+1)
      (FiniteCoverCohomology.affine_open_ext_zero U hU M (n+1))
      (FiniteCoverCohomology.affine_open_ext_zero V hV M (n+1))
      (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ V) hUV M n)
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (n+2)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add _)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

theorem finite_over_line_ext_zero {K : Type} [Field K]
    (f : X ⟶ Proj (PolyGrade K Bool)) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (x : cohomology M (n+2)) : x = 0 := by
  let U (b : Bool) := f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X b)
  have hA (b : Bool) : IsAffineOpen (U b) :=
    (Proj.isAffineOpen_basicOpen _ _ (poly_X_mem b) (by decide)).preimage f
  have hUV : IsAffineOpen (U false ⊓ U true) := by
    have h := (Proj.isAffineOpen_basicOpen (PolyGrade K Bool) _
      (SetLike.mul_mem_graded (poly_X_mem false) (poly_X_mem true)) (by decide)).preimage f
    simpa only [Proj.basicOpen_mul, Scheme.Hom.preimage_inf] using h
  have hc : U false ⊔ U true = ⊤ := by
    apply top_unique
    intro z hz
    have hf : f z ∈ ⨆ b : Bool, Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X b) := by
      rw [projective_coordinate_cover]
      trivial
    obtain ⟨b,hb⟩ := Opens.mem_iSup.mp hf
    cases b with
    | false => exact Or.inl hb
    | true => exact Or.inr hb
  exact two_affine_ext_zero (U false) (U true) (hA false) (hA true) hUV hc M n x

theorem projective_curve_ext_zero {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {N : X.Modules}
    (s : σ → (MaximalSeshadri.Frames.O X ⟶ N))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (x : cohomology M (n+2)) : x = 0 := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let f := sectionsMorphism
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht
  let : IsFinite f := hf
  exact finite_over_line_ext_zero f M n x

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SupportedSheaf
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

variable {X : TopCat.{0}}

lemma finite_closed_support_restriction_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  have hcS : IsClosed (S ∩ V) := by
    rw [← Set.biUnion_of_singleton (S ∩ (V : Set X))]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun x hx => hclosed x hx.1)
  let W : Opens X := U ⊓ ⟨(S ∩ V)ᶜ,hcS.isOpen_compl⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact inf_le_left
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hv⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,fun h => hv h.2⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hz : ∀ b c, b ≠ c → Subsingleton (F.obj.obj (op (D b ⊓ D c))) := by
    intro b c hbc
    apply sections_subsingleton_of_stalks
    intro x hx
    apply hsupp
    intro hs
    cases b <;> cases c
    · exact hbc rfl
    · exact hx.1.2 ⟨hs,hx.2⟩
    · exact hx.2.2 ⟨hs,hx.1⟩
    · exact hbc rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    by_cases he : b = c
    · subst c; rfl
    · let := hz b c he
      exact Subsingleton.elim _ _
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hcomp
  exact ⟨a,ha true⟩

lemma finite_closed_support_flasque (F : X.Sheaf AddCommGrpCat.{0})
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (finite_closed_support_restriction_surjective F S hfin hclosed hsupp i.unop)

end
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

theorem LineBundle.cokernel_flasque [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj (cokernel s)) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hfin : S.Finite := L.cokernel_support_finite hd s hs
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    have hc : closure ({x} : Set X) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
    have hsub : (closure ({x} : Set X)).Subsingleton := by
      apply proper_irreducible_closed_subsingleton hd isClosed_closure
        isIrreducible_singleton.closure
      intro he
      have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
      exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
    have he : closure ({x} : Set X) = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub hy (subset_closure (Set.mem_singleton x))
      · exact subset_closure
    exact he ▸ isClosed_closure
  apply FiniteSupport.finite_closed_support_flasque _ S hfin hclosed
  intro x hx
  apply cokernel_stalk_subsingleton s x
  exact not_not.mp hx

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_EulerExact
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                    
section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

lemma complexExtModule_eq (M : X.Modules) (n : ℕ) :
    complexExtModule f M n = Module.compHom (cohomology M n) (baseScalars f) := by
  apply Module.ext'
  intro r x
  let := sheafComplexLinear f
  change r • x = (baseScalars f r) • x
  rw [Ext.smul_eq_comp_mk₀ (R := ℂ), Ext.smul_eq_comp_mk₀ (R := Γ(X, ⊤))]
  rfl

lemma eulerCharacteristic_eq_extEuler (M : X.Modules) (d : ℕ) :
    eulerCharacteristic f d M =
      letI := sheafComplexLinear f
      Cohomology.extEuler (K := ℂ) (structureSheaf X) M d := by
  unfold eulerCharacteristic Cohomology.extEuler Cohomology.alternatingTrunc
  apply Finset.sum_congr rfl
  intro n hn
  have hh := complexExtModule_eq f M n
  unfold cohomologyDimension
  rw [← hh]

theorem eulerCharacteristic_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₁ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₂ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₃ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₃ n))
    [Subsingleton (cohomology S.X₁ (d+1))] :
    eulerCharacteristic f d S.X₂ =
      eulerCharacteristic f d S.X₁ + eulerCharacteristic f d S.X₃ := by
  let := sheafComplexLinear f
  rw [eulerCharacteristic_eq_extEuler, eulerCharacteristic_eq_extEuler,
    eulerCharacteristic_eq_extEuler]
  apply Cohomology.extEuler_add (K := ℂ) (structureSheaf X) hS d
  · intro n hn
    have hh := complexExtModule_eq f S.X₁ n
    change @FiniteDimensional ℂ (cohomology S.X₁ n) _ _ (complexExtModule f S.X₁ n)
    rw [hh]
    exact hfinite₁ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₂ n
    change @FiniteDimensional ℂ (cohomology S.X₂ n) _ _ (complexExtModule f S.X₂ n)
    rw [hh]
    exact hfinite₂ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₃ n
    change @FiniteDimensional ℂ (cohomology S.X₃ n) _ _ (complexExtModule f S.X₃ n)
    rw [hh]
    exact hfinite₃ n hn

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_FiniteEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite

variable {X : Scheme}

lemma cohomologyDimension_zero (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    cohomologyDimension f M 0 =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      Module.finrank ℂ Γ(M,⊤) := by
  let : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  exact (cohomologyZeroSections f M).finrank_eq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SectionEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

lemma finite_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict
end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

lemma LineBundle.cokernel_ext_zero (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (n : ℕ) (z : cohomology (cokernel s) (n+1)) : z = 0 := by
  let := L.cokernel_flasque hd s hs
  exact FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n (cokernel s) z

theorem projective_section_cokernel_finite {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    letI := Module.compHom (cohomology (cokernel s) n) (baseScalars p)
    Module.Finite ℂ (cohomology (cokernel s) n) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  cases n with
  | succ n =>
    let := Module.compHom (cohomology (cokernel s) (n+1)) (baseScalars p)
    let : Subsingleton (cohomology (cokernel s) (n+1)) := ⟨fun x y =>
      (L.cokernel_ext_zero hd.le s hs n x).trans (L.cokernel_ext_zero hd.le s hs n y).symm⟩
    infer_instance
  | zero =>
    let := sheafComplexLinear p
    let B : LineBundle X := ⟨O X, fun x =>
      ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
    let S := ShortComplex.mk s (cokernel.π s) (cokernel.condition s)
    have hS := L.section_shortExact s hs
    let hL : Module.Finite ℂ (cohomology L.sheaf 0) := by
      change @Module.Finite ℂ (cohomology L.sheaf 0) _ _ (complexExtModule p L.sheaf 0)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite_s01 p hd a ha L 0
    let hO : Module.Finite ℂ (cohomology (O X) 1) := by
      change @Module.Finite ℂ (cohomology (O X) 1) _ _ (complexExtModule p (O X) 1)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite_s01 p hd a ha B 1
    let : Module.Finite ℂ (Ext (O X) S.X₂ 0) := hL
    let : Module.Finite ℂ (Ext (O X) S.X₁ (0+1)) := hO
    have he := Cohomology.finite_middle_of_exact
      (Cohomology.cohomologyMap₂ (K := ℂ) (O X) (S := S) 0)
      (Cohomology.cohomologyBoundary (K := ℂ) (O X) hS 0)
      (Cohomology.cohomology_exact₃ (K := ℂ) (O X) hS 0)
    change @Module.Finite ℂ (cohomology (cokernel s) 0) _ _
      (complexExtModule p (cokernel s) 0) at he
    rw [complexExtModule_eq] at he
    exact he

theorem projective_section_euler_difference {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) =
      letI := Module.compHom Γ(cokernel s, ⊤) (baseScalars p)
      (Module.finrank ℂ Γ(cokernel s,⊤) : ℤ) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  let B : LineBundle X := ⟨O X, fun x =>
    ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (O X).IsQuasicoherent := B.quasicoherent
  let : Subsingleton (cohomology (O X) (1+1)) := ⟨fun x y =>
    (projective_curve_ext_zero p hd a ha (O X) 0 x).trans
      (projective_curve_ext_zero p hd a ha (O X) 0 y).symm⟩
  have he := eulerCharacteristic_add p (L.section_shortExact s hs) 1
    (fun n _ => projective_curve_cohomology_finite_s01 p hd a ha B n)
    (fun n _ => projective_curve_cohomology_finite_s01 p hd a ha L n)
    (fun n _ => projective_section_cokernel_finite p hd a ha L s hs n)
  change eulerCharacteristic p 1 L.sheaf =
    eulerCharacteristic p 1 (O X) + eulerCharacteristic p 1 (cokernel s) at he
  rw [he, add_sub_cancel_left]
  rw [eulerCharacteristic, Finset.sum_range_succ, Finset.sum_range_succ]
  let : Subsingleton (cohomology (cokernel s) 1) := ⟨fun x y =>
    (L.cokernel_ext_zero hd.le s hs 0 x).trans (L.cokernel_ext_zero hd.le s hs 0 y).symm⟩
  have hz : cohomologyDimension p (cokernel s) 1 = 0 := by
    let := Module.compHom (cohomology (cokernel s) 1) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  simp only [Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    hz, Nat.cast_zero, mul_zero, add_zero]
  rw [cohomologyDimension_zero]
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveDegreePositive
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma flasque_zero_of_global_subsingleton (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)]
    [Subsingleton Γ(M,⊤)] : IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext U x
  have hs : Function.Surjective (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Presheaf.IsFlasque.epi
        (F := ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)
        (homOfLE (le_top : U ≤ ⊤)).op)
  let : Subsingleton Γ(M,U) := ⟨fun x y => by
    obtain ⟨a,rfl⟩ := hs x
    obtain ⟨b,rfl⟩ := hs y
    exact congrArg _ (Subsingleton.elim a b)⟩
  exact Subsingleton.elim _ _

variable [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem projective_section_positive_degree_s01_oai (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (hz : isoOpen s ≠ ⊤) :
    0 < eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  let := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let := Module.compHom (cohomology (cokernel s) 0) (baseScalars p)
  let := projective_section_cokernel_finite p hd a ha L s hs 0
  let : Module.Finite ℂ Γ(cokernel s,⊤) :=
    Module.Finite.of_surjective (cohomologyZeroSections p (cokernel s)).toLinearMap
      (cohomologyZeroSections p (cokernel s)).surjective
  rw [projective_section_euler_difference p hd a ha L s hs]
  have ht : Nontrivial Γ(cokernel s,⊤) := by
    by_contra hn
    let : Subsingleton Γ(cokernel s,⊤) := not_nontrivial_iff_subsingleton.mp hn
    have hzero := @flasque_zero_of_global_subsingleton X (cokernel s)
      (L.cokernel_flasque hd.le s hs) inferInstance
    let := CategoryTheory.Preadditive.epi_of_isZero_cokernel s hzero
    let : Mono s := L.mono_section s hs
    let : IsIso s := isIso_of_mono_of_epi s
    apply hz
    apply top_unique
    intro x _
    exact (mem_isoOpen_iff s x).mpr ⟨⊤,trivial,inferInstance⟩
  let := ht
  exact_mod_cast Module.finrank_pos

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01_oai := @OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01_oai
